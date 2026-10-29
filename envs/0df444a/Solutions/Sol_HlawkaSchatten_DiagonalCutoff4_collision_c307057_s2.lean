-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c307057_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:13:40.424215+00:00
-- url     : https://prove2.me/submissions/231c0f38-9df7-48ec-8df5-3089fbfd96c7

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
theorem collision_support_c307057_s2_s2_0 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-3210735187/10000000000 : ℝ)*x 0 + (3208169929/10000000000 : ℝ)*x 1 + (19715447/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3210735187/10000000000 : ℝ)^17 ≤ (707360012821/3125000000000 : ℝ)^13 := by
    have hnat : (3210735187 : ℕ)^17*3125000000000^13 ≤ 707360012821^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3210735187 10000000000 707360012821 3125000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3208169929/10000000000 : ℝ)^17 ≤ (11305936891103/50000000000000 : ℝ)^13 := by
    have hnat : (3208169929 : ℕ)^17*50000000000000^13 ≤ 11305936891103^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3208169929 10000000000 11305936891103 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (19715447/31250000 : ℝ)^17 ≤ (427754732761/781250000000 : ℝ)^13 := by
    have hnat : (19715447 : ℕ)^17*781250000000^13 ≤ 427754732761^13*31250000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19715447 31250000 427754732761 781250000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3210735187/10000000000 : ℝ), (3208169929/10000000000 : ℝ), (19715447/31250000 : ℝ)] ![(707360012821/3125000000000 : ℝ), (11305936891103/50000000000000 : ℝ), (427754732761/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3210735187/10000000000 : ℝ)|^17 ≤ (707360012821/3125000000000 : ℝ)^13
        have hw : |(-3210735187/10000000000 : ℝ)|=(3210735187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3208169929/10000000000 : ℝ)|^17 ≤ (11305936891103/50000000000000 : ℝ)^13
        have hw : |(3208169929/10000000000 : ℝ)|=(3208169929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(19715447/31250000 : ℝ)|^17 ≤ (427754732761/781250000000 : ℝ)^13
        have hw : |(19715447/31250000 : ℝ)|=(19715447/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307057_s2_s2_1 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3208962407/10000000000 : ℝ)*x 0 + (-641279713/2000000000 : ℝ)*x 1 + (6311821289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3208962407/10000000000 : ℝ)^17 ≤ (2261917824827/10000000000000 : ℝ)^13 := by
    have hnat : (3208962407 : ℕ)^17*10000000000000^13 ≤ 2261917824827^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3208962407 10000000000 2261917824827 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (641279713/2000000000 : ℝ)^17 ≤ (4519109737761/20000000000000 : ℝ)^13 := by
    have hnat : (641279713 : ℕ)^17*20000000000000^13 ≤ 4519109737761^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      641279713 2000000000 4519109737761 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6311821289/10000000000 : ℝ)^17 ≤ (54785273044883/100000000000000 : ℝ)^13 := by
    have hnat : (6311821289 : ℕ)^17*100000000000000^13 ≤ 54785273044883^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6311821289 10000000000 54785273044883 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3208962407/10000000000 : ℝ), (-641279713/2000000000 : ℝ), (6311821289/10000000000 : ℝ)] ![(2261917824827/10000000000000 : ℝ), (4519109737761/20000000000000 : ℝ), (54785273044883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3208962407/10000000000 : ℝ)|^17 ≤ (2261917824827/10000000000000 : ℝ)^13
        have hw : |(3208962407/10000000000 : ℝ)|=(3208962407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-641279713/2000000000 : ℝ)|^17 ≤ (4519109737761/20000000000000 : ℝ)^13
        have hw : |(-641279713/2000000000 : ℝ)|=(641279713/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6311821289/10000000000 : ℝ)|^17 ≤ (54785273044883/100000000000000 : ℝ)^13
        have hw : |(6311821289/10000000000 : ℝ)|=(6311821289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307057_s2_s2_6 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2381767607/5000000000 : ℝ)*x 0 + (4766565917/10000000000 : ℝ)*x 1 + (3372150789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2381767607/5000000000 : ℝ)^17 ≤ (947917926379/2500000000000 : ℝ)^13 := by
    have hnat : (2381767607 : ℕ)^17*2500000000000^13 ≤ 947917926379^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2381767607 5000000000 947917926379 2500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4766565917/10000000000 : ℝ)^17 ≤ (7589653315621/20000000000000 : ℝ)^13 := by
    have hnat : (4766565917 : ℕ)^17*20000000000000^13 ≤ 7589653315621^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4766565917 10000000000 7589653315621 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3372150789/10000000000 : ℝ)^17 ≤ (24135016354953/100000000000000 : ℝ)^13 := by
    have hnat : (3372150789 : ℕ)^17*100000000000000^13 ≤ 24135016354953^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3372150789 10000000000 24135016354953 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2381767607/5000000000 : ℝ), (4766565917/10000000000 : ℝ), (3372150789/10000000000 : ℝ)] ![(947917926379/2500000000000 : ℝ), (7589653315621/20000000000000 : ℝ), (24135016354953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2381767607/5000000000 : ℝ)|^17 ≤ (947917926379/2500000000000 : ℝ)^13
        have hw : |(2381767607/5000000000 : ℝ)|=(2381767607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4766565917/10000000000 : ℝ)|^17 ≤ (7589653315621/20000000000000 : ℝ)^13
        have hw : |(4766565917/10000000000 : ℝ)|=(4766565917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3372150789/10000000000 : ℝ)|^17 ≤ (24135016354953/100000000000000 : ℝ)^13
        have hw : |(3372150789/10000000000 : ℝ)|=(3372150789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307057_s2_s2_7 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2668270563/10000000000 : ℝ)*x 0 + (2241240417/10000000000 : ℝ)*x 1 + (1863237523/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2668270563/10000000000 : ℝ)^17 ≤ (8884954587799/50000000000000 : ℝ)^13 := by
    have hnat : (2668270563 : ℕ)^17*50000000000000^13 ≤ 8884954587799^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2668270563 10000000000 8884954587799 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2241240417/10000000000 : ℝ)^17 ≤ (7073082780799/50000000000000 : ℝ)^13 := by
    have hnat : (2241240417 : ℕ)^17*50000000000000^13 ≤ 7073082780799^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241240417 10000000000 7073082780799 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1863237523/2500000000 : ℝ)^17 ≤ (3404196262813/5000000000000 : ℝ)^13 := by
    have hnat : (1863237523 : ℕ)^17*5000000000000^13 ≤ 3404196262813^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1863237523 2500000000 3404196262813 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2668270563/10000000000 : ℝ), (2241240417/10000000000 : ℝ), (1863237523/2500000000 : ℝ)] ![(8884954587799/50000000000000 : ℝ), (7073082780799/50000000000000 : ℝ), (3404196262813/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2668270563/10000000000 : ℝ)|^17 ≤ (8884954587799/50000000000000 : ℝ)^13
        have hw : |(-2668270563/10000000000 : ℝ)|=(2668270563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2241240417/10000000000 : ℝ)|^17 ≤ (7073082780799/50000000000000 : ℝ)^13
        have hw : |(2241240417/10000000000 : ℝ)|=(2241240417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1863237523/2500000000 : ℝ)|^17 ≤ (3404196262813/5000000000000 : ℝ)^13
        have hw : |(1863237523/2500000000 : ℝ)|=(1863237523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307057_s2_s2_8 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2665787851/10000000000 : ℝ)*x 0 + (-1119577519/5000000000 : ℝ)*x 1 + (7456200203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2665787851/10000000000 : ℝ)^17 ≤ (3549658139973/20000000000000 : ℝ)^13 := by
    have hnat : (2665787851 : ℕ)^17*20000000000000^13 ≤ 3549658139973^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2665787851 10000000000 3549658139973 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1119577519/5000000000 : ℝ)^17 ≤ (1766119456099/12500000000000 : ℝ)^13 := by
    have hnat : (1119577519 : ℕ)^17*12500000000000^13 ≤ 1766119456099^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119577519 5000000000 1766119456099 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7456200203/10000000000 : ℝ)^17 ≤ (6812275363603/10000000000000 : ℝ)^13 := by
    have hnat : (7456200203 : ℕ)^17*10000000000000^13 ≤ 6812275363603^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7456200203 10000000000 6812275363603 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2665787851/10000000000 : ℝ), (-1119577519/5000000000 : ℝ), (7456200203/10000000000 : ℝ)] ![(3549658139973/20000000000000 : ℝ), (1766119456099/12500000000000 : ℝ), (6812275363603/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2665787851/10000000000 : ℝ)|^17 ≤ (3549658139973/20000000000000 : ℝ)^13
        have hw : |(2665787851/10000000000 : ℝ)|=(2665787851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1119577519/5000000000 : ℝ)|^17 ≤ (1766119456099/12500000000000 : ℝ)^13
        have hw : |(-1119577519/5000000000 : ℝ)|=(1119577519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7456200203/10000000000 : ℝ)|^17 ≤ (6812275363603/10000000000000 : ℝ)^13
        have hw : |(7456200203/10000000000 : ℝ)|=(7456200203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307057_s2_s2_9 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4395918263/10000000000 : ℝ)*x 0 + (7266356371/10000000000 : ℝ)*x 1 + (3743/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4395918263/10000000000 : ℝ)^17 ≤ (3413647861449/10000000000000 : ℝ)^13 := by
    have hnat : (4395918263 : ℕ)^17*10000000000000^13 ≤ 3413647861449^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4395918263 10000000000 3413647861449 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7266356371/10000000000 : ℝ)^17 ≤ (8232939424089/12500000000000 : ℝ)^13 := by
    have hnat : (7266356371 : ℕ)^17*12500000000000^13 ≤ 8232939424089^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7266356371 10000000000 8232939424089 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3743/1250000000 : ℝ)^17 ≤ (5980161/100000000000000 : ℝ)^13 := by
    have hnat : (3743 : ℕ)^17*100000000000000^13 ≤ 5980161^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3743 1250000000 5980161 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4395918263/10000000000 : ℝ), (7266356371/10000000000 : ℝ), (3743/1250000000 : ℝ)] ![(3413647861449/10000000000000 : ℝ), (8232939424089/12500000000000 : ℝ), (5980161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4395918263/10000000000 : ℝ)|^17 ≤ (3413647861449/10000000000000 : ℝ)^13
        have hw : |(4395918263/10000000000 : ℝ)|=(4395918263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7266356371/10000000000 : ℝ)|^17 ≤ (8232939424089/12500000000000 : ℝ)^13
        have hw : |(7266356371/10000000000 : ℝ)|=(7266356371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3743/1250000000 : ℝ)|^17 ≤ (5980161/100000000000000 : ℝ)^13
        have hw : |(3743/1250000000 : ℝ)|=(3743/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307057_s2_s2_12 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1981757907/5000000000 : ℝ)*x 0 + (6551604617/10000000000 : ℝ)*x 1 + (411865277/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1981757907/5000000000 : ℝ)^17 ≤ (29813508410719/100000000000000 : ℝ)^13 := by
    have hnat : (1981757907 : ℕ)^17*100000000000000^13 ≤ 29813508410719^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1981757907 5000000000 29813508410719 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6551604617/10000000000 : ℝ)^17 ≤ (57522701518319/100000000000000 : ℝ)^13 := by
    have hnat : (6551604617 : ℕ)^17*100000000000000^13 ≤ 57522701518319^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6551604617 10000000000 57522701518319 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (411865277/2000000000 : ℝ)^17 ≤ (50655160221/400000000000 : ℝ)^13 := by
    have hnat : (411865277 : ℕ)^17*400000000000^13 ≤ 50655160221^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411865277 2000000000 50655160221 400000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1981757907/5000000000 : ℝ), (6551604617/10000000000 : ℝ), (411865277/2000000000 : ℝ)] ![(29813508410719/100000000000000 : ℝ), (57522701518319/100000000000000 : ℝ), (50655160221/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1981757907/5000000000 : ℝ)|^17 ≤ (29813508410719/100000000000000 : ℝ)^13
        have hw : |(1981757907/5000000000 : ℝ)|=(1981757907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6551604617/10000000000 : ℝ)|^17 ≤ (57522701518319/100000000000000 : ℝ)^13
        have hw : |(6551604617/10000000000 : ℝ)|=(6551604617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(411865277/2000000000 : ℝ)|^17 ≤ (50655160221/400000000000 : ℝ)^13
        have hw : |(411865277/2000000000 : ℝ)|=(411865277/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307057_s2_s2_13 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-448778401/2000000000 : ℝ)*x 0 + (2665623587/10000000000 : ℝ)*x 1 + (3726523549/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (448778401/2000000000 : ℝ)^17 ≤ (14168055317757/100000000000000 : ℝ)^13 := by
    have hnat : (448778401 : ℕ)^17*100000000000000^13 ≤ 14168055317757^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448778401 2000000000 14168055317757 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2665623587/10000000000 : ℝ)^17 ≤ (8873430286121/50000000000000 : ℝ)^13 := by
    have hnat : (2665623587 : ℕ)^17*50000000000000^13 ≤ 8873430286121^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2665623587 10000000000 8873430286121 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3726523549/5000000000 : ℝ)^17 ≤ (68085084090741/100000000000000 : ℝ)^13 := by
    have hnat : (3726523549 : ℕ)^17*100000000000000^13 ≤ 68085084090741^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3726523549 5000000000 68085084090741 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-448778401/2000000000 : ℝ), (2665623587/10000000000 : ℝ), (3726523549/5000000000 : ℝ)] ![(14168055317757/100000000000000 : ℝ), (8873430286121/50000000000000 : ℝ), (68085084090741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-448778401/2000000000 : ℝ)|^17 ≤ (14168055317757/100000000000000 : ℝ)^13
        have hw : |(-448778401/2000000000 : ℝ)|=(448778401/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2665623587/10000000000 : ℝ)|^17 ≤ (8873430286121/50000000000000 : ℝ)^13
        have hw : |(2665623587/10000000000 : ℝ)|=(2665623587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3726523549/5000000000 : ℝ)|^17 ≤ (68085084090741/100000000000000 : ℝ)^13
        have hw : |(3726523549/5000000000 : ℝ)|=(3726523549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307057_s2_s2_14 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1120901769/5000000000 : ℝ)*x 0 + (-2663142599/10000000000 : ℝ)*x 1 + (7456298047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1120901769/5000000000 : ℝ)^17 ≤ (1768851706237/12500000000000 : ℝ)^13 := by
    have hnat : (1120901769 : ℕ)^17*12500000000000^13 ≤ 1768851706237^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120901769 5000000000 1768851706237 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2663142599/10000000000 : ℝ)^17 ≤ (17725263705777/100000000000000 : ℝ)^13 := by
    have hnat : (2663142599 : ℕ)^17*100000000000000^13 ≤ 17725263705777^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2663142599 10000000000 17725263705777 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7456298047/10000000000 : ℝ)^17 ≤ (68123922638097/100000000000000 : ℝ)^13 := by
    have hnat : (7456298047 : ℕ)^17*100000000000000^13 ≤ 68123922638097^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7456298047 10000000000 68123922638097 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1120901769/5000000000 : ℝ), (-2663142599/10000000000 : ℝ), (7456298047/10000000000 : ℝ)] ![(1768851706237/12500000000000 : ℝ), (17725263705777/100000000000000 : ℝ), (68123922638097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1120901769/5000000000 : ℝ)|^17 ≤ (1768851706237/12500000000000 : ℝ)^13
        have hw : |(1120901769/5000000000 : ℝ)|=(1120901769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2663142599/10000000000 : ℝ)|^17 ≤ (17725263705777/100000000000000 : ℝ)^13
        have hw : |(-2663142599/10000000000 : ℝ)|=(2663142599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7456298047/10000000000 : ℝ)|^17 ≤ (68123922638097/100000000000000 : ℝ)^13
        have hw : |(7456298047/10000000000 : ℝ)|=(7456298047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307057_s2_s2_15 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (7263110523/10000000000 : ℝ)*x 0 + (68745409/156250000 : ℝ)*x 1 + (2991/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7263110523/10000000000 : ℝ)^17 ≤ (65825044513569/100000000000000 : ℝ)^13 := by
    have hnat : (7263110523 : ℕ)^17*100000000000000^13 ≤ 65825044513569^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7263110523 10000000000 65825044513569 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (68745409/156250000 : ℝ)^17 ≤ (17087474752227/50000000000000 : ℝ)^13 := by
    have hnat : (68745409 : ℕ)^17*50000000000000^13 ≤ 17087474752227^13*156250000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68745409 156250000 17087474752227 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2991/1000000000 : ℝ)^17 ≤ (5971283/100000000000000 : ℝ)^13 := by
    have hnat : (2991 : ℕ)^17*100000000000000^13 ≤ 5971283^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2991 1000000000 5971283 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7263110523/10000000000 : ℝ), (68745409/156250000 : ℝ), (2991/1000000000 : ℝ)] ![(65825044513569/100000000000000 : ℝ), (17087474752227/50000000000000 : ℝ), (5971283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7263110523/10000000000 : ℝ)|^17 ≤ (65825044513569/100000000000000 : ℝ)^13
        have hw : |(7263110523/10000000000 : ℝ)|=(7263110523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(68745409/156250000 : ℝ)|^17 ≤ (17087474752227/50000000000000 : ℝ)^13
        have hw : |(68745409/156250000 : ℝ)|=(68745409/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2991/1000000000 : ℝ)|^17 ≤ (5971283/100000000000000 : ℝ)^13
        have hw : |(2991/1000000000 : ℝ)|=(2991/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307057_s2_s2_18 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3274353011/5000000000 : ℝ)*x 0 + (1983474039/5000000000 : ℝ)*x 1 + (205926571/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3274353011/5000000000 : ℝ)^17 ≤ (5748942367771/10000000000000 : ℝ)^13 := by
    have hnat : (3274353011 : ℕ)^17*10000000000000^13 ≤ 5748942367771^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3274353011 5000000000 5748942367771 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1983474039/5000000000 : ℝ)^17 ≤ (1492363708767/5000000000000 : ℝ)^13 := by
    have hnat : (1983474039 : ℕ)^17*5000000000000^13 ≤ 1492363708767^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1983474039 5000000000 1492363708767 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (205926571/1000000000 : ℝ)^17 ≤ (12663302131561/100000000000000 : ℝ)^13 := by
    have hnat : (205926571 : ℕ)^17*100000000000000^13 ≤ 12663302131561^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205926571 1000000000 12663302131561 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3274353011/5000000000 : ℝ), (1983474039/5000000000 : ℝ), (205926571/1000000000 : ℝ)] ![(5748942367771/10000000000000 : ℝ), (1492363708767/5000000000000 : ℝ), (12663302131561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3274353011/5000000000 : ℝ)|^17 ≤ (5748942367771/10000000000000 : ℝ)^13
        have hw : |(3274353011/5000000000 : ℝ)|=(3274353011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1983474039/5000000000 : ℝ)|^17 ≤ (1492363708767/5000000000000 : ℝ)^13
        have hw : |(1983474039/5000000000 : ℝ)|=(1983474039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(205926571/1000000000 : ℝ)|^17 ≤ (12663302131561/100000000000000 : ℝ)^13
        have hw : |(205926571/1000000000 : ℝ)|=(205926571/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307057_s2_s2_19 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1056483361/2500000000 : ℝ)*x 0 + (2309380637/10000000000 : ℝ)*x 1 + (3071106227/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056483361/2500000000 : ℝ)^17 ≤ (32420665896719/100000000000000 : ℝ)^13 := by
    have hnat : (1056483361 : ℕ)^17*100000000000000^13 ≤ 32420665896719^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056483361 2500000000 32420665896719 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2309380637/10000000000 : ℝ)^17 ≤ (7355598104737/50000000000000 : ℝ)^13 := by
    have hnat : (2309380637 : ℕ)^17*50000000000000^13 ≤ 7355598104737^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2309380637 10000000000 7355598104737 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3071106227/5000000000 : ℝ)^17 ≤ (52868137886413/100000000000000 : ℝ)^13 := by
    have hnat : (3071106227 : ℕ)^17*100000000000000^13 ≤ 52868137886413^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3071106227 5000000000 52868137886413 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1056483361/2500000000 : ℝ), (2309380637/10000000000 : ℝ), (3071106227/5000000000 : ℝ)] ![(32420665896719/100000000000000 : ℝ), (7355598104737/50000000000000 : ℝ), (52868137886413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1056483361/2500000000 : ℝ)|^17 ≤ (32420665896719/100000000000000 : ℝ)^13
        have hw : |(-1056483361/2500000000 : ℝ)|=(1056483361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2309380637/10000000000 : ℝ)|^17 ≤ (7355598104737/50000000000000 : ℝ)^13
        have hw : |(2309380637/10000000000 : ℝ)|=(2309380637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3071106227/5000000000 : ℝ)|^17 ≤ (52868137886413/100000000000000 : ℝ)^13
        have hw : |(3071106227/5000000000 : ℝ)|=(3071106227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307057_s2_s2_20 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1155222217/5000000000 : ℝ)*x 0 + (-4221763053/10000000000 : ℝ)*x 1 + (6145141437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1155222217/5000000000 : ℝ)^17 ≤ (1840007316551/12500000000000 : ℝ)^13 := by
    have hnat : (1155222217 : ℕ)^17*12500000000000^13 ≤ 1840007316551^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1155222217 5000000000 1840007316551 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4221763053/10000000000 : ℝ)^17 ≤ (16189416609481/50000000000000 : ℝ)^13 := by
    have hnat : (4221763053 : ℕ)^17*50000000000000^13 ≤ 16189416609481^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4221763053 10000000000 16189416609481 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6145141437/10000000000 : ℝ)^17 ≤ (6612638528593/12500000000000 : ℝ)^13 := by
    have hnat : (6145141437 : ℕ)^17*12500000000000^13 ≤ 6612638528593^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6145141437 10000000000 6612638528593 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1155222217/5000000000 : ℝ), (-4221763053/10000000000 : ℝ), (6145141437/10000000000 : ℝ)] ![(1840007316551/12500000000000 : ℝ), (16189416609481/50000000000000 : ℝ), (6612638528593/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1155222217/5000000000 : ℝ)|^17 ≤ (1840007316551/12500000000000 : ℝ)^13
        have hw : |(1155222217/5000000000 : ℝ)|=(1155222217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4221763053/10000000000 : ℝ)|^17 ≤ (16189416609481/50000000000000 : ℝ)^13
        have hw : |(-4221763053/10000000000 : ℝ)|=(4221763053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6145141437/10000000000 : ℝ)|^17 ≤ (6612638528593/12500000000000 : ℝ)^13
        have hw : |(6145141437/10000000000 : ℝ)|=(6145141437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307057_s2_s2_21 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6194923183/10000000000 : ℝ)*x 0 + (1113920639/2000000000 : ℝ)*x 1 + (-1499923/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6194923183/10000000000 : ℝ)^17 ≤ (53462218864371/100000000000000 : ℝ)^13 := by
    have hnat : (6194923183 : ℕ)^17*100000000000000^13 ≤ 53462218864371^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6194923183 10000000000 53462218864371 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1113920639/2000000000 : ℝ)^17 ≤ (4651749649269/10000000000000 : ℝ)^13 := by
    have hnat : (1113920639 : ℕ)^17*10000000000000^13 ≤ 4651749649269^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1113920639 2000000000 4651749649269 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1499923/1000000000 : ℝ)^17 ≤ (2535578851/12500000000000 : ℝ)^13 := by
    have hnat : (1499923 : ℕ)^17*12500000000000^13 ≤ 2535578851^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1499923 1000000000 2535578851 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6194923183/10000000000 : ℝ), (1113920639/2000000000 : ℝ), (-1499923/1000000000 : ℝ)] ![(53462218864371/100000000000000 : ℝ), (4651749649269/10000000000000 : ℝ), (2535578851/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6194923183/10000000000 : ℝ)|^17 ≤ (53462218864371/100000000000000 : ℝ)^13
        have hw : |(6194923183/10000000000 : ℝ)|=(6194923183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1113920639/2000000000 : ℝ)|^17 ≤ (4651749649269/10000000000000 : ℝ)^13
        have hw : |(1113920639/2000000000 : ℝ)|=(1113920639/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1499923/1000000000 : ℝ)|^17 ≤ (2535578851/12500000000000 : ℝ)^13
        have hw : |(-1499923/1000000000 : ℝ)|=(1499923/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307057_s2_s2_25 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (144852441/400000000 : ℝ)*x 0 + (1113920639/2000000000 : ℝ)*x 1 + (459135191/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (144852441/400000000 : ℝ)^17 ≤ (26493066835429/100000000000000 : ℝ)^13 := by
    have hnat : (144852441 : ℕ)^17*100000000000000^13 ≤ 26493066835429^13*400000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      144852441 400000000 26493066835429 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1113920639/2000000000 : ℝ)^17 ≤ (4651749649269/10000000000000 : ℝ)^13 := by
    have hnat : (1113920639 : ℕ)^17*10000000000000^13 ≤ 4651749649269^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1113920639 2000000000 4651749649269 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (459135191/1250000000 : ℝ)^17 ≤ (13494718330411/50000000000000 : ℝ)^13 := by
    have hnat : (459135191 : ℕ)^17*50000000000000^13 ≤ 13494718330411^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      459135191 1250000000 13494718330411 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(144852441/400000000 : ℝ), (1113920639/2000000000 : ℝ), (459135191/1250000000 : ℝ)] ![(26493066835429/100000000000000 : ℝ), (4651749649269/10000000000000 : ℝ), (13494718330411/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(144852441/400000000 : ℝ)|^17 ≤ (26493066835429/100000000000000 : ℝ)^13
        have hw : |(144852441/400000000 : ℝ)|=(144852441/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1113920639/2000000000 : ℝ)|^17 ≤ (4651749649269/10000000000000 : ℝ)^13
        have hw : |(1113920639/2000000000 : ℝ)|=(1113920639/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(459135191/1250000000 : ℝ)|^17 ≤ (13494718330411/50000000000000 : ℝ)^13
        have hw : |(459135191/1250000000 : ℝ)|=(459135191/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c307057_s2 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((20873/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20873/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(83297/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(83297/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(36299/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(36299/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((69361/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(69361/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(69331/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(69331/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(3021/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(3021/20000 : ℝ)*X 1 2) := by
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
  have main1 : (4817/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4817/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4817/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4817/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (92559/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (20873/25000 : ℝ) ^ (135/32 : ℝ) ≤ (23356581338893015931/50000000000000000000 : ℝ) := by
    have hpowers : (20873/25000 : ℝ)^135 ≤ (23356581338893015931/50000000000000000000 : ℝ)^32 := by
      have hnat : (20873 : ℕ)^135*50000000000000000000^32 ≤ 23356581338893015931^32*25000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20873 25000 23356581338893015931 50000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20873/25000 : ℝ)) (X := (23356581338893015931/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s2_corner0a : (73356581338893015931/50000000000000000000 : ℝ) ≤ (1368892519717889/1250000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (73356581338893015931/50000000000000000000 : ℝ)^32 ≤ (1368892519717889/1250000000000000 : ℝ)^135 := by
      have hnat : (73356581338893015931 : ℕ)^32*1250000000000000^135 ≤ 1368892519717889^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        73356581338893015931 50000000000000000000 1368892519717889 1250000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1368892519717889/1250000000000000 : ℝ)) (X := (73356581338893015931/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s2_corner0b : (48356581338893015931/25000000000000000000 : ℝ) ≤ (5846349964262959/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (48356581338893015931/25000000000000000000 : ℝ)^32 ≤ (5846349964262959/5000000000000000 : ℝ)^135 := by
      have hnat : (48356581338893015931 : ℕ)^32*5000000000000000^135 ≤ 5846349964262959^135*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        48356581338893015931 25000000000000000000 5846349964262959 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5846349964262959/5000000000000000 : ℝ)) (X := (48356581338893015931/25000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(118892519717889/1043650000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(370779885391403/4174600000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (20873/25000 : ℝ)) (alpha := (118892519717889/1043650000000000 : ℝ)) (beta := (370779885391403/4174600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (20873/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(118892519717889/1043650000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(370779885391403/4174600000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (83297/100000 : ℝ) ^ (135/32 : ℝ) ≤ (46254619597667662033/100000000000000000000 : ℝ) := by
    have hpowers : (83297/100000 : ℝ)^135 ≤ (46254619597667662033/100000000000000000000 : ℝ)^32 := by
      have hnat : (83297 : ℕ)^135*100000000000000000000^32 ≤ 46254619597667662033^32*100000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        83297 100000 46254619597667662033 100000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (83297/100000 : ℝ)) (X := (46254619597667662033/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s2_corner1a : (146254619597667662033/100000000000000000000 : ℝ) ≤ (2188603474154923/2000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (146254619597667662033/100000000000000000000 : ℝ)^32 ≤ (2188603474154923/2000000000000000 : ℝ)^135 := by
      have hnat : (146254619597667662033 : ℕ)^32*2000000000000000^135 ≤ 2188603474154923^135*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        146254619597667662033 100000000000000000000 2188603474154923 2000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2188603474154923/2000000000000000 : ℝ)) (X := (146254619597667662033/100000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s2_corner1b : (96254619597667662033/50000000000000000000 : ℝ) ≤ (11679535180050349/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (96254619597667662033/50000000000000000000 : ℝ)^32 ≤ (11679535180050349/10000000000000000 : ℝ)^135 := by
      have hnat : (96254619597667662033 : ℕ)^32*10000000000000000^135 ≤ 11679535180050349^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        96254619597667662033 50000000000000000000 11679535180050349 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11679535180050349/10000000000000000 : ℝ)) (X := (96254619597667662033/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(188603474154923/1665940000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(368258904637867/4164850000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (83297/100000 : ℝ)) (alpha := (188603474154923/1665940000000000 : ℝ)) (beta := (368258904637867/4164850000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (83297/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(188603474154923/1665940000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(368258904637867/4164850000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (36299/100000 : ℝ) ^ (135/32 : ℝ) ≤ (1390931044673898621/100000000000000000000 : ℝ) := by
    have hpowers : (36299/100000 : ℝ)^135 ≤ (1390931044673898621/100000000000000000000 : ℝ)^32 := by
      have hnat : (36299 : ℕ)^135*100000000000000000000^32 ≤ 1390931044673898621^32*100000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        36299 100000 1390931044673898621 100000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (36299/100000 : ℝ)) (X := (1390931044673898621/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s2_corner2a : (101390931044673898621/100000000000000000000 : ℝ) ≤ (10032796689000821/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (101390931044673898621/100000000000000000000 : ℝ)^32 ≤ (10032796689000821/10000000000000000 : ℝ)^135 := by
      have hnat : (101390931044673898621 : ℕ)^32*10000000000000000^135 ≤ 10032796689000821^135*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101390931044673898621 100000000000000000000 10032796689000821 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10032796689000821/10000000000000000 : ℝ)) (X := (101390931044673898621/100000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s2_corner2b : (51390931044673898621/50000000000000000000 : ℝ) ≤ (629078242516277/625000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (51390931044673898621/50000000000000000000 : ℝ)^32 ≤ (629078242516277/625000000000000 : ℝ)^135 := by
      have hnat : (51390931044673898621 : ℕ)^32*625000000000000^135 ≤ 629078242516277^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51390931044673898621 50000000000000000000 629078242516277 625000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (629078242516277/625000000000000 : ℝ)) (X := (51390931044673898621/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(32796689000821/3629900000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(32455191259611/3629900000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (36299/100000 : ℝ)) (alpha := (32796689000821/3629900000000000 : ℝ)) (beta := (32455191259611/3629900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (36299/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(32796689000821/3629900000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(32455191259611/3629900000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-3210735187/10000000000 : ℝ)*X 0 0+(3208169929/10000000000 : ℝ)*X 0 1+(19715447/31250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((3208962407/10000000000 : ℝ)*X 1 0+(-641279713/2000000000 : ℝ)*X 1 1+(6311821289/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((2381767607/5000000000 : ℝ)*X 0 0+(4766565917/10000000000 : ℝ)*X 0 1+(3372150789/10000000000 : ℝ)*X 0 2+(2381767607/5000000000 : ℝ)*X 1 0+(4766565917/10000000000 : ℝ)*X 1 1+(3372150789/10000000000 : ℝ)*X 1 2+(2381767607/5000000000 : ℝ)*X 2 0+(4766565917/10000000000 : ℝ)*X 2 1+(3372150789/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-2668270563/10000000000 : ℝ)*X 0 0+(2241240417/10000000000 : ℝ)*X 0 1+(1863237523/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((2665787851/10000000000 : ℝ)*X 1 0+(-1119577519/5000000000 : ℝ)*X 1 1+(7456200203/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((4395918263/10000000000 : ℝ)*X 2 0+(7266356371/10000000000 : ℝ)*X 2 1+(3743/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_12 : ((1981757907/5000000000 : ℝ)*X 0 0+(6551604617/10000000000 : ℝ)*X 0 1+(411865277/2000000000 : ℝ)*X 0 2+(1981757907/5000000000 : ℝ)*X 1 0+(6551604617/10000000000 : ℝ)*X 1 1+(411865277/2000000000 : ℝ)*X 1 2+(1981757907/5000000000 : ℝ)*X 2 0+(6551604617/10000000000 : ℝ)*X 2 1+(411865277/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s2_s2_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((-448778401/2000000000 : ℝ)*X 0 0+(2665623587/10000000000 : ℝ)*X 0 1+(3726523549/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s2_s2_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((1120901769/5000000000 : ℝ)*X 1 0+(-2663142599/10000000000 : ℝ)*X 1 1+(7456298047/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s2_s2_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((7263110523/10000000000 : ℝ)*X 2 0+(68745409/156250000 : ℝ)*X 2 1+(2991/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s2_s2_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_18 : ((3274353011/5000000000 : ℝ)*X 0 0+(1983474039/5000000000 : ℝ)*X 0 1+(205926571/1000000000 : ℝ)*X 0 2+(3274353011/5000000000 : ℝ)*X 1 0+(1983474039/5000000000 : ℝ)*X 1 1+(205926571/1000000000 : ℝ)*X 1 2+(3274353011/5000000000 : ℝ)*X 2 0+(1983474039/5000000000 : ℝ)*X 2 1+(205926571/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s2_s2_18 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_19 : ((-1056483361/2500000000 : ℝ)*X 0 0+(2309380637/10000000000 : ℝ)*X 0 1+(3071106227/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s2_s2_19 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((1155222217/5000000000 : ℝ)*X 1 0+(-4221763053/10000000000 : ℝ)*X 1 1+(6145141437/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s2_s2_20 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((6194923183/10000000000 : ℝ)*X 2 0+(1113920639/2000000000 : ℝ)*X 2 1+(-1499923/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s2_s2_21 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_25 : ((144852441/400000000 : ℝ)*X 0 0+(1113920639/2000000000 : ℝ)*X 0 1+(459135191/1250000000 : ℝ)*X 0 2+(144852441/400000000 : ℝ)*X 1 0+(1113920639/2000000000 : ℝ)*X 1 1+(459135191/1250000000 : ℝ)*X 1 2+(144852441/400000000 : ℝ)*X 2 0+(1113920639/2000000000 : ℝ)*X 2 1+(459135191/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s2_s2_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((69361/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(69361/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (14006849778994202056781487/947086283750000000000000000000 : ℝ) := by norm_num
    linear_combination (321213503717/500000000000 : ℝ)*(base7) + (358344123637/500000000000 : ℝ)*(base59) + (131943764809/500000000000 : ℝ)*(base60) + (118234088633/40000000000 : ℝ)*(major_s2_0) + (118234088633/40000000000 : ℝ)*(major_s2_1) + (118234088633/40000000000 : ℝ)*(major_s2_2) + (830789/125000000000 : ℝ)*(sp_s2_0) + (190399/31250000000 : ℝ)*(sp_s2_1) + (3613651569531/1000000000000 : ℝ)*(sp_s2_7) + (722754386897/200000000000 : ℝ)*(sp_s2_8) + (3613778027253/1000000000000 : ℝ)*(sp_s2_9) + (158995001563/62500000000 : ℝ)*(sp_s2_12) + (11981141/100000000000 : ℝ)*(sp_s2_13) + (6223903/500000000000 : ℝ)*(sp_s2_25) + (1901505465381/1000000000000 : ℝ)*(f.failure) + (3613778027253/1000000000000 : ℝ)*(f.sum) + (4726013958138896703/6047195606000000000000000000000 : ℝ)*base63 + (431821271979313/725980000000000000000000000 : ℝ)*base64 + (60591467019493/166594000000000000000000000 : ℝ)*base66 + (236377399625681/725980000000000000000000000 : ℝ)*base69 + (2751486179824342689/15153380540000000000000000000000 : ℝ)*base70 + (66536399293113/166984000000000000000000000 : ℝ)*base72 + (345683824074919/1665940000000000000000000000 : ℝ)*base74 + (8171781221813/52182500000000000000000000 : ℝ)*base76 + (1712189872717222911/13909266248000000000000000000000 : ℝ)*base79 + (5711/12500000000000000 : ℝ)*base87 + (5711/12500000000000000 : ℝ)*base89 + (5711/12500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(69331/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(69331/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (45700881213340404233024953090713/6311155694201900000000000000000000000 : ℝ) := by norm_num
    linear_combination (642377310631/1000000000000 : ℝ)*(base7) + (33813/62500000000 : ℝ)*(base40) + (179091690717/250000000000 : ℝ)*(base59) + (452926436387/1000000000000 : ℝ)*(base60) + (2955251857889/1000000000000 : ℝ)*(major_s2_0) + (2955251857889/1000000000000 : ℝ)*(major_s2_1) + (2955251857889/1000000000000 : ℝ)*(major_s2_2) + (6702213/1000000000000 : ℝ)*(sp_s2_1) + (525737/250000000000 : ℝ)*(sp_s2_6) + (6022699/100000000000 : ℝ)*(sp_s2_7) + (3612936477769/1000000000000 : ℝ)*(sp_s2_13) + (1806495001273/500000000000 : ℝ)*(sp_s2_14) + (3612996704759/1000000000000 : ℝ)*(sp_s2_15) + (2543494461639/1000000000000 : ℝ)*(sp_s2_18) + (475279813489/250000000000 : ℝ)*(f.failure) + (3612996704759/1000000000000 : ℝ)*(f.sum) + (62668888786676722889/151179890150000000000000000000000 : ℝ)*base62 + (1026572328400269/3629900000000000000000000000 : ℝ)*base64 + (1187698106151677/4164850000000000000000000000 : ℝ)*base66 + (2056833565120179/3629900000000000000000000000 : ℝ)*base68 + (6915726300197102239/75766902700000000000000000000000 : ℝ)*base70 + (1416615252893993/4174600000000000000000000000 : ℝ)*base72 + (460046229957331/1665940000000000000000000000 : ℝ)*base74 + (218094777672509/1043650000000000000000000000 : ℝ)*base76 + (11224525512667502709/69546331240000000000000000000000 : ℝ)*base78 + (817/1562500000000000 : ℝ)*base87 + (817/1562500000000000 : ℝ)*base89 + (817/1562500000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(3021/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(3021/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (28188300099725333637134373277677/6311155694201900000000000000000000000 : ℝ) := by norm_num
    linear_combination (308839365147/1000000000000 : ℝ)*(base5) + (2316177/1000000000000 : ℝ)*(base16) + (1806437/1000000000000 : ℝ)*(base40) + (7661/20000000000 : ℝ)*(base50) + (810249237/1000000000 : ℝ)*(base59) + (1997917391907/1000000000000 : ℝ)*(major_s2_0) + (1997917391907/1000000000000 : ℝ)*(major_s2_1) + (1997917391907/1000000000000 : ℝ)*(major_s2_2) + (18123143/250000000000 : ℝ)*(sp_s2_6) + (71399063/1000000000000 : ℝ)*(sp_s2_12) + (271056916043/100000000000 : ℝ)*(sp_s2_19) + (2710566844253/1000000000000 : ℝ)*(sp_s2_20) + (3019408525577/1000000000000 : ℝ)*(sp_s2_21) + (244070219447/250000000000 : ℝ)*(sp_s2_25) + (128526413457/100000000000 : ℝ)*(f.failure) + (271056916043/100000000000 : ℝ)*(f.sum) + (35426445894167064609/75589945075000000000000000000000 : ℝ)*base63 + (128312389026473/3629900000000000000000000000 : ℝ)*base65 + (390168679527713/2082425000000000000000000000 : ℝ)*base66 + (622937074180273/3629900000000000000000000000 : ℝ)*base69 + (17897928195931771787/75766902700000000000000000000000 : ℝ)*base70 + (399610657786959/4174600000000000000000000000 : ℝ)*base72 + (1265264450235447/1665940000000000000000000000 : ℝ)*base75 + (385733564291273/1043650000000000000000000000 : ℝ)*base77 + (27401535704920685651/69546331240000000000000000000000 : ℝ)*base78 + (783/1250000000000000 : ℝ)*base86 + (783/1250000000000000 : ℝ)*base88 + (783/1250000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((20873/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20873/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(83297/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(83297/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(36299/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(36299/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((69361/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(69361/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(69331/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(69331/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(3021/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(3021/20000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c307057_s2 p hpa hpb X hX hprev1

#print axioms solution
