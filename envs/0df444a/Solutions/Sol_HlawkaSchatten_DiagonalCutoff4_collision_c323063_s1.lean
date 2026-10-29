-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c323063_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:53:30.926242+00:00
-- url     : https://prove2.me/submissions/28f2480d-92da-4e37-84f9-7af4b686eecb

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
theorem collision_support_c323063_s1_s1_0 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-932754347/10000000000 : ℝ)*x 0 + (5427306873/10000000000 : ℝ)*x 1 + (219536091/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (932754347/10000000000 : ℝ)^21 ≤ (5337766642237/100000000000000 : ℝ)^17 := by
    have hnat : (932754347 : ℕ)^21*100000000000000^17 ≤ 5337766642237^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      932754347 10000000000 5337766642237 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5427306873/10000000000 : ℝ)^21 ≤ (9400774592299/20000000000000 : ℝ)^17 := by
    have hnat : (5427306873 : ℕ)^21*20000000000000^17 ≤ 9400774592299^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427306873 10000000000 9400774592299 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219536091/400000000 : ℝ)^21 ≤ (47658360385727/100000000000000 : ℝ)^17 := by
    have hnat : (219536091 : ℕ)^21*100000000000000^17 ≤ 47658360385727^17*400000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219536091 400000000 47658360385727 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-932754347/10000000000 : ℝ), (5427306873/10000000000 : ℝ), (219536091/400000000 : ℝ)] ![(5337766642237/100000000000000 : ℝ), (9400774592299/20000000000000 : ℝ), (47658360385727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-932754347/10000000000 : ℝ)|^21 ≤ (5337766642237/100000000000000 : ℝ)^17
        have hw : |(-932754347/10000000000 : ℝ)|=(932754347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5427306873/10000000000 : ℝ)|^21 ≤ (9400774592299/20000000000000 : ℝ)^17
        have hw : |(5427306873/10000000000 : ℝ)|=(5427306873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(219536091/400000000 : ℝ)|^21 ≤ (47658360385727/100000000000000 : ℝ)^17
        have hw : |(219536091/400000000 : ℝ)|=(219536091/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s1_s1_1 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (542707161/1000000000 : ℝ)*x 0 + (-929598959/10000000000 : ℝ)*x 1 + (5490715441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542707161/1000000000 : ℝ)^21 ≤ (47001356031973/100000000000000 : ℝ)^17 := by
    have hnat : (542707161 : ℕ)^21*100000000000000^17 ≤ 47001356031973^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542707161 1000000000 47001356031973 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (929598959/10000000000 : ℝ)^21 ≤ (2657734924203/50000000000000 : ℝ)^17 := by
    have hnat : (929598959 : ℕ)^21*50000000000000^17 ≤ 2657734924203^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      929598959 10000000000 2657734924203 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5490715441/10000000000 : ℝ)^21 ≤ (2910349982/6103515625 : ℝ)^17 := by
    have hnat : (5490715441 : ℕ)^21*6103515625^17 ≤ 2910349982^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490715441 10000000000 2910349982 6103515625 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(542707161/1000000000 : ℝ), (-929598959/10000000000 : ℝ), (5490715441/10000000000 : ℝ)] ![(47001356031973/100000000000000 : ℝ), (2657734924203/50000000000000 : ℝ), (2910349982/6103515625 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(542707161/1000000000 : ℝ)|^21 ≤ (47001356031973/100000000000000 : ℝ)^17
        have hw : |(542707161/1000000000 : ℝ)|=(542707161/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-929598959/10000000000 : ℝ)|^21 ≤ (2657734924203/50000000000000 : ℝ)^17
        have hw : |(-929598959/10000000000 : ℝ)|=(929598959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5490715441/10000000000 : ℝ)|^21 ≤ (2910349982/6103515625 : ℝ)^17
        have hw : |(5490715441/10000000000 : ℝ)|=(5490715441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s1_s1_2 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (545929377/1000000000 : ℝ)*x 0 + (548156509/1000000000 : ℝ)*x 1 + (-894498183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545929377/1000000000 : ℝ)^21 ≤ (47346319140583/100000000000000 : ℝ)^17 := by
    have hnat : (545929377 : ℕ)^21*100000000000000^17 ≤ 47346319140583^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545929377 1000000000 47346319140583 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (548156509/1000000000 : ℝ)^21 ≤ (47585031144493/100000000000000 : ℝ)^17 := by
    have hnat : (548156509 : ℕ)^21*100000000000000^17 ≤ 47585031144493^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548156509 1000000000 47585031144493 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (894498183/10000000000 : ℝ)^21 ≤ (5068649697539/100000000000000 : ℝ)^17 := by
    have hnat : (894498183 : ℕ)^21*100000000000000^17 ≤ 5068649697539^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894498183 10000000000 5068649697539 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(545929377/1000000000 : ℝ), (548156509/1000000000 : ℝ), (-894498183/10000000000 : ℝ)] ![(47346319140583/100000000000000 : ℝ), (47585031144493/100000000000000 : ℝ), (5068649697539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(545929377/1000000000 : ℝ)|^21 ≤ (47346319140583/100000000000000 : ℝ)^17
        have hw : |(545929377/1000000000 : ℝ)|=(545929377/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(548156509/1000000000 : ℝ)|^21 ≤ (47585031144493/100000000000000 : ℝ)^17
        have hw : |(548156509/1000000000 : ℝ)|=(548156509/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-894498183/10000000000 : ℝ)|^21 ≤ (5068649697539/100000000000000 : ℝ)^17
        have hw : |(-894498183/10000000000 : ℝ)|=(894498183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s1_s1_6 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (836377649/2000000000 : ℝ)*x 0 + (4124641969/10000000000 : ℝ)*x 1 + (4020735463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (836377649/2000000000 : ℝ)^21 ≤ (266117608151/781250000000 : ℝ)^17 := by
    have hnat : (836377649 : ℕ)^21*781250000000^17 ≤ 266117608151^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      836377649 2000000000 266117608151 781250000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4124641969/10000000000 : ℝ)^21 ≤ (8371994102717/25000000000000 : ℝ)^17 := by
    have hnat : (4124641969 : ℕ)^21*25000000000000^17 ≤ 8371994102717^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4124641969 10000000000 8371994102717 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4020735463/10000000000 : ℝ)^21 ≤ (32448969729071/100000000000000 : ℝ)^17 := by
    have hnat : (4020735463 : ℕ)^21*100000000000000^17 ≤ 32448969729071^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4020735463 10000000000 32448969729071 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(836377649/2000000000 : ℝ), (4124641969/10000000000 : ℝ), (4020735463/10000000000 : ℝ)] ![(266117608151/781250000000 : ℝ), (8371994102717/25000000000000 : ℝ), (32448969729071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(836377649/2000000000 : ℝ)|^21 ≤ (266117608151/781250000000 : ℝ)^17
        have hw : |(836377649/2000000000 : ℝ)|=(836377649/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4124641969/10000000000 : ℝ)|^21 ≤ (8371994102717/25000000000000 : ℝ)^17
        have hw : |(4124641969/10000000000 : ℝ)|=(4124641969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4020735463/10000000000 : ℝ)|^21 ≤ (32448969729071/100000000000000 : ℝ)^17
        have hw : |(4020735463/10000000000 : ℝ)|=(4020735463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s1_s1_7 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-855919057/10000000000 : ℝ)*x 0 + (448236573/1000000000 : ℝ)*x 1 + (6442065993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (855919057/10000000000 : ℝ)^21 ≤ (4799990625801/100000000000000 : ℝ)^17 := by
    have hnat : (855919057 : ℕ)^21*100000000000000^17 ≤ 4799990625801^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      855919057 10000000000 4799990625801 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (448236573/1000000000 : ℝ)^21 ≤ (37111542367551/100000000000000 : ℝ)^17 := by
    have hnat : (448236573 : ℕ)^21*100000000000000^17 ≤ 37111542367551^17*1000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448236573 1000000000 37111542367551 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6442065993/10000000000 : ℝ)^21 ≤ (29044233496487/50000000000000 : ℝ)^17 := by
    have hnat : (6442065993 : ℕ)^21*50000000000000^17 ≤ 29044233496487^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6442065993 10000000000 29044233496487 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-855919057/10000000000 : ℝ), (448236573/1000000000 : ℝ), (6442065993/10000000000 : ℝ)] ![(4799990625801/100000000000000 : ℝ), (37111542367551/100000000000000 : ℝ), (29044233496487/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-855919057/10000000000 : ℝ)|^21 ≤ (4799990625801/100000000000000 : ℝ)^17
        have hw : |(-855919057/10000000000 : ℝ)|=(855919057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(448236573/1000000000 : ℝ)|^21 ≤ (37111542367551/100000000000000 : ℝ)^17
        have hw : |(448236573/1000000000 : ℝ)|=(448236573/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6442065993/10000000000 : ℝ)|^21 ≤ (29044233496487/50000000000000 : ℝ)^17
        have hw : |(6442065993/10000000000 : ℝ)|=(6442065993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s1_s1_8 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (48717727/100000000 : ℝ)*x 0 + (-190660423/10000000000 : ℝ)*x 1 + (6444445997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (48717727/100000000 : ℝ)^21 ≤ (4113406308287/10000000000000 : ℝ)^17 := by
    have hnat : (48717727 : ℕ)^21*10000000000000^17 ≤ 4113406308287^17*100000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48717727 100000000 4113406308287 10000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (190660423/10000000000 : ℝ)^21 ≤ (375479283621/50000000000000 : ℝ)^17 := by
    have hnat : (190660423 : ℕ)^21*50000000000000^17 ≤ 375479283621^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190660423 10000000000 375479283621 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6444445997/10000000000 : ℝ)^21 ≤ (58114978333021/100000000000000 : ℝ)^17 := by
    have hnat : (6444445997 : ℕ)^21*100000000000000^17 ≤ 58114978333021^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6444445997 10000000000 58114978333021 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(48717727/100000000 : ℝ), (-190660423/10000000000 : ℝ), (6444445997/10000000000 : ℝ)] ![(4113406308287/10000000000000 : ℝ), (375479283621/50000000000000 : ℝ), (58114978333021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(48717727/100000000 : ℝ)|^21 ≤ (4113406308287/10000000000000 : ℝ)^17
        have hw : |(48717727/100000000 : ℝ)|=(48717727/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-190660423/10000000000 : ℝ)|^21 ≤ (375479283621/50000000000000 : ℝ)^17
        have hw : |(-190660423/10000000000 : ℝ)|=(190660423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6444445997/10000000000 : ℝ)|^21 ≤ (58114978333021/100000000000000 : ℝ)^17
        have hw : |(6444445997/10000000000 : ℝ)|=(6444445997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s1_s1_9 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4595259207/10000000000 : ℝ)*x 0 + (1344811207/2000000000 : ℝ)*x 1 + (-133821047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4595259207/10000000000 : ℝ)^21 ≤ (19134783416631/50000000000000 : ℝ)^17 := by
    have hnat : (4595259207 : ℕ)^21*50000000000000^17 ≤ 19134783416631^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4595259207 10000000000 19134783416631 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1344811207/2000000000 : ℝ)^21 ≤ (15311368087479/25000000000000 : ℝ)^17 := by
    have hnat : (1344811207 : ℕ)^21*25000000000000^17 ≤ 15311368087479^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344811207 2000000000 15311368087479 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (133821047/10000000000 : ℝ)^21 ≤ (30310050367/6250000000000 : ℝ)^17 := by
    have hnat : (133821047 : ℕ)^21*6250000000000^17 ≤ 30310050367^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133821047 10000000000 30310050367 6250000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4595259207/10000000000 : ℝ), (1344811207/2000000000 : ℝ), (-133821047/10000000000 : ℝ)] ![(19134783416631/50000000000000 : ℝ), (15311368087479/25000000000000 : ℝ), (30310050367/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4595259207/10000000000 : ℝ)|^21 ≤ (19134783416631/50000000000000 : ℝ)^17
        have hw : |(4595259207/10000000000 : ℝ)|=(4595259207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1344811207/2000000000 : ℝ)|^21 ≤ (15311368087479/25000000000000 : ℝ)^17
        have hw : |(1344811207/2000000000 : ℝ)|=(1344811207/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-133821047/10000000000 : ℝ)|^21 ≤ (30310050367/6250000000000 : ℝ)^17
        have hw : |(-133821047/10000000000 : ℝ)|=(133821047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s1_s1_13 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1107123907/2500000000 : ℝ)*x 0 + (2979989749/5000000000 : ℝ)*x 1 + (817155591/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1107123907/2500000000 : ℝ)^21 ≤ (4570170500873/12500000000000 : ℝ)^17 := by
    have hnat : (1107123907 : ℕ)^21*12500000000000^17 ≤ 4570170500873^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107123907 2500000000 4570170500873 12500000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2979989749/5000000000 : ℝ)^21 ≤ (52766851484133/100000000000000 : ℝ)^17 := by
    have hnat : (2979989749 : ℕ)^21*100000000000000^17 ≤ 52766851484133^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2979989749 5000000000 52766851484133 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (817155591/5000000000 : ℝ)^21 ≤ (2134356900179/20000000000000 : ℝ)^17 := by
    have hnat : (817155591 : ℕ)^21*20000000000000^17 ≤ 2134356900179^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      817155591 5000000000 2134356900179 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1107123907/2500000000 : ℝ), (2979989749/5000000000 : ℝ), (817155591/5000000000 : ℝ)] ![(4570170500873/12500000000000 : ℝ), (52766851484133/100000000000000 : ℝ), (2134356900179/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1107123907/2500000000 : ℝ)|^21 ≤ (4570170500873/12500000000000 : ℝ)^17
        have hw : |(1107123907/2500000000 : ℝ)|=(1107123907/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2979989749/5000000000 : ℝ)|^21 ≤ (52766851484133/100000000000000 : ℝ)^17
        have hw : |(2979989749/5000000000 : ℝ)|=(2979989749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(817155591/5000000000 : ℝ)|^21 ≤ (2134356900179/20000000000000 : ℝ)^17
        have hw : |(817155591/5000000000 : ℝ)|=(817155591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s1_s1_14 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-197282109/10000000000 : ℝ)*x 0 + (4846704937/10000000000 : ℝ)*x 1 + (6464990991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (197282109/10000000000 : ℝ)^21 ≤ (783306746701/100000000000000 : ℝ)^17 := by
    have hnat : (197282109 : ℕ)^21*100000000000000^17 ≤ 783306746701^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197282109 10000000000 783306746701 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4846704937/10000000000 : ℝ)^21 ≤ (326982115211/800000000000 : ℝ)^17 := by
    have hnat : (4846704937 : ℕ)^21*800000000000^17 ≤ 326982115211^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4846704937 10000000000 326982115211 800000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6464990991/10000000000 : ℝ)^21 ≤ (29171964419511/50000000000000 : ℝ)^17 := by
    have hnat : (6464990991 : ℕ)^21*50000000000000^17 ≤ 29171964419511^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6464990991 10000000000 29171964419511 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-197282109/10000000000 : ℝ), (4846704937/10000000000 : ℝ), (6464990991/10000000000 : ℝ)] ![(783306746701/100000000000000 : ℝ), (326982115211/800000000000 : ℝ), (29171964419511/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-197282109/10000000000 : ℝ)|^21 ≤ (783306746701/100000000000000 : ℝ)^17
        have hw : |(-197282109/10000000000 : ℝ)|=(197282109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4846704937/10000000000 : ℝ)|^21 ≤ (326982115211/800000000000 : ℝ)^17
        have hw : |(4846704937/10000000000 : ℝ)|=(4846704937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6464990991/10000000000 : ℝ)|^21 ≤ (29171964419511/50000000000000 : ℝ)^17
        have hw : |(6464990991/10000000000 : ℝ)|=(6464990991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s1_s1_15 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2221702697/5000000000 : ℝ)*x 0 + (-436307519/5000000000 : ℝ)*x 1 + (6467383513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2221702697/5000000000 : ℝ)^21 ≤ (18356740758751/50000000000000 : ℝ)^17 := by
    have hnat : (2221702697 : ℕ)^21*50000000000000^17 ≤ 18356740758751^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2221702697 5000000000 18356740758751 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (436307519/5000000000 : ℝ)^21 ≤ (2457958281927/50000000000000 : ℝ)^17 := by
    have hnat : (436307519 : ℕ)^21*50000000000000^17 ≤ 2457958281927^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436307519 5000000000 2457958281927 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6467383513/10000000000 : ℝ)^21 ≤ (58370601906661/100000000000000 : ℝ)^17 := by
    have hnat : (6467383513 : ℕ)^21*100000000000000^17 ≤ 58370601906661^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6467383513 10000000000 58370601906661 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2221702697/5000000000 : ℝ), (-436307519/5000000000 : ℝ), (6467383513/10000000000 : ℝ)] ![(18356740758751/50000000000000 : ℝ), (2457958281927/50000000000000 : ℝ), (58370601906661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2221702697/5000000000 : ℝ)|^21 ≤ (18356740758751/50000000000000 : ℝ)^17
        have hw : |(2221702697/5000000000 : ℝ)|=(2221702697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-436307519/5000000000 : ℝ)|^21 ≤ (2457958281927/50000000000000 : ℝ)^17
        have hw : |(-436307519/5000000000 : ℝ)|=(436307519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6467383513/10000000000 : ℝ)|^21 ≤ (58370601906661/100000000000000 : ℝ)^17
        have hw : |(6467383513/10000000000 : ℝ)|=(6467383513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s1_s1_16 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6430939711/10000000000 : ℝ)*x 0 + (4902974709/10000000000 : ℝ)*x 1 + (-153752587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6430939711/10000000000 : ℝ)^21 ≤ (5796455969419/10000000000000 : ℝ)^17 := by
    have hnat : (6430939711 : ℕ)^21*10000000000000^17 ≤ 5796455969419^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6430939711 10000000000 5796455969419 10000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4902974709/10000000000 : ℝ)^21 ≤ (41459745343427/100000000000000 : ℝ)^17 := by
    have hnat : (4902974709 : ℕ)^21*100000000000000^17 ≤ 41459745343427^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4902974709 10000000000 41459745343427 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (153752587/10000000000 : ℝ)^21 ≤ (287847472319/50000000000000 : ℝ)^17 := by
    have hnat : (153752587 : ℕ)^21*50000000000000^17 ≤ 287847472319^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153752587 10000000000 287847472319 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6430939711/10000000000 : ℝ), (4902974709/10000000000 : ℝ), (-153752587/10000000000 : ℝ)] ![(5796455969419/10000000000000 : ℝ), (41459745343427/100000000000000 : ℝ), (287847472319/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6430939711/10000000000 : ℝ)|^21 ≤ (5796455969419/10000000000000 : ℝ)^17
        have hw : |(6430939711/10000000000 : ℝ)|=(6430939711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4902974709/10000000000 : ℝ)|^21 ≤ (41459745343427/100000000000000 : ℝ)^17
        have hw : |(4902974709/10000000000 : ℝ)|=(4902974709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-153752587/10000000000 : ℝ)|^21 ≤ (287847472319/50000000000000 : ℝ)^17
        have hw : |(-153752587/10000000000 : ℝ)|=(153752587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s1_s1_20 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3403573959/5000000000 : ℝ)*x 0 + (1740087227/5000000000 : ℝ)*x 1 + (81704323/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3403573959/5000000000 : ℝ)^21 ≤ (62181741228451/100000000000000 : ℝ)^17 := by
    have hnat : (3403573959 : ℕ)^21*100000000000000^17 ≤ 62181741228451^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3403573959 5000000000 62181741228451 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1740087227/5000000000 : ℝ)^21 ≤ (13574143447117/50000000000000 : ℝ)^17 := by
    have hnat : (1740087227 : ℕ)^21*50000000000000^17 ≤ 13574143447117^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1740087227 5000000000 13574143447117 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81704323/500000000 : ℝ)^21 ≤ (2133994372451/20000000000000 : ℝ)^17 := by
    have hnat : (81704323 : ℕ)^21*20000000000000^17 ≤ 2133994372451^17*500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81704323 500000000 2133994372451 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3403573959/5000000000 : ℝ), (1740087227/5000000000 : ℝ), (81704323/500000000 : ℝ)] ![(62181741228451/100000000000000 : ℝ), (13574143447117/50000000000000 : ℝ), (2133994372451/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3403573959/5000000000 : ℝ)|^21 ≤ (62181741228451/100000000000000 : ℝ)^17
        have hw : |(3403573959/5000000000 : ℝ)|=(3403573959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1740087227/5000000000 : ℝ)|^21 ≤ (13574143447117/50000000000000 : ℝ)^17
        have hw : |(1740087227/5000000000 : ℝ)|=(1740087227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(81704323/500000000 : ℝ)|^21 ≤ (2133994372451/20000000000000 : ℝ)^17
        have hw : |(81704323/500000000 : ℝ)|=(81704323/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s1_s1_21 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-37727003/2500000000 : ℝ)*x 0 + (242905451/400000000 : ℝ)*x 1 + (5280260649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (37727003/2500000000 : ℝ)^21 ≤ (112513338363/20000000000000 : ℝ)^17 := by
    have hnat : (37727003 : ℕ)^21*20000000000000^17 ≤ 112513338363^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37727003 2500000000 112513338363 20000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (242905451/400000000 : ℝ)^21 ≤ (27000836536221/50000000000000 : ℝ)^17 := by
    have hnat : (242905451 : ℕ)^21*50000000000000^17 ≤ 27000836536221^17*400000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      242905451 400000000 27000836536221 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5280260649/10000000000 : ℝ)^21 ≤ (45435760224973/100000000000000 : ℝ)^17 := by
    have hnat : (5280260649 : ℕ)^21*100000000000000^17 ≤ 45435760224973^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280260649 10000000000 45435760224973 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-37727003/2500000000 : ℝ), (242905451/400000000 : ℝ), (5280260649/10000000000 : ℝ)] ![(112513338363/20000000000000 : ℝ), (27000836536221/50000000000000 : ℝ), (45435760224973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-37727003/2500000000 : ℝ)|^21 ≤ (112513338363/20000000000000 : ℝ)^17
        have hw : |(-37727003/2500000000 : ℝ)|=(37727003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(242905451/400000000 : ℝ)|^21 ≤ (27000836536221/50000000000000 : ℝ)^17
        have hw : |(242905451/400000000 : ℝ)|=(242905451/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5280260649/10000000000 : ℝ)|^21 ≤ (45435760224973/100000000000000 : ℝ)^17
        have hw : |(5280260649/10000000000 : ℝ)|=(5280260649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s1_s1_22 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1292886891/2000000000 : ℝ)*x 0 + (-26639299/2000000000 : ℝ)*x 1 + (1219046743/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1292886891/2000000000 : ℝ)^21 ≤ (14584431155489/25000000000000 : ℝ)^17 := by
    have hnat : (1292886891 : ℕ)^21*25000000000000^17 ≤ 14584431155489^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292886891 2000000000 14584431155489 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26639299/2000000000 : ℝ)^21 ≤ (482166445669/100000000000000 : ℝ)^17 := by
    have hnat : (26639299 : ℕ)^21*100000000000000^17 ≤ 482166445669^17*2000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26639299 2000000000 482166445669 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1219046743/2500000000 : ℝ)^21 ≤ (41180108916293/100000000000000 : ℝ)^17 := by
    have hnat : (1219046743 : ℕ)^21*100000000000000^17 ≤ 41180108916293^17*2500000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1219046743 2500000000 41180108916293 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1292886891/2000000000 : ℝ), (-26639299/2000000000 : ℝ), (1219046743/2500000000 : ℝ)] ![(14584431155489/25000000000000 : ℝ), (482166445669/100000000000000 : ℝ), (41180108916293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1292886891/2000000000 : ℝ)|^21 ≤ (14584431155489/25000000000000 : ℝ)^17
        have hw : |(1292886891/2000000000 : ℝ)|=(1292886891/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-26639299/2000000000 : ℝ)|^21 ≤ (482166445669/100000000000000 : ℝ)^17
        have hw : |(-26639299/2000000000 : ℝ)|=(26639299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1219046743/2500000000 : ℝ)|^21 ≤ (41180108916293/100000000000000 : ℝ)^17
        have hw : |(1219046743/2500000000 : ℝ)|=(1219046743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s1_s1_23 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2188533969/5000000000 : ℝ)*x 0 + (3267777219/5000000000 : ℝ)*x 1 + (-860367091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2188533969/5000000000 : ℝ)^21 ≤ (36037597114353/100000000000000 : ℝ)^17 := by
    have hnat : (2188533969 : ℕ)^21*100000000000000^17 ≤ 36037597114353^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188533969 5000000000 36037597114353 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3267777219/5000000000 : ℝ)^21 ≤ (236526318263/400000000000 : ℝ)^17 := by
    have hnat : (3267777219 : ℕ)^21*400000000000^17 ≤ 236526318263^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3267777219 5000000000 236526318263 400000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (860367091/10000000000 : ℝ)^21 ≤ (4830823304349/100000000000000 : ℝ)^17 := by
    have hnat : (860367091 : ℕ)^21*100000000000000^17 ≤ 4830823304349^17*10000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      860367091 10000000000 4830823304349 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2188533969/5000000000 : ℝ), (3267777219/5000000000 : ℝ), (-860367091/10000000000 : ℝ)] ![(36037597114353/100000000000000 : ℝ), (236526318263/400000000000 : ℝ), (4830823304349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2188533969/5000000000 : ℝ)|^21 ≤ (36037597114353/100000000000000 : ℝ)^17
        have hw : |(2188533969/5000000000 : ℝ)|=(2188533969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3267777219/5000000000 : ℝ)|^21 ≤ (236526318263/400000000000 : ℝ)^17
        have hw : |(3267777219/5000000000 : ℝ)|=(3267777219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-860367091/10000000000 : ℝ)|^21 ≤ (4830823304349/100000000000000 : ℝ)^17
        have hw : |(-860367091/10000000000 : ℝ)|=(860367091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c323063_s1_s1_27 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3498957211/5000000000 : ℝ)*x 0 + (1291939597/5000000000 : ℝ)*x 1 + (1183642731/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3498957211/5000000000 : ℝ)^21 ≤ (16085355578987/25000000000000 : ℝ)^17 := by
    have hnat : (3498957211 : ℕ)^21*25000000000000^17 ≤ 16085355578987^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3498957211 5000000000 16085355578987 25000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1291939597/5000000000 : ℝ)^21 ≤ (9396223020979/50000000000000 : ℝ)^17 := by
    have hnat : (1291939597 : ℕ)^21*50000000000000^17 ≤ 9396223020979^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1291939597 5000000000 9396223020979 50000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1183642731/5000000000 : ℝ)^21 ≤ (16866131628497/100000000000000 : ℝ)^17 := by
    have hnat : (1183642731 : ℕ)^21*100000000000000^17 ≤ 16866131628497^17*5000000000^21 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1183642731 5000000000 16866131628497 100000000000000 21 17 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (21/4 : ℝ)) 21 17 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3498957211/5000000000 : ℝ), (1291939597/5000000000 : ℝ), (1183642731/5000000000 : ℝ)] ![(16085355578987/25000000000000 : ℝ), (9396223020979/50000000000000 : ℝ), (16866131628497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3498957211/5000000000 : ℝ)|^21 ≤ (16085355578987/25000000000000 : ℝ)^17
        have hw : |(3498957211/5000000000 : ℝ)|=(3498957211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1291939597/5000000000 : ℝ)|^21 ≤ (9396223020979/50000000000000 : ℝ)^17
        have hw : |(1291939597/5000000000 : ℝ)|=(1291939597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1183642731/5000000000 : ℝ)|^21 ≤ (16866131628497/100000000000000 : ℝ)^17
        have hw : |(1183642731/5000000000 : ℝ)|=(1183642731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c323063_s1 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (97817/50000 : ℝ) (166881/100000 : ℝ) (80913/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((4333/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4333/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8641/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8641/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16703/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(16703/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((5493/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5493/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5581/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(5581/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(42681/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(42681/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (80913/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (80913/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (80913/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (80913/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (80913/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (80913/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (166881/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  have s1_pow0 : (4333/6250 : ℝ) ^ (83/16 : ℝ) ≤ (467265542487019851/3125000000000000000 : ℝ) := by
    have hpowers : (4333/6250 : ℝ)^83 ≤ (467265542487019851/3125000000000000000 : ℝ)^16 := by
      have hnat : (4333 : ℕ)^83*3125000000000000000^16 ≤ 467265542487019851^16*6250^83 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4333 6250 467265542487019851 3125000000000000000 83 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4333/6250 : ℝ)) (X := (467265542487019851/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (3592265542487019851/3125000000000000000 : ℝ) ≤ (10272264646201847/10000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (3592265542487019851/3125000000000000000 : ℝ)^16 ≤ (10272264646201847/10000000000000000 : ℝ)^83 := by
      have hnat : (3592265542487019851 : ℕ)^16*10000000000000000^83 ≤ 10272264646201847^83*3125000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3592265542487019851 3125000000000000000 10272264646201847 10000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10272264646201847/10000000000000000 : ℝ)) (X := (3592265542487019851/3125000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (2029765542487019851/1562500000000000000 : ℝ) ≤ (10517288282264243/10000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (2029765542487019851/1562500000000000000 : ℝ)^16 ≤ (10517288282264243/10000000000000000 : ℝ)^83 := by
      have hnat : (2029765542487019851 : ℕ)^16*10000000000000000^83 ≤ 10517288282264243^83*1562500000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2029765542487019851 1562500000000000000 10517288282264243 10000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10517288282264243/10000000000000000 : ℝ)) (X := (2029765542487019851/1562500000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(272264646201847/6932800000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(61255909015599/1733200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (4333/6250 : ℝ)) (alpha := (272264646201847/6932800000000000 : ℝ)) (beta := (61255909015599/1733200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (4333/6250 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(272264646201847/6932800000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(61255909015599/1733200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (8641/12500 : ℝ) ^ (83/16 : ℝ) ≤ (7365039637593207159/50000000000000000000 : ℝ) := by
    have hpowers : (8641/12500 : ℝ)^83 ≤ (7365039637593207159/50000000000000000000 : ℝ)^16 := by
      have hnat : (8641 : ℕ)^83*50000000000000000000^16 ≤ 7365039637593207159^16*12500^83 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8641 12500 7365039637593207159 50000000000000000000 83 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8641/12500 : ℝ)) (X := (7365039637593207159/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (57365039637593207159/50000000000000000000 : ℝ) ≤ (10268430230478553/10000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (57365039637593207159/50000000000000000000 : ℝ)^16 ≤ (10268430230478553/10000000000000000 : ℝ)^83 := by
      have hnat : (57365039637593207159 : ℕ)^16*10000000000000000^83 ≤ 10268430230478553^83*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57365039637593207159 50000000000000000000 10268430230478553 10000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10268430230478553/10000000000000000 : ℝ)) (X := (57365039637593207159/50000000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (32365039637593207159/25000000000000000000 : ℝ) ≤ (328448003211691/312500000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (32365039637593207159/25000000000000000000 : ℝ)^16 ≤ (328448003211691/312500000000000 : ℝ)^83 := by
      have hnat : (32365039637593207159 : ℕ)^16*312500000000000^83 ≤ 328448003211691^83*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32365039637593207159 25000000000000000000 328448003211691 312500000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (328448003211691/312500000000000 : ℝ)) (X := (32365039637593207159/25000000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(268430230478553/6912800000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(241905872295559/6912800000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (8641/12500 : ℝ)) (alpha := (268430230478553/6912800000000000 : ℝ)) (beta := (241905872295559/6912800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (8641/12500 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(268430230478553/6912800000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(241905872295559/6912800000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (16703/25000 : ℝ) ^ (83/16 : ℝ) ≤ (2468667340038560249/20000000000000000000 : ℝ) := by
    have hpowers : (16703/25000 : ℝ)^83 ≤ (2468667340038560249/20000000000000000000 : ℝ)^16 := by
      have hnat : (16703 : ℕ)^83*20000000000000000000^16 ≤ 2468667340038560249^16*25000^83 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16703 25000 2468667340038560249 20000000000000000000 83 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16703/25000 : ℝ)) (X := (2468667340038560249/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (22468667340038560249/20000000000000000000 : ℝ) ≤ (40907604902943/40000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (22468667340038560249/20000000000000000000 : ℝ)^16 ≤ (40907604902943/40000000000000 : ℝ)^83 := by
      have hnat : (22468667340038560249 : ℕ)^16*40000000000000^83 ≤ 40907604902943^83*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22468667340038560249 20000000000000000000 40907604902943 40000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (40907604902943/40000000000000 : ℝ)) (X := (22468667340038560249/20000000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (12468667340038560249/10000000000000000000 : ℝ) ≤ (10434492534634379/10000000000000000 : ℝ) ^ (83/16 : ℝ) := by
    have hpowers : (12468667340038560249/10000000000000000000 : ℝ)^16 ≤ (10434492534634379/10000000000000000 : ℝ)^83 := by
      have hnat : (12468667340038560249 : ℕ)^16*10000000000000000^83 ≤ 10434492534634379^83*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12468667340038560249 10000000000000000000 10434492534634379 10000000000000000 16 83 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10434492534634379/10000000000000000 : ℝ)) (X := (12468667340038560249/10000000000000000000 : ℝ)) (by norm_num) 83 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(907604902943/26724800000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(207591308898629/6681200000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (83/16 : ℝ)) (rho := (16703/25000 : ℝ)) (alpha := (907604902943/26724800000000 : ℝ)) (beta := (207591308898629/6681200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (16703/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(907604902943/26724800000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(207591308898629/6681200000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-932754347/10000000000 : ℝ)*X 0 0+(5427306873/10000000000 : ℝ)*X 0 1+(219536091/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((542707161/1000000000 : ℝ)*X 1 0+(-929598959/10000000000 : ℝ)*X 1 1+(5490715441/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((545929377/1000000000 : ℝ)*X 2 0+(548156509/1000000000 : ℝ)*X 2 1+(-894498183/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((836377649/2000000000 : ℝ)*X 0 0+(4124641969/10000000000 : ℝ)*X 0 1+(4020735463/10000000000 : ℝ)*X 0 2+(836377649/2000000000 : ℝ)*X 1 0+(4124641969/10000000000 : ℝ)*X 1 1+(4020735463/10000000000 : ℝ)*X 1 2+(836377649/2000000000 : ℝ)*X 2 0+(4124641969/10000000000 : ℝ)*X 2 1+(4020735463/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-855919057/10000000000 : ℝ)*X 0 0+(448236573/1000000000 : ℝ)*X 0 1+(6442065993/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((48717727/100000000 : ℝ)*X 1 0+(-190660423/10000000000 : ℝ)*X 1 1+(6444445997/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((4595259207/10000000000 : ℝ)*X 2 0+(1344811207/2000000000 : ℝ)*X 2 1+(-133821047/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((1107123907/2500000000 : ℝ)*X 0 0+(2979989749/5000000000 : ℝ)*X 0 1+(817155591/5000000000 : ℝ)*X 0 2+(1107123907/2500000000 : ℝ)*X 1 0+(2979989749/5000000000 : ℝ)*X 1 1+(817155591/5000000000 : ℝ)*X 1 2+(1107123907/2500000000 : ℝ)*X 2 0+(2979989749/5000000000 : ℝ)*X 2 1+(817155591/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-197282109/10000000000 : ℝ)*X 0 0+(4846704937/10000000000 : ℝ)*X 0 1+(6464990991/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((2221702697/5000000000 : ℝ)*X 1 0+(-436307519/5000000000 : ℝ)*X 1 1+(6467383513/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((6430939711/10000000000 : ℝ)*X 2 0+(4902974709/10000000000 : ℝ)*X 2 1+(-153752587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((3403573959/5000000000 : ℝ)*X 0 0+(1740087227/5000000000 : ℝ)*X 0 1+(81704323/500000000 : ℝ)*X 0 2+(3403573959/5000000000 : ℝ)*X 1 0+(1740087227/5000000000 : ℝ)*X 1 1+(81704323/500000000 : ℝ)*X 1 2+(3403573959/5000000000 : ℝ)*X 2 0+(1740087227/5000000000 : ℝ)*X 2 1+(81704323/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-37727003/2500000000 : ℝ)*X 0 0+(242905451/400000000 : ℝ)*X 0 1+(5280260649/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((1292886891/2000000000 : ℝ)*X 1 0+(-26639299/2000000000 : ℝ)*X 1 1+(1219046743/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((2188533969/5000000000 : ℝ)*X 2 0+(3267777219/5000000000 : ℝ)*X 2 1+(-860367091/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((3498957211/5000000000 : ℝ)*X 0 0+(1291939597/5000000000 : ℝ)*X 0 1+(1183642731/5000000000 : ℝ)*X 0 2+(3498957211/5000000000 : ℝ)*X 1 0+(1291939597/5000000000 : ℝ)*X 1 1+(1183642731/5000000000 : ℝ)*X 1 2+(3498957211/5000000000 : ℝ)*X 2 0+(1291939597/5000000000 : ℝ)*X 2 1+(1183642731/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c323063_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((5493/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5493/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (60722680564308879652722321/11546449840000000000000000000000 : ℝ) := by norm_num
    linear_combination (35729182889/250000000000 : ℝ)*(base7) + (54833/200000000000 : ℝ)*(base13) + (10317804609/62500000000 : ℝ)*(base60) + (3633555815669/1000000000000 : ℝ)*(major_s1_0) + (3633555815669/1000000000000 : ℝ)*(major_s1_1) + (3633555815669/1000000000000 : ℝ)*(major_s1_2) + (10460321/1000000000000 : ℝ)*(sp_s1_1) + (711441/200000000000 : ℝ)*(sp_s1_6) + (1332560682213/250000000000 : ℝ)*(sp_s1_7) + (2665137366351/500000000000 : ℝ)*(sp_s1_8) + (2665143156573/500000000000 : ℝ)*(sp_s1_9) + (2000236449277/1000000000000 : ℝ)*(sp_s1_13) + (4331013/100000000000 : ℝ)*(sp_s1_14) + (560061/500000000000 : ℝ)*(sp_s1_22) + (928661637463/500000000000 : ℝ)*(f.failure) + (2665143156573/500000000000 : ℝ)*(f.sum) + (18560637097707942209/115464498400000000000000000000000 : ℝ)*base62 + (1245664283933519/6681200000000000000000000000 : ℝ)*base64 + (4567300007085629/6912800000000000000000000000 : ℝ)*base66 + (403399213257063/668120000000000000000000000 : ℝ)*base69 + (25345274411730662479/115798558400000000000000000000000 : ℝ)*base70 + (1277168204998971/1733200000000000000000000000 : ℝ)*base73 + (843516959981117/6912800000000000000000000000 : ℝ)*base75 + (242726327751363/6932800000000000000000000000 : ℝ)*base77 + (813518208614770919/5990632480000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base82 + (6729/25000000000000000 : ℝ)*base86 + (6729/25000000000000000 : ℝ)*base88 + (6729/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5581/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(5581/12500 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (367461369490044697791121203189/31269229472950000000000000000000000 : ℝ) := by norm_num
    linear_combination (12378288709/62500000000 : ℝ)*(base7) + (877794691783/250000000000 : ℝ)*(major_s1_0) + (877794691783/250000000000 : ℝ)*(major_s1_1) + (877794691783/250000000000 : ℝ)*(major_s1_2) + (7322493/1000000000000 : ℝ)*(sp_s1_0) + (7289923/1000000000000 : ℝ)*(sp_s1_1) + (1500331/200000000000 : ℝ)*(sp_s1_2) + (10290203/125000000000 : ℝ)*(sp_s1_8) + (2558701525433/500000000000 : ℝ)*(sp_s1_14) + (2558662039939/500000000000 : ℝ)*(sp_s1_15) + (511740618977/100000000000 : ℝ)*(sp_s1_16) + (498198365281/250000000000 : ℝ)*(sp_s1_20) + (663613/200000000000 : ℝ)*(sp_s1_21) + (5670663/200000000000 : ℝ)*(sp_s1_27) + (358953839019/200000000000 : ℝ)*(f.failure) + (204696547657/40000000000 : ℝ)*(f.sum) + (3288038817101284023/28866124600000000000000000000000 : ℝ)*base62 + (41083132901853/1670300000000000000000000000 : ℝ)*base64 + (155168899359823/1728200000000000000000000000 : ℝ)*base66 + (107855725601147/167030000000000000000000000 : ℝ)*base68 + (840967736715658947/28949639600000000000000000000000 : ℝ)*base71 + (284437388663133/433300000000000000000000000 : ℝ)*base72 + (1140443630831241/1728200000000000000000000000 : ℝ)*base74 + (1005959597846319/1733200000000000000000000000 : ℝ)*base76 + (42047945020443001/1497658120000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1523/10000000000000000 : ℝ)*base87 + (1523/10000000000000000 : ℝ)*base89 + (1523/10000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(42681/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(42681/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3144580766802311238470775330003/250153835783600000000000000000000000 : ℝ) := by norm_num
    linear_combination (52358862043/250000000000 : ℝ)*(base7) + (95826193063/500000000000 : ℝ)*(base40) + (834241/500000000000 : ℝ)*(base49) + (1622592334107/500000000000 : ℝ)*(major_s1_0) + (1622592334107/500000000000 : ℝ)*(major_s1_1) + (1622592334107/500000000000 : ℝ)*(major_s1_2) + (426213/31250000000 : ℝ)*(sp_s1_1) + (44333621/1000000000000 : ℝ)*(sp_s1_2) + (29093259/250000000000 : ℝ)*(sp_s1_9) + (18514811/1000000000000 : ℝ)*(sp_s1_20) + (1178764615869/250000000000 : ℝ)*(sp_s1_21) + (235752241233/50000000000 : ℝ)*(sp_s1_22) + (235744887841/50000000000 : ℝ)*(sp_s1_23) + (373644191871/200000000000 : ℝ)*(sp_s1_27) + (829402012997/500000000000 : ℝ)*(f.failure) + (1178764615869/250000000000 : ℝ)*(f.sum) + (297150589274075393/57732249200000000000000000000000 : ℝ)*base63 + (753677882865463/3340600000000000000000000000 : ℝ)*base65 + (686331985275347/3456400000000000000000000000 : ℝ)*base66 + (79970191699117/334060000000000000000000000 : ℝ)*base69 + (1023880560855763617/57899279200000000000000000000000 : ℝ)*base70 + (179557473704733/866600000000000000000000000 : ℝ)*base73 + (1072110462480429/3456400000000000000000000000 : ℝ)*base74 + (1416729139067731/3466400000000000000000000000 : ℝ)*base76 + (932890875293382769/2995316240000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (22451/25000000000000000 : ℝ)*base86 + (22451/25000000000000000 : ℝ)*base88 + (22451/25000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (97817/50000 : ℝ) (166881/100000 : ℝ) (80913/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((4333/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4333/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8641/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8641/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16703/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(16703/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((5493/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5493/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5581/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(5581/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(42681/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(42681/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c323063_s1 p hpa hpb X hX hprev0

#print axioms solution
