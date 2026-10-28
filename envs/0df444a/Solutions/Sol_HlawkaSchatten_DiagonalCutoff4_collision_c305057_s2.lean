-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c305057_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:30:14.258931+00:00
-- url     : https://prove2.me/submissions/40d8d652-8edb-4f81-9c8f-bd2ad8e18d7b

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
theorem collision_support_c305057_s2_s2_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3126202541/10000000000 : ℝ)*x 0 + (-3123203161/10000000000 : ℝ)*x 1 + (6485275299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3126202541/10000000000 : ℝ)^67 ≤ (10853282612989/50000000000000 : ℝ)^51 := by
    have hnat : (3126202541 : ℕ)^67*50000000000000^51 ≤ 10853282612989^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3126202541 10000000000 10853282612989 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3123203161/10000000000 : ℝ)^67 ≤ (5419802430293/25000000000000 : ℝ)^51 := by
    have hnat : (3123203161 : ℕ)^67*25000000000000^51 ≤ 5419802430293^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3123203161 10000000000 5419802430293 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6485275299/10000000000 : ℝ)^67 ≤ (28307112517327/50000000000000 : ℝ)^51 := by
    have hnat : (6485275299 : ℕ)^67*50000000000000^51 ≤ 28307112517327^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6485275299 10000000000 28307112517327 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3126202541/10000000000 : ℝ), (-3123203161/10000000000 : ℝ), (6485275299/10000000000 : ℝ)] ![(10853282612989/50000000000000 : ℝ), (5419802430293/25000000000000 : ℝ), (28307112517327/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3126202541/10000000000 : ℝ)|^67 ≤ (10853282612989/50000000000000 : ℝ)^51
        have hw : |(3126202541/10000000000 : ℝ)|=(3126202541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3123203161/10000000000 : ℝ)|^67 ≤ (5419802430293/25000000000000 : ℝ)^51
        have hw : |(-3123203161/10000000000 : ℝ)|=(3123203161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6485275299/10000000000 : ℝ)|^67 ≤ (28307112517327/50000000000000 : ℝ)^51
        have hw : |(6485275299/10000000000 : ℝ)|=(6485275299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305057_s2_s2_6 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (97890309/200000000 : ℝ)*x 0 + (979618711/2000000000 : ℝ)*x 1 + (3128634817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (97890309/200000000 : ℝ)^67 ≤ (19558418414213/50000000000000 : ℝ)^51 := by
    have hnat : (97890309 : ℕ)^67*50000000000000^51 ≤ 19558418414213^51*200000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97890309 200000000 19558418414213 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (979618711/2000000000 : ℝ)^67 ≤ (9788602146751/25000000000000 : ℝ)^51 := by
    have hnat : (979618711 : ℕ)^67*25000000000000^51 ≤ 9788602146751^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      979618711 2000000000 9788602146751 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3128634817/10000000000 : ℝ)^67 ≤ (21728754570191/100000000000000 : ℝ)^51 := by
    have hnat : (3128634817 : ℕ)^67*100000000000000^51 ≤ 21728754570191^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3128634817 10000000000 21728754570191 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(97890309/200000000 : ℝ), (979618711/2000000000 : ℝ), (3128634817/10000000000 : ℝ)] ![(19558418414213/50000000000000 : ℝ), (9788602146751/25000000000000 : ℝ), (21728754570191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(97890309/200000000 : ℝ)|^67 ≤ (19558418414213/50000000000000 : ℝ)^51
        have hw : |(97890309/200000000 : ℝ)|=(97890309/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(979618711/2000000000 : ℝ)|^67 ≤ (9788602146751/25000000000000 : ℝ)^51
        have hw : |(979618711/2000000000 : ℝ)|=(979618711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3128634817/10000000000 : ℝ)|^67 ≤ (21728754570191/100000000000000 : ℝ)^51
        have hw : |(3128634817/10000000000 : ℝ)|=(3128634817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305057_s2_s2_7 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2213797373/10000000000 : ℝ)*x 0 + (438810317/2500000000 : ℝ)*x 1 + (8117794777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2213797373/10000000000 : ℝ)^67 ≤ (13794022317589/100000000000000 : ℝ)^51 := by
    have hnat : (2213797373 : ℕ)^67*100000000000000^51 ≤ 13794022317589^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2213797373 10000000000 13794022317589 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (438810317/2500000000 : ℝ)^67 ≤ (10168713700641/100000000000000 : ℝ)^51 := by
    have hnat : (438810317 : ℕ)^67*100000000000000^51 ≤ 10168713700641^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438810317 2500000000 10168713700641 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8117794777/10000000000 : ℝ)^67 ≤ (38018631982263/50000000000000 : ℝ)^51 := by
    have hnat : (8117794777 : ℕ)^67*50000000000000^51 ≤ 38018631982263^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8117794777 10000000000 38018631982263 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2213797373/10000000000 : ℝ), (438810317/2500000000 : ℝ), (8117794777/10000000000 : ℝ)] ![(13794022317589/100000000000000 : ℝ), (10168713700641/100000000000000 : ℝ), (38018631982263/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2213797373/10000000000 : ℝ)|^67 ≤ (13794022317589/100000000000000 : ℝ)^51
        have hw : |(-2213797373/10000000000 : ℝ)|=(2213797373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(438810317/2500000000 : ℝ)|^67 ≤ (10168713700641/100000000000000 : ℝ)^51
        have hw : |(438810317/2500000000 : ℝ)|=(438810317/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8117794777/10000000000 : ℝ)|^67 ≤ (38018631982263/50000000000000 : ℝ)^51
        have hw : |(8117794777/10000000000 : ℝ)|=(8117794777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305057_s2_s2_8 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1105277443/5000000000 : ℝ)*x 0 + (-350534083/2000000000 : ℝ)*x 1 + (4060770343/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1105277443/5000000000 : ℝ)^67 ≤ (6883743139149/50000000000000 : ℝ)^51 := by
    have hnat : (1105277443 : ℕ)^67*50000000000000^51 ≤ 6883743139149^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105277443 5000000000 6883743139149 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (350534083/2000000000 : ℝ)^67 ≤ (2537287947791/25000000000000 : ℝ)^51 := by
    have hnat : (350534083 : ℕ)^67*25000000000000^51 ≤ 2537287947791^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      350534083 2000000000 2537287947791 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4060770343/5000000000 : ℝ)^67 ≤ (15216672384637/20000000000000 : ℝ)^51 := by
    have hnat : (4060770343 : ℕ)^67*20000000000000^51 ≤ 15216672384637^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4060770343 5000000000 15216672384637 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1105277443/5000000000 : ℝ), (-350534083/2000000000 : ℝ), (4060770343/5000000000 : ℝ)] ![(6883743139149/50000000000000 : ℝ), (2537287947791/25000000000000 : ℝ), (15216672384637/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1105277443/5000000000 : ℝ)|^67 ≤ (6883743139149/50000000000000 : ℝ)^51
        have hw : |(1105277443/5000000000 : ℝ)|=(1105277443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-350534083/2000000000 : ℝ)|^67 ≤ (2537287947791/25000000000000 : ℝ)^51
        have hw : |(-350534083/2000000000 : ℝ)|=(350534083/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4060770343/5000000000 : ℝ)|^67 ≤ (15216672384637/20000000000000 : ℝ)^51
        have hw : |(4060770343/5000000000 : ℝ)|=(4060770343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305057_s2_s2_9 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (926869053/2500000000 : ℝ)*x 0 + (982107189/1250000000 : ℝ)*x 1 + (311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (926869053/2500000000 : ℝ)^67 ≤ (5431468563263/20000000000000 : ℝ)^51 := by
    have hnat : (926869053 : ℕ)^67*20000000000000^51 ≤ 5431468563263^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      926869053 2500000000 5431468563263 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (982107189/1250000000 : ℝ)^67 ≤ (72842657167103/100000000000000 : ℝ)^51 := by
    have hnat : (982107189 : ℕ)^67*100000000000000^51 ≤ 72842657167103^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      982107189 1250000000 72842657167103 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (311/10000000000 : ℝ)^67 ≤ (13727/100000000000000 : ℝ)^51 := by
    have hnat : (311 : ℕ)^67*100000000000000^51 ≤ 13727^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      311 10000000000 13727 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(926869053/2500000000 : ℝ), (982107189/1250000000 : ℝ), (311/10000000000 : ℝ)] ![(5431468563263/20000000000000 : ℝ), (72842657167103/100000000000000 : ℝ), (13727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(926869053/2500000000 : ℝ)|^67 ≤ (5431468563263/20000000000000 : ℝ)^51
        have hw : |(926869053/2500000000 : ℝ)|=(926869053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(982107189/1250000000 : ℝ)|^67 ≤ (72842657167103/100000000000000 : ℝ)^51
        have hw : |(982107189/1250000000 : ℝ)|=(982107189/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(311/10000000000 : ℝ)|^67 ≤ (13727/100000000000000 : ℝ)^51
        have hw : |(311/10000000000 : ℝ)|=(311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305057_s2_s2_12 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3373780449/10000000000 : ℝ)*x 0 + (7149691799/10000000000 : ℝ)*x 1 + (973579329/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3373780449/10000000000 : ℝ)^67 ≤ (959698963271/4000000000000 : ℝ)^51 := by
    have hnat : (3373780449 : ℕ)^67*4000000000000^51 ≤ 959698963271^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3373780449 10000000000 959698963271 4000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7149691799/10000000000 : ℝ)^67 ≤ (64353702652027/100000000000000 : ℝ)^51 := by
    have hnat : (7149691799 : ℕ)^67*100000000000000^51 ≤ 64353702652027^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7149691799 10000000000 64353702652027 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (973579329/5000000000 : ℝ)^67 ≤ (1165382325391/10000000000000 : ℝ)^51 := by
    have hnat : (973579329 : ℕ)^67*10000000000000^51 ≤ 1165382325391^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      973579329 5000000000 1165382325391 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3373780449/10000000000 : ℝ), (7149691799/10000000000 : ℝ), (973579329/5000000000 : ℝ)] ![(959698963271/4000000000000 : ℝ), (64353702652027/100000000000000 : ℝ), (1165382325391/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3373780449/10000000000 : ℝ)|^67 ≤ (959698963271/4000000000000 : ℝ)^51
        have hw : |(3373780449/10000000000 : ℝ)|=(3373780449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7149691799/10000000000 : ℝ)|^67 ≤ (64353702652027/100000000000000 : ℝ)^51
        have hw : |(7149691799/10000000000 : ℝ)|=(7149691799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(973579329/5000000000 : ℝ)|^67 ≤ (1165382325391/10000000000000 : ℝ)^51
        have hw : |(973579329/5000000000 : ℝ)|=(973579329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305057_s2_s2_13 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1758371009/10000000000 : ℝ)*x 0 + (552607213/2500000000 : ℝ)*x 1 + (8118098753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1758371009/10000000000 : ℝ)^67 ≤ (10192540386011/100000000000000 : ℝ)^51 := by
    have hnat : (1758371009 : ℕ)^67*100000000000000^51 ≤ 10192540386011^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1758371009 10000000000 10192540386011 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (552607213/2500000000 : ℝ)^67 ≤ (3441613770223/25000000000000 : ℝ)^51 := by
    have hnat : (552607213 : ℕ)^67*25000000000000^51 ≤ 3441613770223^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552607213 2500000000 3441613770223 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8118098753/10000000000 : ℝ)^67 ≤ (4752562781847/6250000000000 : ℝ)^51 := by
    have hnat : (8118098753 : ℕ)^67*6250000000000^51 ≤ 4752562781847^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8118098753 10000000000 4752562781847 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1758371009/10000000000 : ℝ), (552607213/2500000000 : ℝ), (8118098753/10000000000 : ℝ)] ![(10192540386011/100000000000000 : ℝ), (3441613770223/25000000000000 : ℝ), (4752562781847/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1758371009/10000000000 : ℝ)|^67 ≤ (10192540386011/100000000000000 : ℝ)^51
        have hw : |(-1758371009/10000000000 : ℝ)|=(1758371009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(552607213/2500000000 : ℝ)|^67 ≤ (3441613770223/25000000000000 : ℝ)^51
        have hw : |(552607213/2500000000 : ℝ)|=(552607213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8118098753/10000000000 : ℝ)|^67 ≤ (4752562781847/6250000000000 : ℝ)^51
        have hw : |(8118098753/10000000000 : ℝ)|=(8118098753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305057_s2_s2_14 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1755795599/10000000000 : ℝ)*x 0 + (-551797833/2500000000 : ℝ)*x 1 + (4060921997/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1755795599/10000000000 : ℝ)^67 ≤ (127161660577/1250000000000 : ℝ)^51 := by
    have hnat : (1755795599 : ℕ)^67*1250000000000^51 ≤ 127161660577^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1755795599 10000000000 127161660577 1250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (551797833/2500000000 : ℝ)^67 ≤ (13739972345339/100000000000000 : ℝ)^51 := by
    have hnat : (551797833 : ℕ)^67*100000000000000^51 ≤ 13739972345339^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551797833 2500000000 13739972345339 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4060921997/5000000000 : ℝ)^67 ≤ (76087094788379/100000000000000 : ℝ)^51 := by
    have hnat : (4060921997 : ℕ)^67*100000000000000^51 ≤ 76087094788379^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4060921997 5000000000 76087094788379 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1755795599/10000000000 : ℝ), (-551797833/2500000000 : ℝ), (4060921997/5000000000 : ℝ)] ![(127161660577/1250000000000 : ℝ), (13739972345339/100000000000000 : ℝ), (76087094788379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1755795599/10000000000 : ℝ)|^67 ≤ (127161660577/1250000000000 : ℝ)^51
        have hw : |(1755795599/10000000000 : ℝ)|=(1755795599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-551797833/2500000000 : ℝ)|^67 ≤ (13739972345339/100000000000000 : ℝ)^51
        have hw : |(-551797833/2500000000 : ℝ)|=(551797833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4060921997/5000000000 : ℝ)|^67 ≤ (76087094788379/100000000000000 : ℝ)^51
        have hw : |(4060921997/5000000000 : ℝ)|=(4060921997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305057_s2_s2_15 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7853445663/10000000000 : ℝ)*x 0 + (3711793479/10000000000 : ℝ)*x 1 + (307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7853445663/10000000000 : ℝ)^67 ≤ (72801104228319/100000000000000 : ℝ)^51 := by
    have hnat : (7853445663 : ℕ)^67*100000000000000^51 ≤ 72801104228319^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7853445663 10000000000 72801104228319 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3711793479/10000000000 : ℝ)^67 ≤ (27198895754451/100000000000000 : ℝ)^51 := by
    have hnat : (3711793479 : ℕ)^67*100000000000000^51 ≤ 27198895754451^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3711793479 10000000000 27198895754451 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (307/10000000000 : ℝ)^67 ≤ (2699/20000000000000 : ℝ)^51 := by
    have hnat : (307 : ℕ)^67*20000000000000^51 ≤ 2699^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      307 10000000000 2699 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7853445663/10000000000 : ℝ), (3711793479/10000000000 : ℝ), (307/10000000000 : ℝ)] ![(72801104228319/100000000000000 : ℝ), (27198895754451/100000000000000 : ℝ), (2699/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7853445663/10000000000 : ℝ)|^67 ≤ (72801104228319/100000000000000 : ℝ)^51
        have hw : |(7853445663/10000000000 : ℝ)|=(7853445663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3711793479/10000000000 : ℝ)|^67 ≤ (27198895754451/100000000000000 : ℝ)^51
        have hw : |(3711793479/10000000000 : ℝ)|=(3711793479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(307/10000000000 : ℝ)|^67 ≤ (2699/20000000000000 : ℝ)^51
        have hw : |(307/10000000000 : ℝ)|=(307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305057_s2_s2_18 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7146647813/10000000000 : ℝ)*x 0 + (168886893/500000000 : ℝ)*x 1 + (3115253/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7146647813/10000000000 : ℝ)^67 ≤ (64317710775707/100000000000000 : ℝ)^51 := by
    have hnat : (7146647813 : ℕ)^67*100000000000000^51 ≤ 64317710775707^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7146647813 10000000000 64317710775707 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168886893/500000000 : ℝ)^67 ≤ (4805890594531/20000000000000 : ℝ)^51 := by
    have hnat : (168886893 : ℕ)^67*20000000000000^51 ≤ 4805890594531^51*500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168886893 500000000 4805890594531 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3115253/16000000 : ℝ)^67 ≤ (5826418117777/50000000000000 : ℝ)^51 := by
    have hnat : (3115253 : ℕ)^67*50000000000000^51 ≤ 5826418117777^51*16000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3115253 16000000 5826418117777 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7146647813/10000000000 : ℝ), (168886893/500000000 : ℝ), (3115253/16000000 : ℝ)] ![(64317710775707/100000000000000 : ℝ), (4805890594531/20000000000000 : ℝ), (5826418117777/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7146647813/10000000000 : ℝ)|^67 ≤ (64317710775707/100000000000000 : ℝ)^51
        have hw : |(7146647813/10000000000 : ℝ)|=(7146647813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168886893/500000000 : ℝ)|^67 ≤ (4805890594531/20000000000000 : ℝ)^51
        have hw : |(168886893/500000000 : ℝ)|=(168886893/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3115253/16000000 : ℝ)|^67 ≤ (5826418117777/50000000000000 : ℝ)^51
        have hw : |(3115253/16000000 : ℝ)|=(3115253/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305057_s2_s2_19 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2538404721/5000000000 : ℝ)*x 0 + (1688368389/10000000000 : ℝ)*x 1 + (5836673489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2538404721/5000000000 : ℝ)^67 ≤ (1282558647381/3125000000000 : ℝ)^51 := by
    have hnat : (2538404721 : ℕ)^67*3125000000000^51 ≤ 1282558647381^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2538404721 5000000000 1282558647381 3125000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1688368389/10000000000 : ℝ)^67 ≤ (386512884827/4000000000000 : ℝ)^51 := by
    have hnat : (1688368389 : ℕ)^67*4000000000000^51 ≤ 386512884827^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1688368389 10000000000 386512884827 4000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5836673489/10000000000 : ℝ)^67 ≤ (49295301157777/100000000000000 : ℝ)^51 := by
    have hnat : (5836673489 : ℕ)^67*100000000000000^51 ≤ 49295301157777^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5836673489 10000000000 49295301157777 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2538404721/5000000000 : ℝ), (1688368389/10000000000 : ℝ), (5836673489/10000000000 : ℝ)] ![(1282558647381/3125000000000 : ℝ), (386512884827/4000000000000 : ℝ), (49295301157777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2538404721/5000000000 : ℝ)|^67 ≤ (1282558647381/3125000000000 : ℝ)^51
        have hw : |(-2538404721/5000000000 : ℝ)|=(2538404721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1688368389/10000000000 : ℝ)|^67 ≤ (386512884827/4000000000000 : ℝ)^51
        have hw : |(1688368389/10000000000 : ℝ)|=(1688368389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5836673489/10000000000 : ℝ)|^67 ≤ (49295301157777/100000000000000 : ℝ)^51
        have hw : |(5836673489/10000000000 : ℝ)|=(5836673489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305057_s2_s2_20 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1690183907/10000000000 : ℝ)*x 0 + (-5072132359/10000000000 : ℝ)*x 1 + (5839918927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1690183907/10000000000 : ℝ)^67 ≤ (302389834847/3125000000000 : ℝ)^51 := by
    have hnat : (1690183907 : ℕ)^67*3125000000000^51 ≤ 302389834847^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1690183907 10000000000 302389834847 3125000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5072132359/10000000000 : ℝ)^67 ≤ (4099221139207/10000000000000 : ℝ)^51 := by
    have hnat : (5072132359 : ℕ)^67*10000000000000^51 ≤ 4099221139207^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5072132359 10000000000 4099221139207 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5839918927/10000000000 : ℝ)^67 ≤ (4933131387927/10000000000000 : ℝ)^51 := by
    have hnat : (5839918927 : ℕ)^67*10000000000000^51 ≤ 4933131387927^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5839918927 10000000000 4933131387927 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1690183907/10000000000 : ℝ), (-5072132359/10000000000 : ℝ), (5839918927/10000000000 : ℝ)] ![(302389834847/3125000000000 : ℝ), (4099221139207/10000000000000 : ℝ), (4933131387927/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1690183907/10000000000 : ℝ)|^67 ≤ (302389834847/3125000000000 : ℝ)^51
        have hw : |(1690183907/10000000000 : ℝ)|=(1690183907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5072132359/10000000000 : ℝ)|^67 ≤ (4099221139207/10000000000000 : ℝ)^51
        have hw : |(-5072132359/10000000000 : ℝ)|=(5072132359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5839918927/10000000000 : ℝ)|^67 ≤ (4933131387927/10000000000000 : ℝ)^51
        have hw : |(5839918927/10000000000 : ℝ)|=(5839918927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305057_s2_s2_21 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6209573913/10000000000 : ℝ)*x 0 + (347855441/625000000 : ℝ)*x 1 + (11676419/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6209573913/10000000000 : ℝ)^67 ≤ (10694734525737/20000000000000 : ℝ)^51 := by
    have hnat : (6209573913 : ℕ)^67*20000000000000^51 ≤ 10694734525737^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6209573913 10000000000 10694734525737 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (347855441/625000000 : ℝ)^67 ≤ (5788840079221/12500000000000 : ℝ)^51 := by
    have hnat : (347855441 : ℕ)^67*12500000000000^51 ≤ 5788840079221^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      347855441 625000000 5788840079221 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11676419/1250000000 : ℝ)^67 ≤ (215606721473/100000000000000 : ℝ)^51 := by
    have hnat : (11676419 : ℕ)^67*100000000000000^51 ≤ 215606721473^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11676419 1250000000 215606721473 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6209573913/10000000000 : ℝ), (347855441/625000000 : ℝ), (11676419/1250000000 : ℝ)] ![(10694734525737/20000000000000 : ℝ), (5788840079221/12500000000000 : ℝ), (215606721473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6209573913/10000000000 : ℝ)|^67 ≤ (10694734525737/20000000000000 : ℝ)^51
        have hw : |(6209573913/10000000000 : ℝ)|=(6209573913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(347855441/625000000 : ℝ)|^67 ≤ (5788840079221/12500000000000 : ℝ)^51
        have hw : |(347855441/625000000 : ℝ)|=(347855441/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(11676419/1250000000 : ℝ)|^67 ≤ (215606721473/100000000000000 : ℝ)^51
        have hw : |(11676419/1250000000 : ℝ)|=(11676419/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305057_s2_s2_25 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (696851113/2000000000 : ℝ)*x 0 + (347855441/625000000 : ℝ)*x 1 + (3862560513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (696851113/2000000000 : ℝ)^67 ≤ (3128731188343/12500000000000 : ℝ)^51 := by
    have hnat : (696851113 : ℕ)^67*12500000000000^51 ≤ 3128731188343^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      696851113 2000000000 3128731188343 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (347855441/625000000 : ℝ)^67 ≤ (5788840079221/12500000000000 : ℝ)^51 := by
    have hnat : (347855441 : ℕ)^67*12500000000000^51 ≤ 5788840079221^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      347855441 625000000 5788840079221 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3862560513/10000000000 : ℝ)^67 ≤ (358242873063/1250000000000 : ℝ)^51 := by
    have hnat : (3862560513 : ℕ)^67*1250000000000^51 ≤ 358242873063^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3862560513 10000000000 358242873063 1250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(696851113/2000000000 : ℝ), (347855441/625000000 : ℝ), (3862560513/10000000000 : ℝ)] ![(3128731188343/12500000000000 : ℝ), (5788840079221/12500000000000 : ℝ), (358242873063/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(696851113/2000000000 : ℝ)|^67 ≤ (3128731188343/12500000000000 : ℝ)^51
        have hw : |(696851113/2000000000 : ℝ)|=(696851113/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(347855441/625000000 : ℝ)|^67 ≤ (5788840079221/12500000000000 : ℝ)^51
        have hw : |(347855441/625000000 : ℝ)|=(347855441/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3862560513/10000000000 : ℝ)|^67 ≤ (358242873063/1250000000000 : ℝ)^51
        have hw : |(3862560513/10000000000 : ℝ)|=(3862560513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c305057_s2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((11079/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11079/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2763/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2763/3125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(41813/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(41813/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((39417/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(39417/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19699/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(19699/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(27933/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(27933/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76771/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76771/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (93447/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
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
  have s2_pow0 : (11079/12500 : ℝ) ^ (133/32 : ℝ) ≤ (30279118325579784727/50000000000000000000 : ℝ) := by
    have hpowers : (11079/12500 : ℝ)^133 ≤ (30279118325579784727/50000000000000000000 : ℝ)^32 := by
      have hnat : (11079 : ℕ)^133*50000000000000000000^32 ≤ 30279118325579784727^32*12500^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11079 12500 30279118325579784727 50000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11079/12500 : ℝ)) (X := (30279118325579784727/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner0a : (80279118325579784727/50000000000000000000 : ℝ) ≤ (11206642306096577/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (80279118325579784727/50000000000000000000 : ℝ)^32 ≤ (11206642306096577/10000000000000000 : ℝ)^133 := by
      have hnat : (80279118325579784727 : ℕ)^32*10000000000000000^133 ≤ 11206642306096577^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        80279118325579784727 50000000000000000000 11206642306096577 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11206642306096577/10000000000000000 : ℝ)) (X := (80279118325579784727/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner0b : (55279118325579784727/25000000000000000000 : ℝ) ≤ (12103649941226533/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (55279118325579784727/25000000000000000000 : ℝ)^32 ≤ (12103649941226533/10000000000000000 : ℝ)^133 := by
      have hnat : (55279118325579784727 : ℕ)^32*10000000000000000^133 ≤ 12103649941226533^133*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55279118325579784727 25000000000000000000 12103649941226533 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12103649941226533/10000000000000000 : ℝ)) (X := (55279118325579784727/25000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1206642306096577/8863200000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(224251908782489/2215800000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (11079/12500 : ℝ)) (alpha := (1206642306096577/8863200000000000 : ℝ)) (beta := (224251908782489/2215800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (11079/12500 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1206642306096577/8863200000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(224251908782489/2215800000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (2763/3125 : ℝ) ^ (133/32 : ℝ) ≤ (59947199633428844803/100000000000000000000 : ℝ) := by
    have hpowers : (2763/3125 : ℝ)^133 ≤ (59947199633428844803/100000000000000000000 : ℝ)^32 := by
      have hnat : (2763 : ℕ)^133*100000000000000000000^32 ≤ 59947199633428844803^32*3125^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2763 3125 59947199633428844803 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2763/3125 : ℝ)) (X := (59947199633428844803/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner1a : (159947199633428844803/100000000000000000000 : ℝ) ≤ (2239273198759987/2000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (159947199633428844803/100000000000000000000 : ℝ)^32 ≤ (2239273198759987/2000000000000000 : ℝ)^133 := by
      have hnat : (159947199633428844803 : ℕ)^32*2000000000000000^133 ≤ 2239273198759987^133*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        159947199633428844803 100000000000000000000 2239273198759987 2000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2239273198759987/2000000000000000 : ℝ)) (X := (159947199633428844803/100000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner1b : (109947199633428844803/50000000000000000000 : ℝ) ≤ (12087521050620669/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (109947199633428844803/50000000000000000000 : ℝ)^32 ≤ (12087521050620669/10000000000000000 : ℝ)^133 := by
      have hnat : (109947199633428844803 : ℕ)^32*10000000000000000^133 ≤ 12087521050620669^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        109947199633428844803 50000000000000000000 12087521050620669 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12087521050620669/10000000000000000 : ℝ)) (X := (109947199633428844803/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(239273198759987/1768320000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(445577528410367/4420800000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (2763/3125 : ℝ)) (alpha := (239273198759987/1768320000000000 : ℝ)) (beta := (445577528410367/4420800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (2763/3125 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(239273198759987/1768320000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(445577528410367/4420800000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (41813/100000 : ℝ) ^ (133/32 : ℝ) ≤ (2667320536982227683/100000000000000000000 : ℝ) := by
    have hpowers : (41813/100000 : ℝ)^133 ≤ (2667320536982227683/100000000000000000000 : ℝ)^32 := by
      have hnat : (41813 : ℕ)^133*100000000000000000000^32 ≤ 2667320536982227683^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        41813 100000 2667320536982227683 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (41813/100000 : ℝ)) (X := (2667320536982227683/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner2a : (102667320536982227683/100000000000000000000 : ℝ) ≤ (314485504823381/312500000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (102667320536982227683/100000000000000000000 : ℝ)^32 ≤ (314485504823381/312500000000000 : ℝ)^133 := by
      have hnat : (102667320536982227683 : ℕ)^32*312500000000000^133 ≤ 314485504823381^133*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102667320536982227683 100000000000000000000 314485504823381 312500000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (314485504823381/312500000000000 : ℝ)) (X := (102667320536982227683/100000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner2b : (52667320536982227683/50000000000000000000 : ℝ) ≤ (5062915437870007/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (52667320536982227683/50000000000000000000 : ℝ)^32 ≤ (5062915437870007/5000000000000000 : ℝ)^133 := by
      have hnat : (52667320536982227683 : ℕ)^32*5000000000000000^133 ≤ 5062915437870007^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52667320536982227683 50000000000000000000 5062915437870007 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5062915437870007/5000000000000000 : ℝ)) (X := (52667320536982227683/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1985504823381/130665625000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(31147360695911/2090650000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (41813/100000 : ℝ)) (alpha := (1985504823381/130665625000000 : ℝ)) (beta := (31147360695911/2090650000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (41813/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1985504823381/130665625000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(31147360695911/2090650000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_1 : ((3126202541/10000000000 : ℝ)*X 1 0+(-3123203161/10000000000 : ℝ)*X 1 1+(6485275299/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305057_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((97890309/200000000 : ℝ)*X 0 0+(979618711/2000000000 : ℝ)*X 0 1+(3128634817/10000000000 : ℝ)*X 0 2+(97890309/200000000 : ℝ)*X 1 0+(979618711/2000000000 : ℝ)*X 1 1+(3128634817/10000000000 : ℝ)*X 1 2+(97890309/200000000 : ℝ)*X 2 0+(979618711/2000000000 : ℝ)*X 2 1+(3128634817/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305057_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-2213797373/10000000000 : ℝ)*X 0 0+(438810317/2500000000 : ℝ)*X 0 1+(8117794777/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305057_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((1105277443/5000000000 : ℝ)*X 1 0+(-350534083/2000000000 : ℝ)*X 1 1+(4060770343/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305057_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((926869053/2500000000 : ℝ)*X 2 0+(982107189/1250000000 : ℝ)*X 2 1+(311/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305057_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_12 : ((3373780449/10000000000 : ℝ)*X 0 0+(7149691799/10000000000 : ℝ)*X 0 1+(973579329/5000000000 : ℝ)*X 0 2+(3373780449/10000000000 : ℝ)*X 1 0+(7149691799/10000000000 : ℝ)*X 1 1+(973579329/5000000000 : ℝ)*X 1 2+(3373780449/10000000000 : ℝ)*X 2 0+(7149691799/10000000000 : ℝ)*X 2 1+(973579329/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305057_s2_s2_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((-1758371009/10000000000 : ℝ)*X 0 0+(552607213/2500000000 : ℝ)*X 0 1+(8118098753/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305057_s2_s2_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((1755795599/10000000000 : ℝ)*X 1 0+(-551797833/2500000000 : ℝ)*X 1 1+(4060921997/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305057_s2_s2_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((7853445663/10000000000 : ℝ)*X 2 0+(3711793479/10000000000 : ℝ)*X 2 1+(307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305057_s2_s2_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_18 : ((7146647813/10000000000 : ℝ)*X 0 0+(168886893/500000000 : ℝ)*X 0 1+(3115253/16000000 : ℝ)*X 0 2+(7146647813/10000000000 : ℝ)*X 1 0+(168886893/500000000 : ℝ)*X 1 1+(3115253/16000000 : ℝ)*X 1 2+(7146647813/10000000000 : ℝ)*X 2 0+(168886893/500000000 : ℝ)*X 2 1+(3115253/16000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305057_s2_s2_18 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_19 : ((-2538404721/5000000000 : ℝ)*X 0 0+(1688368389/10000000000 : ℝ)*X 0 1+(5836673489/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305057_s2_s2_19 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((1690183907/10000000000 : ℝ)*X 1 0+(-5072132359/10000000000 : ℝ)*X 1 1+(5839918927/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305057_s2_s2_20 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((6209573913/10000000000 : ℝ)*X 2 0+(347855441/625000000 : ℝ)*X 2 1+(11676419/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305057_s2_s2_21 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_25 : ((696851113/2000000000 : ℝ)*X 0 0+(347855441/625000000 : ℝ)*X 0 1+(3862560513/10000000000 : ℝ)*X 0 2+(696851113/2000000000 : ℝ)*X 1 0+(347855441/625000000 : ℝ)*X 1 1+(3862560513/10000000000 : ℝ)*X 1 2+(696851113/2000000000 : ℝ)*X 2 0+(347855441/625000000 : ℝ)*X 2 1+(3862560513/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305057_s2_s2_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((39417/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(39417/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (143585687738572053479899155527/37924424450400000000000000000000000 : ℝ) := by norm_num
    linear_combination (403277982519/500000000000 : ℝ)*(base7) + (445187/1000000000000 : ℝ)*(base13) + (135215066431/1000000000000 : ℝ)*(base59) + (6406881333/200000000000 : ℝ)*(base60) + (2103197077339/1000000000000 : ℝ)*(major_s2_0) + (2103197077339/1000000000000 : ℝ)*(major_s2_1) + (2103197077339/1000000000000 : ℝ)*(major_s2_2) + (158251/1000000000000 : ℝ)*(sp_s2_1) + (2328628402379/1000000000000 : ℝ)*(sp_s2_7) + (145539918333/62500000000 : ℝ)*(sp_s2_8) + (2328638851579/1000000000000 : ℝ)*(sp_s2_9) + (1090920334387/500000000000 : ℝ)*(sp_s2_12) + (10004013/1000000000000 : ℝ)*(sp_s2_13) + (68889/62500000000 : ℝ)*(sp_s2_25) + (34382145149/25000000000 : ℝ)*(f.failure) + (2328638851579/1000000000000 : ℝ)*(f.sum) + (15378205417878423223/369693820800000000000000000000000 : ℝ)*base62 + (2645229631597001/2090650000000000000000000000 : ℝ)*base65 + (471321258263333/4420800000000000000000000000 : ℝ)*base67 + (85309361287069/2090650000000000000000000000 : ℝ)*base68 + (462734664130211673143/370596981600000000000000000000000 : ℝ)*base71 + (258293552704391/2215800000000000000000000000 : ℝ)*base73 + (111218123701741/353664000000000000000000000 : ℝ)*base75 + (2263164571126843/8863200000000000000000000000 : ℝ)*base77 + (141684107590707771/604667200000000000000000000000 : ℝ)*base79 + (307/625000000000000 : ℝ)*base86 + (307/625000000000000 : ℝ)*base88 + (307/625000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19699/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(19699/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (271929929402133215569642147/15441540900000000000000000000000 : ℝ) := by norm_num
    linear_combination (403217503179/500000000000 : ℝ)*(base7) + (193327/125000000000 : ℝ)*(base40) + (134899649749/1000000000000 : ℝ)*(base59) + (51487661079/500000000000 : ℝ)*(base60) + (525636124303/250000000000 : ℝ)*(major_s2_0) + (525636124303/250000000000 : ℝ)*(major_s2_1) + (525636124303/250000000000 : ℝ)*(major_s2_2) + (4473997/500000000000 : ℝ)*(sp_s2_1) + (3686251/500000000000 : ℝ)*(sp_s2_6) + (157396987/1000000000000 : ℝ)*(sp_s2_8) + (2327831161873/1000000000000 : ℝ)*(sp_s2_13) + (581916204223/250000000000 : ℝ)*(sp_s2_14) + (2327831161873/1000000000000 : ℝ)*(sp_s2_15) + (1090643358023/500000000000 : ℝ)*(sp_s2_18) + (137485908219/100000000000 : ℝ)*(f.failure) + (2327831161873/1000000000000 : ℝ)*(f.sum) + (43640517969987942571/92423455200000000000000000000000 : ℝ)*base62 + (164893447109039/1045325000000000000000000000 : ℝ)*base65 + (149238512359/1105200000000000000000000000 : ℝ)*base66 + (501412700141541/1045325000000000000000000000 : ℝ)*base68 + (29163780910345550089/92649245400000000000000000000000 : ℝ)*base70 + (222492372731267/553950000000000000000000000 : ℝ)*base73 + (5765299483177/88416000000000000000000000 : ℝ)*base75 + (1310809764021629/2215800000000000000000000000 : ℝ)*base76 + (56015691515377687/151166800000000000000000000000 : ℝ)*base79 + (149/312500000000000 : ℝ)*base86 + (149/312500000000000 : ℝ)*base88 + (149/312500000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(27933/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(27933/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (105599352022486699104318755831/15169769780160000000000000000000000 : ℝ) := by norm_num
    linear_combination (18554885131/40000000000 : ℝ)*(base5) + (182794863657/1000000000000 : ℝ)*(base7) + (3197999/250000000000 : ℝ)*(base8) + (2545309/200000000000 : ℝ)*(base16) + (26267/500000000000 : ℝ)*(base50) + (208110695329/250000000000 : ℝ)*(base59) + (1667410265399/1000000000000 : ℝ)*(major_s2_0) + (1667410265399/1000000000000 : ℝ)*(major_s2_1) + (1667410265399/1000000000000 : ℝ)*(major_s2_2) + (13707/500000000000 : ℝ)*(sp_s2_6) + (2130604149747/1000000000000 : ℝ)*(sp_s2_19) + (1065302107599/500000000000 : ℝ)*(sp_s2_20) + (1297244535009/500000000000 : ℝ)*(sp_s2_21) + (50577902029/62500000000 : ℝ)*(sp_s2_25) + (1090323724497/1000000000000 : ℝ)*(f.failure) + (2130616941743/1000000000000 : ℝ)*(f.sum) + (113335700153350335037/369693820800000000000000000000000 : ℝ)*base63 + (925598370105803/1045325000000000000000000000 : ℝ)*base65 + (1079491118601193/4420800000000000000000000000 : ℝ)*base67 + (568437141861853/1045325000000000000000000000 : ℝ)*base69 + (240549119952197873683/370596981600000000000000000000000 : ℝ)*base71 + (1057106858968831/2215800000000000000000000000 : ℝ)*base73 + (315234395393201/353664000000000000000000000 : ℝ)*base75 + (6154321169583383/8863200000000000000000000000 : ℝ)*base77 + (3225705089093751/604667200000000000000000000000 : ℝ)*base79 + (89/390625000000000 : ℝ)*base86 + (89/390625000000000 : ℝ)*base88 + (89/390625000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((11079/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11079/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2763/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2763/3125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(41813/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(41813/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((39417/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(39417/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19699/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(19699/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(27933/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(27933/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c305057_s2 p hpa hpb X hX hprev1

#print axioms solution
