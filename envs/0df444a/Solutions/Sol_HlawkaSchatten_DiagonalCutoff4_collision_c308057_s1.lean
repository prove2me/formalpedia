-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c308057_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:37:17.909107+00:00
-- url     : https://prove2.me/submissions/86a7f540-d6eb-40af-bf77-4823966f5836

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
theorem collision_support_c308057_s1_s1_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-618496027/2000000000 : ℝ)*x 0 + (192369317/625000000 : ℝ)*x 1 + (202199731/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (618496027/2000000000 : ℝ)^69 ≤ (21698879549939/100000000000000 : ℝ)^53 := by
    have hnat : (618496027 : ℕ)^69*100000000000000^53 ≤ 21698879549939^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      618496027 2000000000 21698879549939 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (192369317/625000000 : ℝ)^69 ≤ (21565869173339/100000000000000 : ℝ)^53 := by
    have hnat : (192369317 : ℕ)^69*100000000000000^53 ≤ 21565869173339^53*625000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192369317 625000000 21565869173339 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (202199731/312500000 : ℝ)^69 ≤ (56735251260029/100000000000000 : ℝ)^53 := by
    have hnat : (202199731 : ℕ)^69*100000000000000^53 ≤ 56735251260029^53*312500000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202199731 312500000 56735251260029 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-618496027/2000000000 : ℝ), (192369317/625000000 : ℝ), (202199731/312500000 : ℝ)] ![(21698879549939/100000000000000 : ℝ), (21565869173339/100000000000000 : ℝ), (56735251260029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-618496027/2000000000 : ℝ)|^69 ≤ (21698879549939/100000000000000 : ℝ)^53
        have hw : |(-618496027/2000000000 : ℝ)|=(618496027/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(192369317/625000000 : ℝ)|^69 ≤ (21565869173339/100000000000000 : ℝ)^53
        have hw : |(192369317/625000000 : ℝ)|=(192369317/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(202199731/312500000 : ℝ)|^69 ≤ (56735251260029/100000000000000 : ℝ)^53
        have hw : |(202199731/312500000 : ℝ)|=(202199731/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308057_s1_s1_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (30842261/100000000 : ℝ)*x 0 + (-383711741/1250000000 : ℝ)*x 1 + (6483551601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (30842261/100000000 : ℝ)^69 ≤ (5405877548417/25000000000000 : ℝ)^53 := by
    have hnat : (30842261 : ℕ)^69*25000000000000^53 ≤ 5405877548417^53*100000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30842261 100000000 5405877548417 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (383711741/1250000000 : ℝ)^69 ≤ (1343185113559/6250000000000 : ℝ)^53 := by
    have hnat : (383711741 : ℕ)^69*6250000000000^53 ≤ 1343185113559^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      383711741 1250000000 1343185113559 6250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6483551601/10000000000 : ℝ)^69 ≤ (56885527972511/100000000000000 : ℝ)^53 := by
    have hnat : (6483551601 : ℕ)^69*100000000000000^53 ≤ 56885527972511^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6483551601 10000000000 56885527972511 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(30842261/100000000 : ℝ), (-383711741/1250000000 : ℝ), (6483551601/10000000000 : ℝ)] ![(5405877548417/25000000000000 : ℝ), (1343185113559/6250000000000 : ℝ), (56885527972511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(30842261/100000000 : ℝ)|^69 ≤ (5405877548417/25000000000000 : ℝ)^53
        have hw : |(30842261/100000000 : ℝ)|=(30842261/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-383711741/1250000000 : ℝ)|^69 ≤ (1343185113559/6250000000000 : ℝ)^53
        have hw : |(-383711741/1250000000 : ℝ)|=(383711741/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6483551601/10000000000 : ℝ)|^69 ≤ (56885527972511/100000000000000 : ℝ)^53
        have hw : |(6483551601/10000000000 : ℝ)|=(6483551601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308057_s1_s1_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1172254099/2000000000 : ℝ)*x 0 + (1176364819/2000000000 : ℝ)*x 1 + (1199099/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1172254099/2000000000 : ℝ)^69 ≤ (49882882598929/100000000000000 : ℝ)^53 := by
    have hnat : (1172254099 : ℕ)^69*100000000000000^53 ≤ 49882882598929^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1172254099 2000000000 49882882598929 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1176364819/2000000000 : ℝ)^69 ≤ (1252768334581/2500000000000 : ℝ)^53 := by
    have hnat : (1176364819 : ℕ)^69*2500000000000^53 ≤ 1252768334581^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1176364819 2000000000 1252768334581 2500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1199099/2000000000 : ℝ)^69 ≤ (6384001543/100000000000000 : ℝ)^53 := by
    have hnat : (1199099 : ℕ)^69*100000000000000^53 ≤ 6384001543^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1199099 2000000000 6384001543 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1172254099/2000000000 : ℝ), (1176364819/2000000000 : ℝ), (1199099/2000000000 : ℝ)] ![(49882882598929/100000000000000 : ℝ), (1252768334581/2500000000000 : ℝ), (6384001543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1172254099/2000000000 : ℝ)|^69 ≤ (49882882598929/100000000000000 : ℝ)^53
        have hw : |(1172254099/2000000000 : ℝ)|=(1172254099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1176364819/2000000000 : ℝ)|^69 ≤ (1252768334581/2500000000000 : ℝ)^53
        have hw : |(1176364819/2000000000 : ℝ)|=(1176364819/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1199099/2000000000 : ℝ)|^69 ≤ (6384001543/100000000000000 : ℝ)^53
        have hw : |(1199099/2000000000 : ℝ)|=(1199099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308057_s1_s1_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4873866493/10000000000 : ℝ)*x 0 + (4890957583/10000000000 : ℝ)*x 1 + (3054837253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4873866493/10000000000 : ℝ)^69 ≤ (39232573725589/100000000000000 : ℝ)^53 := by
    have hnat : (4873866493 : ℕ)^69*100000000000000^53 ≤ 39232573725589^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4873866493 10000000000 39232573725589 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4890957583/10000000000 : ℝ)^69 ≤ (39411776934309/100000000000000 : ℝ)^53 := by
    have hnat : (4890957583 : ℕ)^69*100000000000000^53 ≤ 39411776934309^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4890957583 10000000000 39411776934309 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3054837253/10000000000 : ℝ)^69 ≤ (10677824664367/50000000000000 : ℝ)^53 := by
    have hnat : (3054837253 : ℕ)^69*50000000000000^53 ≤ 10677824664367^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3054837253 10000000000 10677824664367 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4873866493/10000000000 : ℝ), (4890957583/10000000000 : ℝ), (3054837253/10000000000 : ℝ)] ![(39232573725589/100000000000000 : ℝ), (39411776934309/100000000000000 : ℝ), (10677824664367/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4873866493/10000000000 : ℝ)|^69 ≤ (39232573725589/100000000000000 : ℝ)^53
        have hw : |(4873866493/10000000000 : ℝ)|=(4873866493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4890957583/10000000000 : ℝ)|^69 ≤ (39411776934309/100000000000000 : ℝ)^53
        have hw : |(4890957583/10000000000 : ℝ)|=(4890957583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3054837253/10000000000 : ℝ)|^69 ≤ (10677824664367/50000000000000 : ℝ)^53
        have hw : |(3054837253/10000000000 : ℝ)|=(3054837253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308057_s1_s1_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-42201387/200000000 : ℝ)*x 0 + (124737919/1000000000 : ℝ)*x 1 + (8437286163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42201387/200000000 : ℝ)^69 ≤ (13192005875457/100000000000000 : ℝ)^53 := by
    have hnat : (42201387 : ℕ)^69*100000000000000^53 ≤ 13192005875457^53*200000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42201387 200000000 13192005875457 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (124737919/1000000000 : ℝ)^69 ≤ (3327073413567/50000000000000 : ℝ)^53 := by
    have hnat : (124737919 : ℕ)^69*50000000000000^53 ≤ 3327073413567^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124737919 1000000000 3327073413567 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8437286163/10000000000 : ℝ)^69 ≤ (16030769456929/20000000000000 : ℝ)^53 := by
    have hnat : (8437286163 : ℕ)^69*20000000000000^53 ≤ 16030769456929^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8437286163 10000000000 16030769456929 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-42201387/200000000 : ℝ), (124737919/1000000000 : ℝ), (8437286163/10000000000 : ℝ)] ![(13192005875457/100000000000000 : ℝ), (3327073413567/50000000000000 : ℝ), (16030769456929/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-42201387/200000000 : ℝ)|^69 ≤ (13192005875457/100000000000000 : ℝ)^53
        have hw : |(-42201387/200000000 : ℝ)|=(42201387/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(124737919/1000000000 : ℝ)|^69 ≤ (3327073413567/50000000000000 : ℝ)^53
        have hw : |(124737919/1000000000 : ℝ)|=(124737919/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8437286163/10000000000 : ℝ)|^69 ≤ (16030769456929/20000000000000 : ℝ)^53
        have hw : |(8437286163/10000000000 : ℝ)|=(8437286163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308057_s1_s1_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1717245677/10000000000 : ℝ)*x 0 + (-411419261/2500000000 : ℝ)*x 1 + (1690892841/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1717245677/10000000000 : ℝ)^69 ≤ (2522193821947/25000000000000 : ℝ)^53 := by
    have hnat : (1717245677 : ℕ)^69*25000000000000^53 ≤ 2522193821947^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1717245677 10000000000 2522193821947 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (411419261/2500000000 : ℝ)^69 ≤ (9544856409143/100000000000000 : ℝ)^53 := by
    have hnat : (411419261 : ℕ)^69*100000000000000^53 ≤ 9544856409143^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411419261 2500000000 9544856409143 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1690892841/2000000000 : ℝ)^69 ≤ (80366368287689/100000000000000 : ℝ)^53 := by
    have hnat : (1690892841 : ℕ)^69*100000000000000^53 ≤ 80366368287689^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1690892841 2000000000 80366368287689 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1717245677/10000000000 : ℝ), (-411419261/2500000000 : ℝ), (1690892841/2000000000 : ℝ)] ![(2522193821947/25000000000000 : ℝ), (9544856409143/100000000000000 : ℝ), (80366368287689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1717245677/10000000000 : ℝ)|^69 ≤ (2522193821947/25000000000000 : ℝ)^53
        have hw : |(1717245677/10000000000 : ℝ)|=(1717245677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-411419261/2500000000 : ℝ)|^69 ≤ (9544856409143/100000000000000 : ℝ)^53
        have hw : |(-411419261/2500000000 : ℝ)|=(411419261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1690892841/2000000000 : ℝ)|^69 ≤ (80366368287689/100000000000000 : ℝ)^53
        have hw : |(1690892841/2000000000 : ℝ)|=(1690892841/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308057_s1_s1_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1691230699/5000000000 : ℝ)*x 0 + (2016967497/2500000000 : ℝ)*x 1 + (-449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1691230699/5000000000 : ℝ)^69 ≤ (6096133546343/25000000000000 : ℝ)^53 := by
    have hnat : (1691230699 : ℕ)^69*25000000000000^53 ≤ 6096133546343^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1691230699 5000000000 6096133546343 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2016967497/2500000000 : ℝ)^69 ≤ (75615465785687/100000000000000 : ℝ)^53 := by
    have hnat : (2016967497 : ℕ)^69*100000000000000^53 ≤ 75615465785687^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016967497 2500000000 75615465785687 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (449/10000000000 : ℝ)^69 ≤ (849/3125000000000 : ℝ)^53 := by
    have hnat : (449 : ℕ)^69*3125000000000^53 ≤ 849^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449 10000000000 849 3125000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1691230699/5000000000 : ℝ), (2016967497/2500000000 : ℝ), (-449/10000000000 : ℝ)] ![(6096133546343/25000000000000 : ℝ), (75615465785687/100000000000000 : ℝ), (849/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1691230699/5000000000 : ℝ)|^69 ≤ (6096133546343/25000000000000 : ℝ)^53
        have hw : |(1691230699/5000000000 : ℝ)|=(1691230699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2016967497/2500000000 : ℝ)|^69 ≤ (75615465785687/100000000000000 : ℝ)^53
        have hw : |(2016967497/2500000000 : ℝ)|=(2016967497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-449/10000000000 : ℝ)|^69 ≤ (849/3125000000000 : ℝ)^53
        have hw : |(-449/10000000000 : ℝ)|=(449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308057_s1_s1_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3006755899/10000000000 : ℝ)*x 0 + (7418415729/10000000000 : ℝ)*x 1 + (936230197/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3006755899/10000000000 : ℝ)^69 ≤ (20919095509419/100000000000000 : ℝ)^53 := by
    have hnat : (3006755899 : ℕ)^69*100000000000000^53 ≤ 20919095509419^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3006755899 10000000000 20919095509419 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7418415729/10000000000 : ℝ)^69 ≤ (67789092806329/100000000000000 : ℝ)^53 := by
    have hnat : (7418415729 : ℕ)^69*100000000000000^53 ≤ 67789092806329^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7418415729 10000000000 67789092806329 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (936230197/5000000000 : ℝ)^69 ≤ (11291811668081/100000000000000 : ℝ)^53 := by
    have hnat : (936230197 : ℕ)^69*100000000000000^53 ≤ 11291811668081^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      936230197 5000000000 11291811668081 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3006755899/10000000000 : ℝ), (7418415729/10000000000 : ℝ), (936230197/5000000000 : ℝ)] ![(20919095509419/100000000000000 : ℝ), (67789092806329/100000000000000 : ℝ), (11291811668081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3006755899/10000000000 : ℝ)|^69 ≤ (20919095509419/100000000000000 : ℝ)^53
        have hw : |(3006755899/10000000000 : ℝ)|=(3006755899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7418415729/10000000000 : ℝ)|^69 ≤ (67789092806329/100000000000000 : ℝ)^53
        have hw : |(7418415729/10000000000 : ℝ)|=(7418415729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(936230197/5000000000 : ℝ)|^69 ≤ (11291811668081/100000000000000 : ℝ)^53
        have hw : |(936230197/5000000000 : ℝ)|=(936230197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308057_s1_s1_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1678889447/10000000000 : ℝ)*x 0 + (1716970653/10000000000 : ℝ)*x 1 + (8434300927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1678889447/10000000000 : ℝ)^69 ≤ (1959279986307/20000000000000 : ℝ)^53 := by
    have hnat : (1678889447 : ℕ)^69*20000000000000^53 ≤ 1959279986307^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1678889447 10000000000 1959279986307 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1716970653/10000000000 : ℝ)^69 ≤ (2017334360641/20000000000000 : ℝ)^53 := by
    have hnat : (1716970653 : ℕ)^69*20000000000000^53 ≤ 2017334360641^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1716970653 10000000000 2017334360641 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8434300927/10000000000 : ℝ)^69 ≤ (80116928254077/100000000000000 : ℝ)^53 := by
    have hnat : (8434300927 : ℕ)^69*100000000000000^53 ≤ 80116928254077^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8434300927 10000000000 80116928254077 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1678889447/10000000000 : ℝ), (1716970653/10000000000 : ℝ), (8434300927/10000000000 : ℝ)] ![(1959279986307/20000000000000 : ℝ), (2017334360641/20000000000000 : ℝ), (80116928254077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1678889447/10000000000 : ℝ)|^69 ≤ (1959279986307/20000000000000 : ℝ)^53
        have hw : |(-1678889447/10000000000 : ℝ)|=(1678889447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1716970653/10000000000 : ℝ)|^69 ≤ (2017334360641/20000000000000 : ℝ)^53
        have hw : |(1716970653/10000000000 : ℝ)|=(1716970653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8434300927/10000000000 : ℝ)|^69 ≤ (80116928254077/100000000000000 : ℝ)^53
        have hw : |(8434300927/10000000000 : ℝ)|=(8434300927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308057_s1_s1_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (156726781/1250000000 : ℝ)*x 0 + (-2082963197/10000000000 : ℝ)*x 1 + (8451470173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (156726781/1250000000 : ℝ)^69 ≤ (3349436267303/50000000000000 : ℝ)^53 := by
    have hnat : (156726781 : ℕ)^69*50000000000000^53 ≤ 3349436267303^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156726781 1250000000 3349436267303 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2082963197/10000000000 : ℝ)^69 ≤ (12971809711761/100000000000000 : ℝ)^53 := by
    have hnat : (2082963197 : ℕ)^69*100000000000000^53 ≤ 12971809711761^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082963197 10000000000 12971809711761 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8451470173/10000000000 : ℝ)^69 ≤ (313786397401/390625000000 : ℝ)^53 := by
    have hnat : (8451470173 : ℕ)^69*390625000000^53 ≤ 313786397401^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8451470173 10000000000 313786397401 390625000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(156726781/1250000000 : ℝ), (-2082963197/10000000000 : ℝ), (8451470173/10000000000 : ℝ)] ![(3349436267303/50000000000000 : ℝ), (12971809711761/100000000000000 : ℝ), (313786397401/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(156726781/1250000000 : ℝ)|^69 ≤ (3349436267303/50000000000000 : ℝ)^53
        have hw : |(156726781/1250000000 : ℝ)|=(156726781/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2082963197/10000000000 : ℝ)|^69 ≤ (12971809711761/100000000000000 : ℝ)^53
        have hw : |(-2082963197/10000000000 : ℝ)|=(2082963197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8451470173/10000000000 : ℝ)|^69 ≤ (313786397401/390625000000 : ℝ)^53
        have hw : |(8451470173/10000000000 : ℝ)|=(8451470173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308057_s1_s1_16 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8066348897/10000000000 : ℝ)*x 0 + (846109677/2500000000 : ℝ)*x 1 + (-9/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8066348897/10000000000 : ℝ)^69 ≤ (18899226555113/25000000000000 : ℝ)^53 := by
    have hnat : (8066348897 : ℕ)^69*25000000000000^53 ≤ 18899226555113^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8066348897 10000000000 18899226555113 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (846109677/2500000000 : ℝ)^69 ≤ (4880618751101/20000000000000 : ℝ)^53 := by
    have hnat : (846109677 : ℕ)^69*20000000000000^53 ≤ 4880618751101^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846109677 2500000000 4880618751101 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9/400000000 : ℝ)^69 ≤ (2763/25000000000000 : ℝ)^53 := by
    have hnat : (9 : ℕ)^69*25000000000000^53 ≤ 2763^53*400000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9 400000000 2763 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8066348897/10000000000 : ℝ), (846109677/2500000000 : ℝ), (-9/400000000 : ℝ)] ![(18899226555113/25000000000000 : ℝ), (4880618751101/20000000000000 : ℝ), (2763/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8066348897/10000000000 : ℝ)|^69 ≤ (18899226555113/25000000000000 : ℝ)^53
        have hw : |(8066348897/10000000000 : ℝ)|=(8066348897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(846109677/2500000000 : ℝ)|^69 ≤ (4880618751101/20000000000000 : ℝ)^53
        have hw : |(846109677/2500000000 : ℝ)|=(846109677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-9/400000000 : ℝ)|^69 ≤ (2763/25000000000000 : ℝ)^53
        have hw : |(-9/400000000 : ℝ)|=(9/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308057_s1_s1_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1476620263/2000000000 : ℝ)*x 0 + (3052126853/10000000000 : ℝ)*x 1 + (1873470251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1476620263/2000000000 : ℝ)^69 ≤ (33684637255949/50000000000000 : ℝ)^53 := by
    have hnat : (1476620263 : ℕ)^69*50000000000000^53 ≤ 33684637255949^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1476620263 2000000000 33684637255949 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3052126853/10000000000 : ℝ)^69 ≤ (21330984782263/100000000000000 : ℝ)^53 := by
    have hnat : (3052126853 : ℕ)^69*100000000000000^53 ≤ 21330984782263^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3052126853 10000000000 21330984782263 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1873470251/10000000000 : ℝ)^69 ≤ (5649870343333/50000000000000 : ℝ)^53 := by
    have hnat : (1873470251 : ℕ)^69*50000000000000^53 ≤ 5649870343333^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1873470251 10000000000 5649870343333 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1476620263/2000000000 : ℝ), (3052126853/10000000000 : ℝ), (1873470251/10000000000 : ℝ)] ![(33684637255949/50000000000000 : ℝ), (21330984782263/100000000000000 : ℝ), (5649870343333/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1476620263/2000000000 : ℝ)|^69 ≤ (33684637255949/50000000000000 : ℝ)^53
        have hw : |(1476620263/2000000000 : ℝ)|=(1476620263/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3052126853/10000000000 : ℝ)|^69 ≤ (21330984782263/100000000000000 : ℝ)^53
        have hw : |(3052126853/10000000000 : ℝ)|=(3052126853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1873470251/10000000000 : ℝ)|^69 ≤ (5649870343333/50000000000000 : ℝ)^53
        have hw : |(1873470251/10000000000 : ℝ)|=(1873470251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308057_s1_s1_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-695598967/1250000000 : ℝ)*x 0 + (88296613/500000000 : ℝ)*x 1 + (5221471021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (695598967/1250000000 : ℝ)^69 ≤ (23311665848593/50000000000000 : ℝ)^53 := by
    have hnat : (695598967 : ℕ)^69*50000000000000^53 ≤ 23311665848593^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      695598967 1250000000 23311665848593 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (88296613/500000000 : ℝ)^69 ≤ (5231370186807/50000000000000 : ℝ)^53 := by
    have hnat : (88296613 : ℕ)^69*50000000000000^53 ≤ 5231370186807^53*500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88296613 500000000 5231370186807 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5221471021/10000000000 : ℝ)^69 ≤ (42913927914649/100000000000000 : ℝ)^53 := by
    have hnat : (5221471021 : ℕ)^69*100000000000000^53 ≤ 42913927914649^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221471021 10000000000 42913927914649 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-695598967/1250000000 : ℝ), (88296613/500000000 : ℝ), (5221471021/10000000000 : ℝ)] ![(23311665848593/50000000000000 : ℝ), (5231370186807/50000000000000 : ℝ), (42913927914649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-695598967/1250000000 : ℝ)|^69 ≤ (23311665848593/50000000000000 : ℝ)^53
        have hw : |(-695598967/1250000000 : ℝ)|=(695598967/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(88296613/500000000 : ℝ)|^69 ≤ (5231370186807/50000000000000 : ℝ)^53
        have hw : |(88296613/500000000 : ℝ)|=(88296613/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5221471021/10000000000 : ℝ)|^69 ≤ (42913927914649/100000000000000 : ℝ)^53
        have hw : |(5221471021/10000000000 : ℝ)|=(5221471021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308057_s1_s1_22 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (151212881/2000000000 : ℝ)*x 0 + (-5353679267/10000000000 : ℝ)*x 1 + (3034586229/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (151212881/2000000000 : ℝ)^69 ≤ (693490472307/20000000000000 : ℝ)^53 := by
    have hnat : (151212881 : ℕ)^69*20000000000000^53 ≤ 693490472307^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151212881 2000000000 693490472307 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5353679267/10000000000 : ℝ)^69 ≤ (44333914326637/100000000000000 : ℝ)^53 := by
    have hnat : (5353679267 : ℕ)^69*100000000000000^53 ≤ 44333914326637^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353679267 10000000000 44333914326637 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3034586229/5000000000 : ℝ)^69 ≤ (1304965832481/2500000000000 : ℝ)^53 := by
    have hnat : (3034586229 : ℕ)^69*2500000000000^53 ≤ 1304965832481^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3034586229 5000000000 1304965832481 2500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(151212881/2000000000 : ℝ), (-5353679267/10000000000 : ℝ), (3034586229/5000000000 : ℝ)] ![(693490472307/20000000000000 : ℝ), (44333914326637/100000000000000 : ℝ), (1304965832481/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(151212881/2000000000 : ℝ)|^69 ≤ (693490472307/20000000000000 : ℝ)^53
        have hw : |(151212881/2000000000 : ℝ)|=(151212881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5353679267/10000000000 : ℝ)|^69 ≤ (44333914326637/100000000000000 : ℝ)^53
        have hw : |(-5353679267/10000000000 : ℝ)|=(5353679267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3034586229/5000000000 : ℝ)|^69 ≤ (1304965832481/2500000000000 : ℝ)^53
        have hw : |(3034586229/5000000000 : ℝ)|=(3034586229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308057_s1_s1_23 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (249811379/400000000 : ℝ)*x 0 + (5463483027/10000000000 : ℝ)*x 1 + (57617697/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (249811379/400000000 : ℝ)^69 ≤ (54179144424533/100000000000000 : ℝ)^53 := by
    have hnat : (249811379 : ℕ)^69*100000000000000^53 ≤ 54179144424533^53*400000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249811379 400000000 54179144424533 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5463483027/10000000000 : ℝ)^69 ≤ (22760675215699/50000000000000 : ℝ)^53 := by
    have hnat : (5463483027 : ℕ)^69*50000000000000^53 ≤ 22760675215699^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463483027 10000000000 22760675215699 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (57617697/5000000000 : ℝ)^69 ≤ (5990102707/2000000000000 : ℝ)^53 := by
    have hnat : (57617697 : ℕ)^69*2000000000000^53 ≤ 5990102707^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57617697 5000000000 5990102707 2000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(249811379/400000000 : ℝ), (5463483027/10000000000 : ℝ), (57617697/5000000000 : ℝ)] ![(54179144424533/100000000000000 : ℝ), (22760675215699/50000000000000 : ℝ), (5990102707/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(249811379/400000000 : ℝ)|^69 ≤ (54179144424533/100000000000000 : ℝ)^53
        have hw : |(249811379/400000000 : ℝ)|=(249811379/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5463483027/10000000000 : ℝ)|^69 ≤ (22760675215699/50000000000000 : ℝ)^53
        have hw : |(5463483027/10000000000 : ℝ)|=(5463483027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(57617697/5000000000 : ℝ)|^69 ≤ (5990102707/2000000000000 : ℝ)^53
        have hw : |(57617697/5000000000 : ℝ)|=(57617697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308057_s1_s1_27 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (174988921/625000000 : ℝ)*x 0 + (5463483027/10000000000 : ℝ)*x 1 + (2252605107/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174988921/625000000 : ℝ)^69 ≤ (1906454947821/10000000000000 : ℝ)^53 := by
    have hnat : (174988921 : ℕ)^69*10000000000000^53 ≤ 1906454947821^53*625000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174988921 625000000 1906454947821 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5463483027/10000000000 : ℝ)^69 ≤ (22760675215699/50000000000000 : ℝ)^53 := by
    have hnat : (5463483027 : ℕ)^69*50000000000000^53 ≤ 22760675215699^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463483027 10000000000 22760675215699 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2252605107/5000000000 : ℝ)^69 ≤ (35414100079407/100000000000000 : ℝ)^53 := by
    have hnat : (2252605107 : ℕ)^69*100000000000000^53 ≤ 35414100079407^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252605107 5000000000 35414100079407 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(174988921/625000000 : ℝ), (5463483027/10000000000 : ℝ), (2252605107/5000000000 : ℝ)] ![(1906454947821/10000000000000 : ℝ), (22760675215699/50000000000000 : ℝ), (35414100079407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(174988921/625000000 : ℝ)|^69 ≤ (1906454947821/10000000000000 : ℝ)^53
        have hw : |(174988921/625000000 : ℝ)|=(174988921/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5463483027/10000000000 : ℝ)|^69 ≤ (22760675215699/50000000000000 : ℝ)^53
        have hw : |(5463483027/10000000000 : ℝ)|=(5463483027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2252605107/5000000000 : ℝ)|^69 ≤ (35414100079407/100000000000000 : ℝ)^53
        have hw : |(2252605107/5000000000 : ℝ)|=(2252605107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308057_s1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((93471/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(93471/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(92459/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(92459/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(26639/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(26639/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((20633/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20633/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(82343/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(82343/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(7093/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(7093/20000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (93471/100000 : ℝ) ^ (17/4 : ℝ) ≤ (2345453352973269803/3125000000000000000 : ℝ) := by
    have hpowers : (93471/100000 : ℝ)^17 ≤ (2345453352973269803/3125000000000000000 : ℝ)^4 := by
      have hnat : (93471 : ℕ)^17*3125000000000000000^4 ≤ 2345453352973269803^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        93471 100000 2345453352973269803 3125000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (93471/100000 : ℝ)) (X := (2345453352973269803/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (5470453352973269803/3125000000000000000 : ℝ) ≤ (2852050789079979/2500000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (5470453352973269803/3125000000000000000 : ℝ)^4 ≤ (2852050789079979/2500000000000000 : ℝ)^17 := by
      have hnat : (5470453352973269803 : ℕ)^4*2500000000000000^17 ≤ 2852050789079979^17*3125000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5470453352973269803 3125000000000000000 2852050789079979 2500000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2852050789079979/2500000000000000 : ℝ)) (X := (5470453352973269803/3125000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (3907953352973269803/1562500000000000000 : ℝ) ≤ (12407305990187723/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (3907953352973269803/1562500000000000000 : ℝ)^4 ≤ (12407305990187723/10000000000000000 : ℝ)^17 := by
      have hnat : (3907953352973269803 : ℕ)^4*10000000000000000^17 ≤ 12407305990187723^17*1562500000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3907953352973269803 1562500000000000000 12407305990187723 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12407305990187723/10000000000000000 : ℝ)) (X := (3907953352973269803/1562500000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(352050789079979/2336775000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(999102833867807/9347100000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (93471/100000 : ℝ)) (alpha := (352050789079979/2336775000000000 : ℝ)) (beta := (999102833867807/9347100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (93471/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(352050789079979/2336775000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(999102833867807/9347100000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (92459/100000 : ℝ) ^ (17/4 : ℝ) ≤ (71661198270601653639/100000000000000000000 : ℝ) := by
    have hpowers : (92459/100000 : ℝ)^17 ≤ (71661198270601653639/100000000000000000000 : ℝ)^4 := by
      have hnat : (92459 : ℕ)^17*100000000000000000000^4 ≤ 71661198270601653639^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        92459 100000 71661198270601653639 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (92459/100000 : ℝ)) (X := (71661198270601653639/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (171661198270601653639/100000000000000000000 : ℝ) ≤ (1135578010159231/1000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (171661198270601653639/100000000000000000000 : ℝ)^4 ≤ (1135578010159231/1000000000000000 : ℝ)^17 := by
      have hnat : (171661198270601653639 : ℕ)^4*1000000000000000^17 ≤ 1135578010159231^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        171661198270601653639 100000000000000000000 1135578010159231 1000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1135578010159231/1000000000000000 : ℝ)) (X := (171661198270601653639/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (121661198270601653639/50000000000000000000 : ℝ) ≤ (770453425390491/625000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (121661198270601653639/50000000000000000000 : ℝ)^4 ≤ (770453425390491/625000000000000 : ℝ)^17 := by
      have hnat : (121661198270601653639 : ℕ)^4*625000000000000^17 ≤ 770453425390491^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        121661198270601653639 50000000000000000000 770453425390491 625000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (770453425390491/625000000000000 : ℝ)) (X := (121661198270601653639/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(135578010159231/924590000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(485737352327773/4622950000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (92459/100000 : ℝ)) (alpha := (135578010159231/924590000000000 : ℝ)) (beta := (485737352327773/4622950000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (92459/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(135578010159231/924590000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(485737352327773/4622950000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (26639/50000 : ℝ) ^ (17/4 : ℝ) ≤ (860475769648232347/12500000000000000000 : ℝ) := by
    have hpowers : (26639/50000 : ℝ)^17 ≤ (860475769648232347/12500000000000000000 : ℝ)^4 := by
      have hnat : (26639 : ℕ)^17*12500000000000000000^4 ≤ 860475769648232347^4*50000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26639 50000 860475769648232347 12500000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26639/50000 : ℝ)) (X := (860475769648232347/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (13360475769648232347/12500000000000000000 : ℝ) ≤ (10157873557063519/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (13360475769648232347/12500000000000000000 : ℝ)^4 ≤ (10157873557063519/10000000000000000 : ℝ)^17 := by
      have hnat : (13360475769648232347 : ℕ)^4*10000000000000000^17 ≤ 10157873557063519^17*12500000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13360475769648232347 12500000000000000000 10157873557063519 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10157873557063519/10000000000000000 : ℝ)) (X := (13360475769648232347/12500000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (7110475769648232347/6250000000000000000 : ℝ) ≤ (1288519128836179/1250000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (7110475769648232347/6250000000000000000 : ℝ)^4 ≤ (1288519128836179/1250000000000000 : ℝ)^17 := by
      have hnat : (7110475769648232347 : ℕ)^4*1250000000000000^17 ≤ 1288519128836179^17*6250000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7110475769648232347 6250000000000000000 1288519128836179 1250000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1288519128836179/1250000000000000 : ℝ)) (X := (7110475769648232347/6250000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(157873557063519/5327800000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(150279473625913/5327800000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (26639/50000 : ℝ)) (alpha := (157873557063519/5327800000000000 : ℝ)) (beta := (150279473625913/5327800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (26639/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(157873557063519/5327800000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(150279473625913/5327800000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-618496027/2000000000 : ℝ)*X 0 0+(192369317/625000000 : ℝ)*X 0 1+(202199731/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308057_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((30842261/100000000 : ℝ)*X 1 0+(-383711741/1250000000 : ℝ)*X 1 1+(6483551601/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308057_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1172254099/2000000000 : ℝ)*X 2 0+(1176364819/2000000000 : ℝ)*X 2 1+(1199099/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308057_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((4873866493/10000000000 : ℝ)*X 0 0+(4890957583/10000000000 : ℝ)*X 0 1+(3054837253/10000000000 : ℝ)*X 0 2+(4873866493/10000000000 : ℝ)*X 1 0+(4890957583/10000000000 : ℝ)*X 1 1+(3054837253/10000000000 : ℝ)*X 1 2+(4873866493/10000000000 : ℝ)*X 2 0+(4890957583/10000000000 : ℝ)*X 2 1+(3054837253/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308057_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-42201387/200000000 : ℝ)*X 0 0+(124737919/1000000000 : ℝ)*X 0 1+(8437286163/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308057_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((1717245677/10000000000 : ℝ)*X 1 0+(-411419261/2500000000 : ℝ)*X 1 1+(1690892841/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308057_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((1691230699/5000000000 : ℝ)*X 2 0+(2016967497/2500000000 : ℝ)*X 2 1+(-449/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308057_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((3006755899/10000000000 : ℝ)*X 0 0+(7418415729/10000000000 : ℝ)*X 0 1+(936230197/5000000000 : ℝ)*X 0 2+(3006755899/10000000000 : ℝ)*X 1 0+(7418415729/10000000000 : ℝ)*X 1 1+(936230197/5000000000 : ℝ)*X 1 2+(3006755899/10000000000 : ℝ)*X 2 0+(7418415729/10000000000 : ℝ)*X 2 1+(936230197/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308057_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-1678889447/10000000000 : ℝ)*X 0 0+(1716970653/10000000000 : ℝ)*X 0 1+(8434300927/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308057_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((156726781/1250000000 : ℝ)*X 1 0+(-2082963197/10000000000 : ℝ)*X 1 1+(8451470173/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308057_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((8066348897/10000000000 : ℝ)*X 2 0+(846109677/2500000000 : ℝ)*X 2 1+(-9/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308057_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((1476620263/2000000000 : ℝ)*X 0 0+(3052126853/10000000000 : ℝ)*X 0 1+(1873470251/10000000000 : ℝ)*X 0 2+(1476620263/2000000000 : ℝ)*X 1 0+(3052126853/10000000000 : ℝ)*X 1 1+(1873470251/10000000000 : ℝ)*X 1 2+(1476620263/2000000000 : ℝ)*X 2 0+(3052126853/10000000000 : ℝ)*X 2 1+(1873470251/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308057_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-695598967/1250000000 : ℝ)*X 0 0+(88296613/500000000 : ℝ)*X 0 1+(5221471021/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308057_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((151212881/2000000000 : ℝ)*X 1 0+(-5353679267/10000000000 : ℝ)*X 1 1+(3034586229/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308057_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((249811379/400000000 : ℝ)*X 2 0+(5463483027/10000000000 : ℝ)*X 2 1+(57617697/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308057_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((174988921/625000000 : ℝ)*X 0 0+(5463483027/10000000000 : ℝ)*X 0 1+(2252605107/5000000000 : ℝ)*X 0 2+(174988921/625000000 : ℝ)*X 1 0+(5463483027/10000000000 : ℝ)*X 1 1+(2252605107/5000000000 : ℝ)*X 1 2+(174988921/625000000 : ℝ)*X 2 0+(5463483027/10000000000 : ℝ)*X 2 1+(2252605107/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308057_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((20633/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20633/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (37532569317521095878765634637401/3837008386662850000000000000000000000 : ℝ) := by norm_num
    linear_combination (45467069841/50000000000 : ℝ)*(base7) + (392969/500000000000 : ℝ)*(base50) + (1379/976562500 : ℝ)*(base59) + (920636600047/500000000000 : ℝ)*(major_s1_0) + (920636600047/500000000000 : ℝ)*(major_s1_1) + (920636600047/500000000000 : ℝ)*(major_s1_2) + (10181/3906250000 : ℝ)*(sp_s1_0) + (243620680197/125000000000 : ℝ)*(sp_s1_7) + (1949026172153/1000000000000 : ℝ)*(sp_s1_8) + (974520499687/500000000000 : ℝ)*(sp_s1_9) + (416857584059/200000000000 : ℝ)*(sp_s1_13) + (36475731/500000000000 : ℝ)*(sp_s1_14) + (14827221/1000000000000 : ℝ)*(sp_s1_15) + (878589/500000000000 : ℝ)*(sp_s1_27) + (1174948280653/1000000000000 : ℝ)*(f.failure) + (974520499687/500000000000 : ℝ)*(f.sum) + (133296021370078046683/246301530100000000000000000000000 : ℝ)*base63 + (375003921641721/2663900000000000000000000000 : ℝ)*base64 + (1269530519874579/2311475000000000000000000000 : ℝ)*base66 + (113321465307827/2663900000000000000000000000 : ℝ)*base69 + (617494542966016579/49799479380000000000000000000000 : ℝ)*base71 + (1255435380749671/4673550000000000000000000000 : ℝ)*base72 + (320106292351879/924590000000000000000000000 : ℝ)*base75 + (684709451062363/4673550000000000000000000000 : ℝ)*base76 + (163445445755368603007/432111759450000000000000000000000 : ℝ)*base78 + (12283/100000000000000000 : ℝ)*base87 + (12283/100000000000000000 : ℝ)*base89 + (12283/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(82343/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(82343/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (70797683624609475818503919991321/3837008386662850000000000000000000000 : ℝ) := by norm_num
    linear_combination (454346923799/500000000000 : ℝ)*(base7) + (982929/500000000000 : ℝ)*(base13) + (19373/10000000000 : ℝ)*(base40) + (528566809/125000000000 : ℝ)*(base60) + (460562815653/250000000000 : ℝ)*(major_s1_0) + (460562815653/250000000000 : ℝ)*(major_s1_1) + (460562815653/250000000000 : ℝ)*(major_s1_2) + (7156743/1000000000000 : ℝ)*(sp_s1_1) + (4096189/1000000000000 : ℝ)*(sp_s1_6) + (84698491/500000000000 : ℝ)*(sp_s1_8) + (1950765900723/1000000000000 : ℝ)*(sp_s1_14) + (1950591312857/1000000000000 : ℝ)*(sp_s1_15) + (1950767866581/1000000000000 : ℝ)*(sp_s1_16) + (1042131075337/500000000000 : ℝ)*(sp_s1_20) + (235114479853/200000000000 : ℝ)*(f.failure) + (1950767866581/1000000000000 : ℝ)*(f.sum) + (50554969772946240303/123150765050000000000000000000000 : ℝ)*base62 + (301598011174649/1331950000000000000000000000 : ℝ)*base64 + (144210231161683/577868750000000000000000000 : ℝ)*base66 + (541345895162811/665975000000000000000000000 : ℝ)*base68 + (3878386793749227411/8299913230000000000000000000000 : ℝ)*base71 + (2030280711697111/1557850000000000000000000000 : ℝ)*base72 + (22751530359389/57786875000000000000000000 : ℝ)*base74 + (211138956575313/1557850000000000000000000000 : ℝ)*base76 + (13905417078036620683/36009313287500000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (3483/20000000000000000 : ℝ)*base87 + (3483/20000000000000000 : ℝ)*base89 + (3483/20000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(7093/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(7093/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (103413078832097470674305331/28807450630000000000000000000000 : ℝ) := by norm_num
    linear_combination (864057874091/1000000000000 : ℝ)*(base5) + (333830287321/1000000000000 : ℝ)*(base7) + (23033/1000000000000 : ℝ)*(base8) + (851909/200000000000 : ℝ)*(base40) + (120552848283/1000000000000 : ℝ)*(base50) + (197600111927/250000000000 : ℝ)*(base59) + (37933543181/31250000000 : ℝ)*(major_s1_0) + (37933543181/31250000000 : ℝ)*(major_s1_1) + (37933543181/31250000000 : ℝ)*(major_s1_2) + (39126449/500000000000 : ℝ)*(sp_s1_2) + (1448100024881/1000000000000 : ℝ)*(sp_s1_21) + (724050023957/500000000000 : ℝ)*(sp_s1_22) + (2312079669107/1000000000000 : ℝ)*(sp_s1_23) + (24436601661/100000000000 : ℝ)*(sp_s1_27) + (38729680169/50000000000 : ℝ)*(f.failure) + (724050023957/500000000000 : ℝ)*(f.sum) + (220895688663709871/452760165625000000000000000000 : ℝ)*base63 + (4798473988011/39175000000000000000000000 : ℝ)*base64 + (3699185308604879/4622950000000000000000000000 : ℝ)*base66 + (8092509038143/39175000000000000000000000 : ℝ)*base68 + (12764039383717709/22885790156250000000000000000 : ℝ)*base71 + (104902369129309/146048437500000000000000000 : ℝ)*base72 + (136840492969547/924590000000000000000000000 : ℝ)*base75 + (274522474314241/4673550000000000000000000000 : ℝ)*base77 + (25555853942240186611/27006984965625000000000000000000 : ℝ)*base78 + (4159/5000000000000000 : ℝ)*base87 + (4159/5000000000000000 : ℝ)*base89 + (4159/5000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((93471/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(93471/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(92459/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(92459/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(26639/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(26639/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((20633/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20633/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(82343/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(82343/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(7093/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(7093/20000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c308057_s1 p hpa hpb X hX hprev0

#print axioms solution
