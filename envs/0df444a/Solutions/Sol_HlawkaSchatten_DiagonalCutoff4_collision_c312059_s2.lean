-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c312059_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:20:10.8847+00:00
-- url     : https://prove2.me/submissions/e041a144-f57c-4c34-8d6e-a621607015e7

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
theorem collision_support_c312059_s2_s2_0 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-338550249/1000000000 : ℝ)*x 0 + (3370245379/10000000000 : ℝ)*x 1 + (583712739/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (338550249/1000000000 : ℝ)^73 ≤ (12489858879049/50000000000000 : ℝ)^57 := by
    have hnat : (338550249 : ℕ)^73*50000000000000^57 ≤ 12489858879049^57*1000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338550249 1000000000 12489858879049 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3370245379/10000000000 : ℝ)^73 ≤ (24835635793471/100000000000000 : ℝ)^57 := by
    have hnat : (3370245379 : ℕ)^73*100000000000000^57 ≤ 24835635793471^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3370245379 10000000000 24835635793471 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (583712739/1000000000 : ℝ)^73 ≤ (50184646433679/100000000000000 : ℝ)^57 := by
    have hnat : (583712739 : ℕ)^73*100000000000000^57 ≤ 50184646433679^57*1000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      583712739 1000000000 50184646433679 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-338550249/1000000000 : ℝ), (3370245379/10000000000 : ℝ), (583712739/1000000000 : ℝ)] ![(12489858879049/50000000000000 : ℝ), (24835635793471/100000000000000 : ℝ), (50184646433679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-338550249/1000000000 : ℝ)|^73 ≤ (12489858879049/50000000000000 : ℝ)^57
        have hw : |(-338550249/1000000000 : ℝ)|=(338550249/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3370245379/10000000000 : ℝ)|^73 ≤ (24835635793471/100000000000000 : ℝ)^57
        have hw : |(3370245379/10000000000 : ℝ)|=(3370245379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(583712739/1000000000 : ℝ)|^73 ≤ (50184646433679/100000000000000 : ℝ)^57
        have hw : |(583712739/1000000000 : ℝ)|=(583712739/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312059_s2_s2_1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (674372111/2000000000 : ℝ)*x 0 + (-1678190799/5000000000 : ℝ)*x 1 + (1172138223/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (674372111/2000000000 : ℝ)^73 ≤ (497017604213/2000000000000 : ℝ)^57 := by
    have hnat : (674372111 : ℕ)^73*2000000000000^57 ≤ 497017604213^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674372111 2000000000 497017604213 2000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1678190799/5000000000 : ℝ)^73 ≤ (12352435264513/50000000000000 : ℝ)^57 := by
    have hnat : (1678190799 : ℕ)^73*50000000000000^57 ≤ 12352435264513^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1678190799 5000000000 12352435264513 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1172138223/2000000000 : ℝ)^73 ≤ (6305531156419/12500000000000 : ℝ)^57 := by
    have hnat : (1172138223 : ℕ)^73*12500000000000^57 ≤ 6305531156419^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1172138223 2000000000 6305531156419 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(674372111/2000000000 : ℝ), (-1678190799/5000000000 : ℝ), (1172138223/2000000000 : ℝ)] ![(497017604213/2000000000000 : ℝ), (12352435264513/50000000000000 : ℝ), (6305531156419/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(674372111/2000000000 : ℝ)|^73 ≤ (497017604213/2000000000000 : ℝ)^57
        have hw : |(674372111/2000000000 : ℝ)|=(674372111/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1678190799/5000000000 : ℝ)|^73 ≤ (12352435264513/50000000000000 : ℝ)^57
        have hw : |(-1678190799/5000000000 : ℝ)|=(1678190799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1172138223/2000000000 : ℝ)|^73 ≤ (6305531156419/12500000000000 : ℝ)^57
        have hw : |(1172138223/2000000000 : ℝ)|=(1172138223/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312059_s2_s2_2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2825893957/5000000000 : ℝ)*x 0 + (5549466221/10000000000 : ℝ)*x 1 + (-467501919/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2825893957/5000000000 : ℝ)^73 ≤ (24076535593409/50000000000000 : ℝ)^57 := by
    have hnat : (2825893957 : ℕ)^73*50000000000000^57 ≤ 24076535593409^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2825893957 5000000000 24076535593409 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5549466221/10000000000 : ℝ)^73 ≤ (47039433064037/100000000000000 : ℝ)^57 := by
    have hnat : (5549466221 : ℕ)^73*100000000000000^57 ≤ 47039433064037^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5549466221 10000000000 47039433064037 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (467501919/5000000000 : ℝ)^73 ≤ (961499146837/20000000000000 : ℝ)^57 := by
    have hnat : (467501919 : ℕ)^73*20000000000000^57 ≤ 961499146837^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467501919 5000000000 961499146837 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2825893957/5000000000 : ℝ), (5549466221/10000000000 : ℝ), (-467501919/5000000000 : ℝ)] ![(24076535593409/50000000000000 : ℝ), (47039433064037/100000000000000 : ℝ), (961499146837/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2825893957/5000000000 : ℝ)|^73 ≤ (24076535593409/50000000000000 : ℝ)^57
        have hw : |(2825893957/5000000000 : ℝ)|=(2825893957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5549466221/10000000000 : ℝ)|^73 ≤ (47039433064037/100000000000000 : ℝ)^57
        have hw : |(5549466221/10000000000 : ℝ)|=(5549466221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-467501919/5000000000 : ℝ)|^73 ≤ (961499146837/20000000000000 : ℝ)^57
        have hw : |(-467501919/5000000000 : ℝ)|=(467501919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312059_s2_s2_5 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-41/1250000000 : ℝ)*x 0 + (41/1250000000 : ℝ)*x 1 + (1999999999/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41/1250000000 : ℝ)^73 ≤ (13003/50000000000000 : ℝ)^57 := by
    have hnat : (41 : ℕ)^73*50000000000000^57 ≤ 13003^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41 1250000000 13003 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41/1250000000 : ℝ)^73 ≤ (13003/50000000000000 : ℝ)^57 := by
    have hnat : (41 : ℕ)^73*50000000000000^57 ≤ 13003^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41 1250000000 13003 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1999999999/2000000000 : ℝ)^73 ≤ (19999999987193/20000000000000 : ℝ)^57 := by
    have hnat : (1999999999 : ℕ)^73*20000000000000^57 ≤ 19999999987193^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1999999999 2000000000 19999999987193 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-41/1250000000 : ℝ), (41/1250000000 : ℝ), (1999999999/2000000000 : ℝ)] ![(13003/50000000000000 : ℝ), (13003/50000000000000 : ℝ), (19999999987193/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-41/1250000000 : ℝ)|^73 ≤ (13003/50000000000000 : ℝ)^57
        have hw : |(-41/1250000000 : ℝ)|=(41/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(41/1250000000 : ℝ)|^73 ≤ (13003/50000000000000 : ℝ)^57
        have hw : |(41/1250000000 : ℝ)|=(41/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1999999999/2000000000 : ℝ)|^73 ≤ (19999999987193/20000000000000 : ℝ)^57
        have hw : |(1999999999/2000000000 : ℝ)|=(1999999999/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312059_s2_s2_6 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (269228337/625000000 : ℝ)*x 0 + (4619412123/10000000000 : ℝ)*x 1 + (945898869/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269228337/625000000 : ℝ)^73 ≤ (2125452999619/6250000000000 : ℝ)^57 := by
    have hnat : (269228337 : ℕ)^73*6250000000000^57 ≤ 2125452999619^57*625000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269228337 625000000 2125452999619 6250000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4619412123/10000000000 : ℝ)^73 ≤ (18595403866763/50000000000000 : ℝ)^57 := by
    have hnat : (4619412123 : ℕ)^73*50000000000000^57 ≤ 18595403866763^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4619412123 10000000000 18595403866763 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (945898869/2500000000 : ℝ)^73 ≤ (7200486065359/25000000000000 : ℝ)^57 := by
    have hnat : (945898869 : ℕ)^73*25000000000000^57 ≤ 7200486065359^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      945898869 2500000000 7200486065359 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(269228337/625000000 : ℝ), (4619412123/10000000000 : ℝ), (945898869/2500000000 : ℝ)] ![(2125452999619/6250000000000 : ℝ), (18595403866763/50000000000000 : ℝ), (7200486065359/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(269228337/625000000 : ℝ)|^73 ≤ (2125452999619/6250000000000 : ℝ)^57
        have hw : |(269228337/625000000 : ℝ)|=(269228337/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4619412123/10000000000 : ℝ)|^73 ≤ (18595403866763/50000000000000 : ℝ)^57
        have hw : |(4619412123/10000000000 : ℝ)|=(4619412123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(945898869/2500000000 : ℝ)|^73 ≤ (7200486065359/25000000000000 : ℝ)^57
        have hw : |(945898869/2500000000 : ℝ)|=(945898869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312059_s2_s2_7 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1639598879/5000000000 : ℝ)*x 0 + (301006779/1000000000 : ℝ)*x 1 + (3114146519/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1639598879/5000000000 : ℝ)^73 ≤ (5994910933937/25000000000000 : ℝ)^57 := by
    have hnat : (1639598879 : ℕ)^73*25000000000000^57 ≤ 5994910933937^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1639598879 5000000000 5994910933937 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (301006779/1000000000 : ℝ)^73 ≤ (10744389081719/50000000000000 : ℝ)^57 := by
    have hnat : (301006779 : ℕ)^73*50000000000000^57 ≤ 10744389081719^57*1000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      301006779 1000000000 10744389081719 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3114146519/5000000000 : ℝ)^73 ≤ (1704111814987/3125000000000 : ℝ)^57 := by
    have hnat : (3114146519 : ℕ)^73*3125000000000^57 ≤ 1704111814987^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3114146519 5000000000 1704111814987 3125000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1639598879/5000000000 : ℝ), (301006779/1000000000 : ℝ), (3114146519/5000000000 : ℝ)] ![(5994910933937/25000000000000 : ℝ), (10744389081719/50000000000000 : ℝ), (1704111814987/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1639598879/5000000000 : ℝ)|^73 ≤ (5994910933937/25000000000000 : ℝ)^57
        have hw : |(-1639598879/5000000000 : ℝ)|=(1639598879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(301006779/1000000000 : ℝ)|^73 ≤ (10744389081719/50000000000000 : ℝ)^57
        have hw : |(301006779/1000000000 : ℝ)|=(301006779/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3114146519/5000000000 : ℝ)|^73 ≤ (1704111814987/3125000000000 : ℝ)^57
        have hw : |(3114146519/5000000000 : ℝ)|=(3114146519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312059_s2_s2_8 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (81799549/250000000 : ℝ)*x 0 + (-1494230861/5000000000 : ℝ)*x 1 + (3125952283/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (81799549/250000000 : ℝ)^73 ≤ (583791169/2441406250 : ℝ)^57 := by
    have hnat : (81799549 : ℕ)^73*2441406250^57 ≤ 583791169^57*250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81799549 250000000 583791169 2441406250 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1494230861/5000000000 : ℝ)^73 ≤ (425828712671/2000000000000 : ℝ)^57 := by
    have hnat : (1494230861 : ℕ)^73*2000000000000^57 ≤ 425828712671^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1494230861 5000000000 425828712671 2000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3125952283/5000000000 : ℝ)^73 ≤ (54796478062533/100000000000000 : ℝ)^57 := by
    have hnat : (3125952283 : ℕ)^73*100000000000000^57 ≤ 54796478062533^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3125952283 5000000000 54796478062533 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(81799549/250000000 : ℝ), (-1494230861/5000000000 : ℝ), (3125952283/5000000000 : ℝ)] ![(583791169/2441406250 : ℝ), (425828712671/2000000000000 : ℝ), (54796478062533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(81799549/250000000 : ℝ)|^73 ≤ (583791169/2441406250 : ℝ)^57
        have hw : |(81799549/250000000 : ℝ)|=(81799549/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1494230861/5000000000 : ℝ)|^73 ≤ (425828712671/2000000000000 : ℝ)^57
        have hw : |(-1494230861/5000000000 : ℝ)|=(1494230861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3125952283/5000000000 : ℝ)|^73 ≤ (54796478062533/100000000000000 : ℝ)^57
        have hw : |(3125952283/5000000000 : ℝ)|=(3125952283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312059_s2_s2_9 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (689620353/1250000000 : ℝ)*x 0 + (5895940771/10000000000 : ℝ)*x 1 + (-557635043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (689620353/1250000000 : ℝ)^73 ≤ (46686875557157/100000000000000 : ℝ)^57 := by
    have hnat : (689620353 : ℕ)^73*100000000000000^57 ≤ 46686875557157^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689620353 1250000000 46686875557157 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5895940771/10000000000 : ℝ)^73 ≤ (50833143613557/100000000000000 : ℝ)^57 := by
    have hnat : (5895940771 : ℕ)^73*100000000000000^57 ≤ 50833143613557^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5895940771 10000000000 50833143613557 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (557635043/10000000000 : ℝ)^73 ≤ (2479980807469/100000000000000 : ℝ)^57 := by
    have hnat : (557635043 : ℕ)^73*100000000000000^57 ≤ 2479980807469^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      557635043 10000000000 2479980807469 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(689620353/1250000000 : ℝ), (5895940771/10000000000 : ℝ), (-557635043/10000000000 : ℝ)] ![(46686875557157/100000000000000 : ℝ), (50833143613557/100000000000000 : ℝ), (2479980807469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(689620353/1250000000 : ℝ)|^73 ≤ (46686875557157/100000000000000 : ℝ)^57
        have hw : |(689620353/1250000000 : ℝ)|=(689620353/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5895940771/10000000000 : ℝ)|^73 ≤ (50833143613557/100000000000000 : ℝ)^57
        have hw : |(5895940771/10000000000 : ℝ)|=(5895940771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-557635043/10000000000 : ℝ)|^73 ≤ (2479980807469/100000000000000 : ℝ)^57
        have hw : |(-557635043/10000000000 : ℝ)|=(557635043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312059_s2_s2_13 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2067761261/5000000000 : ℝ)*x 0 + (222809183/400000000 : ℝ)*x 1 + (362094397/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2067761261/5000000000 : ℝ)^73 ≤ (32276749979839/100000000000000 : ℝ)^57 := by
    have hnat : (2067761261 : ℕ)^73*100000000000000^57 ≤ 32276749979839^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067761261 5000000000 32276749979839 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (222809183/400000000 : ℝ)^73 ≤ (738514884411/1562500000000 : ℝ)^57 := by
    have hnat : (222809183 : ℕ)^73*1562500000000^57 ≤ 738514884411^57*400000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222809183 400000000 738514884411 1562500000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (362094397/1250000000 : ℝ)^73 ≤ (20458297397089/100000000000000 : ℝ)^57 := by
    have hnat : (362094397 : ℕ)^73*100000000000000^57 ≤ 20458297397089^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      362094397 1250000000 20458297397089 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2067761261/5000000000 : ℝ), (222809183/400000000 : ℝ), (362094397/1250000000 : ℝ)] ![(32276749979839/100000000000000 : ℝ), (738514884411/1562500000000 : ℝ), (20458297397089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2067761261/5000000000 : ℝ)|^73 ≤ (32276749979839/100000000000000 : ℝ)^57
        have hw : |(2067761261/5000000000 : ℝ)|=(2067761261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(222809183/400000000 : ℝ)|^73 ≤ (738514884411/1562500000000 : ℝ)^57
        have hw : |(222809183/400000000 : ℝ)|=(222809183/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(362094397/1250000000 : ℝ)|^73 ≤ (20458297397089/100000000000000 : ℝ)^57
        have hw : |(362094397/1250000000 : ℝ)|=(362094397/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312059_s2_s2_14 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3017351141/10000000000 : ℝ)*x 0 + (1634350647/5000000000 : ℝ)*x 1 + (1557778753/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3017351141/10000000000 : ℝ)^73 ≤ (21555391634959/100000000000000 : ℝ)^57 := by
    have hnat : (3017351141 : ℕ)^73*100000000000000^57 ≤ 21555391634959^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3017351141 10000000000 21555391634959 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1634350647/5000000000 : ℝ)^73 ≤ (1194069253739/5000000000000 : ℝ)^57 := by
    have hnat : (1634350647 : ℕ)^73*5000000000000^57 ≤ 1194069253739^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1634350647 5000000000 1194069253739 5000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1557778753/2500000000 : ℝ)^73 ≤ (54563223265699/100000000000000 : ℝ)^57 := by
    have hnat : (1557778753 : ℕ)^73*100000000000000^57 ≤ 54563223265699^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1557778753 2500000000 54563223265699 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3017351141/10000000000 : ℝ), (1634350647/5000000000 : ℝ), (1557778753/2500000000 : ℝ)] ![(21555391634959/100000000000000 : ℝ), (1194069253739/5000000000000 : ℝ), (54563223265699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3017351141/10000000000 : ℝ)|^73 ≤ (21555391634959/100000000000000 : ℝ)^57
        have hw : |(-3017351141/10000000000 : ℝ)|=(3017351141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1634350647/5000000000 : ℝ)|^73 ≤ (1194069253739/5000000000000 : ℝ)^57
        have hw : |(1634350647/5000000000 : ℝ)|=(1634350647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1557778753/2500000000 : ℝ)|^73 ≤ (54563223265699/100000000000000 : ℝ)^57
        have hw : |(1557778753/2500000000 : ℝ)|=(1557778753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312059_s2_s2_15 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (60072097/200000000 : ℝ)*x 0 + (-650761983/2000000000 : ℝ)*x 1 + (1250945309/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (60072097/200000000 : ℝ)^73 ≤ (21429706035799/100000000000000 : ℝ)^57 := by
    have hnat : (60072097 : ℕ)^73*100000000000000^57 ≤ 21429706035799^57*200000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60072097 200000000 21429706035799 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (650761983/2000000000 : ℝ)^73 ≤ (593553425671/2500000000000 : ℝ)^57 := by
    have hnat : (650761983 : ℕ)^73*2500000000000^57 ≤ 593553425671^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      650761983 2000000000 593553425671 2500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1250945309/2000000000 : ℝ)^73 ≤ (54828156926379/100000000000000 : ℝ)^57 := by
    have hnat : (1250945309 : ℕ)^73*100000000000000^57 ≤ 54828156926379^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1250945309 2000000000 54828156926379 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(60072097/200000000 : ℝ), (-650761983/2000000000 : ℝ), (1250945309/2000000000 : ℝ)] ![(21429706035799/100000000000000 : ℝ), (593553425671/2500000000000 : ℝ), (54828156926379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(60072097/200000000 : ℝ)|^73 ≤ (21429706035799/100000000000000 : ℝ)^57
        have hw : |(60072097/200000000 : ℝ)|=(60072097/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-650761983/2000000000 : ℝ)|^73 ≤ (593553425671/2500000000000 : ℝ)^57
        have hw : |(-650761983/2000000000 : ℝ)|=(650761983/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1250945309/2000000000 : ℝ)|^73 ≤ (54828156926379/100000000000000 : ℝ)^57
        have hw : |(1250945309/2000000000 : ℝ)|=(1250945309/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312059_s2_s2_16 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6048485031/10000000000 : ℝ)*x 0 + (2680926063/5000000000 : ℝ)*x 1 + (-277406373/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6048485031/10000000000 : ℝ)^73 ≤ (52523593388167/100000000000000 : ℝ)^57 := by
    have hnat : (6048485031 : ℕ)^73*100000000000000^57 ≤ 52523593388167^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6048485031 10000000000 52523593388167 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2680926063/5000000000 : ℝ)^73 ≤ (45012489288151/100000000000000 : ℝ)^57 := by
    have hnat : (2680926063 : ℕ)^73*100000000000000^57 ≤ 45012489288151^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2680926063 5000000000 45012489288151 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (277406373/5000000000 : ℝ)^73 ≤ (2463917314129/100000000000000 : ℝ)^57 := by
    have hnat : (277406373 : ℕ)^73*100000000000000^57 ≤ 2463917314129^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277406373 5000000000 2463917314129 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6048485031/10000000000 : ℝ), (2680926063/5000000000 : ℝ), (-277406373/5000000000 : ℝ)] ![(52523593388167/100000000000000 : ℝ), (45012489288151/100000000000000 : ℝ), (2463917314129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6048485031/10000000000 : ℝ)|^73 ≤ (52523593388167/100000000000000 : ℝ)^57
        have hw : |(6048485031/10000000000 : ℝ)|=(6048485031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2680926063/5000000000 : ℝ)|^73 ≤ (45012489288151/100000000000000 : ℝ)^57
        have hw : |(2680926063/5000000000 : ℝ)|=(2680926063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-277406373/5000000000 : ℝ)|^73 ≤ (2463917314129/100000000000000 : ℝ)^57
        have hw : |(-277406373/5000000000 : ℝ)|=(277406373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312059_s2_s2_20 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5161109281/10000000000 : ℝ)*x 0 + (183008503/400000000 : ℝ)*x 1 + (722539769/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5161109281/10000000000 : ℝ)^73 ≤ (8573132227391/20000000000000 : ℝ)^57 := by
    have hnat : (5161109281 : ℕ)^73*20000000000000^57 ≤ 8573132227391^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5161109281 10000000000 8573132227391 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (183008503/400000000 : ℝ)^73 ≤ (18367841845251/50000000000000 : ℝ)^57 := by
    have hnat : (183008503 : ℕ)^73*50000000000000^57 ≤ 18367841845251^57*400000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183008503 400000000 18367841845251 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (722539769/2500000000 : ℝ)^73 ≤ (20398655144443/100000000000000 : ℝ)^57 := by
    have hnat : (722539769 : ℕ)^73*100000000000000^57 ≤ 20398655144443^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      722539769 2500000000 20398655144443 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5161109281/10000000000 : ℝ), (183008503/400000000 : ℝ), (722539769/2500000000 : ℝ)] ![(8573132227391/20000000000000 : ℝ), (18367841845251/50000000000000 : ℝ), (20398655144443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5161109281/10000000000 : ℝ)|^73 ≤ (8573132227391/20000000000000 : ℝ)^57
        have hw : |(5161109281/10000000000 : ℝ)|=(5161109281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(183008503/400000000 : ℝ)|^73 ≤ (18367841845251/50000000000000 : ℝ)^57
        have hw : |(183008503/400000000 : ℝ)|=(183008503/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(722539769/2500000000 : ℝ)|^73 ≤ (20398655144443/100000000000000 : ℝ)^57
        have hw : |(722539769/2500000000 : ℝ)|=(722539769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312059_s2_s2_21 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3391756241/10000000000 : ℝ)*x 0 + (3377743341/10000000000 : ℝ)*x 1 + (5825326963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3391756241/10000000000 : ℝ)^73 ≤ (200310627019/800000000000 : ℝ)^57 := by
    have hnat : (3391756241 : ℕ)^73*800000000000^57 ≤ 200310627019^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3391756241 10000000000 200310627019 800000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3377743341/10000000000 : ℝ)^73 ≤ (24906420675621/100000000000000 : ℝ)^57 := by
    have hnat : (3377743341 : ℕ)^73*100000000000000^57 ≤ 24906420675621^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3377743341 10000000000 24906420675621 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5825326963/10000000000 : ℝ)^73 ≤ (6256843866101/12500000000000 : ℝ)^57 := by
    have hnat : (5825326963 : ℕ)^73*12500000000000^57 ≤ 6256843866101^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5825326963 10000000000 6256843866101 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3391756241/10000000000 : ℝ), (3377743341/10000000000 : ℝ), (5825326963/10000000000 : ℝ)] ![(200310627019/800000000000 : ℝ), (24906420675621/100000000000000 : ℝ), (6256843866101/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3391756241/10000000000 : ℝ)|^73 ≤ (200310627019/800000000000 : ℝ)^57
        have hw : |(-3391756241/10000000000 : ℝ)|=(3391756241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3377743341/10000000000 : ℝ)|^73 ≤ (24906420675621/100000000000000 : ℝ)^57
        have hw : |(3377743341/10000000000 : ℝ)|=(3377743341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5825326963/10000000000 : ℝ)|^73 ≤ (6256843866101/12500000000000 : ℝ)^57
        have hw : |(5825326963/10000000000 : ℝ)|=(5825326963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312059_s2_s2_22 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1689688343/5000000000 : ℝ)*x 0 + (-1681295829/5000000000 : ℝ)*x 1 + (5848937989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1689688343/5000000000 : ℝ)^73 ≤ (24921846204917/100000000000000 : ℝ)^57 := by
    have hnat : (1689688343 : ℕ)^73*100000000000000^57 ≤ 24921846204917^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1689688343 5000000000 24921846204917 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1681295829/5000000000 : ℝ)^73 ≤ (12381713019307/50000000000000 : ℝ)^57 := by
    have hnat : (1681295829 : ℕ)^73*50000000000000^57 ≤ 12381713019307^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1681295829 5000000000 12381713019307 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5848937989/10000000000 : ℝ)^73 ≤ (1572335241783/3125000000000 : ℝ)^57 := by
    have hnat : (5848937989 : ℕ)^73*3125000000000^57 ≤ 1572335241783^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5848937989 10000000000 1572335241783 3125000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1689688343/5000000000 : ℝ), (-1681295829/5000000000 : ℝ), (5848937989/10000000000 : ℝ)] ![(24921846204917/100000000000000 : ℝ), (12381713019307/50000000000000 : ℝ), (1572335241783/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1689688343/5000000000 : ℝ)|^73 ≤ (24921846204917/100000000000000 : ℝ)^57
        have hw : |(1689688343/5000000000 : ℝ)|=(1689688343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1681295829/5000000000 : ℝ)|^73 ≤ (12381713019307/50000000000000 : ℝ)^57
        have hw : |(-1681295829/5000000000 : ℝ)|=(1681295829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5848937989/10000000000 : ℝ)|^73 ≤ (1572335241783/3125000000000 : ℝ)^57
        have hw : |(5848937989/10000000000 : ℝ)|=(5848937989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312059_s2_s2_23 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (248141101/400000000 : ℝ)*x 0 + (2508090457/5000000000 : ℝ)*x 1 + (-874966937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (248141101/400000000 : ℝ)^73 ≤ (54254034175851/100000000000000 : ℝ)^57 := by
    have hnat : (248141101 : ℕ)^73*100000000000000^57 ≤ 54254034175851^57*400000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      248141101 400000000 54254034175851 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2508090457/5000000000 : ℝ)^73 ≤ (10332547946831/25000000000000 : ℝ)^57 := by
    have hnat : (2508090457 : ℕ)^73*25000000000000^57 ≤ 10332547946831^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2508090457 5000000000 10332547946831 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (874966937/10000000000 : ℝ)^73 ≤ (551971752739/12500000000000 : ℝ)^57 := by
    have hnat : (874966937 : ℕ)^73*12500000000000^57 ≤ 551971752739^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874966937 10000000000 551971752739 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(248141101/400000000 : ℝ), (2508090457/5000000000 : ℝ), (-874966937/10000000000 : ℝ)] ![(54254034175851/100000000000000 : ℝ), (10332547946831/25000000000000 : ℝ), (551971752739/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(248141101/400000000 : ℝ)|^73 ≤ (54254034175851/100000000000000 : ℝ)^57
        have hw : |(248141101/400000000 : ℝ)|=(248141101/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2508090457/5000000000 : ℝ)|^73 ≤ (10332547946831/25000000000000 : ℝ)^57
        have hw : |(2508090457/5000000000 : ℝ)|=(2508090457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-874966937/10000000000 : ℝ)|^73 ≤ (551971752739/12500000000000 : ℝ)^57
        have hw : |(-874966937/10000000000 : ℝ)|=(874966937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312059_s2_s2_27 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (23784937/78125000 : ℝ)*x 0 + (184150301/312500000 : ℝ)*x 1 + (1819380459/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (23784937/78125000 : ℝ)^73 ≤ (21803834673829/100000000000000 : ℝ)^57 := by
    have hnat : (23784937 : ℕ)^73*100000000000000^57 ≤ 21803834673829^57*78125000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23784937 78125000 21803834673829 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (184150301/312500000 : ℝ)^73 ≤ (507985726223/1000000000000 : ℝ)^57 := by
    have hnat : (184150301 : ℕ)^73*1000000000000^57 ≤ 507985726223^57*312500000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      184150301 312500000 507985726223 1000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1819380459/5000000000 : ℝ)^73 ≤ (27397592682991/100000000000000 : ℝ)^57 := by
    have hnat : (1819380459 : ℕ)^73*100000000000000^57 ≤ 27397592682991^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1819380459 5000000000 27397592682991 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(23784937/78125000 : ℝ), (184150301/312500000 : ℝ), (1819380459/5000000000 : ℝ)] ![(21803834673829/100000000000000 : ℝ), (507985726223/1000000000000 : ℝ), (27397592682991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(23784937/78125000 : ℝ)|^73 ≤ (21803834673829/100000000000000 : ℝ)^57
        have hw : |(23784937/78125000 : ℝ)|=(23784937/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(184150301/312500000 : ℝ)|^73 ≤ (507985726223/1000000000000 : ℝ)^57
        have hw : |(184150301/312500000 : ℝ)|=(184150301/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1819380459/5000000000 : ℝ)|^73 ≤ (27397592682991/100000000000000 : ℝ)^57
        have hw : |(1819380459/5000000000 : ℝ)|=(1819380459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c312059_s2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((8583/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8583/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(33487/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(33487/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(40441/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(40441/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((7413/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7413/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29037/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(29037/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1579/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(1579/20000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78337/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78337/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base60 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s2_pow0 : (8583/12500 : ℝ) ^ (9/2 : ℝ) ≤ (9209815968412137493/50000000000000000000 : ℝ) := by
    have hpowers : (8583/12500 : ℝ)^9 ≤ (9209815968412137493/50000000000000000000 : ℝ)^2 := by
      have hnat : (8583 : ℕ)^9*50000000000000000000^2 ≤ 9209815968412137493^2*12500^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8583 12500 9209815968412137493 50000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8583/12500 : ℝ)) (X := (9209815968412137493/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s2_corner0a : (59209815968412137493/50000000000000000000 : ℝ) ≤ (1297855650708843/1250000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (59209815968412137493/50000000000000000000 : ℝ)^2 ≤ (1297855650708843/1250000000000000 : ℝ)^9 := by
      have hnat : (59209815968412137493 : ℕ)^2*1250000000000000^9 ≤ 1297855650708843^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59209815968412137493 50000000000000000000 1297855650708843 1250000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1297855650708843/1250000000000000 : ℝ)) (X := (59209815968412137493/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s2_corner0b : (34209815968412137493/25000000000000000000 : ℝ) ≤ (10721833307048839/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (34209815968412137493/25000000000000000000 : ℝ)^2 ≤ (10721833307048839/10000000000000000 : ℝ)^9 := by
      have hnat : (34209815968412137493 : ℕ)^2*10000000000000000^9 ≤ 10721833307048839^9*25000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        34209815968412137493 25000000000000000000 10721833307048839 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10721833307048839/10000000000000000 : ℝ)) (X := (34209815968412137493/25000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(47855650708843/858300000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(67797620275619/1373280000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (8583/12500 : ℝ)) (alpha := (47855650708843/858300000000000 : ℝ)) (beta := (67797620275619/1373280000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (8583/12500 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(47855650708843/858300000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(67797620275619/1373280000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (33487/50000 : ℝ) ^ (9/2 : ℝ) ≤ (1646561930804630279/10000000000000000000 : ℝ) := by
    have hpowers : (33487/50000 : ℝ)^9 ≤ (1646561930804630279/10000000000000000000 : ℝ)^2 := by
      have hnat : (33487 : ℕ)^9*10000000000000000000^2 ≤ 1646561930804630279^2*50000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33487 50000 1646561930804630279 10000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (33487/50000 : ℝ)) (X := (1646561930804630279/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s2_corner1a : (11646561930804630279/10000000000000000000 : ℝ) ≤ (2586131580227153/2500000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (11646561930804630279/10000000000000000000 : ℝ)^2 ≤ (2586131580227153/2500000000000000 : ℝ)^9 := by
      have hnat : (11646561930804630279 : ℕ)^2*2500000000000000^9 ≤ 2586131580227153^9*10000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11646561930804630279 10000000000000000000 2586131580227153 2500000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2586131580227153/2500000000000000 : ℝ)) (X := (11646561930804630279/10000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s2_corner1b : (6646561930804630279/5000000000000000000 : ℝ) ≤ (10653018423308213/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (6646561930804630279/5000000000000000000 : ℝ)^2 ≤ (10653018423308213/10000000000000000 : ℝ)^9 := by
      have hnat : (6646561930804630279 : ℕ)^2*10000000000000000^9 ≤ 10653018423308213^9*5000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6646561930804630279 5000000000000000000 10653018423308213 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10653018423308213/10000000000000000 : ℝ)) (X := (6646561930804630279/5000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(86131580227153/1674350000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(308492102399601/6697400000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (33487/50000 : ℝ)) (alpha := (86131580227153/1674350000000000 : ℝ)) (beta := (308492102399601/6697400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (33487/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(86131580227153/1674350000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(308492102399601/6697400000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (40441/100000 : ℝ) ^ (9/2 : ℝ) ≤ (340195435873999383/20000000000000000000 : ℝ) := by
    have hpowers : (40441/100000 : ℝ)^9 ≤ (340195435873999383/20000000000000000000 : ℝ)^2 := by
      have hnat : (40441 : ℕ)^9*20000000000000000000^2 ≤ 340195435873999383^2*100000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        40441 100000 340195435873999383 20000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (40441/100000 : ℝ)) (X := (340195435873999383/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s2_corner2a : (20340195435873999383/20000000000000000000 : ℝ) ≤ (2509387985890609/2500000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (20340195435873999383/20000000000000000000 : ℝ)^2 ≤ (2509387985890609/2500000000000000 : ℝ)^9 := by
      have hnat : (20340195435873999383 : ℕ)^2*2500000000000000^9 ≤ 2509387985890609^9*20000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20340195435873999383 20000000000000000000 2509387985890609 2500000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2509387985890609/2500000000000000 : ℝ)) (X := (20340195435873999383/20000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s2_corner2b : (10340195435873999383/10000000000000000000 : ℝ) ≤ (5037309261571187/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (10340195435873999383/10000000000000000000 : ℝ)^2 ≤ (5037309261571187/5000000000000000 : ℝ)^9 := by
      have hnat : (10340195435873999383 : ℕ)^2*5000000000000000^9 ≤ 5037309261571187^9*10000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10340195435873999383 10000000000000000000 5037309261571187 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5037309261571187/5000000000000000 : ℝ)) (X := (10340195435873999383/10000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(9387985890609/1011025000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(18533289789969/2022050000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (40441/100000 : ℝ)) (alpha := (9387985890609/1011025000000000 : ℝ)) (beta := (18533289789969/2022050000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (40441/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(9387985890609/1011025000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(18533289789969/2022050000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-338550249/1000000000 : ℝ)*X 0 0+(3370245379/10000000000 : ℝ)*X 0 1+(583712739/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312059_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((674372111/2000000000 : ℝ)*X 1 0+(-1678190799/5000000000 : ℝ)*X 1 1+(1172138223/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312059_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((2825893957/5000000000 : ℝ)*X 2 0+(5549466221/10000000000 : ℝ)*X 2 1+(-467501919/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312059_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_5 : ((-41/1250000000 : ℝ)*X 0 0+(41/1250000000 : ℝ)*X 0 1+(1999999999/2000000000 : ℝ)*X 0 2+(-41/1250000000 : ℝ)*X 1 0+(41/1250000000 : ℝ)*X 1 1+(1999999999/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312059_s2_s2_5 p hpa hpb (pair X 2)
    change _ ≤ P 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((269228337/625000000 : ℝ)*X 0 0+(4619412123/10000000000 : ℝ)*X 0 1+(945898869/2500000000 : ℝ)*X 0 2+(269228337/625000000 : ℝ)*X 1 0+(4619412123/10000000000 : ℝ)*X 1 1+(945898869/2500000000 : ℝ)*X 1 2+(269228337/625000000 : ℝ)*X 2 0+(4619412123/10000000000 : ℝ)*X 2 1+(945898869/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312059_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-1639598879/5000000000 : ℝ)*X 0 0+(301006779/1000000000 : ℝ)*X 0 1+(3114146519/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312059_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((81799549/250000000 : ℝ)*X 1 0+(-1494230861/5000000000 : ℝ)*X 1 1+(3125952283/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312059_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((689620353/1250000000 : ℝ)*X 2 0+(5895940771/10000000000 : ℝ)*X 2 1+(-557635043/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312059_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((2067761261/5000000000 : ℝ)*X 0 0+(222809183/400000000 : ℝ)*X 0 1+(362094397/1250000000 : ℝ)*X 0 2+(2067761261/5000000000 : ℝ)*X 1 0+(222809183/400000000 : ℝ)*X 1 1+(362094397/1250000000 : ℝ)*X 1 2+(2067761261/5000000000 : ℝ)*X 2 0+(222809183/400000000 : ℝ)*X 2 1+(362094397/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312059_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-3017351141/10000000000 : ℝ)*X 0 0+(1634350647/5000000000 : ℝ)*X 0 1+(1557778753/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312059_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((60072097/200000000 : ℝ)*X 1 0+(-650761983/2000000000 : ℝ)*X 1 1+(1250945309/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312059_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((6048485031/10000000000 : ℝ)*X 2 0+(2680926063/5000000000 : ℝ)*X 2 1+(-277406373/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312059_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((5161109281/10000000000 : ℝ)*X 0 0+(183008503/400000000 : ℝ)*X 0 1+(722539769/2500000000 : ℝ)*X 0 2+(5161109281/10000000000 : ℝ)*X 1 0+(183008503/400000000 : ℝ)*X 1 1+(722539769/2500000000 : ℝ)*X 1 2+(5161109281/10000000000 : ℝ)*X 2 0+(183008503/400000000 : ℝ)*X 2 1+(722539769/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312059_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-3391756241/10000000000 : ℝ)*X 0 0+(3377743341/10000000000 : ℝ)*X 0 1+(5825326963/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312059_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((1689688343/5000000000 : ℝ)*X 1 0+(-1681295829/5000000000 : ℝ)*X 1 1+(5848937989/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312059_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((248141101/400000000 : ℝ)*X 2 0+(2508090457/5000000000 : ℝ)*X 2 1+(-874966937/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312059_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((23784937/78125000 : ℝ)*X 0 0+(184150301/312500000 : ℝ)*X 0 1+(1819380459/5000000000 : ℝ)*X 0 2+(23784937/78125000 : ℝ)*X 1 0+(184150301/312500000 : ℝ)*X 1 1+(1819380459/5000000000 : ℝ)*X 1 2+(23784937/78125000 : ℝ)*X 2 0+(184150301/312500000 : ℝ)*X 2 1+(1819380459/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312059_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((7413/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7413/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1083413011288734548501927462331/193725143069350000000000000000000000 : ℝ) := by norm_num
    linear_combination (61050303161/25000000000 : ℝ)*(base60) + (4811495193987/500000000000 : ℝ)*(major_s2_0) + (4811495193987/500000000000 : ℝ)*(major_s2_1) + (9623175772969/1000000000000 : ℝ)*(major_s2_2) + (3238871/250000000000 : ℝ)*(sp_s2_1) + (48088543/1000000000000 : ℝ)*(sp_s2_2) + (46346249/250000000000 : ℝ)*(sp_s2_5) + (1480149/1000000000000 : ℝ)*(sp_s2_6) + (6740232323167/500000000000 : ℝ)*(sp_s2_7) + (6740346398613/500000000000 : ℝ)*(sp_s2_8) + (13480657664167/1000000000000 : ℝ)*(sp_s2_9) + (5765241684743/1000000000000 : ℝ)*(sp_s2_13) + (30138297/125000000000 : ℝ)*(sp_s2_14) + (29994163/1000000000000 : ℝ)*(sp_s2_27) + (1153054631811/200000000000 : ℝ)*(f.failure) + (1348070575271/100000000000 : ℝ)*(f.sum) + (19492787788776309469/33856194175000000000000000000000 : ℝ)*base63 + (1600034896247661/2022050000000000000000000000 : ℝ)*base65 + (2635099564049313/3348700000000000000000000000 : ℝ)*base66 + (357464299627347/505512500000000000000000000 : ℝ)*base69 + (983871897060019047/1446271262500000000000000000000 : ℝ)*base71 + (35096060851017/45776000000000000000000000 : ℝ)*base72 + (164138679545301/837175000000000000000000000 : ℝ)*base75 + (41002799865307/143050000000000000000000000 : ℝ)*base77 + (3830918211400938133/38322522800000000000000000000000 : ℝ)*base79 + (10557/20000000000000000 : ℝ)*base86 + (10557/20000000000000000 : ℝ)*base88 + (9443/20000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29037/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(29037/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (23766643562102841/2000000000000000000000 : ℝ) := by norm_num
    linear_combination (2413521513567/1000000000000 : ℝ)*(base60) + (594723035237/62500000000 : ℝ)*(major_s2_0) + (594723035237/62500000000 : ℝ)*(major_s2_1) + (4196644087167/250000000000 : ℝ)*(major_s2_2) + (497121/1000000000000 : ℝ)*(sp_s2_0) + (16163953/1000000000000 : ℝ)*(sp_s2_1) + (1817751946219/250000000000 : ℝ)*(sp_s2_5) + (13515499/500000000000 : ℝ)*(sp_s2_6) + (20910931/125000000000 : ℝ)*(sp_s2_7) + (533202007851/40000000000 : ℝ)*(sp_s2_14) + (13330201816891/1000000000000 : ℝ)*(sp_s2_15) + (13330099293973/1000000000000 : ℝ)*(sp_s2_16) + (5700888154633/1000000000000 : ℝ)*(sp_s2_20) + (118686871/1000000000000 : ℝ)*(sp_s2_23) + (5700915185631/1000000000000 : ℝ)*(f.failure) + (3332554495211/250000000000 : ℝ)*(f.sum) + (1029444915624659099/8464048543750000000000000000000 : ℝ)*base62 + (151310776071831/1011025000000000000000000000 : ℝ)*base65 + (157267667110299/837175000000000000000000000 : ℝ)*base67 + (184053554137523/1011025000000000000000000000 : ℝ)*base69 + (1191107522038136293/8677627575000000000000000000000 : ℝ)*base70 + (638559807661/3433200000000000000000000 : ℝ)*base73 + (390387213645931/1674350000000000000000000000 : ℝ)*base75 + (64330154714113/429150000000000000000000000 : ℝ)*base77 + (870270625961438783/7185473025000000000000000000000 : ℝ)*base78 + (27103/100000000000000000 : ℝ)*base87 + (27103/100000000000000000 : ℝ)*base89 + (27103/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1579/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(1579/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (909806551887168783609929013/67712388350000000000000000000000 : ℝ) := by norm_num
    linear_combination (50363/125000000000 : ℝ)*(base8) + (670153/250000000000 : ℝ)*(base40) + (28381/10000000000 : ℝ)*(base50) + (1203801711177/1000000000000 : ℝ)*(base60) + (3290218231559/500000000000 : ℝ)*(major_s2_0) + (3290218231559/500000000000 : ℝ)*(major_s2_1) + (3290218231559/500000000000 : ℝ)*(major_s2_2) + (5257397/50000000000 : ℝ)*(sp_s2_2) + (11174171/100000000000 : ℝ)*(sp_s2_13) + (2883453/31250000000 : ℝ)*(sp_s2_16) + (1152304135693/125000000000 : ℝ)*(sp_s2_21) + (144038023257/15625000000 : ℝ)*(sp_s2_22) + (9218236070011/1000000000000 : ℝ)*(sp_s2_23) + (985580804323/250000000000 : ℝ)*(sp_s2_27) + (3942434959001/1000000000000 : ℝ)*(f.failure) + (144038023257/15625000000 : ℝ)*(f.sum) + (26621959120327223577/33856194175000000000000000000000 : ℝ)*base62 + (170367275688437/505512500000000000000000000 : ℝ)*base64 + (478093726753399/3348700000000000000000000000 : ℝ)*base67 + (31132559182003/252756250000000000000000000 : ℝ)*base68 + (6792866528389635247/17355255150000000000000000000000 : ℝ)*base70 + (35575017086411/686640000000000000000000000 : ℝ)*base72 + (113208208218651/1674350000000000000000000000 : ℝ)*base74 + (33672803136377/429150000000000000000000000 : ℝ)*base77 + (35498738380622379203/114967568400000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (66087/100000000000000000 : ℝ)*base86 + (66087/100000000000000000 : ℝ)*base88 + (66087/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((8583/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8583/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(33487/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(33487/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(40441/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(40441/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((7413/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7413/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29037/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(29037/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1579/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(1579/20000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c312059_s2 p hpa hpb X hX hprev1

#print axioms solution
