-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c313059_s0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:34:11.353476+00:00
-- url     : https://prove2.me/submissions/834570b7-12a4-4628-8268-c9871c67640a

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
theorem collision_support_c313059_s0_s0_0 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-3008407377/10000000000 : ℝ)*x 0 + (752101847/2500000000 : ℝ)*x 1 + (3209568589/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3008407377/10000000000 : ℝ)^37 ≤ (10799397252659/50000000000000 : ℝ)^29 := by
    have hnat : (3008407377 : ℕ)^37*50000000000000^29 ≤ 10799397252659^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3008407377 10000000000 10799397252659 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (752101847/2500000000 : ℝ)^37 ≤ (10799397303039/50000000000000 : ℝ)^29 := by
    have hnat : (752101847 : ℕ)^37*50000000000000^29 ≤ 10799397303039^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      752101847 2500000000 10799397303039 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3209568589/5000000000 : ℝ)^37 ≤ (28401205436573/50000000000000 : ℝ)^29 := by
    have hnat : (3209568589 : ℕ)^37*50000000000000^29 ≤ 28401205436573^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3209568589 5000000000 28401205436573 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3008407377/10000000000 : ℝ), (752101847/2500000000 : ℝ), (3209568589/5000000000 : ℝ)] ![(10799397252659/50000000000000 : ℝ), (10799397303039/50000000000000 : ℝ), (28401205436573/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3008407377/10000000000 : ℝ)|^37 ≤ (10799397252659/50000000000000 : ℝ)^29
        have hw : |(-3008407377/10000000000 : ℝ)|=(3008407377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(752101847/2500000000 : ℝ)|^37 ≤ (10799397303039/50000000000000 : ℝ)^29
        have hw : |(752101847/2500000000 : ℝ)|=(752101847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3209568589/5000000000 : ℝ)|^37 ≤ (28401205436573/50000000000000 : ℝ)^29
        have hw : |(3209568589/5000000000 : ℝ)|=(3209568589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313059_s0_s0_7 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-57995419/250000000 : ℝ)*x 0 + (104930101/2500000000 : ℝ)*x 1 + (67348223/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (57995419/250000000 : ℝ)^37 ≤ (15502667112223/100000000000000 : ℝ)^29 := by
    have hnat : (57995419 : ℕ)^37*100000000000000^29 ≤ 15502667112223^29*250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57995419 250000000 15502667112223 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104930101/2500000000 : ℝ)^37 ≤ (1750197267457/100000000000000 : ℝ)^29 := by
    have hnat : (104930101 : ℕ)^37*100000000000000^29 ≤ 1750197267457^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104930101 2500000000 1750197267457 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67348223/78125000 : ℝ)^37 ≤ (82747135604837/100000000000000 : ℝ)^29 := by
    have hnat : (67348223 : ℕ)^37*100000000000000^29 ≤ 82747135604837^29*78125000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67348223 78125000 82747135604837 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-57995419/250000000 : ℝ), (104930101/2500000000 : ℝ), (67348223/78125000 : ℝ)] ![(15502667112223/100000000000000 : ℝ), (1750197267457/100000000000000 : ℝ), (82747135604837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-57995419/250000000 : ℝ)|^37 ≤ (15502667112223/100000000000000 : ℝ)^29
        have hw : |(-57995419/250000000 : ℝ)|=(57995419/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(104930101/2500000000 : ℝ)|^37 ≤ (1750197267457/100000000000000 : ℝ)^29
        have hw : |(104930101/2500000000 : ℝ)|=(104930101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(67348223/78125000 : ℝ)|^37 ≤ (82747135604837/100000000000000 : ℝ)^29
        have hw : |(67348223/78125000 : ℝ)|=(67348223/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313059_s0_s0_8 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1125401511/10000000000 : ℝ)*x 0 + (-446123387/2500000000 : ℝ)*x 1 + (1724113287/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1125401511/10000000000 : ℝ)^37 ≤ (77003280849/1250000000000 : ℝ)^29 := by
    have hnat : (1125401511 : ℕ)^37*1250000000000^29 ≤ 77003280849^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125401511 10000000000 77003280849 1250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (446123387/2500000000 : ℝ)^37 ≤ (1386584590433/12500000000000 : ℝ)^29 := by
    have hnat : (446123387 : ℕ)^37*12500000000000^29 ≤ 1386584590433^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      446123387 2500000000 1386584590433 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1724113287/2000000000 : ℝ)^37 ≤ (16549412157899/20000000000000 : ℝ)^29 := by
    have hnat : (1724113287 : ℕ)^37*20000000000000^29 ≤ 16549412157899^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1724113287 2000000000 16549412157899 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1125401511/10000000000 : ℝ), (-446123387/2500000000 : ℝ), (1724113287/2000000000 : ℝ)] ![(77003280849/1250000000000 : ℝ), (1386584590433/12500000000000 : ℝ), (16549412157899/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1125401511/10000000000 : ℝ)|^37 ≤ (77003280849/1250000000000 : ℝ)^29
        have hw : |(1125401511/10000000000 : ℝ)|=(1125401511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-446123387/2500000000 : ℝ)|^37 ≤ (1386584590433/12500000000000 : ℝ)^29
        have hw : |(-446123387/2500000000 : ℝ)|=(446123387/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1724113287/2000000000 : ℝ)|^37 ≤ (16549412157899/20000000000000 : ℝ)^29
        have hw : |(1724113287/2000000000 : ℝ)|=(1724113287/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313059_s0_s0_9 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (977600443/2500000000 : ℝ)*x 0 + (943233891/1250000000 : ℝ)*x 1 + (-3123/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (977600443/2500000000 : ℝ)^37 ≤ (30180798618251/100000000000000 : ℝ)^29 := by
    have hnat : (977600443 : ℕ)^37*100000000000000^29 ≤ 30180798618251^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977600443 2500000000 30180798618251 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (943233891/1250000000 : ℝ)^37 ≤ (69819067073763/100000000000000 : ℝ)^29 := by
    have hnat : (943233891 : ℕ)^37*100000000000000^29 ≤ 69819067073763^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      943233891 1250000000 69819067073763 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3123/125000000 : ℝ)^37 ≤ (67146207/50000000000000 : ℝ)^29 := by
    have hnat : (3123 : ℕ)^37*50000000000000^29 ≤ 67146207^29*125000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3123 125000000 67146207 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(977600443/2500000000 : ℝ), (943233891/1250000000 : ℝ), (-3123/125000000 : ℝ)] ![(30180798618251/100000000000000 : ℝ), (69819067073763/100000000000000 : ℝ), (67146207/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(977600443/2500000000 : ℝ)|^37 ≤ (30180798618251/100000000000000 : ℝ)^29
        have hw : |(977600443/2500000000 : ℝ)|=(977600443/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(943233891/1250000000 : ℝ)|^37 ≤ (69819067073763/100000000000000 : ℝ)^29
        have hw : |(943233891/1250000000 : ℝ)|=(943233891/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3123/125000000 : ℝ)|^37 ≤ (67146207/50000000000000 : ℝ)^29
        have hw : |(-3123/125000000 : ℝ)|=(3123/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313059_s0_s0_13 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1746472773/10000000000 : ℝ)*x 0 + (2073460453/2500000000 : ℝ)*x 1 + (850902149/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1746472773/10000000000 : ℝ)^37 ≤ (10792026698967/100000000000000 : ℝ)^29 := by
    have hnat : (1746472773 : ℕ)^37*100000000000000^29 ≤ 10792026698967^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1746472773 10000000000 10792026698967 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2073460453/2500000000 : ℝ)^37 ≤ (15753372270117/20000000000000 : ℝ)^29 := by
    have hnat : (2073460453 : ℕ)^37*20000000000000^29 ≤ 15753372270117^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073460453 2500000000 15753372270117 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (850902149/5000000000 : ℝ)^37 ≤ (2088222386821/20000000000000 : ℝ)^29 := by
    have hnat : (850902149 : ℕ)^37*20000000000000^29 ≤ 2088222386821^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850902149 5000000000 2088222386821 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1746472773/10000000000 : ℝ), (2073460453/2500000000 : ℝ), (850902149/5000000000 : ℝ)] ![(10792026698967/100000000000000 : ℝ), (15753372270117/20000000000000 : ℝ), (2088222386821/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1746472773/10000000000 : ℝ)|^37 ≤ (10792026698967/100000000000000 : ℝ)^29
        have hw : |(1746472773/10000000000 : ℝ)|=(1746472773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2073460453/2500000000 : ℝ)|^37 ≤ (15753372270117/20000000000000 : ℝ)^29
        have hw : |(2073460453/2500000000 : ℝ)|=(2073460453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(850902149/5000000000 : ℝ)|^37 ≤ (2088222386821/20000000000000 : ℝ)^29
        have hw : |(850902149/5000000000 : ℝ)|=(850902149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313059_s0_s0_14 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-925392077/10000000000 : ℝ)*x 0 + (1379225833/10000000000 : ℝ)*x 1 + (1796668241/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (925392077/10000000000 : ℝ)^37 ≤ (239962993663/5000000000000 : ℝ)^29 := by
    have hnat : (925392077 : ℕ)^37*5000000000000^29 ≤ 239962993663^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      925392077 10000000000 239962993663 5000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1379225833/10000000000 : ℝ)^37 ≤ (3992670067329/50000000000000 : ℝ)^29 := by
    have hnat : (1379225833 : ℕ)^37*50000000000000^29 ≤ 3992670067329^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379225833 10000000000 3992670067329 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1796668241/2000000000 : ℝ)^37 ≤ (87215399974859/100000000000000 : ℝ)^29 := by
    have hnat : (1796668241 : ℕ)^37*100000000000000^29 ≤ 87215399974859^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1796668241 2000000000 87215399974859 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-925392077/10000000000 : ℝ), (1379225833/10000000000 : ℝ), (1796668241/2000000000 : ℝ)] ![(239962993663/5000000000000 : ℝ), (3992670067329/50000000000000 : ℝ), (87215399974859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-925392077/10000000000 : ℝ)|^37 ≤ (239962993663/5000000000000 : ℝ)^29
        have hw : |(-925392077/10000000000 : ℝ)|=(925392077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1379225833/10000000000 : ℝ)|^37 ≤ (3992670067329/50000000000000 : ℝ)^29
        have hw : |(1379225833/10000000000 : ℝ)|=(1379225833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1796668241/2000000000 : ℝ)|^37 ≤ (87215399974859/100000000000000 : ℝ)^29
        have hw : |(1796668241/2000000000 : ℝ)|=(1796668241/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313059_s0_s0_15 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (663721/8000000 : ℝ)*x 0 + (-1463038193/10000000000 : ℝ)*x 1 + (1796668231/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663721/8000000 : ℝ)^37 ≤ (4175032567307/100000000000000 : ℝ)^29 := by
    have hnat : (663721 : ℕ)^37*100000000000000^29 ≤ 4175032567307^29*8000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663721 8000000 4175032567307 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1463038193/10000000000 : ℝ)^37 ≤ (43047840341/500000000000 : ℝ)^29 := by
    have hnat : (1463038193 : ℕ)^37*500000000000^29 ≤ 43047840341^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1463038193 10000000000 43047840341 500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1796668231/2000000000 : ℝ)^37 ≤ (87215399355519/100000000000000 : ℝ)^29 := by
    have hnat : (1796668231 : ℕ)^37*100000000000000^29 ≤ 87215399355519^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1796668231 2000000000 87215399355519 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663721/8000000 : ℝ), (-1463038193/10000000000 : ℝ), (1796668231/2000000000 : ℝ)] ![(4175032567307/100000000000000 : ℝ), (43047840341/500000000000 : ℝ), (87215399355519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663721/8000000 : ℝ)|^37 ≤ (4175032567307/100000000000000 : ℝ)^29
        have hw : |(663721/8000000 : ℝ)|=(663721/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1463038193/10000000000 : ℝ)|^37 ≤ (43047840341/500000000000 : ℝ)^29
        have hw : |(-1463038193/10000000000 : ℝ)|=(1463038193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1796668231/2000000000 : ℝ)|^37 ≤ (87215399355519/100000000000000 : ℝ)^29
        have hw : |(1796668231/2000000000 : ℝ)|=(1796668231/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313059_s0_s0_16 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (8789316967/10000000000 : ℝ)*x 0 + (1140987063/5000000000 : ℝ)*x 1 + (-23/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8789316967/10000000000 : ℝ)^37 ≤ (21204814644353/25000000000000 : ℝ)^29 := by
    have hnat : (8789316967 : ℕ)^37*25000000000000^29 ≤ 21204814644353^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8789316967 10000000000 21204814644353 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1140987063/5000000000 : ℝ)^37 ≤ (121445931231/800000000000 : ℝ)^29 := by
    have hnat : (1140987063 : ℕ)^37*800000000000^29 ≤ 121445931231^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1140987063 5000000000 121445931231 800000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (23/1000000000 : ℝ)^37 ≤ (17973/100000000000000 : ℝ)^29 := by
    have hnat : (23 : ℕ)^37*100000000000000^29 ≤ 17973^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23 1000000000 17973 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8789316967/10000000000 : ℝ), (1140987063/5000000000 : ℝ), (-23/1000000000 : ℝ)] ![(21204814644353/25000000000000 : ℝ), (121445931231/800000000000 : ℝ), (17973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8789316967/10000000000 : ℝ)|^37 ≤ (21204814644353/25000000000000 : ℝ)^29
        have hw : |(8789316967/10000000000 : ℝ)|=(8789316967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1140987063/5000000000 : ℝ)|^37 ≤ (121445931231/800000000000 : ℝ)^29
        have hw : |(1140987063/5000000000 : ℝ)|=(1140987063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-23/1000000000 : ℝ)|^37 ≤ (17973/100000000000000 : ℝ)^29
        have hw : |(-23/1000000000 : ℝ)|=(23/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313059_s0_s0_20 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (849596413/1250000000 : ℝ)*x 0 + (3216484357/10000000000 : ℝ)*x 1 + (461020299/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (849596413/1250000000 : ℝ)^37 ≤ (1222000312147/2000000000000 : ℝ)^29 := by
    have hnat : (849596413 : ℕ)^37*2000000000000^29 ≤ 1222000312147^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849596413 1250000000 1222000312147 2000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3216484357/10000000000 : ℝ)^37 ≤ (23522672899263/100000000000000 : ℝ)^29 := by
    have hnat : (3216484357 : ℕ)^37*100000000000000^29 ≤ 23522672899263^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3216484357 10000000000 23522672899263 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (461020299/2000000000 : ℝ)^37 ≤ (15377311488171/100000000000000 : ℝ)^29 := by
    have hnat : (461020299 : ℕ)^37*100000000000000^29 ≤ 15377311488171^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      461020299 2000000000 15377311488171 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(849596413/1250000000 : ℝ), (3216484357/10000000000 : ℝ), (461020299/2000000000 : ℝ)] ![(1222000312147/2000000000000 : ℝ), (23522672899263/100000000000000 : ℝ), (15377311488171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(849596413/1250000000 : ℝ)|^37 ≤ (1222000312147/2000000000000 : ℝ)^29
        have hw : |(849596413/1250000000 : ℝ)|=(849596413/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3216484357/10000000000 : ℝ)|^37 ≤ (23522672899263/100000000000000 : ℝ)^29
        have hw : |(3216484357/10000000000 : ℝ)|=(3216484357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(461020299/2000000000 : ℝ)|^37 ≤ (15377311488171/100000000000000 : ℝ)^29
        have hw : |(461020299/2000000000 : ℝ)|=(461020299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313059_s0_s0_21 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1334758597/2000000000 : ℝ)*x 0 + (557654691/2500000000 : ℝ)*x 1 + (3432933993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1334758597/2000000000 : ℝ)^37 ≤ (59693058209469/100000000000000 : ℝ)^29 := by
    have hnat : (1334758597 : ℕ)^37*100000000000000^29 ≤ 59693058209469^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1334758597 2000000000 59693058209469 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (557654691/2500000000 : ℝ)^37 ≤ (14746216997481/100000000000000 : ℝ)^29 := by
    have hnat : (557654691 : ℕ)^37*100000000000000^29 ≤ 14746216997481^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      557654691 2500000000 14746216997481 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3432933993/10000000000 : ℝ)^37 ≤ (25560724785423/100000000000000 : ℝ)^29 := by
    have hnat : (3432933993 : ℕ)^37*100000000000000^29 ≤ 25560724785423^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3432933993 10000000000 25560724785423 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1334758597/2000000000 : ℝ), (557654691/2500000000 : ℝ), (3432933993/10000000000 : ℝ)] ![(59693058209469/100000000000000 : ℝ), (14746216997481/100000000000000 : ℝ), (25560724785423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1334758597/2000000000 : ℝ)|^37 ≤ (59693058209469/100000000000000 : ℝ)^29
        have hw : |(-1334758597/2000000000 : ℝ)|=(1334758597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(557654691/2500000000 : ℝ)|^37 ≤ (14746216997481/100000000000000 : ℝ)^29
        have hw : |(557654691/2500000000 : ℝ)|=(557654691/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3432933993/10000000000 : ℝ)|^37 ≤ (25560724785423/100000000000000 : ℝ)^29
        have hw : |(3432933993/10000000000 : ℝ)|=(3432933993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313059_s0_s0_22 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (664084507/10000000000 : ℝ)*x 0 + (-748202489/10000000000 : ℝ)*x 1 + (2365706043/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664084507/10000000000 : ℝ)^37 ≤ (3142819538379/100000000000000 : ℝ)^29 := by
    have hnat : (664084507 : ℕ)^37*100000000000000^29 ≤ 3142819538379^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664084507 10000000000 3142819538379 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (748202489/10000000000 : ℝ)^37 ≤ (3659348243873/100000000000000 : ℝ)^29 := by
    have hnat : (748202489 : ℕ)^37*100000000000000^29 ≤ 3659348243873^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      748202489 10000000000 3659348243873 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2365706043/2500000000 : ℝ)^37 ≤ (23299458051959/25000000000000 : ℝ)^29 := by
    have hnat : (2365706043 : ℕ)^37*25000000000000^29 ≤ 23299458051959^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2365706043 2500000000 23299458051959 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664084507/10000000000 : ℝ), (-748202489/10000000000 : ℝ), (2365706043/2500000000 : ℝ)] ![(3142819538379/100000000000000 : ℝ), (3659348243873/100000000000000 : ℝ), (23299458051959/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664084507/10000000000 : ℝ)|^37 ≤ (3142819538379/100000000000000 : ℝ)^29
        have hw : |(664084507/10000000000 : ℝ)|=(664084507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-748202489/10000000000 : ℝ)|^37 ≤ (3659348243873/100000000000000 : ℝ)^29
        have hw : |(-748202489/10000000000 : ℝ)|=(748202489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2365706043/2500000000 : ℝ)|^37 ≤ (23299458051959/25000000000000 : ℝ)^29
        have hw : |(2365706043/2500000000 : ℝ)|=(2365706043/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313059_s0_s0_23 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (8646736801/10000000000 : ℝ)*x 0 + (1242853369/5000000000 : ℝ)*x 1 + (830127/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8646736801/10000000000 : ℝ)^37 ≤ (83067696564849/100000000000000 : ℝ)^29 := by
    have hnat : (8646736801 : ℕ)^37*100000000000000^29 ≤ 83067696564849^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8646736801 10000000000 83067696564849 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1242853369/5000000000 : ℝ)^37 ≤ (16930798666163/100000000000000 : ℝ)^29 := by
    have hnat : (1242853369 : ℕ)^37*100000000000000^29 ≤ 16930798666163^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1242853369 5000000000 16930798666163 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (830127/5000000000 : ℝ)^37 ≤ (376187249/25000000000000 : ℝ)^29 := by
    have hnat : (830127 : ℕ)^37*25000000000000^29 ≤ 376187249^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      830127 5000000000 376187249 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8646736801/10000000000 : ℝ), (1242853369/5000000000 : ℝ), (830127/5000000000 : ℝ)] ![(83067696564849/100000000000000 : ℝ), (16930798666163/100000000000000 : ℝ), (376187249/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8646736801/10000000000 : ℝ)|^37 ≤ (83067696564849/100000000000000 : ℝ)^29
        have hw : |(8646736801/10000000000 : ℝ)|=(8646736801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1242853369/5000000000 : ℝ)|^37 ≤ (16930798666163/100000000000000 : ℝ)^29
        have hw : |(1242853369/5000000000 : ℝ)|=(1242853369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(830127/5000000000 : ℝ)|^37 ≤ (376187249/25000000000000 : ℝ)^29
        have hw : |(830127/5000000000 : ℝ)|=(830127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313059_s0_s0_27 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (31286831/250000000 : ℝ)*x 0 + (835654097/1000000000 : ℝ)*x 1 + (2071630067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (31286831/250000000 : ℝ)^37 ≤ (3526991541913/50000000000000 : ℝ)^29 := by
    have hnat : (31286831 : ℕ)^37*50000000000000^29 ≤ 3526991541913^29*250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31286831 250000000 3526991541913 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (835654097/1000000000 : ℝ)^37 ≤ (19881842875903/25000000000000 : ℝ)^29 := by
    have hnat : (835654097 : ℕ)^37*25000000000000^29 ≤ 19881842875903^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      835654097 1000000000 19881842875903 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2071630067/10000000000 : ℝ)^37 ≤ (2683729078183/20000000000000 : ℝ)^29 := by
    have hnat : (2071630067 : ℕ)^37*20000000000000^29 ≤ 2683729078183^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071630067 10000000000 2683729078183 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(31286831/250000000 : ℝ), (835654097/1000000000 : ℝ), (2071630067/10000000000 : ℝ)] ![(3526991541913/50000000000000 : ℝ), (19881842875903/25000000000000 : ℝ), (2683729078183/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(31286831/250000000 : ℝ)|^37 ≤ (3526991541913/50000000000000 : ℝ)^29
        have hw : |(31286831/250000000 : ℝ)|=(31286831/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(835654097/1000000000 : ℝ)|^37 ≤ (19881842875903/25000000000000 : ℝ)^29
        have hw : |(835654097/1000000000 : ℝ)|=(835654097/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2071630067/10000000000 : ℝ)|^37 ≤ (2683729078183/20000000000000 : ℝ)^29
        have hw : |(2071630067/10000000000 : ℝ)|=(2071630067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c313059_s0 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]]) : (0 : ℝ) ≤ ((42031/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(42031/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(83689/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(83689/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(17817/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(17817/25000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (78599/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (78599/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (78599/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (78599/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78599/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78599/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (176973/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  have s0_pow0 : (1 : ℝ) ^ (73/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^73 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^73*1^16 ≤ 1^16*1^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5820351075331079/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5820351075331079/5000000000000000 : ℝ)^73 := by
      have hnat : (2 : ℕ)^16*5000000000000000^73 ≤ 5820351075331079^73*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5820351075331079 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5820351075331079/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12722560406774351/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12722560406774351/10000000000000000 : ℝ)^73 := by
      have hnat : (3 : ℕ)^16*10000000000000000^73 ≤ 12722560406774351^73*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12722560406774351 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12722560406774351/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(820351075331079/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1081858256112193/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (820351075331079/5000000000000000 : ℝ)) (beta := (1081858256112193/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(820351075331079/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1081858256112193/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (73/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^73 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^73*1^16 ≤ 1^16*1^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5820351075331079/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5820351075331079/5000000000000000 : ℝ)^73 := by
      have hnat : (2 : ℕ)^16*5000000000000000^73 ≤ 5820351075331079^73*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5820351075331079 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5820351075331079/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12722560406774351/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12722560406774351/10000000000000000 : ℝ)^73 := by
      have hnat : (3 : ℕ)^16*10000000000000000^73 ≤ 12722560406774351^73*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12722560406774351 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12722560406774351/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(820351075331079/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(1081858256112193/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (820351075331079/5000000000000000 : ℝ)) (beta := (1081858256112193/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(820351075331079/5000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(1081858256112193/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (73/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^73 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^73*1^16 ≤ 1^16*1^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5820351075331079/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5820351075331079/5000000000000000 : ℝ)^73 := by
      have hnat : (2 : ℕ)^16*5000000000000000^73 ≤ 5820351075331079^73*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5820351075331079 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5820351075331079/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12722560406774351/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12722560406774351/10000000000000000 : ℝ)^73 := by
      have hnat : (3 : ℕ)^16*10000000000000000^73 ≤ 12722560406774351^73*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12722560406774351 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12722560406774351/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(820351075331079/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1081858256112193/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (820351075331079/5000000000000000 : ℝ)) (beta := (1081858256112193/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(820351075331079/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1081858256112193/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-3008407377/10000000000 : ℝ)*X 0 0+(752101847/2500000000 : ℝ)*X 0 1+(3209568589/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313059_s0_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-57995419/250000000 : ℝ)*X 0 0+(104930101/2500000000 : ℝ)*X 0 1+(67348223/78125000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313059_s0_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1125401511/10000000000 : ℝ)*X 1 0+(-446123387/2500000000 : ℝ)*X 1 1+(1724113287/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313059_s0_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((977600443/2500000000 : ℝ)*X 2 0+(943233891/1250000000 : ℝ)*X 2 1+(-3123/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313059_s0_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((1746472773/10000000000 : ℝ)*X 0 0+(2073460453/2500000000 : ℝ)*X 0 1+(850902149/5000000000 : ℝ)*X 0 2+(1746472773/10000000000 : ℝ)*X 1 0+(2073460453/2500000000 : ℝ)*X 1 1+(850902149/5000000000 : ℝ)*X 1 2+(1746472773/10000000000 : ℝ)*X 2 0+(2073460453/2500000000 : ℝ)*X 2 1+(850902149/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313059_s0_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-925392077/10000000000 : ℝ)*X 0 0+(1379225833/10000000000 : ℝ)*X 0 1+(1796668241/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313059_s0_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((663721/8000000 : ℝ)*X 1 0+(-1463038193/10000000000 : ℝ)*X 1 1+(1796668231/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313059_s0_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((8789316967/10000000000 : ℝ)*X 2 0+(1140987063/5000000000 : ℝ)*X 2 1+(-23/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313059_s0_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((849596413/1250000000 : ℝ)*X 0 0+(3216484357/10000000000 : ℝ)*X 0 1+(461020299/2000000000 : ℝ)*X 0 2+(849596413/1250000000 : ℝ)*X 1 0+(3216484357/10000000000 : ℝ)*X 1 1+(461020299/2000000000 : ℝ)*X 1 2+(849596413/1250000000 : ℝ)*X 2 0+(3216484357/10000000000 : ℝ)*X 2 1+(461020299/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313059_s0_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-1334758597/2000000000 : ℝ)*X 0 0+(557654691/2500000000 : ℝ)*X 0 1+(3432933993/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313059_s0_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((664084507/10000000000 : ℝ)*X 1 0+(-748202489/10000000000 : ℝ)*X 1 1+(2365706043/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313059_s0_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((8646736801/10000000000 : ℝ)*X 2 0+(1242853369/5000000000 : ℝ)*X 2 1+(830127/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313059_s0_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((31286831/250000000 : ℝ)*X 0 0+(835654097/1000000000 : ℝ)*X 0 1+(2071630067/10000000000 : ℝ)*X 0 2+(31286831/250000000 : ℝ)*X 1 0+(835654097/1000000000 : ℝ)*X 1 1+(2071630067/10000000000 : ℝ)*X 1 2+(31286831/250000000 : ℝ)*X 2 0+(835654097/1000000000 : ℝ)*X 2 1+(2071630067/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313059_s0_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((42031/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(42031/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (31906580772087767408787/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (186052187/100000000000 : ℝ)*(base5) + (1048003144311/1000000000000 : ℝ)*(base7) + (101283/25000000000 : ℝ)*(base44) + (16354111681/62500000000 : ℝ)*(base53) + (1534930360857/1000000000000 : ℝ)*(major_s0_0) + (1534926309537/1000000000000 : ℝ)*(major_s0_1) + (1273264573961/1000000000000 : ℝ)*(major_s0_2) + (1284323317433/1000000000000 : ℝ)*(sp_s0_7) + (642094642917/500000000000 : ℝ)*(sp_s0_8) + (96741155519/62500000000 : ℝ)*(sp_s0_9) + (1951763299223/1000000000000 : ℝ)*(sp_s0_13) + (1772421/200000000000 : ℝ)*(sp_s0_14) + (8677649/62500000000 : ℝ)*(sp_s0_15) + (1045651/125000000000 : ℝ)*(sp_s0_27) + (905633093309/1000000000000 : ℝ)*(f.failure) + (772998983217/500000000000 : ℝ)*(f.sum) + (26148139279187/625000000000000000000000000 : ℝ)*base62 + (5027000870593527/10000000000000000000000000000 : ℝ)*base64 + (1273890549115359/10000000000000000000000000000 : ℝ)*base66 + (1181352193933919/5000000000000000000000000000 : ℝ)*base68 + (4455107895244121/10000000000000000000000000000 : ℝ)*base70 + (1804737332370599/10000000000000000000000000000 : ℝ)*base72 + (749162083299577/5000000000000000000000000000 : ℝ)*base74 + (2158105156825297/5000000000000000000000000000 : ℝ)*base76 + (608497872242979/5000000000000000000000000000 : ℝ)*base78 + (37517/100000000000000000 : ℝ)*base86 + (37517/100000000000000000 : ℝ)*base88 + (37517/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(83689/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(83689/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1446184537072672336107/200000000000000000000000000 : ℝ) := by norm_num
    linear_combination (542008403557/1000000000000 : ℝ)*(base5) + (534454892783/500000000000 : ℝ)*(base7) + (7332421/1000000000000 : ℝ)*(base53) + (4366735553/25000000000 : ℝ)*(base60) + (302253465893/200000000000 : ℝ)*(major_s0_0) + (302253465893/200000000000 : ℝ)*(major_s0_1) + (377814999261/250000000000 : ℝ)*(major_s0_2) + (2395757/500000000000 : ℝ)*(sp_s0_0) + (5163923/250000000000 : ℝ)*(sp_s0_7) + (54316467/1000000000000 : ℝ)*(sp_s0_8) + (375066841343/250000000000 : ℝ)*(sp_s0_14) + (150023849611/100000000000 : ℝ)*(sp_s0_15) + (510577137139/250000000000 : ℝ)*(sp_s0_16) + (1418572914023/1000000000000 : ℝ)*(sp_s0_20) + (445835766007/500000000000 : ℝ)*(f.failure) + (750150072499/500000000000 : ℝ)*(f.sum) + (406390639387741/5000000000000000000000000000 : ℝ)*base62 + (1041537493660627/2500000000000000000000000000 : ℝ)*base64 + (1330883410066651/2000000000000000000000000000 : ℝ)*base66 + (347319606457619/1250000000000000000000000000 : ℝ)*base68 + (1670231929378519/5000000000000000000000000000 : ℝ)*base70 + (170754390933349/2000000000000000000000000000 : ℝ)*base73 + (689814355011453/1000000000000000000000000000 : ℝ)*base74 + (361049817311453/1000000000000000000000000000 : ℝ)*base76 + (128573943566651/1000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (21591/50000000000000000 : ℝ)*base86 + (21591/50000000000000000 : ℝ)*base88 + (21591/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(17817/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(17817/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (49179094297316752477083/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (174335497983/1000000000000 : ℝ)*(base5) + (157734082331/250000000000 : ℝ)*(base7) + (16677207629/250000000000 : ℝ)*(base33) + (773605493643/1000000000000 : ℝ)*(base44) + (53888697207/500000000000 : ℝ)*(base50) + (337317530033/250000000000 : ℝ)*(major_s0_0) + (128474691401/200000000000 : ℝ)*(major_s0_1) + (176997368831/125000000000 : ℝ)*(major_s0_2) + (256039823/1000000000000 : ℝ)*(sp_s0_15) + (10033413/250000000000 : ℝ)*(sp_s0_16) + (324861817051/200000000000 : ℝ)*(sp_s0_21) + (391869360637/500000000000 : ℝ)*(sp_s0_22) + (173189561907/100000000000 : ℝ)*(sp_s0_23) + (518445225093/1000000000000 : ℝ)*(sp_s0_27) + (417724943697/500000000000 : ℝ)*(f.failure) + (324861817051/200000000000 : ℝ)*(f.sum) + (3605287027330797/5000000000000000000000000000 : ℝ)*base62 + (798376091493617/1250000000000000000000000000 : ℝ)*base64 + (464768819152393/2000000000000000000000000000 : ℝ)*base67 + (215107824448649/625000000000000000000000000 : ℝ)*base68 + (41069813507301/125000000000000000000000000 : ℝ)*base70 + (2049912386007631/2500000000000000000000000000 : ℝ)*base72 + (499489558048321/1000000000000000000000000000 : ℝ)*base74 + (774006751954393/1250000000000000000000000000 : ℝ)*base76 + (3330385870731441/10000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (26561/50000000000000000 : ℝ)*base86 + (26561/50000000000000000 : ℝ)*base88 + (26561/50000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]]) : (0 : ℝ) ≤ ((42031/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(42031/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(83689/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(83689/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(17817/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(17817/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c313059_s0 p hpa hpb X hX

#print axioms solution
