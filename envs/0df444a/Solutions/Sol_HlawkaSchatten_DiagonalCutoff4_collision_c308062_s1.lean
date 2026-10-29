-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c308062_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:38:51.501137+00:00
-- url     : https://prove2.me/submissions/17347cde-0351-4e53-b828-35c7fd652ba6

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
theorem collision_support_c308062_s1_s1_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-184249139/2000000000 : ℝ)*x 0 + (2538067453/5000000000 : ℝ)*x 1 + (-624269199/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (184249139/2000000000 : ℝ)^69 ≤ (4484707307707/100000000000000 : ℝ)^53 := by
    have hnat : (184249139 : ℕ)^69*100000000000000^53 ≤ 4484707307707^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      184249139 2000000000 4484707307707 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2538067453/5000000000 : ℝ)^69 ≤ (20682713153687/50000000000000 : ℝ)^53 := by
    have hnat : (2538067453 : ℕ)^69*50000000000000^53 ≤ 20682713153687^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2538067453 5000000000 20682713153687 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (624269199/1000000000 : ℝ)^69 ≤ (6768733296591/12500000000000 : ℝ)^53 := by
    have hnat : (624269199 : ℕ)^69*12500000000000^53 ≤ 6768733296591^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      624269199 1000000000 6768733296591 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-184249139/2000000000 : ℝ), (2538067453/5000000000 : ℝ), (-624269199/1000000000 : ℝ)] ![(4484707307707/100000000000000 : ℝ), (20682713153687/50000000000000 : ℝ), (6768733296591/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-184249139/2000000000 : ℝ)|^69 ≤ (4484707307707/100000000000000 : ℝ)^53
        have hw : |(-184249139/2000000000 : ℝ)|=(184249139/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2538067453/5000000000 : ℝ)|^69 ≤ (20682713153687/50000000000000 : ℝ)^53
        have hw : |(2538067453/5000000000 : ℝ)|=(2538067453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-624269199/1000000000 : ℝ)|^69 ≤ (6768733296591/12500000000000 : ℝ)^53
        have hw : |(-624269199/1000000000 : ℝ)|=(624269199/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308062_s1_s1_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1019052813/2000000000 : ℝ)*x 0 + (-114003233/1250000000 : ℝ)*x 1 + (-6229873217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1019052813/2000000000 : ℝ)^69 ≤ (10392121087689/25000000000000 : ℝ)^53 := by
    have hnat : (1019052813 : ℕ)^69*25000000000000^53 ≤ 10392121087689^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019052813 2000000000 10392121087689 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (114003233/1250000000 : ℝ)^69 ≤ (2213181619087/50000000000000 : ℝ)^53 := by
    have hnat : (114003233 : ℕ)^69*50000000000000^53 ≤ 2213181619087^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114003233 1250000000 2213181619087 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6229873217/10000000000 : ℝ)^69 ≤ (5400515240011/10000000000000 : ℝ)^53 := by
    have hnat : (6229873217 : ℕ)^69*10000000000000^53 ≤ 5400515240011^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6229873217 10000000000 5400515240011 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1019052813/2000000000 : ℝ), (-114003233/1250000000 : ℝ), (-6229873217/10000000000 : ℝ)] ![(10392121087689/25000000000000 : ℝ), (2213181619087/50000000000000 : ℝ), (5400515240011/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1019052813/2000000000 : ℝ)|^69 ≤ (10392121087689/25000000000000 : ℝ)^53
        have hw : |(1019052813/2000000000 : ℝ)|=(1019052813/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-114003233/1250000000 : ℝ)|^69 ≤ (2213181619087/50000000000000 : ℝ)^53
        have hw : |(-114003233/1250000000 : ℝ)|=(114003233/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6229873217/10000000000 : ℝ)|^69 ≤ (5400515240011/10000000000000 : ℝ)^53
        have hw : |(-6229873217/10000000000 : ℝ)|=(6229873217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308062_s1_s1_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-287516739/2000000000 : ℝ)*x 0 + (1013078323/5000000000 : ℝ)*x 1 + (-1676588007/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (287516739/2000000000 : ℝ)^69 ≤ (8004490775347/100000000000000 : ℝ)^53 := by
    have hnat : (287516739 : ℕ)^69*100000000000000^53 ≤ 8004490775347^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287516739 2000000000 8004490775347 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1013078323/5000000000 : ℝ)^69 ≤ (2502630629351/20000000000000 : ℝ)^53 := by
    have hnat : (1013078323 : ℕ)^69*20000000000000^53 ≤ 2502630629351^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1013078323 5000000000 2502630629351 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1676588007/2000000000 : ℝ)^69 ≤ (79482356067303/100000000000000 : ℝ)^53 := by
    have hnat : (1676588007 : ℕ)^69*100000000000000^53 ≤ 79482356067303^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1676588007 2000000000 79482356067303 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-287516739/2000000000 : ℝ), (1013078323/5000000000 : ℝ), (-1676588007/2000000000 : ℝ)] ![(8004490775347/100000000000000 : ℝ), (2502630629351/20000000000000 : ℝ), (79482356067303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-287516739/2000000000 : ℝ)|^69 ≤ (8004490775347/100000000000000 : ℝ)^53
        have hw : |(-287516739/2000000000 : ℝ)|=(287516739/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1013078323/5000000000 : ℝ)|^69 ≤ (2502630629351/20000000000000 : ℝ)^53
        have hw : |(1013078323/5000000000 : ℝ)|=(1013078323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1676588007/2000000000 : ℝ)|^69 ≤ (79482356067303/100000000000000 : ℝ)^53
        have hw : |(-1676588007/2000000000 : ℝ)|=(1676588007/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308062_s1_s1_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (303996167/1250000000 : ℝ)*x 0 + (-122438731/1250000000 : ℝ)*x 1 + (-8365908783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (303996167/1250000000 : ℝ)^69 ≤ (7935183201473/50000000000000 : ℝ)^53 := by
    have hnat : (303996167 : ℕ)^69*50000000000000^53 ≤ 7935183201473^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      303996167 1250000000 7935183201473 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (122438731/1250000000 : ℝ)^69 ≤ (121436069063/2500000000000 : ℝ)^53 := by
    have hnat : (122438731 : ℕ)^69*2500000000000^53 ≤ 121436069063^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122438731 1250000000 121436069063 2500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8365908783/10000000000 : ℝ)^69 ≤ (79272190820383/100000000000000 : ℝ)^53 := by
    have hnat : (8365908783 : ℕ)^69*100000000000000^53 ≤ 79272190820383^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8365908783 10000000000 79272190820383 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(303996167/1250000000 : ℝ), (-122438731/1250000000 : ℝ), (-8365908783/10000000000 : ℝ)] ![(7935183201473/50000000000000 : ℝ), (121436069063/2500000000000 : ℝ), (79272190820383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(303996167/1250000000 : ℝ)|^69 ≤ (7935183201473/50000000000000 : ℝ)^53
        have hw : |(303996167/1250000000 : ℝ)|=(303996167/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-122438731/1250000000 : ℝ)|^69 ≤ (121436069063/2500000000000 : ℝ)^53
        have hw : |(-122438731/1250000000 : ℝ)|=(122438731/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8365908783/10000000000 : ℝ)|^69 ≤ (79272190820383/100000000000000 : ℝ)^53
        have hw : |(-8365908783/10000000000 : ℝ)|=(8365908783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308062_s1_s1_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (17412283/62500000 : ℝ)*x 0 + (1880751991/2500000000 : ℝ)*x 1 + (982404807/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17412283/62500000 : ℝ)^69 ≤ (18941797700161/100000000000000 : ℝ)^53 := by
    have hnat : (17412283 : ℕ)^69*100000000000000^53 ≤ 18941797700161^53*62500000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17412283 62500000 18941797700161 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1880751991/2500000000 : ℝ)^69 ≤ (69036021368547/100000000000000 : ℝ)^53 := by
    have hnat : (1880751991 : ℕ)^69*100000000000000^53 ≤ 69036021368547^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1880751991 2500000000 69036021368547 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (982404807/5000000000 : ℝ)^69 ≤ (3005545229681/25000000000000 : ℝ)^53 := by
    have hnat : (982404807 : ℕ)^69*25000000000000^53 ≤ 3005545229681^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      982404807 5000000000 3005545229681 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(17412283/62500000 : ℝ), (1880751991/2500000000 : ℝ), (982404807/5000000000 : ℝ)] ![(18941797700161/100000000000000 : ℝ), (69036021368547/100000000000000 : ℝ), (3005545229681/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(17412283/62500000 : ℝ)|^69 ≤ (18941797700161/100000000000000 : ℝ)^53
        have hw : |(17412283/62500000 : ℝ)|=(17412283/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1880751991/2500000000 : ℝ)|^69 ≤ (69036021368547/100000000000000 : ℝ)^53
        have hw : |(1880751991/2500000000 : ℝ)|=(1880751991/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(982404807/5000000000 : ℝ)|^69 ≤ (3005545229681/25000000000000 : ℝ)^53
        have hw : |(982404807/5000000000 : ℝ)|=(982404807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308062_s1_s1_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (183455087/500000000 : ℝ)*x 0 + (7843677783/10000000000 : ℝ)*x 1 + (2547/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (183455087/500000000 : ℝ)^69 ≤ (13554268976357/50000000000000 : ℝ)^53 := by
    have hnat : (183455087 : ℕ)^69*50000000000000^53 ≤ 13554268976357^53*500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183455087 500000000 13554268976357 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7843677783/10000000000 : ℝ)^69 ≤ (72891459918051/100000000000000 : ℝ)^53 := by
    have hnat : (7843677783 : ℕ)^69*100000000000000^53 ≤ 72891459918051^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7843677783 10000000000 72891459918051 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2547/2000000000 : ℝ)^69 ≤ (52883/2500000000000 : ℝ)^53 := by
    have hnat : (2547 : ℕ)^69*2500000000000^53 ≤ 52883^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2547 2000000000 52883 2500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(183455087/500000000 : ℝ), (7843677783/10000000000 : ℝ), (2547/2000000000 : ℝ)] ![(13554268976357/50000000000000 : ℝ), (72891459918051/100000000000000 : ℝ), (52883/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(183455087/500000000 : ℝ)|^69 ≤ (13554268976357/50000000000000 : ℝ)^53
        have hw : |(183455087/500000000 : ℝ)|=(183455087/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7843677783/10000000000 : ℝ)|^69 ≤ (72891459918051/100000000000000 : ℝ)^53
        have hw : |(7843677783/10000000000 : ℝ)|=(7843677783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2547/2000000000 : ℝ)|^69 ≤ (52883/2500000000000 : ℝ)^53
        have hw : |(2547/2000000000 : ℝ)|=(2547/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308062_s1_s1_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-509335433/5000000000 : ℝ)*x 0 + (462838023/2000000000 : ℝ)*x 1 + (-8425739991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (509335433/5000000000 : ℝ)^69 ≤ (2555891545023/50000000000000 : ℝ)^53 := by
    have hnat : (509335433 : ℕ)^69*50000000000000^53 ≤ 2555891545023^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      509335433 5000000000 2555891545023 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (462838023/2000000000 : ℝ)^69 ≤ (3719285405973/25000000000000 : ℝ)^53 := by
    have hnat : (462838023 : ℕ)^69*25000000000000^53 ≤ 3719285405973^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      462838023 2000000000 3719285405973 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8425739991/10000000000 : ℝ)^69 ≤ (80011075268893/100000000000000 : ℝ)^53 := by
    have hnat : (8425739991 : ℕ)^69*100000000000000^53 ≤ 80011075268893^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8425739991 10000000000 80011075268893 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-509335433/5000000000 : ℝ), (462838023/2000000000 : ℝ), (-8425739991/10000000000 : ℝ)] ![(2555891545023/50000000000000 : ℝ), (3719285405973/25000000000000 : ℝ), (80011075268893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-509335433/5000000000 : ℝ)|^69 ≤ (2555891545023/50000000000000 : ℝ)^53
        have hw : |(-509335433/5000000000 : ℝ)|=(509335433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(462838023/2000000000 : ℝ)|^69 ≤ (3719285405973/25000000000000 : ℝ)^53
        have hw : |(462838023/2000000000 : ℝ)|=(462838023/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8425739991/10000000000 : ℝ)|^69 ≤ (80011075268893/100000000000000 : ℝ)^53
        have hw : |(-8425739991/10000000000 : ℝ)|=(8425739991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308062_s1_s1_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1949336207/10000000000 : ℝ)*x 0 + (-739185761/5000000000 : ℝ)*x 1 + (-8408622063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1949336207/10000000000 : ℝ)^69 ≤ (11899067768877/100000000000000 : ℝ)^53 := by
    have hnat : (1949336207 : ℕ)^69*100000000000000^53 ≤ 11899067768877^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1949336207 10000000000 11899067768877 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (739185761/5000000000 : ℝ)^69 ≤ (1660283355721/20000000000000 : ℝ)^53 := by
    have hnat : (739185761 : ℕ)^69*20000000000000^53 ≤ 1660283355721^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      739185761 5000000000 1660283355721 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8408622063/10000000000 : ℝ)^69 ≤ (79799515440523/100000000000000 : ℝ)^53 := by
    have hnat : (8408622063 : ℕ)^69*100000000000000^53 ≤ 79799515440523^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8408622063 10000000000 79799515440523 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1949336207/10000000000 : ℝ), (-739185761/5000000000 : ℝ), (-8408622063/10000000000 : ℝ)] ![(11899067768877/100000000000000 : ℝ), (1660283355721/20000000000000 : ℝ), (79799515440523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1949336207/10000000000 : ℝ)|^69 ≤ (11899067768877/100000000000000 : ℝ)^53
        have hw : |(1949336207/10000000000 : ℝ)|=(1949336207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-739185761/5000000000 : ℝ)|^69 ≤ (1660283355721/20000000000000 : ℝ)^53
        have hw : |(-739185761/5000000000 : ℝ)|=(739185761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8408622063/10000000000 : ℝ)|^69 ≤ (79799515440523/100000000000000 : ℝ)^53
        have hw : |(-8408622063/10000000000 : ℝ)|=(8408622063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308062_s1_s1_16 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5866477/8000000 : ℝ)*x 0 + (376355947/1250000000 : ℝ)*x 1 + (1995594091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5866477/8000000 : ℝ)^69 ≤ (66775850193429/100000000000000 : ℝ)^53 := by
    have hnat : (5866477 : ℕ)^69*100000000000000^53 ≤ 66775850193429^53*8000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5866477 8000000 66775850193429 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (376355947/1250000000 : ℝ)^69 ≤ (5239041076033/25000000000000 : ℝ)^53 := by
    have hnat : (376355947 : ℕ)^69*25000000000000^53 ≤ 5239041076033^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      376355947 1250000000 5239041076033 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1995594091/10000000000 : ℝ)^69 ≤ (12267985489619/100000000000000 : ℝ)^53 := by
    have hnat : (1995594091 : ℕ)^69*100000000000000^53 ≤ 12267985489619^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1995594091 10000000000 12267985489619 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5866477/8000000 : ℝ), (376355947/1250000000 : ℝ), (1995594091/10000000000 : ℝ)] ![(66775850193429/100000000000000 : ℝ), (5239041076033/25000000000000 : ℝ), (12267985489619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5866477/8000000 : ℝ)|^69 ≤ (66775850193429/100000000000000 : ℝ)^53
        have hw : |(5866477/8000000 : ℝ)|=(5866477/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(376355947/1250000000 : ℝ)|^69 ≤ (5239041076033/25000000000000 : ℝ)^53
        have hw : |(376355947/1250000000 : ℝ)|=(376355947/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1995594091/10000000000 : ℝ)|^69 ≤ (12267985489619/100000000000000 : ℝ)^53
        have hw : |(1995594091/10000000000 : ℝ)|=(1995594091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308062_s1_s1_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (804433463/1000000000 : ℝ)*x 0 + (341300419/1000000000 : ℝ)*x 1 + (3219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (804433463/1000000000 : ℝ)^69 ≤ (75328417890573/100000000000000 : ℝ)^53 := by
    have hnat : (804433463 : ℕ)^69*100000000000000^53 ≤ 75328417890573^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      804433463 1000000000 75328417890573 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (341300419/1000000000 : ℝ)^69 ≤ (24671581749279/100000000000000 : ℝ)^53 := by
    have hnat : (341300419 : ℕ)^69*100000000000000^53 ≤ 24671581749279^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341300419 1000000000 24671581749279 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3219/10000000000 : ℝ)^69 ≤ (353011/100000000000000 : ℝ)^53 := by
    have hnat : (3219 : ℕ)^69*100000000000000^53 ≤ 353011^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3219 10000000000 353011 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(804433463/1000000000 : ℝ), (341300419/1000000000 : ℝ), (3219/10000000000 : ℝ)] ![(75328417890573/100000000000000 : ℝ), (24671581749279/100000000000000 : ℝ), (353011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(804433463/1000000000 : ℝ)|^69 ≤ (75328417890573/100000000000000 : ℝ)^53
        have hw : |(804433463/1000000000 : ℝ)|=(804433463/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(341300419/1000000000 : ℝ)|^69 ≤ (24671581749279/100000000000000 : ℝ)^53
        have hw : |(341300419/1000000000 : ℝ)|=(341300419/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3219/10000000000 : ℝ)|^69 ≤ (353011/100000000000000 : ℝ)^53
        have hw : |(3219/10000000000 : ℝ)|=(3219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308062_s1_s1_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-66227121/2000000000 : ℝ)*x 0 + (7127268781/10000000000 : ℝ)*x 1 + (-4412689951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66227121/2000000000 : ℝ)^69 ≤ (1183627924649/100000000000000 : ℝ)^53 := by
    have hnat : (66227121 : ℕ)^69*100000000000000^53 ≤ 1183627924649^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66227121 2000000000 1183627924649 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7127268781/10000000000 : ℝ)^69 ≤ (64346151131181/100000000000000 : ℝ)^53 := by
    have hnat : (7127268781 : ℕ)^69*100000000000000^53 ≤ 64346151131181^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7127268781 10000000000 64346151131181 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4412689951/10000000000 : ℝ)^69 ≤ (34470220923039/100000000000000 : ℝ)^53 := by
    have hnat : (4412689951 : ℕ)^69*100000000000000^53 ≤ 34470220923039^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4412689951 10000000000 34470220923039 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-66227121/2000000000 : ℝ), (7127268781/10000000000 : ℝ), (-4412689951/10000000000 : ℝ)] ![(1183627924649/100000000000000 : ℝ), (64346151131181/100000000000000 : ℝ), (34470220923039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-66227121/2000000000 : ℝ)|^69 ≤ (1183627924649/100000000000000 : ℝ)^53
        have hw : |(-66227121/2000000000 : ℝ)|=(66227121/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7127268781/10000000000 : ℝ)|^69 ≤ (64346151131181/100000000000000 : ℝ)^53
        have hw : |(7127268781/10000000000 : ℝ)|=(7127268781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4412689951/10000000000 : ℝ)|^69 ≤ (34470220923039/100000000000000 : ℝ)^53
        have hw : |(-4412689951/10000000000 : ℝ)|=(4412689951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308062_s1_s1_22 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7320523587/10000000000 : ℝ)*x 0 + (-456575247/10000000000 : ℝ)*x 1 + (-4125126727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7320523587/10000000000 : ℝ)^69 ≤ (66626838591143/100000000000000 : ℝ)^53 := by
    have hnat : (7320523587 : ℕ)^69*100000000000000^53 ≤ 66626838591143^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7320523587 10000000000 66626838591143 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (456575247/10000000000 : ℝ)^69 ≤ (1798195264369/100000000000000 : ℝ)^53 := by
    have hnat : (456575247 : ℕ)^69*100000000000000^53 ≤ 1798195264369^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456575247 10000000000 1798195264369 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4125126727/10000000000 : ℝ)^69 ≤ (1973435383361/6250000000000 : ℝ)^53 := by
    have hnat : (4125126727 : ℕ)^69*6250000000000^53 ≤ 1973435383361^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4125126727 10000000000 1973435383361 6250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7320523587/10000000000 : ℝ), (-456575247/10000000000 : ℝ), (-4125126727/10000000000 : ℝ)] ![(66626838591143/100000000000000 : ℝ), (1798195264369/100000000000000 : ℝ), (1973435383361/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7320523587/10000000000 : ℝ)|^69 ≤ (66626838591143/100000000000000 : ℝ)^53
        have hw : |(7320523587/10000000000 : ℝ)|=(7320523587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-456575247/10000000000 : ℝ)|^69 ≤ (1798195264369/100000000000000 : ℝ)^53
        have hw : |(-456575247/10000000000 : ℝ)|=(456575247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4125126727/10000000000 : ℝ)|^69 ≤ (1973435383361/6250000000000 : ℝ)^53
        have hw : |(-4125126727/10000000000 : ℝ)|=(4125126727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308062_s1_s1_23 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2437335511/10000000000 : ℝ)*x 0 + (7622167159/10000000000 : ℝ)*x 1 + (219178969/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2437335511/10000000000 : ℝ)^69 ≤ (15915971297813/100000000000000 : ℝ)^53 := by
    have hnat : (2437335511 : ℕ)^69*100000000000000^53 ≤ 15915971297813^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2437335511 10000000000 15915971297813 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7622167159/10000000000 : ℝ)^69 ≤ (35111511081743/50000000000000 : ℝ)^53 := by
    have hnat : (7622167159 : ℕ)^69*50000000000000^53 ≤ 35111511081743^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7622167159 10000000000 35111511081743 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219178969/1000000000 : ℝ)^69 ≤ (13861006523869/100000000000000 : ℝ)^53 := by
    have hnat : (219178969 : ℕ)^69*100000000000000^53 ≤ 13861006523869^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219178969 1000000000 13861006523869 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2437335511/10000000000 : ℝ), (7622167159/10000000000 : ℝ), (219178969/1000000000 : ℝ)] ![(15915971297813/100000000000000 : ℝ), (35111511081743/50000000000000 : ℝ), (13861006523869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2437335511/10000000000 : ℝ)|^69 ≤ (15915971297813/100000000000000 : ℝ)^53
        have hw : |(2437335511/10000000000 : ℝ)|=(2437335511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7622167159/10000000000 : ℝ)|^69 ≤ (35111511081743/50000000000000 : ℝ)^53
        have hw : |(7622167159/10000000000 : ℝ)|=(7622167159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(219178969/1000000000 : ℝ)|^69 ≤ (13861006523869/100000000000000 : ℝ)^53
        have hw : |(219178969/1000000000 : ℝ)|=(219178969/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308062_s1_s1_27 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4220640753/5000000000 : ℝ)*x 0 + (573758997/2000000000 : ℝ)*x 1 + (-14132379/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4220640753/5000000000 : ℝ)^69 ≤ (80203264688013/100000000000000 : ℝ)^53 := by
    have hnat : (4220640753 : ℕ)^69*100000000000000^53 ≤ 80203264688013^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4220640753 5000000000 80203264688013 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (573758997/2000000000 : ℝ)^69 ≤ (1967823571563/10000000000000 : ℝ)^53 := by
    have hnat : (573758997 : ℕ)^69*10000000000000^53 ≤ 1967823571563^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      573758997 2000000000 1967823571563 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (14132379/2500000000 : ℝ)^69 ≤ (4739983703/4000000000000 : ℝ)^53 := by
    have hnat : (14132379 : ℕ)^69*4000000000000^53 ≤ 4739983703^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14132379 2500000000 4739983703 4000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4220640753/5000000000 : ℝ), (573758997/2000000000 : ℝ), (-14132379/2500000000 : ℝ)] ![(80203264688013/100000000000000 : ℝ), (1967823571563/10000000000000 : ℝ), (4739983703/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4220640753/5000000000 : ℝ)|^69 ≤ (80203264688013/100000000000000 : ℝ)^53
        have hw : |(4220640753/5000000000 : ℝ)|=(4220640753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(573758997/2000000000 : ℝ)|^69 ≤ (1967823571563/10000000000000 : ℝ)^53
        have hw : |(573758997/2000000000 : ℝ)|=(573758997/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-14132379/2500000000 : ℝ)|^69 ≤ (4739983703/4000000000000 : ℝ)^53
        have hw : |(-14132379/2500000000 : ℝ)|=(14132379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308062_s1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((93471/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(93471/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(92459/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(92459/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-20401/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-20401/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((8331/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8331/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(82979/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(82979/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-3409/5000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-3409/5000 : ℝ)*X 1 2) := by
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
  have main2 : (3861/5000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (3861/5000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (11517/6250 : ℝ) := by
    linarith only [f.Tcap]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 0 (by
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (92459/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(135578010159231/924590000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(485737352327773/4622950000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (20401/25000 : ℝ) ^ (17/4 : ℝ) ≤ (42147677712397511293/100000000000000000000 : ℝ) := by
    have hpowers : (20401/25000 : ℝ)^17 ≤ (42147677712397511293/100000000000000000000 : ℝ)^4 := by
      have hnat : (20401 : ℕ)^17*100000000000000000000^4 ≤ 42147677712397511293^4*25000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20401 25000 42147677712397511293 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20401/25000 : ℝ)) (X := (42147677712397511293/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (142147677712397511293/100000000000000000000 : ℝ) ≤ (10862724601264483/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (142147677712397511293/100000000000000000000 : ℝ)^4 ≤ (10862724601264483/10000000000000000 : ℝ)^17 := by
      have hnat : (142147677712397511293 : ℕ)^4*10000000000000000^17 ≤ 10862724601264483^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        142147677712397511293 100000000000000000000 10862724601264483 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10862724601264483/10000000000000000 : ℝ)) (X := (142147677712397511293/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (92147677712397511293/50000000000000000000 : ℝ) ≤ (11547127845847253/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (92147677712397511293/50000000000000000000 : ℝ)^4 ≤ (11547127845847253/10000000000000000 : ℝ)^17 := by
      have hnat : (92147677712397511293 : ℕ)^4*10000000000000000^17 ≤ 11547127845847253^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        92147677712397511293 50000000000000000000 11547127845847253 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11547127845847253/10000000000000000 : ℝ)) (X := (92147677712397511293/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(862724601264483/8160400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(68440324458277/816040000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (20401/25000 : ℝ)) (alpha := (862724601264483/8160400000000000 : ℝ)) (beta := (68440324458277/816040000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (20401/25000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(862724601264483/8160400000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(68440324458277/816040000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-184249139/2000000000 : ℝ)*X 0 0+(2538067453/5000000000 : ℝ)*X 0 1+(-624269199/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308062_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1019052813/2000000000 : ℝ)*X 1 0+(-114003233/1250000000 : ℝ)*X 1 1+(-6229873217/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308062_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-287516739/2000000000 : ℝ)*X 0 0+(1013078323/5000000000 : ℝ)*X 0 1+(-1676588007/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308062_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((303996167/1250000000 : ℝ)*X 1 0+(-122438731/1250000000 : ℝ)*X 1 1+(-8365908783/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308062_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((17412283/62500000 : ℝ)*X 2 0+(1880751991/2500000000 : ℝ)*X 2 1+(982404807/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308062_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((183455087/500000000 : ℝ)*X 0 0+(7843677783/10000000000 : ℝ)*X 0 1+(2547/2000000000 : ℝ)*X 0 2+(183455087/500000000 : ℝ)*X 1 0+(7843677783/10000000000 : ℝ)*X 1 1+(2547/2000000000 : ℝ)*X 1 2+(183455087/500000000 : ℝ)*X 2 0+(7843677783/10000000000 : ℝ)*X 2 1+(2547/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308062_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-509335433/5000000000 : ℝ)*X 0 0+(462838023/2000000000 : ℝ)*X 0 1+(-8425739991/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308062_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((1949336207/10000000000 : ℝ)*X 1 0+(-739185761/5000000000 : ℝ)*X 1 1+(-8408622063/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308062_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((5866477/8000000 : ℝ)*X 2 0+(376355947/1250000000 : ℝ)*X 2 1+(1995594091/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308062_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((804433463/1000000000 : ℝ)*X 0 0+(341300419/1000000000 : ℝ)*X 0 1+(3219/10000000000 : ℝ)*X 0 2+(804433463/1000000000 : ℝ)*X 1 0+(341300419/1000000000 : ℝ)*X 1 1+(3219/10000000000 : ℝ)*X 1 2+(804433463/1000000000 : ℝ)*X 2 0+(341300419/1000000000 : ℝ)*X 2 1+(3219/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308062_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-66227121/2000000000 : ℝ)*X 0 0+(7127268781/10000000000 : ℝ)*X 0 1+(-4412689951/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308062_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((7320523587/10000000000 : ℝ)*X 1 0+(-456575247/10000000000 : ℝ)*X 1 1+(-4125126727/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308062_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((2437335511/10000000000 : ℝ)*X 2 0+(7622167159/10000000000 : ℝ)*X 2 1+(219178969/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308062_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((4220640753/5000000000 : ℝ)*X 0 0+(573758997/2000000000 : ℝ)*X 0 1+(-14132379/2500000000 : ℝ)*X 0 2+(4220640753/5000000000 : ℝ)*X 1 0+(573758997/2000000000 : ℝ)*X 1 1+(-14132379/2500000000 : ℝ)*X 1 2+(4220640753/5000000000 : ℝ)*X 2 0+(573758997/2000000000 : ℝ)*X 2 1+(-14132379/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308062_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((8331/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8331/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3129443757534451566349797159/377251211800000000000000000000000 : ℝ) := by norm_num
    linear_combination (10606012227/500000000000 : ℝ)*(base5) + (453348454213/500000000000 : ℝ)*(base7) + (32987/1000000000000 : ℝ)*(base60) + (1892261174531/1000000000000 : ℝ)*(major_s1_0) + (1892261174531/1000000000000 : ℝ)*(major_s1_1) + (1892261174531/1000000000000 : ℝ)*(major_s1_2) + (1297459/1000000000000 : ℝ)*(sp_s1_1) + (2020103704099/1000000000000 : ℝ)*(sp_s1_7) + (505011074723/250000000000 : ℝ)*(sp_s1_8) + (2041279464941/1000000000000 : ℝ)*(sp_s1_9) + (104648473657/50000000000 : ℝ)*(sp_s1_13) + (13919/7812500000 : ℝ)*(sp_s1_14) + (2994469/50000000000 : ℝ)*(sp_s1_15) + (9511311/250000000000 : ℝ)*(sp_s1_23) + (75467786823/62500000000 : ℝ)*(f.failure) + (2020105485731/1000000000000 : ℝ)*(f.sum) + (234513027950238073667/754502423600000000000000000000000 : ℝ)*base63 + (292837640983671/816040000000000000000000000 : ℝ)*base65 + (873386494783911/2311475000000000000000000000 : ℝ)*base66 + (6323791106698193/8160400000000000000000000000 : ℝ)*base69 + (856250617606886869/54482910600000000000000000000000 : ℝ)*base70 + (423729337609199/1335300000000000000000000000 : ℝ)*base72 + (96212428963597/184918000000000000000000000 : ℝ)*base75 + (169578937739857/333825000000000000000000000 : ℝ)*base77 + (10484590956172508027/123460502700000000000000000000000 : ℝ)*base79 + (403/6250000000000000 : ℝ)*base87 + (403/6250000000000000 : ℝ)*base89 + (403/6250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(82979/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(82979/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7213490738515093147903964301/377251211800000000000000000000000 : ℝ) := by norm_num
    linear_combination (56063/1000000000000 : ℝ)*(base5) + (906842126827/1000000000000 : ℝ)*(base7) + (6695690663/500000000000 : ℝ)*(base60) + (1858332292161/1000000000000 : ℝ)*(major_s1_0) + (1858332292161/1000000000000 : ℝ)*(major_s1_1) + (1858332292161/1000000000000 : ℝ)*(major_s1_2) + (2246707/500000000000 : ℝ)*(sp_s1_0) + (2172677/1000000000000 : ℝ)*(sp_s1_1) + (694503/5000000000 : ℝ)*(sp_s1_8) + (493450256697/250000000000 : ℝ)*(sp_s1_14) + (986832223463/500000000000 : ℝ)*(sp_s1_15) + (986902788133/500000000000 : ℝ)*(sp_s1_16) + (418529693621/200000000000 : ℝ)*(sp_s1_20) + (1379253/50000000000 : ℝ)*(sp_s1_27) + (592916991201/500000000000 : ℝ)*(f.failure) + (986902760101/500000000000 : ℝ)*(f.sum) + (133493259078774425063/754502423600000000000000000000000 : ℝ)*base62 + (116930257965181/816040000000000000000000000 : ℝ)*base65 + (25596598067793/288934375000000000000000000 : ℝ)*base67 + (4324299064926117/8160400000000000000000000000 : ℝ)*base68 + (32532858719786123229/127126791400000000000000000000000 : ℝ)*base71 + (2579993329729149/3115700000000000000000000000 : ℝ)*base73 + (433332750697399/924590000000000000000000000 : ℝ)*base74 + (17821337340127/48682812500000000000000000 : ℝ)*base76 + (37327242619153895757/288074506300000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (49911/50000000000000000 : ℝ)*base87 + (49911/50000000000000000 : ℝ)*base89 + (49911/50000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-3409/5000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-3409/5000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1475996299488684051349069323/377251211800000000000000000000000 : ℝ) := by norm_num
    linear_combination (67886883181/100000000000 : ℝ)*(base7) + (44529763051/1000000000000 : ℝ)*(base39) + (12968725797/1000000000000 : ℝ)*(base43) + (450283/1000000000000 : ℝ)*(base50) + (10118059627/500000000000 : ℝ)*(base59) + (1703195403303/1000000000000 : ℝ)*(major_s1_0) + (1690226677507/1000000000000 : ℝ)*(major_s1_1) + (1703195403303/1000000000000 : ℝ)*(major_s1_2) + (2186883/250000000000 : ℝ)*(sp_s1_0) + (8494113/100000000000 : ℝ)*(sp_s1_9) + (1889585187903/1000000000000 : ℝ)*(sp_s1_21) + (118910166327/62500000000 : ℝ)*(sp_s1_22) + (377901798861/200000000000 : ℝ)*(sp_s1_23) + (882853640881/500000000000 : ℝ)*(sp_s1_27) + (33963701561/31250000000 : ℝ)*(f.failure) + (118910166327/62500000000 : ℝ)*(f.sum) + (144335318083667162249/754502423600000000000000000000000 : ℝ)*base62 + (119350852713711/816040000000000000000000000 : ℝ)*base65 + (659297057873143/2311475000000000000000000000 : ℝ)*base67 + (9133179941018891/8160400000000000000000000000 : ℝ)*base68 + (6535450187368712427/127126791400000000000000000000000 : ℝ)*base71 + (2134195809139427/3115700000000000000000000000 : ℝ)*base73 + (142427958615619/231147500000000000000000000 : ℝ)*base74 + (74972636783467/1557850000000000000000000000 : ℝ)*base76 + (32512531633122705373/288074506300000000000000000000000 : ℝ)*base78 + (999/781250000000000 : ℝ)*base87 + (871/3125000000000000 : ℝ)*base89 + (999/781250000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((93471/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(93471/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(92459/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(92459/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-20401/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-20401/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((8331/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8331/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(82979/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(82979/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-3409/5000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-3409/5000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c308062_s1 p hpa hpb X hX hprev0

#print axioms solution
