-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301063_s4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:40:58.373659+00:00
-- url     : https://prove2.me/submissions/b8655444-f31b-4a4c-81b9-75a7c2a09c35

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
theorem collision_support_c301063_s4_s4_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-39301851/500000000 : ℝ)*x 0 + (1414898419/2500000000 : ℝ)*x 1 + (5892434757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (39301851/500000000 : ℝ)^65 ≤ (3425873535807/100000000000000 : ℝ)^49 := by
    have hnat : (39301851 : ℕ)^65*100000000000000^49 ≤ 3425873535807^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39301851 500000000 3425873535807 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1414898419/2500000000 : ℝ)^65 ≤ (46996127116397/100000000000000 : ℝ)^49 := by
    have hnat : (1414898419 : ℕ)^65*100000000000000^49 ≤ 46996127116397^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1414898419 2500000000 46996127116397 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5892434757/10000000000 : ℝ)^65 ≤ (12394499832943/25000000000000 : ℝ)^49 := by
    have hnat : (5892434757 : ℕ)^65*25000000000000^49 ≤ 12394499832943^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5892434757 10000000000 12394499832943 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-39301851/500000000 : ℝ), (1414898419/2500000000 : ℝ), (5892434757/10000000000 : ℝ)] ![(3425873535807/100000000000000 : ℝ), (46996127116397/100000000000000 : ℝ), (12394499832943/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-39301851/500000000 : ℝ)|^65 ≤ (3425873535807/100000000000000 : ℝ)^49
        have hw : |(-39301851/500000000 : ℝ)|=(39301851/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1414898419/2500000000 : ℝ)|^65 ≤ (46996127116397/100000000000000 : ℝ)^49
        have hw : |(1414898419/2500000000 : ℝ)|=(1414898419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5892434757/10000000000 : ℝ)|^65 ≤ (12394499832943/25000000000000 : ℝ)^49
        have hw : |(5892434757/10000000000 : ℝ)|=(5892434757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s4_s4_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2829872093/5000000000 : ℝ)*x 0 + (-789010651/10000000000 : ℝ)*x 1 + (5890744829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2829872093/5000000000 : ℝ)^65 ≤ (46997785027863/100000000000000 : ℝ)^49 := by
    have hnat : (2829872093 : ℕ)^65*100000000000000^49 ≤ 46997785027863^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2829872093 5000000000 46997785027863 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (789010651/10000000000 : ℝ)^65 ≤ (3443076393947/100000000000000 : ℝ)^49 := by
    have hnat : (789010651 : ℕ)^65*100000000000000^49 ≤ 3443076393947^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      789010651 10000000000 3443076393947 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5890744829/10000000000 : ℝ)^65 ≤ (49559138564513/100000000000000 : ℝ)^49 := by
    have hnat : (5890744829 : ℕ)^65*100000000000000^49 ≤ 49559138564513^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5890744829 10000000000 49559138564513 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2829872093/5000000000 : ℝ), (-789010651/10000000000 : ℝ), (5890744829/10000000000 : ℝ)] ![(46997785027863/100000000000000 : ℝ), (3443076393947/100000000000000 : ℝ), (49559138564513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2829872093/5000000000 : ℝ)|^65 ≤ (46997785027863/100000000000000 : ℝ)^49
        have hw : |(2829872093/5000000000 : ℝ)|=(2829872093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-789010651/10000000000 : ℝ)|^65 ≤ (3443076393947/100000000000000 : ℝ)^49
        have hw : |(-789010651/10000000000 : ℝ)|=(789010651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5890744829/10000000000 : ℝ)|^65 ≤ (49559138564513/100000000000000 : ℝ)^49
        have hw : |(5890744829/10000000000 : ℝ)|=(5890744829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s4_s4_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5735685493/10000000000 : ℝ)*x 0 + (2928417521/5000000000 : ℝ)*x 1 + (-708113209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5735685493/10000000000 : ℝ)^65 ≤ (47836131305289/100000000000000 : ℝ)^49 := by
    have hnat : (5735685493 : ℕ)^65*100000000000000^49 ≤ 47836131305289^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5735685493 10000000000 47836131305289 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2928417521/5000000000 : ℝ)^65 ≤ (1967242228059/4000000000000 : ℝ)^49 := by
    have hnat : (2928417521 : ℕ)^65*4000000000000^49 ≤ 1967242228059^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2928417521 5000000000 1967242228059 4000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (708113209/10000000000 : ℝ)^65 ≤ (1491406492113/50000000000000 : ℝ)^49 := by
    have hnat : (708113209 : ℕ)^65*50000000000000^49 ≤ 1491406492113^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      708113209 10000000000 1491406492113 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5735685493/10000000000 : ℝ), (2928417521/5000000000 : ℝ), (-708113209/10000000000 : ℝ)] ![(47836131305289/100000000000000 : ℝ), (1967242228059/4000000000000 : ℝ), (1491406492113/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5735685493/10000000000 : ℝ)|^65 ≤ (47836131305289/100000000000000 : ℝ)^49
        have hw : |(5735685493/10000000000 : ℝ)|=(5735685493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2928417521/5000000000 : ℝ)|^65 ≤ (1967242228059/4000000000000 : ℝ)^49
        have hw : |(2928417521/5000000000 : ℝ)|=(2928417521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-708113209/10000000000 : ℝ)|^65 ≤ (1491406492113/50000000000000 : ℝ)^49
        have hw : |(-708113209/10000000000 : ℝ)|=(708113209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s4_s4_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4661708511/10000000000 : ℝ)*x 0 + (551010813/1250000000 : ℝ)*x 1 + (805562371/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4661708511/10000000000 : ℝ)^65 ≤ (36334145212733/100000000000000 : ℝ)^49 := by
    have hnat : (4661708511 : ℕ)^65*100000000000000^49 ≤ 36334145212733^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4661708511 10000000000 36334145212733 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (551010813/1250000000 : ℝ)^65 ≤ (8433869704583/25000000000000 : ℝ)^49 := by
    have hnat : (551010813 : ℕ)^65*25000000000000^49 ≤ 8433869704583^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551010813 1250000000 8433869704583 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (805562371/2000000000 : ℝ)^65 ≤ (14965187976443/50000000000000 : ℝ)^49 := by
    have hnat : (805562371 : ℕ)^65*50000000000000^49 ≤ 14965187976443^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      805562371 2000000000 14965187976443 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4661708511/10000000000 : ℝ), (551010813/1250000000 : ℝ), (805562371/2000000000 : ℝ)] ![(36334145212733/100000000000000 : ℝ), (8433869704583/25000000000000 : ℝ), (14965187976443/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4661708511/10000000000 : ℝ)|^65 ≤ (36334145212733/100000000000000 : ℝ)^49
        have hw : |(4661708511/10000000000 : ℝ)|=(4661708511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(551010813/1250000000 : ℝ)|^65 ≤ (8433869704583/25000000000000 : ℝ)^49
        have hw : |(551010813/1250000000 : ℝ)|=(551010813/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(805562371/2000000000 : ℝ)|^65 ≤ (14965187976443/50000000000000 : ℝ)^49
        have hw : |(805562371/2000000000 : ℝ)|=(805562371/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s4_s4_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-505793251/5000000000 : ℝ)*x 0 + (3123788407/10000000000 : ℝ)*x 1 + (994627943/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (505793251/5000000000 : ℝ)^65 ≤ (1196867469747/25000000000000 : ℝ)^49 := by
    have hnat : (505793251 : ℕ)^65*25000000000000^49 ≤ 1196867469747^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505793251 5000000000 1196867469747 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3123788407/10000000000 : ℝ)^65 ≤ (21363858123291/100000000000000 : ℝ)^49 := by
    have hnat : (3123788407 : ℕ)^65*100000000000000^49 ≤ 21363858123291^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3123788407 10000000000 21363858123291 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (994627943/1250000000 : ℝ)^65 ≤ (36924335991303/50000000000000 : ℝ)^49 := by
    have hnat : (994627943 : ℕ)^65*50000000000000^49 ≤ 36924335991303^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      994627943 1250000000 36924335991303 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-505793251/5000000000 : ℝ), (3123788407/10000000000 : ℝ), (994627943/1250000000 : ℝ)] ![(1196867469747/25000000000000 : ℝ), (21363858123291/100000000000000 : ℝ), (36924335991303/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-505793251/5000000000 : ℝ)|^65 ≤ (1196867469747/25000000000000 : ℝ)^49
        have hw : |(-505793251/5000000000 : ℝ)|=(505793251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3123788407/10000000000 : ℝ)|^65 ≤ (21363858123291/100000000000000 : ℝ)^49
        have hw : |(3123788407/10000000000 : ℝ)|=(3123788407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(994627943/1250000000 : ℝ)|^65 ≤ (36924335991303/50000000000000 : ℝ)^49
        have hw : |(994627943/1250000000 : ℝ)|=(994627943/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s4_s4_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1787687899/5000000000 : ℝ)*x 0 + (-54313001/2500000000 : ℝ)*x 1 + (1988740407/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1787687899/5000000000 : ℝ)^65 ≤ (12777254943281/50000000000000 : ℝ)^49 := by
    have hnat : (1787687899 : ℕ)^65*50000000000000^49 ≤ 12777254943281^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1787687899 5000000000 12777254943281 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54313001/2500000000 : ℝ)^65 ≤ (311101112463/50000000000000 : ℝ)^49 := by
    have hnat : (54313001 : ℕ)^65*50000000000000^49 ≤ 311101112463^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54313001 2500000000 311101112463 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1988740407/2500000000 : ℝ)^65 ≤ (73823287874027/100000000000000 : ℝ)^49 := by
    have hnat : (1988740407 : ℕ)^65*100000000000000^49 ≤ 73823287874027^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1988740407 2500000000 73823287874027 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1787687899/5000000000 : ℝ), (-54313001/2500000000 : ℝ), (1988740407/2500000000 : ℝ)] ![(12777254943281/50000000000000 : ℝ), (311101112463/50000000000000 : ℝ), (73823287874027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1787687899/5000000000 : ℝ)|^65 ≤ (12777254943281/50000000000000 : ℝ)^49
        have hw : |(1787687899/5000000000 : ℝ)|=(1787687899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-54313001/2500000000 : ℝ)|^65 ≤ (311101112463/50000000000000 : ℝ)^49
        have hw : |(-54313001/2500000000 : ℝ)|=(54313001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1988740407/2500000000 : ℝ)|^65 ≤ (73823287874027/100000000000000 : ℝ)^49
        have hw : |(1988740407/2500000000 : ℝ)|=(1988740407/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s4_s4_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (432088467/1250000000 : ℝ)*x 0 + (8083244269/10000000000 : ℝ)*x 1 + (-7724037/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (432088467/1250000000 : ℝ)^65 ≤ (244355375853/1000000000000 : ℝ)^49 := by
    have hnat : (432088467 : ℕ)^65*1000000000000^49 ≤ 244355375853^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432088467 1250000000 244355375853 1000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8083244269/10000000000 : ℝ)^65 ≤ (18851660707469/25000000000000 : ℝ)^49 := by
    have hnat : (8083244269 : ℕ)^65*25000000000000^49 ≤ 18851660707469^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8083244269 10000000000 18851660707469 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7724037/1000000000 : ℝ)^65 ≤ (39454893473/25000000000000 : ℝ)^49 := by
    have hnat : (7724037 : ℕ)^65*25000000000000^49 ≤ 39454893473^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7724037 1000000000 39454893473 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(432088467/1250000000 : ℝ), (8083244269/10000000000 : ℝ), (-7724037/1000000000 : ℝ)] ![(244355375853/1000000000000 : ℝ), (18851660707469/25000000000000 : ℝ), (39454893473/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(432088467/1250000000 : ℝ)|^65 ≤ (244355375853/1000000000000 : ℝ)^49
        have hw : |(432088467/1250000000 : ℝ)|=(432088467/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8083244269/10000000000 : ℝ)|^65 ≤ (18851660707469/25000000000000 : ℝ)^49
        have hw : |(8083244269/10000000000 : ℝ)|=(8083244269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7724037/1000000000 : ℝ)|^65 ≤ (39454893473/25000000000000 : ℝ)^49
        have hw : |(-7724037/1000000000 : ℝ)|=(7724037/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s4_s4_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3521544731/10000000000 : ℝ)*x 0 + (3578271291/5000000000 : ℝ)*x 1 + (373455611/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3521544731/10000000000 : ℝ)^65 ≤ (12522692915671/50000000000000 : ℝ)^49 := by
    have hnat : (3521544731 : ℕ)^65*50000000000000^49 ≤ 12522692915671^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3521544731 10000000000 12522692915671 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3578271291/5000000000 : ℝ)^65 ≤ (3207963590227/5000000000000 : ℝ)^49 := by
    have hnat : (3578271291 : ℕ)^65*5000000000000^49 ≤ 3207963590227^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3578271291 5000000000 3207963590227 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (373455611/2000000000 : ℝ)^65 ≤ (5397671175467/50000000000000 : ℝ)^49 := by
    have hnat : (373455611 : ℕ)^65*50000000000000^49 ≤ 5397671175467^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      373455611 2000000000 5397671175467 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3521544731/10000000000 : ℝ), (3578271291/5000000000 : ℝ), (373455611/2000000000 : ℝ)] ![(12522692915671/50000000000000 : ℝ), (3207963590227/5000000000000 : ℝ), (5397671175467/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3521544731/10000000000 : ℝ)|^65 ≤ (12522692915671/50000000000000 : ℝ)^49
        have hw : |(3521544731/10000000000 : ℝ)|=(3521544731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3578271291/5000000000 : ℝ)|^65 ≤ (3207963590227/5000000000000 : ℝ)^49
        have hw : |(3578271291/5000000000 : ℝ)|=(3578271291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(373455611/2000000000 : ℝ)|^65 ≤ (5397671175467/50000000000000 : ℝ)^49
        have hw : |(373455611/2000000000 : ℝ)|=(373455611/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s4_s4_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-183167999/10000000000 : ℝ)*x 0 + (872863657/2500000000 : ℝ)*x 1 + (40147361/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (183167999/10000000000 : ℝ)^65 ≤ (49615436639/10000000000000 : ℝ)^49 := by
    have hnat : (183167999 : ℕ)^65*10000000000000^49 ≤ 49615436639^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183167999 10000000000 49615436639 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (872863657/2500000000 : ℝ)^65 ≤ (24761902177123/100000000000000 : ℝ)^49 := by
    have hnat : (872863657 : ℕ)^65*100000000000000^49 ≤ 24761902177123^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872863657 2500000000 24761902177123 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40147361/50000000 : ℝ)^65 ≤ (37370971718981/50000000000000 : ℝ)^49 := by
    have hnat : (40147361 : ℕ)^65*50000000000000^49 ≤ 37370971718981^49*50000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40147361 50000000 37370971718981 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-183167999/10000000000 : ℝ), (872863657/2500000000 : ℝ), (40147361/50000000 : ℝ)] ![(49615436639/10000000000000 : ℝ), (24761902177123/100000000000000 : ℝ), (37370971718981/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-183167999/10000000000 : ℝ)|^65 ≤ (49615436639/10000000000000 : ℝ)^49
        have hw : |(-183167999/10000000000 : ℝ)|=(183167999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(872863657/2500000000 : ℝ)|^65 ≤ (24761902177123/100000000000000 : ℝ)^49
        have hw : |(872863657/2500000000 : ℝ)|=(872863657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(40147361/50000000 : ℝ)|^65 ≤ (37370971718981/50000000000000 : ℝ)^49
        have hw : |(40147361/50000000 : ℝ)|=(40147361/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s4_s4_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (756055159/2500000000 : ℝ)*x 0 + (-1016539511/10000000000 : ℝ)*x 1 + (1605476189/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (756055159/2500000000 : ℝ)^65 ≤ (20465288519177/100000000000000 : ℝ)^49 := by
    have hnat : (756055159 : ℕ)^65*100000000000000^49 ≤ 20465288519177^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      756055159 2500000000 20465288519177 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1016539511/10000000000 : ℝ)^65 ≤ (4818589627241/100000000000000 : ℝ)^49 := by
    have hnat : (1016539511 : ℕ)^65*100000000000000^49 ≤ 4818589627241^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016539511 10000000000 4818589627241 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1605476189/2000000000 : ℝ)^65 ≤ (74716121835671/100000000000000 : ℝ)^49 := by
    have hnat : (1605476189 : ℕ)^65*100000000000000^49 ≤ 74716121835671^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1605476189 2000000000 74716121835671 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(756055159/2500000000 : ℝ), (-1016539511/10000000000 : ℝ), (1605476189/2000000000 : ℝ)] ![(20465288519177/100000000000000 : ℝ), (4818589627241/100000000000000 : ℝ), (74716121835671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(756055159/2500000000 : ℝ)|^65 ≤ (20465288519177/100000000000000 : ℝ)^49
        have hw : |(756055159/2500000000 : ℝ)|=(756055159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1016539511/10000000000 : ℝ)|^65 ≤ (4818589627241/100000000000000 : ℝ)^49
        have hw : |(-1016539511/10000000000 : ℝ)|=(1016539511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1605476189/2000000000 : ℝ)|^65 ≤ (74716121835671/100000000000000 : ℝ)^49
        have hw : |(1605476189/2000000000 : ℝ)|=(1605476189/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s4_s4_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3930392641/5000000000 : ℝ)*x 0 + (3734738407/10000000000 : ℝ)*x 1 + (-27927083/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3930392641/5000000000 : ℝ)^65 ≤ (36333092565369/50000000000000 : ℝ)^49 := by
    have hnat : (3930392641 : ℕ)^65*50000000000000^49 ≤ 36333092565369^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3930392641 5000000000 36333092565369 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3734738407/10000000000 : ℝ)^65 ≤ (5415269074421/20000000000000 : ℝ)^49 := by
    have hnat : (3734738407 : ℕ)^65*20000000000000^49 ≤ 5415269074421^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3734738407 10000000000 5415269074421 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (27927083/2500000000 : ℝ)^65 ≤ (32183684731/12500000000000 : ℝ)^49 := by
    have hnat : (27927083 : ℕ)^65*12500000000000^49 ≤ 32183684731^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27927083 2500000000 32183684731 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3930392641/5000000000 : ℝ), (3734738407/10000000000 : ℝ), (-27927083/2500000000 : ℝ)] ![(36333092565369/50000000000000 : ℝ), (5415269074421/20000000000000 : ℝ), (32183684731/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3930392641/5000000000 : ℝ)|^65 ≤ (36333092565369/50000000000000 : ℝ)^49
        have hw : |(3930392641/5000000000 : ℝ)|=(3930392641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3734738407/10000000000 : ℝ)|^65 ≤ (5415269074421/20000000000000 : ℝ)^49
        have hw : |(3734738407/10000000000 : ℝ)|=(3734738407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-27927083/2500000000 : ℝ)|^65 ≤ (32183684731/12500000000000 : ℝ)^49
        have hw : |(-27927083/2500000000 : ℝ)|=(27927083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s4_s4_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3775515449/5000000000 : ℝ)*x 0 + (1506869837/5000000000 : ℝ)*x 1 + (1859574911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3775515449/5000000000 : ℝ)^65 ≤ (68892437772069/100000000000000 : ℝ)^49 := by
    have hnat : (3775515449 : ℕ)^65*100000000000000^49 ≤ 68892437772069^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3775515449 5000000000 68892437772069 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1506869837/5000000000 : ℝ)^65 ≤ (20371256269457/100000000000000 : ℝ)^49 := by
    have hnat : (1506869837 : ℕ)^65*100000000000000^49 ≤ 20371256269457^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1506869837 5000000000 20371256269457 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1859574911/10000000000 : ℝ)^65 ≤ (10736305954321/100000000000000 : ℝ)^49 := by
    have hnat : (1859574911 : ℕ)^65*100000000000000^49 ≤ 10736305954321^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1859574911 10000000000 10736305954321 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3775515449/5000000000 : ℝ), (1506869837/5000000000 : ℝ), (1859574911/10000000000 : ℝ)] ![(68892437772069/100000000000000 : ℝ), (20371256269457/100000000000000 : ℝ), (10736305954321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3775515449/5000000000 : ℝ)|^65 ≤ (68892437772069/100000000000000 : ℝ)^49
        have hw : |(3775515449/5000000000 : ℝ)|=(3775515449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1506869837/5000000000 : ℝ)|^65 ≤ (20371256269457/100000000000000 : ℝ)^49
        have hw : |(1506869837/5000000000 : ℝ)|=(1506869837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1859574911/10000000000 : ℝ)|^65 ≤ (10736305954321/100000000000000 : ℝ)^49
        have hw : |(1859574911/10000000000 : ℝ)|=(1859574911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s4_s4_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-93336331/5000000000 : ℝ)*x 0 + (7281548697/10000000000 : ℝ)*x 1 + (2209242339/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (93336331/5000000000 : ℝ)^65 ≤ (508786582623/100000000000000 : ℝ)^49 := by
    have hnat : (93336331 : ℕ)^65*100000000000000^49 ≤ 508786582623^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93336331 5000000000 508786582623 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7281548697/10000000000 : ℝ)^65 ≤ (1641253277709/2500000000000 : ℝ)^49 := by
    have hnat : (7281548697 : ℕ)^65*2500000000000^49 ≤ 1641253277709^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7281548697 10000000000 1641253277709 2500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2209242339/5000000000 : ℝ)^65 ≤ (33841082306601/100000000000000 : ℝ)^49 := by
    have hnat : (2209242339 : ℕ)^65*100000000000000^49 ≤ 33841082306601^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209242339 5000000000 33841082306601 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-93336331/5000000000 : ℝ), (7281548697/10000000000 : ℝ), (2209242339/5000000000 : ℝ)] ![(508786582623/100000000000000 : ℝ), (1641253277709/2500000000000 : ℝ), (33841082306601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-93336331/5000000000 : ℝ)|^65 ≤ (508786582623/100000000000000 : ℝ)^49
        have hw : |(-93336331/5000000000 : ℝ)|=(93336331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7281548697/10000000000 : ℝ)|^65 ≤ (1641253277709/2500000000000 : ℝ)^49
        have hw : |(7281548697/10000000000 : ℝ)|=(7281548697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2209242339/5000000000 : ℝ)|^65 ≤ (33841082306601/100000000000000 : ℝ)^49
        have hw : |(2209242339/5000000000 : ℝ)|=(2209242339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s4_s4_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (195155921/250000000 : ℝ)*x 0 + (-104672561/10000000000 : ℝ)*x 1 + (761240819/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (195155921/250000000 : ℝ)^65 ≤ (17999509167273/25000000000000 : ℝ)^49 := by
    have hnat : (195155921 : ℕ)^65*25000000000000^49 ≤ 17999509167273^49*250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195155921 250000000 17999509167273 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104672561/10000000000 : ℝ)^65 ≤ (11809123449/5000000000000 : ℝ)^49 := by
    have hnat : (104672561 : ℕ)^65*5000000000000^49 ≤ 11809123449^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104672561 10000000000 11809123449 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (761240819/2000000000 : ℝ)^65 ≤ (2776578085757/10000000000000 : ℝ)^49 := by
    have hnat : (761240819 : ℕ)^65*10000000000000^49 ≤ 2776578085757^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      761240819 2000000000 2776578085757 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(195155921/250000000 : ℝ), (-104672561/10000000000 : ℝ), (761240819/2000000000 : ℝ)] ![(17999509167273/25000000000000 : ℝ), (11809123449/5000000000000 : ℝ), (2776578085757/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(195155921/250000000 : ℝ)|^65 ≤ (17999509167273/25000000000000 : ℝ)^49
        have hw : |(195155921/250000000 : ℝ)|=(195155921/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-104672561/10000000000 : ℝ)|^65 ≤ (11809123449/5000000000000 : ℝ)^49
        have hw : |(-104672561/10000000000 : ℝ)|=(104672561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(761240819/2000000000 : ℝ)|^65 ≤ (2776578085757/10000000000000 : ℝ)^49
        have hw : |(761240819/2000000000 : ℝ)|=(761240819/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s4_s4_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2942172619/10000000000 : ℝ)*x 0 + (2034077933/2500000000 : ℝ)*x 1 + (-73373/800000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2942172619/10000000000 : ℝ)^65 ≤ (4933010543081/25000000000000 : ℝ)^49 := by
    have hnat : (2942172619 : ℕ)^65*25000000000000^49 ≤ 4933010543081^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2942172619 10000000000 4933010543081 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2034077933/2500000000 : ℝ)^65 ≤ (76064049451173/100000000000000 : ℝ)^49 := by
    have hnat : (2034077933 : ℕ)^65*100000000000000^49 ≤ 76064049451173^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2034077933 2500000000 76064049451173 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (73373/800000 : ℝ)^65 ≤ (2101954183427/50000000000000 : ℝ)^49 := by
    have hnat : (73373 : ℕ)^65*50000000000000^49 ≤ 2101954183427^49*800000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73373 800000 2101954183427 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2942172619/10000000000 : ℝ), (2034077933/2500000000 : ℝ), (-73373/800000 : ℝ)] ![(4933010543081/25000000000000 : ℝ), (76064049451173/100000000000000 : ℝ), (2101954183427/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2942172619/10000000000 : ℝ)|^65 ≤ (4933010543081/25000000000000 : ℝ)^49
        have hw : |(2942172619/10000000000 : ℝ)|=(2942172619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2034077933/2500000000 : ℝ)|^65 ≤ (76064049451173/100000000000000 : ℝ)^49
        have hw : |(2034077933/2500000000 : ℝ)|=(2034077933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-73373/800000 : ℝ)|^65 ≤ (2101954183427/50000000000000 : ℝ)^49
        have hw : |(-73373/800000 : ℝ)|=(73373/800000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s4_s4_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (769032187/1000000000 : ℝ)*x 0 + (2647264021/10000000000 : ℝ)*x 1 + (513948007/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (769032187/1000000000 : ℝ)^65 ≤ (705832920779/1000000000000 : ℝ)^49 := by
    have hnat : (769032187 : ℕ)^65*1000000000000^49 ≤ 705832920779^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      769032187 1000000000 705832920779 1000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2647264021/10000000000 : ℝ)^65 ≤ (8576160429283/50000000000000 : ℝ)^49 := by
    have hnat : (2647264021 : ℕ)^65*50000000000000^49 ≤ 8576160429283^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647264021 10000000000 8576160429283 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (513948007/2500000000 : ℝ)^65 ≤ (12264387048587/100000000000000 : ℝ)^49 := by
    have hnat : (513948007 : ℕ)^65*100000000000000^49 ≤ 12264387048587^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513948007 2500000000 12264387048587 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(769032187/1000000000 : ℝ), (2647264021/10000000000 : ℝ), (513948007/2500000000 : ℝ)] ![(705832920779/1000000000000 : ℝ), (8576160429283/50000000000000 : ℝ), (12264387048587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(769032187/1000000000 : ℝ)|^65 ≤ (705832920779/1000000000000 : ℝ)^49
        have hw : |(769032187/1000000000 : ℝ)|=(769032187/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2647264021/10000000000 : ℝ)|^65 ≤ (8576160429283/50000000000000 : ℝ)^49
        have hw : |(2647264021/10000000000 : ℝ)|=(2647264021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(513948007/2500000000 : ℝ)|^65 ≤ (12264387048587/100000000000000 : ℝ)^49
        have hw : |(513948007/2500000000 : ℝ)|=(513948007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301063_s4 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev3 : (0 : ℝ) ≤ ((7933/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7933/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79441/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(79441/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19097/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19097/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2259/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2259/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18163/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(18163/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(69771/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(69771/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (92391/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  rcases hprev3 with ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩
  have s4_pow0 : (7933/10000 : ℝ) ^ (129/32 : ℝ) ≤ (9829858047752935787/25000000000000000000 : ℝ) := by
    have hpowers : (7933/10000 : ℝ)^129 ≤ (9829858047752935787/25000000000000000000 : ℝ)^32 := by
      have hnat : (7933 : ℕ)^129*25000000000000000000^32 ≤ 9829858047752935787^32*10000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7933 10000 9829858047752935787 25000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7933/10000 : ℝ)) (X := (9829858047752935787/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s4_corner0a : (34829858047752935787/25000000000000000000 : ℝ) ≤ (2714337459019203/2500000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (34829858047752935787/25000000000000000000 : ℝ)^32 ≤ (2714337459019203/2500000000000000 : ℝ)^129 := by
      have hnat : (34829858047752935787 : ℕ)^32*2500000000000000^129 ≤ 2714337459019203^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        34829858047752935787 25000000000000000000 2714337459019203 2500000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2714337459019203/2500000000000000 : ℝ)) (X := (34829858047752935787/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s4_corner0b : (22329858047752935787/12500000000000000000 : ℝ) ≤ (2309594078982251/2000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (22329858047752935787/12500000000000000000 : ℝ)^32 ≤ (2309594078982251/2000000000000000 : ℝ)^129 := by
      have hnat : (22329858047752935787 : ℕ)^32*2000000000000000^129 ≤ 2309594078982251^129*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22329858047752935787 12500000000000000000 2309594078982251 2000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2309594078982251/2000000000000000 : ℝ)) (X := (22329858047752935787/12500000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s4_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(214337459019203/1983250000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(690620558834443/7933000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (7933/10000 : ℝ)) (alpha := (214337459019203/1983250000000000 : ℝ)) (beta := (690620558834443/7933000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow0,s4_corner0a]) (by linarith only [s4_pow0,s4_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (7933/10000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(214337459019203/1983250000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(690620558834443/7933000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow1 : (79441/100000 : ℝ) ^ (129/32 : ℝ) ≤ (7908337627975397727/20000000000000000000 : ℝ) := by
    have hpowers : (79441/100000 : ℝ)^129 ≤ (7908337627975397727/20000000000000000000 : ℝ)^32 := by
      have hnat : (79441 : ℕ)^129*20000000000000000000^32 ≤ 7908337627975397727^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        79441 100000 7908337627975397727 20000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (79441/100000 : ℝ)) (X := (7908337627975397727/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s4_corner1a : (27908337627975397727/20000000000000000000 : ℝ) ≤ (5430821935044187/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (27908337627975397727/20000000000000000000 : ℝ)^32 ≤ (5430821935044187/5000000000000000 : ℝ)^129 := by
      have hnat : (27908337627975397727 : ℕ)^32*5000000000000000^129 ≤ 5430821935044187^129*20000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27908337627975397727 20000000000000000000 5430821935044187 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5430821935044187/5000000000000000 : ℝ)) (X := (27908337627975397727/20000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s4_corner1b : (17908337627975397727/10000000000000000000 : ℝ) ≤ (11555091829227009/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (17908337627975397727/10000000000000000000 : ℝ)^32 ≤ (11555091829227009/10000000000000000 : ℝ)^129 := by
      have hnat : (17908337627975397727 : ℕ)^32*10000000000000000^129 ≤ 11555091829227009^129*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17908337627975397727 10000000000000000000 11555091829227009 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11555091829227009/10000000000000000 : ℝ)) (X := (17908337627975397727/10000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s4_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(430821935044187/3972050000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(138689591827727/1588820000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (79441/100000 : ℝ)) (alpha := (430821935044187/3972050000000000 : ℝ)) (beta := (138689591827727/1588820000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow1,s4_corner1a]) (by linarith only [s4_pow1,s4_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (79441/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(430821935044187/3972050000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(138689591827727/1588820000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow2 : (19097/25000 : ℝ) ^ (129/32 : ℝ) ≤ (8440828997097593667/25000000000000000000 : ℝ) := by
    have hpowers : (19097/25000 : ℝ)^129 ≤ (8440828997097593667/25000000000000000000 : ℝ)^32 := by
      have hnat : (19097 : ℕ)^129*25000000000000000000^32 ≤ 8440828997097593667^32*25000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19097 25000 8440828997097593667 25000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19097/25000 : ℝ)) (X := (8440828997097593667/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s4_corner2a : (33440828997097593667/25000000000000000000 : ℝ) ≤ (1074829103353793/1000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (33440828997097593667/25000000000000000000 : ℝ)^32 ≤ (1074829103353793/1000000000000000 : ℝ)^129 := by
      have hnat : (33440828997097593667 : ℕ)^32*1000000000000000^129 ≤ 1074829103353793^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33440828997097593667 25000000000000000000 1074829103353793 1000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1074829103353793/1000000000000000 : ℝ)) (X := (33440828997097593667/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s4_corner2b : (20940828997097593667/12500000000000000000 : ℝ) ≤ (11365451506800959/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (20940828997097593667/12500000000000000000 : ℝ)^32 ≤ (11365451506800959/10000000000000000 : ℝ)^129 := by
      have hnat : (20940828997097593667 : ℕ)^32*10000000000000000^129 ≤ 11365451506800959^129*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20940828997097593667 12500000000000000000 11365451506800959 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11365451506800959/10000000000000000 : ℝ)) (X := (20940828997097593667/12500000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s4_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(74829103353793/763880000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(617160473263029/7638800000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (19097/25000 : ℝ)) (alpha := (74829103353793/763880000000000 : ℝ)) (beta := (617160473263029/7638800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow2,s4_corner2a]) (by linarith only [s4_pow2,s4_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (19097/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(74829103353793/763880000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(617160473263029/7638800000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s4_0 : ((-39301851/500000000 : ℝ)*X 0 0+(1414898419/2500000000 : ℝ)*X 0 1+(5892434757/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s4_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_1 : ((2829872093/5000000000 : ℝ)*X 1 0+(-789010651/10000000000 : ℝ)*X 1 1+(5890744829/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s4_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_2 : ((5735685493/10000000000 : ℝ)*X 2 0+(2928417521/5000000000 : ℝ)*X 2 1+(-708113209/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s4_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_6 : ((4661708511/10000000000 : ℝ)*X 0 0+(551010813/1250000000 : ℝ)*X 0 1+(805562371/2000000000 : ℝ)*X 0 2+(4661708511/10000000000 : ℝ)*X 1 0+(551010813/1250000000 : ℝ)*X 1 1+(805562371/2000000000 : ℝ)*X 1 2+(4661708511/10000000000 : ℝ)*X 2 0+(551010813/1250000000 : ℝ)*X 2 1+(805562371/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s4_s4_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_7 : ((-505793251/5000000000 : ℝ)*X 0 0+(3123788407/10000000000 : ℝ)*X 0 1+(994627943/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s4_s4_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_8 : ((1787687899/5000000000 : ℝ)*X 1 0+(-54313001/2500000000 : ℝ)*X 1 1+(1988740407/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s4_s4_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_9 : ((432088467/1250000000 : ℝ)*X 2 0+(8083244269/10000000000 : ℝ)*X 2 1+(-7724037/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s4_s4_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_13 : ((3521544731/10000000000 : ℝ)*X 0 0+(3578271291/5000000000 : ℝ)*X 0 1+(373455611/2000000000 : ℝ)*X 0 2+(3521544731/10000000000 : ℝ)*X 1 0+(3578271291/5000000000 : ℝ)*X 1 1+(373455611/2000000000 : ℝ)*X 1 2+(3521544731/10000000000 : ℝ)*X 2 0+(3578271291/5000000000 : ℝ)*X 2 1+(373455611/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s4_s4_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_14 : ((-183167999/10000000000 : ℝ)*X 0 0+(872863657/2500000000 : ℝ)*X 0 1+(40147361/50000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s4_s4_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_15 : ((756055159/2500000000 : ℝ)*X 1 0+(-1016539511/10000000000 : ℝ)*X 1 1+(1605476189/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s4_s4_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_16 : ((3930392641/5000000000 : ℝ)*X 2 0+(3734738407/10000000000 : ℝ)*X 2 1+(-27927083/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s4_s4_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_20 : ((3775515449/5000000000 : ℝ)*X 0 0+(1506869837/5000000000 : ℝ)*X 0 1+(1859574911/10000000000 : ℝ)*X 0 2+(3775515449/5000000000 : ℝ)*X 1 0+(1506869837/5000000000 : ℝ)*X 1 1+(1859574911/10000000000 : ℝ)*X 1 2+(3775515449/5000000000 : ℝ)*X 2 0+(1506869837/5000000000 : ℝ)*X 2 1+(1859574911/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s4_s4_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_21 : ((-93336331/5000000000 : ℝ)*X 0 0+(7281548697/10000000000 : ℝ)*X 0 1+(2209242339/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s4_s4_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_22 : ((195155921/250000000 : ℝ)*X 1 0+(-104672561/10000000000 : ℝ)*X 1 1+(761240819/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s4_s4_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_23 : ((2942172619/10000000000 : ℝ)*X 2 0+(2034077933/2500000000 : ℝ)*X 2 1+(-73373/800000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s4_s4_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_27 : ((769032187/1000000000 : ℝ)*X 0 0+(2647264021/10000000000 : ℝ)*X 0 1+(513948007/2500000000 : ℝ)*X 0 2+(769032187/1000000000 : ℝ)*X 1 0+(2647264021/10000000000 : ℝ)*X 1 1+(513948007/2500000000 : ℝ)*X 1 2+(769032187/1000000000 : ℝ)*X 2 0+(2647264021/10000000000 : ℝ)*X 2 1+(513948007/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s4_s4_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s4_0 : (0 : ℝ) ≤ ((2259/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2259/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (251670738624013767145205403/37927119425000000000000000000000 : ℝ) := by norm_num
    linear_combination (594750657631/1000000000000 : ℝ)*(base7) + (782283/1000000000000 : ℝ)*(base50) + (1170699303/25000000000 : ℝ)*(base60) + (488016283631/250000000000 : ℝ)*(major_s4_0) + (488016283631/250000000000 : ℝ)*(major_s4_1) + (488016283631/250000000000 : ℝ)*(major_s4_2) + (338529/62500000000 : ℝ)*(sp_s4_0) + (186867/250000000000 : ℝ)*(sp_s4_6) + (1109056157939/500000000000 : ℝ)*(sp_s4_7) + (277269594387/125000000000 : ℝ)*(sp_s4_8) + (221815671227/100000000000 : ℝ)*(sp_s4_9) + (1914390492167/1000000000000 : ℝ)*(sp_s4_13) + (7804551/200000000000 : ℝ)*(sp_s4_14) + (21413/500000000000 : ℝ)*(sp_s4_23) + (329910145501/250000000000 : ℝ)*(f.failure) + (277269594387/125000000000 : ℝ)*(f.sum) + (38346750454971746911/75854238850000000000000000000000 : ℝ)*base63 + (665925543221221/1909700000000000000000000000 : ℝ)*base64 + (338204479321931/794410000000000000000000000 : ℝ)*base66 + (59415522209291/95485000000000000000000000 : ℝ)*base69 + (18753841085060730097/75748250500000000000000000000000 : ℝ)*base70 + (226195547882327/495812500000000000000000000 : ℝ)*base73 + (1752960428359993/3972050000000000000000000000 : ℝ)*base75 + (197592894890943/495812500000000000000000000 : ℝ)*base77 + (4391380368147529011/78775681625000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (2519/6250000000000000 : ℝ)*base86 + (2519/6250000000000000 : ℝ)*base88 + (2519/6250000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s4_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18163/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(18163/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (21401265333331812361039119331509/1504379191992625000000000000000000000 : ℝ) := by norm_num
    linear_combination (309200626497/500000000000 : ℝ)*(base7) + (157561/1000000000000 : ℝ)*(base24) + (1843/40000000000 : ℝ)*(base49) + (470047909713/250000000000 : ℝ)*(major_s4_0) + (470047909713/250000000000 : ℝ)*(major_s4_1) + (470047909713/250000000000 : ℝ)*(major_s4_2) + (96233/1000000000000 : ℝ)*(sp_s4_2) + (89085553/1000000000000 : ℝ)*(sp_s4_8) + (1054212549399/500000000000 : ℝ)*(sp_s4_14) + (210833892379/100000000000 : ℝ)*(sp_s4_15) + (527106938887/250000000000 : ℝ)*(sp_s4_16) + (1889354247111/1000000000000 : ℝ)*(sp_s4_20) + (582109/200000000000 : ℝ)*(sp_s4_21) + (99464479/1000000000000 : ℝ)*(sp_s4_27) + (254210491719/200000000000 : ℝ)*(f.failure) + (2108428009343/1000000000000 : ℝ)*(f.sum) + (37259151613325520887/75854238850000000000000000000000 : ℝ)*base62 + (54391990394863/1909700000000000000000000000 : ℝ)*base64 + (154058447805861/794410000000000000000000000 : ℝ)*base66 + (16322652043273/38194000000000000000000000 : ℝ)*base68 + (9501005841091000881/75748250500000000000000000000000 : ℝ)*base70 + (43580009739427/247906250000000000000000000 : ℝ)*base72 + (393102006489341/3972050000000000000000000000 : ℝ)*base74 + (277654957039081/1983250000000000000000000000 : ℝ)*base77 + (70927169250258949531/157551363250000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (339/5000000000000000 : ℝ)*base87 + (339/5000000000000000 : ℝ)*base89 + (339/5000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s4_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(69771/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(69771/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (41492367896712867377701590360171/3008758383985250000000000000000000000 : ℝ) := by norm_num
    linear_combination (612268674519/1000000000000 : ℝ)*(base7) + (12306122089/100000000000 : ℝ)*(base40) + (565467/500000000000 : ℝ)*(base49) + (226023366343/125000000000 : ℝ)*(major_s4_0) + (226023366343/125000000000 : ℝ)*(major_s4_1) + (226023366343/125000000000 : ℝ)*(major_s4_2) + (7800231/500000000000 : ℝ)*(sp_s4_1) + (17338561/1000000000000 : ℝ)*(sp_s4_2) + (25058081/250000000000 : ℝ)*(sp_s4_9) + (1592331/62500000000 : ℝ)*(sp_s4_20) + (201687286467/100000000000 : ℝ)*(sp_s4_21) + (2016857264207/1000000000000 : ℝ)*(sp_s4_22) + (252094411723/125000000000 : ℝ)*(sp_s4_23) + (1834618829807/1000000000000 : ℝ)*(sp_s4_27) + (152796954073/125000000000 : ℝ)*(f.failure) + (201687286467/100000000000 : ℝ)*(f.sum) + (256456858131589897/9481779856250000000000000000000 : ℝ)*base63 + (19467529487031/477425000000000000000000000 : ℝ)*base65 + (10661217582337/198602500000000000000000000 : ℝ)*base66 + (17370258203641/23871250000000000000000000 : ℝ)*base69 + (12885523418586333809/37874125250000000000000000000000 : ℝ)*base71 + (626569513711523/1983250000000000000000000000 : ℝ)*base73 + (2404898724905773/3972050000000000000000000000 : ℝ)*base75 + (2148803982397507/1983250000000000000000000000 : ℝ)*base77 + (88043936532151700657/157551363250000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (1387/3125000000000000 : ℝ)*base86 + (1387/3125000000000000 : ℝ)*base88 + (1387/3125000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev3 : (0 : ℝ) ≤ ((7933/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7933/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79441/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(79441/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19097/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19097/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2259/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2259/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18163/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(18163/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(69771/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(69771/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301063_s4 p hpa hpb X hX hprev3

#print axioms solution
