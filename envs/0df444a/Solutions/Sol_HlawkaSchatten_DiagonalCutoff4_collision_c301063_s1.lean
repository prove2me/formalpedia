-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301063_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:39:35.029426+00:00
-- url     : https://prove2.me/submissions/9bae9349-2642-4ce5-9f9e-5d6f8e871efb

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
theorem collision_support_c301063_s1_s1_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-4690839/200000000 : ℝ)*x 0 + (2841734297/5000000000 : ℝ)*x 1 + (3056379613/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4690839/200000000 : ℝ)^65 ≤ (688727848563/100000000000000 : ℝ)^49 := by
    have hnat : (4690839 : ℕ)^65*100000000000000^49 ≤ 688727848563^49*200000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4690839 200000000 688727848563 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2841734297/5000000000 : ℝ)^65 ≤ (47259296103913/100000000000000 : ℝ)^49 := by
    have hnat : (2841734297 : ℕ)^65*100000000000000^49 ≤ 47259296103913^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2841734297 5000000000 47259296103913 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3056379613/5000000000 : ℝ)^65 ≤ (3253248502251/6250000000000 : ℝ)^49 := by
    have hnat : (3056379613 : ℕ)^65*6250000000000^49 ≤ 3253248502251^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3056379613 5000000000 3253248502251 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4690839/200000000 : ℝ), (2841734297/5000000000 : ℝ), (3056379613/5000000000 : ℝ)] ![(688727848563/100000000000000 : ℝ), (47259296103913/100000000000000 : ℝ), (3253248502251/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4690839/200000000 : ℝ)|^65 ≤ (688727848563/100000000000000 : ℝ)^49
        have hw : |(-4690839/200000000 : ℝ)|=(4690839/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2841734297/5000000000 : ℝ)|^65 ≤ (47259296103913/100000000000000 : ℝ)^49
        have hw : |(2841734297/5000000000 : ℝ)|=(2841734297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3056379613/5000000000 : ℝ)|^65 ≤ (3253248502251/6250000000000 : ℝ)^49
        have hw : |(3056379613/5000000000 : ℝ)|=(3056379613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s1_s1_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-173877233/2500000000 : ℝ)*x 0 + (482760247/2500000000 : ℝ)*x 1 + (8909657667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (173877233/2500000000 : ℝ)^65 ≤ (2912588345721/100000000000000 : ℝ)^49 := by
    have hnat : (173877233 : ℕ)^65*100000000000000^49 ≤ 2912588345721^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173877233 2500000000 2912588345721 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (482760247/2500000000 : ℝ)^65 ≤ (1410881581041/12500000000000 : ℝ)^49 := by
    have hnat : (482760247 : ℕ)^65*12500000000000^49 ≤ 1410881581041^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482760247 2500000000 1410881581041 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8909657667/10000000000 : ℝ)^65 ≤ (85800358995329/100000000000000 : ℝ)^49 := by
    have hnat : (8909657667 : ℕ)^65*100000000000000^49 ≤ 85800358995329^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8909657667 10000000000 85800358995329 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-173877233/2500000000 : ℝ), (482760247/2500000000 : ℝ), (8909657667/10000000000 : ℝ)] ![(2912588345721/100000000000000 : ℝ), (1410881581041/12500000000000 : ℝ), (85800358995329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-173877233/2500000000 : ℝ)|^65 ≤ (2912588345721/100000000000000 : ℝ)^49
        have hw : |(-173877233/2500000000 : ℝ)|=(173877233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(482760247/2500000000 : ℝ)|^65 ≤ (1410881581041/12500000000000 : ℝ)^49
        have hw : |(482760247/2500000000 : ℝ)|=(482760247/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8909657667/10000000000 : ℝ)|^65 ≤ (85800358995329/100000000000000 : ℝ)^49
        have hw : |(8909657667/10000000000 : ℝ)|=(8909657667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s1_s1_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (86902649/400000000 : ℝ)*x 0 + (-134379077/5000000000 : ℝ)*x 1 + (1784711003/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86902649/400000000 : ℝ)^65 ≤ (6598487882143/50000000000000 : ℝ)^49 := by
    have hnat : (86902649 : ℕ)^65*50000000000000^49 ≤ 6598487882143^49*400000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86902649 400000000 6598487882143 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134379077/5000000000 : ℝ)^65 ≤ (206271941279/25000000000000 : ℝ)^49 := by
    have hnat : (134379077 : ℕ)^65*25000000000000^49 ≤ 206271941279^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134379077 5000000000 206271941279 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1784711003/2000000000 : ℝ)^65 ≤ (21494484114107/25000000000000 : ℝ)^49 := by
    have hnat : (1784711003 : ℕ)^65*25000000000000^49 ≤ 21494484114107^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1784711003 2000000000 21494484114107 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(86902649/400000000 : ℝ), (-134379077/5000000000 : ℝ), (1784711003/2000000000 : ℝ)] ![(6598487882143/50000000000000 : ℝ), (206271941279/25000000000000 : ℝ), (21494484114107/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(86902649/400000000 : ℝ)|^65 ≤ (6598487882143/50000000000000 : ℝ)^49
        have hw : |(86902649/400000000 : ℝ)|=(86902649/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-134379077/5000000000 : ℝ)|^65 ≤ (206271941279/25000000000000 : ℝ)^49
        have hw : |(-134379077/5000000000 : ℝ)|=(134379077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1784711003/2000000000 : ℝ)|^65 ≤ (21494484114107/25000000000000 : ℝ)^49
        have hw : |(1784711003/2000000000 : ℝ)|=(1784711003/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s1_s1_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (436794757/2000000000 : ℝ)*x 0 + (8978778943/10000000000 : ℝ)*x 1 + (-20154957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436794757/2000000000 : ℝ)^65 ≤ (13288974771547/100000000000000 : ℝ)^49 := by
    have hnat : (436794757 : ℕ)^65*100000000000000^49 ≤ 13288974771547^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436794757 2000000000 13288974771547 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8978778943/10000000000 : ℝ)^65 ≤ (86684468160769/100000000000000 : ℝ)^49 := by
    have hnat : (8978778943 : ℕ)^65*100000000000000^49 ≤ 86684468160769^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8978778943 10000000000 86684468160769 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20154957/10000000000 : ℝ)^65 ≤ (1659816421/6250000000000 : ℝ)^49 := by
    have hnat : (20154957 : ℕ)^65*6250000000000^49 ≤ 1659816421^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20154957 10000000000 1659816421 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(436794757/2000000000 : ℝ), (8978778943/10000000000 : ℝ), (-20154957/10000000000 : ℝ)] ![(13288974771547/100000000000000 : ℝ), (86684468160769/100000000000000 : ℝ), (1659816421/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(436794757/2000000000 : ℝ)|^65 ≤ (13288974771547/100000000000000 : ℝ)^49
        have hw : |(436794757/2000000000 : ℝ)|=(436794757/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8978778943/10000000000 : ℝ)|^65 ≤ (86684468160769/100000000000000 : ℝ)^49
        have hw : |(8978778943/10000000000 : ℝ)|=(8978778943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-20154957/10000000000 : ℝ)|^65 ≤ (1659816421/6250000000000 : ℝ)^49
        have hw : |(-20154957/10000000000 : ℝ)|=(20154957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s1_s1_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (602332537/2000000000 : ℝ)*x 0 + (7510573463/10000000000 : ℝ)*x 1 + (385100859/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (602332537/2000000000 : ℝ)^65 ≤ (20352634768931/100000000000000 : ℝ)^49 := by
    have hnat : (602332537 : ℕ)^65*100000000000000^49 ≤ 20352634768931^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      602332537 2000000000 20352634768931 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7510573463/10000000000 : ℝ)^65 ≤ (34201611027383/50000000000000 : ℝ)^49 := by
    have hnat : (7510573463 : ℕ)^65*50000000000000^49 ≤ 34201611027383^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7510573463 10000000000 34201611027383 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (385100859/2000000000 : ℝ)^65 ≤ (562207158177/5000000000000 : ℝ)^49 := by
    have hnat : (385100859 : ℕ)^65*5000000000000^49 ≤ 562207158177^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385100859 2000000000 562207158177 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(602332537/2000000000 : ℝ), (7510573463/10000000000 : ℝ), (385100859/2000000000 : ℝ)] ![(20352634768931/100000000000000 : ℝ), (34201611027383/50000000000000 : ℝ), (562207158177/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(602332537/2000000000 : ℝ)|^65 ≤ (20352634768931/100000000000000 : ℝ)^49
        have hw : |(602332537/2000000000 : ℝ)|=(602332537/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7510573463/10000000000 : ℝ)|^65 ≤ (34201611027383/50000000000000 : ℝ)^49
        have hw : |(7510573463/10000000000 : ℝ)|=(7510573463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(385100859/2000000000 : ℝ)|^65 ≤ (562207158177/5000000000000 : ℝ)^49
        have hw : |(385100859/2000000000 : ℝ)|=(385100859/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s1_s1_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-55722941/2500000000 : ℝ)*x 0 + (1029109831/5000000000 : ℝ)*x 1 + (9009075067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (55722941/2500000000 : ℝ)^65 ≤ (643718737297/100000000000000 : ℝ)^49 := by
    have hnat : (55722941 : ℕ)^65*100000000000000^49 ≤ 643718737297^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55722941 2500000000 643718737297 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1029109831/5000000000 : ℝ)^65 ≤ (12283602511801/100000000000000 : ℝ)^49 := by
    have hnat : (1029109831 : ℕ)^65*100000000000000^49 ≤ 12283602511801^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029109831 5000000000 12283602511801 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9009075067/10000000000 : ℝ)^65 ≤ (87072678731653/100000000000000 : ℝ)^49 := by
    have hnat : (9009075067 : ℕ)^65*100000000000000^49 ≤ 87072678731653^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9009075067 10000000000 87072678731653 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-55722941/2500000000 : ℝ), (1029109831/5000000000 : ℝ), (9009075067/10000000000 : ℝ)] ![(643718737297/100000000000000 : ℝ), (12283602511801/100000000000000 : ℝ), (87072678731653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-55722941/2500000000 : ℝ)|^65 ≤ (643718737297/100000000000000 : ℝ)^49
        have hw : |(-55722941/2500000000 : ℝ)|=(55722941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1029109831/5000000000 : ℝ)|^65 ≤ (12283602511801/100000000000000 : ℝ)^49
        have hw : |(1029109831/5000000000 : ℝ)|=(1029109831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9009075067/10000000000 : ℝ)|^65 ≤ (87072678731653/100000000000000 : ℝ)^49
        have hw : |(9009075067/10000000000 : ℝ)|=(9009075067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s1_s1_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1781769351/10000000000 : ℝ)*x 0 + (-638093109/10000000000 : ℝ)*x 1 + (9023483863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1781769351/10000000000 : ℝ)^65 ≤ (1014452135341/10000000000000 : ℝ)^49 := by
    have hnat : (1781769351 : ℕ)^65*10000000000000^49 ≤ 1014452135341^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1781769351 10000000000 1014452135341 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (638093109/10000000000 : ℝ)^65 ≤ (1299008872803/50000000000000 : ℝ)^49 := by
    have hnat : (638093109 : ℕ)^65*50000000000000^49 ≤ 1299008872803^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      638093109 10000000000 1299008872803 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9023483863/10000000000 : ℝ)^65 ≤ (87257460882049/100000000000000 : ℝ)^49 := by
    have hnat : (9023483863 : ℕ)^65*100000000000000^49 ≤ 87257460882049^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9023483863 10000000000 87257460882049 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1781769351/10000000000 : ℝ), (-638093109/10000000000 : ℝ), (9023483863/10000000000 : ℝ)] ![(1014452135341/10000000000000 : ℝ), (1299008872803/50000000000000 : ℝ), (87257460882049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1781769351/10000000000 : ℝ)|^65 ≤ (1014452135341/10000000000000 : ℝ)^49
        have hw : |(1781769351/10000000000 : ℝ)|=(1781769351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-638093109/10000000000 : ℝ)|^65 ≤ (1299008872803/50000000000000 : ℝ)^49
        have hw : |(-638093109/10000000000 : ℝ)|=(638093109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9023483863/10000000000 : ℝ)|^65 ≤ (87257460882049/100000000000000 : ℝ)^49
        have hw : |(9023483863/10000000000 : ℝ)|=(9023483863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s1_s1_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8745728029/10000000000 : ℝ)*x 0 + (1268552209/5000000000 : ℝ)*x 1 + (-8856663/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8745728029/10000000000 : ℝ)^65 ≤ (83712549628179/100000000000000 : ℝ)^49 := by
    have hnat : (8745728029 : ℕ)^65*100000000000000^49 ≤ 83712549628179^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8745728029 10000000000 83712549628179 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1268552209/5000000000 : ℝ)^65 ≤ (2026499908943/12500000000000 : ℝ)^49 := by
    have hnat : (1268552209 : ℕ)^65*12500000000000^49 ≤ 2026499908943^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1268552209 5000000000 2026499908943 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8856663/2000000000 : ℝ)^65 ≤ (75451081791/100000000000000 : ℝ)^49 := by
    have hnat : (8856663 : ℕ)^65*100000000000000^49 ≤ 75451081791^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8856663 2000000000 75451081791 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8745728029/10000000000 : ℝ), (1268552209/5000000000 : ℝ), (-8856663/2000000000 : ℝ)] ![(83712549628179/100000000000000 : ℝ), (2026499908943/12500000000000 : ℝ), (75451081791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8745728029/10000000000 : ℝ)|^65 ≤ (83712549628179/100000000000000 : ℝ)^49
        have hw : |(8745728029/10000000000 : ℝ)|=(8745728029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1268552209/5000000000 : ℝ)|^65 ≤ (2026499908943/12500000000000 : ℝ)^49
        have hw : |(1268552209/5000000000 : ℝ)|=(1268552209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8856663/2000000000 : ℝ)|^65 ≤ (75451081791/100000000000000 : ℝ)^49
        have hw : |(-8856663/2000000000 : ℝ)|=(8856663/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s1_s1_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3916662429/5000000000 : ℝ)*x 0 + (2577200247/10000000000 : ℝ)*x 1 + (381829551/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3916662429/5000000000 : ℝ)^65 ≤ (9041205032009/12500000000000 : ℝ)^49 := by
    have hnat : (3916662429 : ℕ)^65*12500000000000^49 ≤ 9041205032009^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3916662429 5000000000 9041205032009 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2577200247/10000000000 : ℝ)^65 ≤ (8276372294111/50000000000000 : ℝ)^49 := by
    have hnat : (2577200247 : ℕ)^65*50000000000000^49 ≤ 8276372294111^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2577200247 10000000000 8276372294111 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (381829551/2000000000 : ℝ)^65 ≤ (5558807573207/50000000000000 : ℝ)^49 := by
    have hnat : (381829551 : ℕ)^65*50000000000000^49 ≤ 5558807573207^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      381829551 2000000000 5558807573207 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3916662429/5000000000 : ℝ), (2577200247/10000000000 : ℝ), (381829551/2000000000 : ℝ)] ![(9041205032009/12500000000000 : ℝ), (8276372294111/50000000000000 : ℝ), (5558807573207/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3916662429/5000000000 : ℝ)|^65 ≤ (9041205032009/12500000000000 : ℝ)^49
        have hw : |(3916662429/5000000000 : ℝ)|=(3916662429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2577200247/10000000000 : ℝ)|^65 ≤ (8276372294111/50000000000000 : ℝ)^49
        have hw : |(2577200247/10000000000 : ℝ)|=(2577200247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(381829551/2000000000 : ℝ)|^65 ≤ (5558807573207/50000000000000 : ℝ)^49
        have hw : |(381829551/2000000000 : ℝ)|=(381829551/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s1_s1_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-81405119/2500000000 : ℝ)*x 0 + (4071027293/5000000000 : ℝ)*x 1 + (3280859577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (81405119/2500000000 : ℝ)^65 ≤ (66519131033/6250000000000 : ℝ)^49 := by
    have hnat : (81405119 : ℕ)^65*6250000000000^49 ≤ 66519131033^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81405119 2500000000 66519131033 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4071027293/5000000000 : ℝ)^65 ≤ (761352768281/1000000000000 : ℝ)^49 := by
    have hnat : (4071027293 : ℕ)^65*1000000000000^49 ≤ 761352768281^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4071027293 5000000000 761352768281 1000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3280859577/10000000000 : ℝ)^65 ≤ (1425026067011/6250000000000 : ℝ)^49 := by
    have hnat : (3280859577 : ℕ)^65*6250000000000^49 ≤ 1425026067011^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3280859577 10000000000 1425026067011 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-81405119/2500000000 : ℝ), (4071027293/5000000000 : ℝ), (3280859577/10000000000 : ℝ)] ![(66519131033/6250000000000 : ℝ), (761352768281/1000000000000 : ℝ), (1425026067011/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-81405119/2500000000 : ℝ)|^65 ≤ (66519131033/6250000000000 : ℝ)^49
        have hw : |(-81405119/2500000000 : ℝ)|=(81405119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4071027293/5000000000 : ℝ)|^65 ≤ (761352768281/1000000000000 : ℝ)^49
        have hw : |(4071027293/5000000000 : ℝ)|=(4071027293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3280859577/10000000000 : ℝ)|^65 ≤ (1425026067011/6250000000000 : ℝ)^49
        have hw : |(3280859577/10000000000 : ℝ)|=(3280859577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s1_s1_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4316886421/5000000000 : ℝ)*x 0 + (-57229029/10000000000 : ℝ)*x 1 + (2699182037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4316886421/5000000000 : ℝ)^65 ≤ (41146999478797/50000000000000 : ℝ)^49 := by
    have hnat : (4316886421 : ℕ)^65*50000000000000^49 ≤ 41146999478797^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4316886421 5000000000 41146999478797 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (57229029/10000000000 : ℝ)^65 ≤ (26506323179/25000000000000 : ℝ)^49 := by
    have hnat : (57229029 : ℕ)^65*25000000000000^49 ≤ 26506323179^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57229029 10000000000 26506323179 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2699182037/10000000000 : ℝ)^65 ≤ (439999393241/2500000000000 : ℝ)^49 := by
    have hnat : (2699182037 : ℕ)^65*2500000000000^49 ≤ 439999393241^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699182037 10000000000 439999393241 2500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4316886421/5000000000 : ℝ), (-57229029/10000000000 : ℝ), (2699182037/10000000000 : ℝ)] ![(41146999478797/50000000000000 : ℝ), (26506323179/25000000000000 : ℝ), (439999393241/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4316886421/5000000000 : ℝ)|^65 ≤ (41146999478797/50000000000000 : ℝ)^49
        have hw : |(4316886421/5000000000 : ℝ)|=(4316886421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-57229029/10000000000 : ℝ)|^65 ≤ (26506323179/25000000000000 : ℝ)^49
        have hw : |(-57229029/10000000000 : ℝ)|=(57229029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2699182037/10000000000 : ℝ)|^65 ≤ (439999393241/2500000000000 : ℝ)^49
        have hw : |(2699182037/10000000000 : ℝ)|=(2699182037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s1_s1_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (74927487/500000000 : ℝ)*x 0 + (4633878129/5000000000 : ℝ)*x 1 + (-85712523/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (74927487/500000000 : ℝ)^65 ≤ (2015777398197/25000000000000 : ℝ)^49 := by
    have hnat : (74927487 : ℕ)^65*25000000000000^49 ≤ 2015777398197^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74927487 500000000 2015777398197 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4633878129/5000000000 : ℝ)^65 ≤ (90404656486959/100000000000000 : ℝ)^49 := by
    have hnat : (4633878129 : ℕ)^65*100000000000000^49 ≤ 90404656486959^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4633878129 5000000000 90404656486959 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85712523/2000000000 : ℝ)^65 ≤ (766116955403/50000000000000 : ℝ)^49 := by
    have hnat : (85712523 : ℕ)^65*50000000000000^49 ≤ 766116955403^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85712523 2000000000 766116955403 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(74927487/500000000 : ℝ), (4633878129/5000000000 : ℝ), (-85712523/2000000000 : ℝ)] ![(2015777398197/25000000000000 : ℝ), (90404656486959/100000000000000 : ℝ), (766116955403/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(74927487/500000000 : ℝ)|^65 ≤ (2015777398197/25000000000000 : ℝ)^49
        have hw : |(74927487/500000000 : ℝ)|=(74927487/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4633878129/5000000000 : ℝ)|^65 ≤ (90404656486959/100000000000000 : ℝ)^49
        have hw : |(4633878129/5000000000 : ℝ)|=(4633878129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-85712523/2000000000 : ℝ)|^65 ≤ (766116955403/50000000000000 : ℝ)^49
        have hw : |(-85712523/2000000000 : ℝ)|=(85712523/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s1_s1_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1983113973/2500000000 : ℝ)*x 0 + (2581887581/10000000000 : ℝ)*x 1 + (348818413/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1983113973/2500000000 : ℝ)^65 ≤ (9193295131957/12500000000000 : ℝ)^49 := by
    have hnat : (1983113973 : ℕ)^65*12500000000000^49 ≤ 9193295131957^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1983113973 2500000000 9193295131957 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2581887581/10000000000 : ℝ)^65 ≤ (16592692484663/100000000000000 : ℝ)^49 := by
    have hnat : (2581887581 : ℕ)^65*100000000000000^49 ≤ 16592692484663^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2581887581 10000000000 16592692484663 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (348818413/2000000000 : ℝ)^65 ≤ (9860946443323/100000000000000 : ℝ)^49 := by
    have hnat : (348818413 : ℕ)^65*100000000000000^49 ≤ 9860946443323^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      348818413 2000000000 9860946443323 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1983113973/2500000000 : ℝ), (2581887581/10000000000 : ℝ), (348818413/2000000000 : ℝ)] ![(9193295131957/12500000000000 : ℝ), (16592692484663/100000000000000 : ℝ), (9860946443323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1983113973/2500000000 : ℝ)|^65 ≤ (9193295131957/12500000000000 : ℝ)^49
        have hw : |(1983113973/2500000000 : ℝ)|=(1983113973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2581887581/10000000000 : ℝ)|^65 ≤ (16592692484663/100000000000000 : ℝ)^49
        have hw : |(2581887581/10000000000 : ℝ)|=(2581887581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(348818413/2000000000 : ℝ)|^65 ≤ (9860946443323/100000000000000 : ℝ)^49
        have hw : |(348818413/2000000000 : ℝ)|=(348818413/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301063_s1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((96243/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(96243/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(23883/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(23883/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(469/500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(469/500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((18271/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18271/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2839/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2839/3125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17637/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(17637/20000 : ℝ)*X 1 2) := by
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
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  have s1_pow0 : (96243/100000 : ℝ) ^ (129/32 : ℝ) ≤ (85695278379140951697/100000000000000000000 : ℝ) := by
    have hpowers : (96243/100000 : ℝ)^129 ≤ (85695278379140951697/100000000000000000000 : ℝ)^32 := by
      have hnat : (96243 : ℕ)^129*100000000000000000000^32 ≤ 85695278379140951697^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        96243 100000 85695278379140951697 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (96243/100000 : ℝ)) (X := (85695278379140951697/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (185695278379140951697/100000000000000000000 : ℝ) ≤ (11659482727648373/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (185695278379140951697/100000000000000000000 : ℝ)^32 ≤ (11659482727648373/10000000000000000 : ℝ)^129 := by
      have hnat : (185695278379140951697 : ℕ)^32*10000000000000000^129 ≤ 11659482727648373^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        185695278379140951697 100000000000000000000 11659482727648373 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11659482727648373/10000000000000000 : ℝ)) (X := (185695278379140951697/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (135695278379140951697/50000000000000000000 : ℝ) ≤ (12810272941719999/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (135695278379140951697/50000000000000000000 : ℝ)^32 ≤ (12810272941719999/10000000000000000 : ℝ)^129 := by
      have hnat : (135695278379140951697 : ℕ)^32*10000000000000000^129 ≤ 12810272941719999^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        135695278379140951697 50000000000000000000 12810272941719999 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12810272941719999/10000000000000000 : ℝ)) (X := (135695278379140951697/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1659482727648373/9624300000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(575395107035813/4812150000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (96243/100000 : ℝ)) (alpha := (1659482727648373/9624300000000000 : ℝ)) (beta := (575395107035813/4812150000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (96243/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1659482727648373/9624300000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(575395107035813/4812150000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (23883/25000 : ℝ) ^ (129/32 : ℝ) ≤ (4158580726022042023/5000000000000000000 : ℝ) := by
    have hpowers : (23883/25000 : ℝ)^129 ≤ (4158580726022042023/5000000000000000000 : ℝ)^32 := by
      have hnat : (23883 : ℕ)^129*5000000000000000000^32 ≤ 4158580726022042023^32*25000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23883 25000 4158580726022042023 5000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (23883/25000 : ℝ)) (X := (4158580726022042023/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (9158580726022042023/5000000000000000000 : ℝ) ≤ (464798930010391/400000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (9158580726022042023/5000000000000000000 : ℝ)^32 ≤ (464798930010391/400000000000000 : ℝ)^129 := by
      have hnat : (9158580726022042023 : ℕ)^32*400000000000000^129 ≤ 464798930010391^129*5000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9158580726022042023 5000000000000000000 464798930010391 400000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (464798930010391/400000000000000 : ℝ)) (X := (9158580726022042023/5000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (6658580726022042023/2500000000000000000 : ℝ) ≤ (12750755433569643/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (6658580726022042023/2500000000000000000 : ℝ)^32 ≤ (12750755433569643/10000000000000000 : ℝ)^129 := by
      have hnat : (6658580726022042023 : ℕ)^32*10000000000000000^129 ≤ 12750755433569643^129*2500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6658580726022042023 2500000000000000000 12750755433569643 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12750755433569643/10000000000000000 : ℝ)) (X := (6658580726022042023/2500000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(21599643336797/127376000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(282695545827467/2388300000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (23883/25000 : ℝ)) (alpha := (21599643336797/127376000000000 : ℝ)) (beta := (282695545827467/2388300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (23883/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(21599643336797/127376000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(282695545827467/2388300000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (469/500 : ℝ) ^ (129/32 : ℝ) ≤ (77257863194454771293/100000000000000000000 : ℝ) := by
    have hpowers : (469/500 : ℝ)^129 ≤ (77257863194454771293/100000000000000000000 : ℝ)^32 := by
      have hnat : (469 : ℕ)^129*100000000000000000000^32 ≤ 77257863194454771293^32*500^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        469 500 77257863194454771293 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (469/500 : ℝ)) (X := (77257863194454771293/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (177257863194454771293/100000000000000000000 : ℝ) ≤ (72036001946543/62500000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (177257863194454771293/100000000000000000000 : ℝ)^32 ≤ (72036001946543/62500000000000 : ℝ)^129 := by
      have hnat : (177257863194454771293 : ℕ)^32*62500000000000^129 ≤ 72036001946543^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        177257863194454771293 100000000000000000000 72036001946543 62500000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (72036001946543/62500000000000 : ℝ)) (X := (177257863194454771293/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (127257863194454771293/50000000000000000000 : ℝ) ≤ (12607889299135039/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (127257863194454771293/50000000000000000000 : ℝ)^32 ≤ (12607889299135039/10000000000000000 : ℝ)^129 := by
      have hnat : (127257863194454771293 : ℕ)^32*10000000000000000^129 ≤ 12607889299135039^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        127257863194454771293 50000000000000000000 12607889299135039 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12607889299135039/10000000000000000 : ℝ)) (X := (127257863194454771293/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(9536001946543/58625000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1082128987688159/9380000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (469/500 : ℝ)) (alpha := (9536001946543/58625000000000 : ℝ)) (beta := (1082128987688159/9380000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (469/500 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(9536001946543/58625000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1082128987688159/9380000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-4690839/200000000 : ℝ)*X 0 0+(2841734297/5000000000 : ℝ)*X 0 1+(3056379613/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-173877233/2500000000 : ℝ)*X 0 0+(482760247/2500000000 : ℝ)*X 0 1+(8909657667/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((86902649/400000000 : ℝ)*X 1 0+(-134379077/5000000000 : ℝ)*X 1 1+(1784711003/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((436794757/2000000000 : ℝ)*X 2 0+(8978778943/10000000000 : ℝ)*X 2 1+(-20154957/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((602332537/2000000000 : ℝ)*X 0 0+(7510573463/10000000000 : ℝ)*X 0 1+(385100859/2000000000 : ℝ)*X 0 2+(602332537/2000000000 : ℝ)*X 1 0+(7510573463/10000000000 : ℝ)*X 1 1+(385100859/2000000000 : ℝ)*X 1 2+(602332537/2000000000 : ℝ)*X 2 0+(7510573463/10000000000 : ℝ)*X 2 1+(385100859/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-55722941/2500000000 : ℝ)*X 0 0+(1029109831/5000000000 : ℝ)*X 0 1+(9009075067/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((1781769351/10000000000 : ℝ)*X 1 0+(-638093109/10000000000 : ℝ)*X 1 1+(9023483863/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((8745728029/10000000000 : ℝ)*X 2 0+(1268552209/5000000000 : ℝ)*X 2 1+(-8856663/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((3916662429/5000000000 : ℝ)*X 0 0+(2577200247/10000000000 : ℝ)*X 0 1+(381829551/2000000000 : ℝ)*X 0 2+(3916662429/5000000000 : ℝ)*X 1 0+(2577200247/10000000000 : ℝ)*X 1 1+(381829551/2000000000 : ℝ)*X 1 2+(3916662429/5000000000 : ℝ)*X 2 0+(2577200247/10000000000 : ℝ)*X 2 1+(381829551/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-81405119/2500000000 : ℝ)*X 0 0+(4071027293/5000000000 : ℝ)*X 0 1+(3280859577/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((4316886421/5000000000 : ℝ)*X 1 0+(-57229029/10000000000 : ℝ)*X 1 1+(2699182037/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((74927487/500000000 : ℝ)*X 2 0+(4633878129/5000000000 : ℝ)*X 2 1+(-85712523/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((1983113973/2500000000 : ℝ)*X 0 0+(2581887581/10000000000 : ℝ)*X 0 1+(348818413/2000000000 : ℝ)*X 0 2+(1983113973/2500000000 : ℝ)*X 1 0+(2581887581/10000000000 : ℝ)*X 1 1+(348818413/2000000000 : ℝ)*X 1 2+(1983113973/2500000000 : ℝ)*X 2 0+(2581887581/10000000000 : ℝ)*X 2 1+(348818413/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((18271/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18271/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1218157076232087653438964246383/171115883470000000000000000000000000 : ℝ) := by norm_num
    linear_combination (35789529199/40000000000 : ℝ)*(base7) + (16169/15625000000 : ℝ)*(base50) + (41720014767/250000000000 : ℝ)*(base53) + (28927/31250000000 : ℝ)*(base60) + (196256931347/125000000000 : ℝ)*(major_s1_0) + (196256931347/125000000000 : ℝ)*(major_s1_1) + (1403175391707/1000000000000 : ℝ)*(major_s1_2) + (1509229/250000000000 : ℝ)*(sp_s1_0) + (1360656916809/1000000000000 : ℝ)*(sp_s1_7) + (1360726169127/1000000000000 : ℝ)*(sp_s1_8) + (1527610145847/1000000000000 : ℝ)*(sp_s1_9) + (978065773669/500000000000 : ℝ)*(sp_s1_13) + (33566527/500000000000 : ℝ)*(sp_s1_14) + (979413/250000000000 : ℝ)*(sp_s1_15) + (1061393317363/1000000000000 : ℝ)*(f.failure) + (1527610145847/1000000000000 : ℝ)*(f.sum) + (222154641766861253/933427250000000000000000000000 : ℝ)*base62 + (2776089076253413/9380000000000000000000000000 : ℝ)*base65 + (857576135133809/1194150000000000000000000000 : ℝ)*base66 + (17638321408023/117250000000000000000000000 : ℝ)*base68 + (2798644006690959791/18423660000000000000000000000000 : ℝ)*base71 + (3064020965312677/4812150000000000000000000000 : ℝ)*base72 + (4573428381137/7961000000000000000000000 : ℝ)*base75 + (745022672467499/4812150000000000000000000000 : ℝ)*base77 + (1935217555016016107/12769842050000000000000000000000 : ℝ)*base78 + (1103/25000000000000000 : ℝ)*base87 + (1103/25000000000000000 : ℝ)*base89 + (26103/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2839/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2839/3125 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1694309689621266060261644945799/171115883470000000000000000000000000 : ℝ) := by norm_num
    linear_combination (446951893199/500000000000 : ℝ)*(base7) + (753009/1000000000000 : ℝ)*(base13) + (1252909/1000000000000 : ℝ)*(base40) + (4642606757/25000000000 : ℝ)*(base53) + (780017/500000000000 : ℝ)*(base59) + (1508639338461/1000000000000 : ℝ)*(major_s1_0) + (1508639338461/1000000000000 : ℝ)*(major_s1_1) + (1322935068181/1000000000000 : ℝ)*(major_s1_2) + (432983/1000000000000 : ℝ)*(sp_s1_7) + (29469479/250000000000 : ℝ)*(sp_s1_8) + (315276049543/250000000000 : ℝ)*(sp_s1_14) + (157623438281/125000000000 : ℝ)*(sp_s1_15) + (361702413611/250000000000 : ℝ)*(sp_s1_16) + (478444602541/250000000000 : ℝ)*(sp_s1_20) + (1019874623767/1000000000000 : ℝ)*(f.failure) + (361702413611/250000000000 : ℝ)*(f.sum) + (3057251700226980633/7467418000000000000000000000000 : ℝ)*base63 + (4408651341080779/9380000000000000000000000000 : ℝ)*base65 + (545580067471379/796100000000000000000000000 : ℝ)*base67 + (39814203306533/58625000000000000000000000 : ℝ)*base69 + (4889415494533589557/42988540000000000000000000000000 : ℝ)*base71 + (1194797050661411/1604050000000000000000000000 : ℝ)*base73 + (620166163102541/636880000000000000000000000 : ℝ)*base75 + (1367850588603651/3208100000000000000000000000 : ℝ)*base77 + (4529217427276985531/25539684100000000000000000000000 : ℝ)*base79 + (2427/25000000000000000 : ℝ)*base87 + (2427/25000000000000000 : ℝ)*base89 + (2427/25000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17637/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(17637/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (413512616657620698130194795979/34223176694000000000000000000000000 : ℝ) := by norm_num
    linear_combination (911660372461/1000000000000 : ℝ)*(base7) + (2273/7812500000 : ℝ)*(base34) + (7560196499/125000000000 : ℝ)*(base40) + (13204851997/125000000000 : ℝ)*(base43) + (242867/250000000000 : ℝ)*(base49) + (105719/200000000000 : ℝ)*(base59) + (1474101917251/1000000000000 : ℝ)*(major_s1_0) + (1368463392219/1000000000000 : ℝ)*(major_s1_1) + (294820441639/200000000000 : ℝ)*(major_s1_2) + (103172269/1000000000000 : ℝ)*(sp_s1_9) + (1284506456561/1000000000000 : ℝ)*(sp_s1_21) + (1390145563481/1000000000000 : ℝ)*(sp_s1_22) + (321100893809/250000000000 : ℝ)*(sp_s1_23) + (1908186817/1000000000 : ℝ)*(sp_s1_27) + (996526735483/1000000000000 : ℝ)*(f.failure) + (1390145563481/1000000000000 : ℝ)*(f.sum) + (386383618681328013/1493483600000000000000000000000 : ℝ)*base62 + (889311163096999/1876000000000000000000000000 : ℝ)*base64 + (677573076185079/796100000000000000000000000 : ℝ)*base66 + (482415513967/2931250000000000000000000 : ℝ)*base68 + (12300958530633891611/25793124000000000000000000000000 : ℝ)*base70 + (278675185110823/1203037500000000000000000000 : ℝ)*base72 + (2364740333729/5095040000000000000000000 : ℝ)*base74 + (3306124164416027/9624300000000000000000000000 : ℝ)*base76 + (20963470840621403011/76619052300000000000000000000000 : ℝ)*base78 + (21823/25000000000000000 : ℝ)*base87 + (21823/25000000000000000 : ℝ)*base89 + (21823/25000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((96243/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(96243/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(23883/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(23883/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(469/500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(469/500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((18271/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18271/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2839/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2839/3125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17637/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(17637/20000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301063_s1 p hpa hpb X hX hprev0

#print axioms solution
