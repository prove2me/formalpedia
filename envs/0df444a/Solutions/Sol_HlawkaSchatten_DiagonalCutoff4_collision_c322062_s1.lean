-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c322062_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:47:28.861996+00:00
-- url     : https://prove2.me/submissions/e23cb1e9-52fe-46f4-8a51-81c2f8ff87e1

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
theorem collision_support_c322062_s1_s1_0 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-734038317/5000000000 : ℝ)*x 0 + (2482584031/5000000000 : ℝ)*x 1 + (-1119064521/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (734038317/5000000000 : ℝ)^83 ≤ (9284603197019/100000000000000 : ℝ)^67 := by
    have hnat : (734038317 : ℕ)^83*100000000000000^67 ≤ 9284603197019^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      734038317 5000000000 9284603197019 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2482584031/5000000000 : ℝ)^83 ≤ (21003475774477/50000000000000 : ℝ)^67 := by
    have hnat : (2482584031 : ℕ)^83*50000000000000^67 ≤ 21003475774477^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2482584031 5000000000 21003475774477 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1119064521/2000000000 : ℝ)^83 ≤ (1217711130899/2500000000000 : ℝ)^67 := by
    have hnat : (1119064521 : ℕ)^83*2500000000000^67 ≤ 1217711130899^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119064521 2000000000 1217711130899 2500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-734038317/5000000000 : ℝ), (2482584031/5000000000 : ℝ), (-1119064521/2000000000 : ℝ)] ![(9284603197019/100000000000000 : ℝ), (21003475774477/50000000000000 : ℝ), (1217711130899/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-734038317/5000000000 : ℝ)|^83 ≤ (9284603197019/100000000000000 : ℝ)^67
        have hw : |(-734038317/5000000000 : ℝ)|=(734038317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2482584031/5000000000 : ℝ)|^83 ≤ (21003475774477/50000000000000 : ℝ)^67
        have hw : |(2482584031/5000000000 : ℝ)|=(2482584031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1119064521/2000000000 : ℝ)|^83 ≤ (1217711130899/2500000000000 : ℝ)^67
        have hw : |(-1119064521/2000000000 : ℝ)|=(1119064521/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322062_s1_s1_1 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (621446837/1250000000 : ℝ)*x 0 + (-146781267/1000000000 : ℝ)*x 1 + (-279464311/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (621446837/1250000000 : ℝ)^83 ≤ (5259263491551/12500000000000 : ℝ)^67 := by
    have hnat : (621446837 : ℕ)^83*12500000000000^67 ≤ 5259263491551^67*1250000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      621446837 1250000000 5259263491551 12500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (146781267/1000000000 : ℝ)^83 ≤ (928253518391/10000000000000 : ℝ)^67 := by
    have hnat : (146781267 : ℕ)^83*10000000000000^67 ≤ 928253518391^67*1000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      146781267 1000000000 928253518391 10000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (279464311/500000000 : ℝ)^83 ≤ (12160839216549/25000000000000 : ℝ)^67 := by
    have hnat : (279464311 : ℕ)^83*25000000000000^67 ≤ 12160839216549^67*500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279464311 500000000 12160839216549 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(621446837/1250000000 : ℝ), (-146781267/1000000000 : ℝ), (-279464311/500000000 : ℝ)] ![(5259263491551/12500000000000 : ℝ), (928253518391/10000000000000 : ℝ), (12160839216549/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(621446837/1250000000 : ℝ)|^83 ≤ (5259263491551/12500000000000 : ℝ)^67
        have hw : |(621446837/1250000000 : ℝ)|=(621446837/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-146781267/1000000000 : ℝ)|^83 ≤ (928253518391/10000000000000 : ℝ)^67
        have hw : |(-146781267/1000000000 : ℝ)|=(146781267/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-279464311/500000000 : ℝ)|^83 ≤ (12160839216549/25000000000000 : ℝ)^67
        have hw : |(-279464311/500000000 : ℝ)|=(279464311/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322062_s1_s1_2 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1021022973/2000000000 : ℝ)*x 0 + (5113041153/10000000000 : ℝ)*x 1 + (1921527671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1021022973/2000000000 : ℝ)^83 ≤ (21739297055137/50000000000000 : ℝ)^67 := by
    have hnat : (1021022973 : ℕ)^83*50000000000000^67 ≤ 21739297055137^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021022973 2000000000 21739297055137 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5113041153/10000000000 : ℝ)^83 ≤ (10890558987943/25000000000000 : ℝ)^67 := by
    have hnat : (5113041153 : ℕ)^83*25000000000000^67 ≤ 10890558987943^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5113041153 10000000000 10890558987943 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1921527671/10000000000 : ℝ)^83 ≤ (1619896240571/12500000000000 : ℝ)^67 := by
    have hnat : (1921527671 : ℕ)^83*12500000000000^67 ≤ 1619896240571^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1921527671 10000000000 1619896240571 12500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1021022973/2000000000 : ℝ), (5113041153/10000000000 : ℝ), (1921527671/10000000000 : ℝ)] ![(21739297055137/50000000000000 : ℝ), (10890558987943/25000000000000 : ℝ), (1619896240571/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1021022973/2000000000 : ℝ)|^83 ≤ (21739297055137/50000000000000 : ℝ)^67
        have hw : |(1021022973/2000000000 : ℝ)|=(1021022973/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5113041153/10000000000 : ℝ)|^83 ≤ (10890558987943/25000000000000 : ℝ)^67
        have hw : |(5113041153/10000000000 : ℝ)|=(5113041153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1921527671/10000000000 : ℝ)|^83 ≤ (1619896240571/12500000000000 : ℝ)^67
        have hw : |(1921527671/10000000000 : ℝ)|=(1921527671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322062_s1_s1_7 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-565552731/5000000000 : ℝ)*x 0 + (1137258337/2500000000 : ℝ)*x 1 + (-6225046681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (565552731/5000000000 : ℝ)^83 ≤ (6721620504201/100000000000000 : ℝ)^67 := by
    have hnat : (565552731 : ℕ)^83*100000000000000^67 ≤ 6721620504201^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565552731 5000000000 6721620504201 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1137258337/2500000000 : ℝ)^83 ≤ (37690175897641/100000000000000 : ℝ)^67 := by
    have hnat : (1137258337 : ℕ)^83*100000000000000^67 ≤ 37690175897641^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1137258337 2500000000 37690175897641 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6225046681/10000000000 : ℝ)^83 ≤ (11117640716539/20000000000000 : ℝ)^67 := by
    have hnat : (6225046681 : ℕ)^83*20000000000000^67 ≤ 11117640716539^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6225046681 10000000000 11117640716539 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-565552731/5000000000 : ℝ), (1137258337/2500000000 : ℝ), (-6225046681/10000000000 : ℝ)] ![(6721620504201/100000000000000 : ℝ), (37690175897641/100000000000000 : ℝ), (11117640716539/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-565552731/5000000000 : ℝ)|^83 ≤ (6721620504201/100000000000000 : ℝ)^67
        have hw : |(-565552731/5000000000 : ℝ)|=(565552731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1137258337/2500000000 : ℝ)|^83 ≤ (37690175897641/100000000000000 : ℝ)^67
        have hw : |(1137258337/2500000000 : ℝ)|=(1137258337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6225046681/10000000000 : ℝ)|^83 ≤ (11117640716539/20000000000000 : ℝ)^67
        have hw : |(-6225046681/10000000000 : ℝ)|=(6225046681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322062_s1_s1_8 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2485273479/5000000000 : ℝ)*x 0 + (-450469237/5000000000 : ℝ)*x 1 + (-5977775997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2485273479/5000000000 : ℝ)^83 ≤ (42063333462029/100000000000000 : ℝ)^67 := by
    have hnat : (2485273479 : ℕ)^83*100000000000000^67 ≤ 42063333462029^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2485273479 5000000000 42063333462029 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (450469237/5000000000 : ℝ)^83 ≤ (19807521023/390625000000 : ℝ)^67 := by
    have hnat : (450469237 : ℕ)^83*390625000000^67 ≤ 19807521023^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450469237 5000000000 19807521023 390625000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5977775997/10000000000 : ℝ)^83 ≤ (6608242641717/12500000000000 : ℝ)^67 := by
    have hnat : (5977775997 : ℕ)^83*12500000000000^67 ≤ 6608242641717^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5977775997 10000000000 6608242641717 12500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2485273479/5000000000 : ℝ), (-450469237/5000000000 : ℝ), (-5977775997/10000000000 : ℝ)] ![(42063333462029/100000000000000 : ℝ), (19807521023/390625000000 : ℝ), (6608242641717/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2485273479/5000000000 : ℝ)|^83 ≤ (42063333462029/100000000000000 : ℝ)^67
        have hw : |(2485273479/5000000000 : ℝ)|=(2485273479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-450469237/5000000000 : ℝ)|^83 ≤ (19807521023/390625000000 : ℝ)^67
        have hw : |(-450469237/5000000000 : ℝ)|=(450469237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5977775997/10000000000 : ℝ)|^83 ≤ (6608242641717/12500000000000 : ℝ)^67
        have hw : |(-5977775997/10000000000 : ℝ)|=(5977775997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322062_s1_s1_9 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4875955741/10000000000 : ℝ)*x 0 + (1186697667/2000000000 : ℝ)*x 1 + (1107034537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4875955741/10000000000 : ℝ)^83 ≤ (41073958692973/100000000000000 : ℝ)^67 := by
    have hnat : (4875955741 : ℕ)^83*100000000000000^67 ≤ 41073958692973^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4875955741 10000000000 41073958692973 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1186697667/2000000000 : ℝ)^83 ≤ (52381169395827/100000000000000 : ℝ)^67 := by
    have hnat : (1186697667 : ℕ)^83*100000000000000^67 ≤ 52381169395827^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1186697667 2000000000 52381169395827 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1107034537/10000000000 : ℝ)^83 ≤ (6544871904799/100000000000000 : ℝ)^67 := by
    have hnat : (1107034537 : ℕ)^83*100000000000000^67 ≤ 6544871904799^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107034537 10000000000 6544871904799 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4875955741/10000000000 : ℝ), (1186697667/2000000000 : ℝ), (1107034537/10000000000 : ℝ)] ![(41073958692973/100000000000000 : ℝ), (52381169395827/100000000000000 : ℝ), (6544871904799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4875955741/10000000000 : ℝ)|^83 ≤ (41073958692973/100000000000000 : ℝ)^67
        have hw : |(4875955741/10000000000 : ℝ)|=(4875955741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1186697667/2000000000 : ℝ)|^83 ≤ (52381169395827/100000000000000 : ℝ)^67
        have hw : |(1186697667/2000000000 : ℝ)|=(1186697667/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1107034537/10000000000 : ℝ)|^83 ≤ (6544871904799/100000000000000 : ℝ)^67
        have hw : |(1107034537/10000000000 : ℝ)|=(1107034537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322062_s1_s1_13 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5131456901/10000000000 : ℝ)*x 0 + (302179087/500000000 : ℝ)*x 1 + (-534469179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5131456901/10000000000 : ℝ)^83 ≤ (4375668691039/10000000000000 : ℝ)^67 := by
    have hnat : (5131456901 : ℕ)^83*10000000000000^67 ≤ 4375668691039^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5131456901 10000000000 4375668691039 10000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (302179087/500000000 : ℝ)^83 ≤ (53587833269189/100000000000000 : ℝ)^67 := by
    have hnat : (302179087 : ℕ)^83*100000000000000^67 ≤ 53587833269189^67*500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      302179087 500000000 53587833269189 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (534469179/10000000000 : ℝ)^83 ≤ (2655479812339/100000000000000 : ℝ)^67 := by
    have hnat : (534469179 : ℕ)^83*100000000000000^67 ≤ 2655479812339^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534469179 10000000000 2655479812339 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5131456901/10000000000 : ℝ), (302179087/500000000 : ℝ), (-534469179/10000000000 : ℝ)] ![(4375668691039/10000000000000 : ℝ), (53587833269189/100000000000000 : ℝ), (2655479812339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5131456901/10000000000 : ℝ)|^83 ≤ (4375668691039/10000000000000 : ℝ)^67
        have hw : |(5131456901/10000000000 : ℝ)|=(5131456901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(302179087/500000000 : ℝ)|^83 ≤ (53587833269189/100000000000000 : ℝ)^67
        have hw : |(302179087/500000000 : ℝ)|=(302179087/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-534469179/10000000000 : ℝ)|^83 ≤ (2655479812339/100000000000000 : ℝ)^67
        have hw : |(-534469179/10000000000 : ℝ)|=(534469179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322062_s1_s1_14 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-807309107/10000000000 : ℝ)*x 0 + (97135343/200000000 : ℝ)*x 1 + (-307231329/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (807309107/10000000000 : ℝ)^83 ≤ (442623474617/10000000000000 : ℝ)^67 := by
    have hnat : (807309107 : ℕ)^83*10000000000000^67 ≤ 442623474617^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      807309107 10000000000 442623474617 10000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (97135343/200000000 : ℝ)^83 ≤ (10218452949267/25000000000000 : ℝ)^67 := by
    have hnat : (97135343 : ℕ)^83*25000000000000^67 ≤ 10218452949267^67*200000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97135343 200000000 10218452949267 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (307231329/500000000 : ℝ)^83 ≤ (27349976722147/50000000000000 : ℝ)^67 := by
    have hnat : (307231329 : ℕ)^83*50000000000000^67 ≤ 27349976722147^67*500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      307231329 500000000 27349976722147 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-807309107/10000000000 : ℝ), (97135343/200000000 : ℝ), (-307231329/500000000 : ℝ)] ![(442623474617/10000000000000 : ℝ), (10218452949267/25000000000000 : ℝ), (27349976722147/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-807309107/10000000000 : ℝ)|^83 ≤ (442623474617/10000000000000 : ℝ)^67
        have hw : |(-807309107/10000000000 : ℝ)|=(807309107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(97135343/200000000 : ℝ)|^83 ≤ (10218452949267/25000000000000 : ℝ)^67
        have hw : |(97135343/200000000 : ℝ)|=(97135343/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-307231329/500000000 : ℝ)|^83 ≤ (27349976722147/50000000000000 : ℝ)^67
        have hw : |(-307231329/500000000 : ℝ)|=(307231329/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322062_s1_s1_15 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1169242611/2500000000 : ℝ)*x 0 + (-124518509/1000000000 : ℝ)*x 1 + (-753548773/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1169242611/2500000000 : ℝ)^83 ≤ (39007687758277/100000000000000 : ℝ)^67 := by
    have hnat : (1169242611 : ℕ)^83*100000000000000^67 ≤ 39007687758277^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1169242611 2500000000 39007687758277 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (124518509/1000000000 : ℝ)^83 ≤ (3785649246611/50000000000000 : ℝ)^67 := by
    have hnat : (124518509 : ℕ)^83*50000000000000^67 ≤ 3785649246611^67*1000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124518509 1000000000 3785649246611 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (753548773/1250000000 : ℝ)^83 ≤ (53421013738927/100000000000000 : ℝ)^67 := by
    have hnat : (753548773 : ℕ)^83*100000000000000^67 ≤ 53421013738927^67*1250000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      753548773 1250000000 53421013738927 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1169242611/2500000000 : ℝ), (-124518509/1000000000 : ℝ), (-753548773/1250000000 : ℝ)] ![(39007687758277/100000000000000 : ℝ), (3785649246611/50000000000000 : ℝ), (53421013738927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1169242611/2500000000 : ℝ)|^83 ≤ (39007687758277/100000000000000 : ℝ)^67
        have hw : |(1169242611/2500000000 : ℝ)|=(1169242611/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-124518509/1000000000 : ℝ)|^83 ≤ (3785649246611/50000000000000 : ℝ)^67
        have hw : |(-124518509/1000000000 : ℝ)|=(124518509/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-753548773/1250000000 : ℝ)|^83 ≤ (53421013738927/100000000000000 : ℝ)^67
        have hw : |(-753548773/1250000000 : ℝ)|=(753548773/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322062_s1_s1_16 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5790788953/10000000000 : ℝ)*x 0 + (5005202263/10000000000 : ℝ)*x 1 + (283671061/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5790788953/10000000000 : ℝ)^83 ≤ (5082508251503/10000000000000 : ℝ)^67 := by
    have hnat : (5790788953 : ℕ)^83*10000000000000^67 ≤ 5082508251503^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5790788953 10000000000 5082508251503 10000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5005202263/10000000000 : ℝ)^83 ≤ (8485388267429/20000000000000 : ℝ)^67 := by
    have hnat : (5005202263 : ℕ)^83*20000000000000^67 ≤ 8485388267429^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5005202263 10000000000 8485388267429 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (283671061/2500000000 : ℝ)^83 ≤ (134959522599/2000000000000 : ℝ)^67 := by
    have hnat : (283671061 : ℕ)^83*2000000000000^67 ≤ 134959522599^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283671061 2500000000 134959522599 2000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5790788953/10000000000 : ℝ), (5005202263/10000000000 : ℝ), (283671061/2500000000 : ℝ)] ![(5082508251503/10000000000000 : ℝ), (8485388267429/20000000000000 : ℝ), (134959522599/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5790788953/10000000000 : ℝ)|^83 ≤ (5082508251503/10000000000000 : ℝ)^67
        have hw : |(5790788953/10000000000 : ℝ)|=(5790788953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5005202263/10000000000 : ℝ)|^83 ≤ (8485388267429/20000000000000 : ℝ)^67
        have hw : |(5005202263/10000000000 : ℝ)|=(5005202263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(283671061/2500000000 : ℝ)|^83 ≤ (134959522599/2000000000000 : ℝ)^67
        have hw : |(283671061/2500000000 : ℝ)|=(283671061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322062_s1_s1_20 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1270711821/2000000000 : ℝ)*x 0 + (480099541/1000000000 : ℝ)*x 1 + (-108128121/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1270711821/2000000000 : ℝ)^83 ≤ (11402665158753/20000000000000 : ℝ)^67 := by
    have hnat : (1270711821 : ℕ)^83*20000000000000^67 ≤ 11402665158753^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1270711821 2000000000 11402665158753 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (480099541/1000000000 : ℝ)^83 ≤ (10073289353577/25000000000000 : ℝ)^67 := by
    have hnat : (480099541 : ℕ)^83*25000000000000^67 ≤ 10073289353577^67*1000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      480099541 1000000000 10073289353577 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108128121/2000000000 : ℝ)^83 ≤ (673379192463/25000000000000 : ℝ)^67 := by
    have hnat : (108128121 : ℕ)^83*25000000000000^67 ≤ 673379192463^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108128121 2000000000 673379192463 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1270711821/2000000000 : ℝ), (480099541/1000000000 : ℝ), (-108128121/2000000000 : ℝ)] ![(11402665158753/20000000000000 : ℝ), (10073289353577/25000000000000 : ℝ), (673379192463/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1270711821/2000000000 : ℝ)|^83 ≤ (11402665158753/20000000000000 : ℝ)^67
        have hw : |(1270711821/2000000000 : ℝ)|=(1270711821/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(480099541/1000000000 : ℝ)|^83 ≤ (10073289353577/25000000000000 : ℝ)^67
        have hw : |(480099541/1000000000 : ℝ)|=(480099541/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-108128121/2000000000 : ℝ)|^83 ≤ (673379192463/25000000000000 : ℝ)^67
        have hw : |(-108128121/2000000000 : ℝ)|=(108128121/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322062_s1_s1_21 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-59902283/1000000000 : ℝ)*x 0 + (5318113949/10000000000 : ℝ)*x 1 + (-5825679253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (59902283/1000000000 : ℝ)^83 ≤ (611673336057/20000000000000 : ℝ)^67 := by
    have hnat : (59902283 : ℕ)^83*20000000000000^67 ≤ 611673336057^67*1000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59902283 1000000000 611673336057 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5318113949/10000000000 : ℝ)^83 ≤ (45736921075439/100000000000000 : ℝ)^67 := by
    have hnat : (5318113949 : ℕ)^83*100000000000000^67 ≤ 45736921075439^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5318113949 10000000000 45736921075439 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5825679253/10000000000 : ℝ)^83 ≤ (25602356115511/50000000000000 : ℝ)^67 := by
    have hnat : (5825679253 : ℕ)^83*50000000000000^67 ≤ 25602356115511^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5825679253 10000000000 25602356115511 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-59902283/1000000000 : ℝ), (5318113949/10000000000 : ℝ), (-5825679253/10000000000 : ℝ)] ![(611673336057/20000000000000 : ℝ), (45736921075439/100000000000000 : ℝ), (25602356115511/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-59902283/1000000000 : ℝ)|^83 ≤ (611673336057/20000000000000 : ℝ)^67
        have hw : |(-59902283/1000000000 : ℝ)|=(59902283/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5318113949/10000000000 : ℝ)|^83 ≤ (45736921075439/100000000000000 : ℝ)^67
        have hw : |(5318113949/10000000000 : ℝ)|=(5318113949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5825679253/10000000000 : ℝ)|^83 ≤ (25602356115511/50000000000000 : ℝ)^67
        have hw : |(-5825679253/10000000000 : ℝ)|=(5825679253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322062_s1_s1_22 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2932515819/5000000000 : ℝ)*x 0 + (-569621287/5000000000 : ℝ)*x 1 + (-307803609/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2932515819/5000000000 : ℝ)^83 ≤ (12908386075093/25000000000000 : ℝ)^67 := by
    have hnat : (2932515819 : ℕ)^83*25000000000000^67 ≤ 12908386075093^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2932515819 5000000000 12908386075093 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (569621287/5000000000 : ℝ)^83 ≤ (6781574299973/100000000000000 : ℝ)^67 := by
    have hnat : (569621287 : ℕ)^83*100000000000000^67 ≤ 6781574299973^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569621287 5000000000 6781574299973 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (307803609/625000000 : ℝ)^83 ≤ (20792440693241/50000000000000 : ℝ)^67 := by
    have hnat : (307803609 : ℕ)^83*50000000000000^67 ≤ 20792440693241^67*625000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      307803609 625000000 20792440693241 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2932515819/5000000000 : ℝ), (-569621287/5000000000 : ℝ), (-307803609/625000000 : ℝ)] ![(12908386075093/25000000000000 : ℝ), (6781574299973/100000000000000 : ℝ), (20792440693241/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2932515819/5000000000 : ℝ)|^83 ≤ (12908386075093/25000000000000 : ℝ)^67
        have hw : |(2932515819/5000000000 : ℝ)|=(2932515819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-569621287/5000000000 : ℝ)|^83 ≤ (6781574299973/100000000000000 : ℝ)^67
        have hw : |(-569621287/5000000000 : ℝ)|=(569621287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-307803609/625000000 : ℝ)|^83 ≤ (20792440693241/50000000000000 : ℝ)^67
        have hw : |(-307803609/625000000 : ℝ)|=(307803609/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322062_s1_s1_23 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2372860567/5000000000 : ℝ)*x 0 + (5466550479/10000000000 : ℝ)*x 1 + (1921283927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2372860567/5000000000 : ℝ)^83 ≤ (19859634687961/50000000000000 : ℝ)^67 := by
    have hnat : (2372860567 : ℕ)^83*50000000000000^67 ≤ 19859634687961^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2372860567 5000000000 19859634687961 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5466550479/10000000000 : ℝ)^83 ≤ (47323597068463/100000000000000 : ℝ)^67 := by
    have hnat : (5466550479 : ℕ)^83*100000000000000^67 ≤ 47323597068463^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5466550479 10000000000 47323597068463 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1921283927/10000000000 : ℝ)^83 ≤ (12957133533483/100000000000000 : ℝ)^67 := by
    have hnat : (1921283927 : ℕ)^83*100000000000000^67 ≤ 12957133533483^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1921283927 10000000000 12957133533483 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2372860567/5000000000 : ℝ), (5466550479/10000000000 : ℝ), (1921283927/10000000000 : ℝ)] ![(19859634687961/50000000000000 : ℝ), (47323597068463/100000000000000 : ℝ), (12957133533483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2372860567/5000000000 : ℝ)|^83 ≤ (19859634687961/50000000000000 : ℝ)^67
        have hw : |(2372860567/5000000000 : ℝ)|=(2372860567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5466550479/10000000000 : ℝ)|^83 ≤ (47323597068463/100000000000000 : ℝ)^67
        have hw : |(5466550479/10000000000 : ℝ)|=(5466550479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1921283927/10000000000 : ℝ)|^83 ≤ (12957133533483/100000000000000 : ℝ)^67
        have hw : |(1921283927/10000000000 : ℝ)|=(1921283927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322062_s1_s1_27 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (261611567/400000000 : ℝ)*x 0 + (1124504791/2500000000 : ℝ)*x 1 + (-352057857/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (261611567/400000000 : ℝ)^83 ≤ (59096315113307/100000000000000 : ℝ)^67 := by
    have hnat : (261611567 : ℕ)^83*100000000000000^67 ≤ 59096315113307^67*400000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261611567 400000000 59096315113307 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1124504791/2500000000 : ℝ)^83 ≤ (9291818657731/25000000000000 : ℝ)^67 := by
    have hnat : (1124504791 : ℕ)^83*25000000000000^67 ≤ 9291818657731^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124504791 2500000000 9291818657731 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (352057857/5000000000 : ℝ)^83 ≤ (3736410234223/100000000000000 : ℝ)^67 := by
    have hnat : (352057857 : ℕ)^83*100000000000000^67 ≤ 3736410234223^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352057857 5000000000 3736410234223 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(261611567/400000000 : ℝ), (1124504791/2500000000 : ℝ), (-352057857/5000000000 : ℝ)] ![(59096315113307/100000000000000 : ℝ), (9291818657731/25000000000000 : ℝ), (3736410234223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(261611567/400000000 : ℝ)|^83 ≤ (59096315113307/100000000000000 : ℝ)^67
        have hw : |(261611567/400000000 : ℝ)|=(261611567/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1124504791/2500000000 : ℝ)|^83 ≤ (9291818657731/25000000000000 : ℝ)^67
        have hw : |(1124504791/2500000000 : ℝ)|=(1124504791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-352057857/5000000000 : ℝ)|^83 ≤ (3736410234223/100000000000000 : ℝ)^67
        have hw : |(-352057857/5000000000 : ℝ)|=(352057857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c322062_s1 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((14083/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14083/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17497/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(17497/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-59479/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-59479/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1439/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1439/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1451/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1451/4000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-23087/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-23087/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2522/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2522/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2522/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2522/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2522/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2522/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
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
  have s1_pow0 : (14083/20000 : ℝ) ^ (41/8 : ℝ) ≤ (1035533333837743267/6250000000000000000 : ℝ) := by
    have hpowers : (14083/20000 : ℝ)^41 ≤ (1035533333837743267/6250000000000000000 : ℝ)^8 := by
      have hnat : (14083 : ℕ)^41*6250000000000000000^8 ≤ 1035533333837743267^8*20000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14083 20000 1035533333837743267 6250000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14083/20000 : ℝ)) (X := (1035533333837743267/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (7285533333837743267/6250000000000000000 : ℝ) ≤ (5151829526100411/5000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (7285533333837743267/6250000000000000000 : ℝ)^8 ≤ (5151829526100411/5000000000000000 : ℝ)^41 := by
      have hnat : (7285533333837743267 : ℕ)^8*5000000000000000^41 ≤ 5151829526100411^41*6250000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7285533333837743267 6250000000000000000 5151829526100411 5000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5151829526100411/5000000000000000 : ℝ)) (X := (7285533333837743267/6250000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (4160533333837743267/3125000000000000000 : ℝ) ≤ (10574344627065497/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (4160533333837743267/3125000000000000000 : ℝ)^8 ≤ (10574344627065497/10000000000000000 : ℝ)^41 := by
      have hnat : (4160533333837743267 : ℕ)^8*10000000000000000^41 ≤ 10574344627065497^41*3125000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4160533333837743267 3125000000000000000 10574344627065497 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10574344627065497/10000000000000000 : ℝ)) (X := (4160533333837743267/3125000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(151829526100411/3520750000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(10827422994587/281660000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (14083/20000 : ℝ)) (alpha := (151829526100411/3520750000000000 : ℝ)) (beta := (10827422994587/281660000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (14083/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(151829526100411/3520750000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(10827422994587/281660000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (17497/25000 : ℝ) ^ (41/8 : ℝ) ≤ (16060011933229578303/100000000000000000000 : ℝ) := by
    have hpowers : (17497/25000 : ℝ)^41 ≤ (16060011933229578303/100000000000000000000 : ℝ)^8 := by
      have hnat : (17497 : ℕ)^41*100000000000000000000^8 ≤ 16060011933229578303^8*25000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17497 25000 16060011933229578303 100000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17497/25000 : ℝ)) (X := (16060011933229578303/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (116060011933229578303/100000000000000000000 : ℝ) ≤ (2573718272627449/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (116060011933229578303/100000000000000000000 : ℝ)^8 ≤ (2573718272627449/2500000000000000 : ℝ)^41 := by
      have hnat : (116060011933229578303 : ℕ)^8*2500000000000000^41 ≤ 2573718272627449^41*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        116060011933229578303 100000000000000000000 2573718272627449 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2573718272627449/2500000000000000 : ℝ)) (X := (116060011933229578303/100000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (66060011933229578303/50000000000000000000 : ℝ) ≤ (2639633591160877/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (66060011933229578303/50000000000000000000 : ℝ)^8 ≤ (2639633591160877/2500000000000000 : ℝ)^41 := by
      have hnat : (66060011933229578303 : ℕ)^8*2500000000000000^41 ≤ 2639633591160877^41*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        66060011933229578303 50000000000000000000 2639633591160877 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2639633591160877/2500000000000000 : ℝ)) (X := (66060011933229578303/50000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(73718272627449/1749700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(16478829633357/437425000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (17497/25000 : ℝ)) (alpha := (73718272627449/1749700000000000 : ℝ)) (beta := (16478829633357/437425000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (17497/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(73718272627449/1749700000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(16478829633357/437425000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (59479/100000 : ℝ) ^ (41/8 : ℝ) ≤ (69761168853285171/1000000000000000000 : ℝ) := by
    have hpowers : (59479/100000 : ℝ)^41 ≤ (69761168853285171/1000000000000000000 : ℝ)^8 := by
      have hnat : (59479 : ℕ)^41*1000000000000000000^8 ≤ 69761168853285171^8*100000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59479 100000 69761168853285171 1000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (59479/100000 : ℝ)) (X := (69761168853285171/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (1069761168853285171/1000000000000000000 : ℝ) ≤ (10132450792613141/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (1069761168853285171/1000000000000000000 : ℝ)^8 ≤ (10132450792613141/10000000000000000 : ℝ)^41 := by
      have hnat : (1069761168853285171 : ℕ)^8*10000000000000000^41 ≤ 10132450792613141^41*1000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1069761168853285171 1000000000000000000 10132450792613141 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10132450792613141/10000000000000000 : ℝ)) (X := (1069761168853285171/1000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (569761168853285171/500000000000000000 : ℝ) ≤ (1282265285318477/1250000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (569761168853285171/500000000000000000 : ℝ)^8 ≤ (1282265285318477/1250000000000000 : ℝ)^41 := by
      have hnat : (569761168853285171 : ℕ)^8*1250000000000000^41 ≤ 1282265285318477^41*500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        569761168853285171 500000000000000000 1282265285318477 1250000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1282265285318477/1250000000000000 : ℝ)) (X := (569761168853285171/500000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(132450792613141/5947900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(5026859597387/237916000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (59479/100000 : ℝ)) (alpha := (132450792613141/5947900000000000 : ℝ)) (beta := (5026859597387/237916000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (59479/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(132450792613141/5947900000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(5026859597387/237916000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-734038317/5000000000 : ℝ)*X 0 0+(2482584031/5000000000 : ℝ)*X 0 1+(-1119064521/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322062_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((621446837/1250000000 : ℝ)*X 1 0+(-146781267/1000000000 : ℝ)*X 1 1+(-279464311/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322062_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1021022973/2000000000 : ℝ)*X 2 0+(5113041153/10000000000 : ℝ)*X 2 1+(1921527671/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322062_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-565552731/5000000000 : ℝ)*X 0 0+(1137258337/2500000000 : ℝ)*X 0 1+(-6225046681/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322062_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((2485273479/5000000000 : ℝ)*X 1 0+(-450469237/5000000000 : ℝ)*X 1 1+(-5977775997/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322062_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((4875955741/10000000000 : ℝ)*X 2 0+(1186697667/2000000000 : ℝ)*X 2 1+(1107034537/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322062_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((5131456901/10000000000 : ℝ)*X 0 0+(302179087/500000000 : ℝ)*X 0 1+(-534469179/10000000000 : ℝ)*X 0 2+(5131456901/10000000000 : ℝ)*X 1 0+(302179087/500000000 : ℝ)*X 1 1+(-534469179/10000000000 : ℝ)*X 1 2+(5131456901/10000000000 : ℝ)*X 2 0+(302179087/500000000 : ℝ)*X 2 1+(-534469179/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322062_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-807309107/10000000000 : ℝ)*X 0 0+(97135343/200000000 : ℝ)*X 0 1+(-307231329/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322062_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((1169242611/2500000000 : ℝ)*X 1 0+(-124518509/1000000000 : ℝ)*X 1 1+(-753548773/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322062_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((5790788953/10000000000 : ℝ)*X 2 0+(5005202263/10000000000 : ℝ)*X 2 1+(283671061/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322062_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((1270711821/2000000000 : ℝ)*X 0 0+(480099541/1000000000 : ℝ)*X 0 1+(-108128121/2000000000 : ℝ)*X 0 2+(1270711821/2000000000 : ℝ)*X 1 0+(480099541/1000000000 : ℝ)*X 1 1+(-108128121/2000000000 : ℝ)*X 1 2+(1270711821/2000000000 : ℝ)*X 2 0+(480099541/1000000000 : ℝ)*X 2 1+(-108128121/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322062_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-59902283/1000000000 : ℝ)*X 0 0+(5318113949/10000000000 : ℝ)*X 0 1+(-5825679253/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322062_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((2932515819/5000000000 : ℝ)*X 1 0+(-569621287/5000000000 : ℝ)*X 1 1+(-307803609/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322062_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((2372860567/5000000000 : ℝ)*X 2 0+(5466550479/10000000000 : ℝ)*X 2 1+(1921283927/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322062_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((261611567/400000000 : ℝ)*X 0 0+(1124504791/2500000000 : ℝ)*X 0 1+(-352057857/5000000000 : ℝ)*X 0 2+(261611567/400000000 : ℝ)*X 1 0+(1124504791/2500000000 : ℝ)*X 1 1+(-352057857/5000000000 : ℝ)*X 1 2+(261611567/400000000 : ℝ)*X 2 0+(1124504791/2500000000 : ℝ)*X 2 1+(-352057857/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322062_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((1439/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1439/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (43329736821401889248226298394829/3664058829807250000000000000000000000 : ℝ) := by norm_num
    linear_combination (20119899579/62500000000 : ℝ)*(base39) + (81616968513/1000000000000 : ℝ)*(base49) + (226960490789/1000000000000 : ℝ)*(base60) + (6698969346513/1000000000000 : ℝ)*(major_s1_0) + (6698969346513/1000000000000 : ℝ)*(major_s1_1) + (6698969346513/1000000000000 : ℝ)*(major_s1_2) + (104511059/1000000000000 : ℝ)*(sp_s1_0) + (3892739/200000000000 : ℝ)*(sp_s1_1) + (9926681814519/1000000000000 : ℝ)*(sp_s1_7) + (4963301709569/500000000000 : ℝ)*(sp_s1_8) + (1240829625369/125000000000 : ℝ)*(sp_s1_9) + (3471148425573/1000000000000 : ℝ)*(sp_s1_13) + (20430343/125000000000 : ℝ)*(sp_s1_15) + (74661313/500000000000 : ℝ)*(sp_s1_23) + (3471148425573/1000000000000 : ℝ)*(f.failure) + (4963393162789/500000000000 : ℝ)*(f.sum) + (8095364863771404427/52035203150000000000000000000000 : ℝ)*base63 + (100321945220433/237916000000000000000000000 : ℝ)*base64 + (337129950764733/874850000000000000000000000 : ℝ)*base66 + (3048276305814263/5947900000000000000000000000 : ℝ)*base69 + (173890447356700530581/418821378500000000000000000000000 : ℝ)*base70 + (20942185142667/56332000000000000000000000 : ℝ)*base72 + (313540917201993/1749700000000000000000000000 : ℝ)*base74 + (758805784755707/3520750000000000000000000000 : ℝ)*base76 + (11264148340929890743/24641025100000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (3327/10000000000000000 : ℝ)*base87 + (3327/10000000000000000 : ℝ)*base89 + (3327/10000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1451/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1451/4000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (15885996658067548453104117483681/916014707451812500000000000000000000 : ℝ) := by norm_num
    linear_combination (277124349911/1000000000000 : ℝ)*(base39) + (163784550473/1000000000000 : ℝ)*(base49) + (927221/250000000000 : ℝ)*(base60) + (6887706442667/1000000000000 : ℝ)*(major_s1_0) + (6887706442667/1000000000000 : ℝ)*(major_s1_1) + (6887706442667/1000000000000 : ℝ)*(major_s1_2) + (32806627/1000000000000 : ℝ)*(sp_s1_2) + (106603/1600000000 : ℝ)*(sp_s1_7) + (85036857/1000000000000 : ℝ)*(sp_s1_8) + (5103197871673/500000000000 : ℝ)*(sp_s1_14) + (2551594333341/250000000000 : ℝ)*(sp_s1_15) + (5103214781797/500000000000 : ℝ)*(sp_s1_16) + (1784362341393/500000000000 : ℝ)*(sp_s1_20) + (220051483/1000000000000 : ℝ)*(sp_s1_27) + (356894473427/100000000000 : ℝ)*(f.failure) + (10206462370221/1000000000000 : ℝ)*(f.sum) + (26588598502761560213/52035203150000000000000000000000 : ℝ)*base63 + (263572002630269/1189580000000000000000000000 : ℝ)*base65 + (478787466920467/874850000000000000000000000 : ℝ)*base66 + (3571618726884217/5947900000000000000000000000 : ℝ)*base69 + (60461418590903150721/418821378500000000000000000000000 : ℝ)*base71 + (77117492974169/281660000000000000000000000 : ℝ)*base72 + (774167804381243/1749700000000000000000000000 : ℝ)*base75 + (647532628569631/1760375000000000000000000000 : ℝ)*base77 + (16407931113695331037/24641025100000000000000000000000 : ℝ)*base78 + (673/1000000000000000 : ℝ)*base87 + (673/1000000000000000 : ℝ)*base89 + (673/1000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-23087/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-23087/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6994128863890328766672049880007/916014707451812500000000000000000000 : ℝ) := by norm_num
    linear_combination (500053/250000000000 : ℝ)*(base11) + (820620986051/1000000000000 : ℝ)*(base39) + (106034335693/1000000000000 : ℝ)*(base49) + (673032137037/125000000000 : ℝ)*(major_s1_0) + (673032137037/125000000000 : ℝ)*(major_s1_1) + (673032137037/125000000000 : ℝ)*(major_s1_2) + (1781577/500000000000 : ℝ)*(sp_s1_1) + (2905537/50000000000 : ℝ)*(sp_s1_2) + (8683351/500000000000 : ℝ)*(sp_s1_9) + (29003823/1000000000000 : ℝ)*(sp_s1_20) + (1994648643961/250000000000 : ℝ)*(sp_s1_21) + (3989296506451/500000000000 : ℝ)*(sp_s1_22) + (1595704219723/200000000000 : ℝ)*(sp_s1_23) + (1394943033789/500000000000 : ℝ)*(sp_s1_27) + (2789915071401/1000000000000 : ℝ)*(f.failure) + (997324572007/125000000000 : ℝ)*(f.sum) + (11588101061277092271/52035203150000000000000000000000 : ℝ)*base62 + (75707142487941/297395000000000000000000000 : ℝ)*base64 + (472208949881759/874850000000000000000000000 : ℝ)*base67 + (1016300096946007/2973950000000000000000000000 : ℝ)*base68 + (18455093330299637113/104705344625000000000000000000000 : ℝ)*base70 + (30428273795399/140830000000000000000000000 : ℝ)*base72 + (716934140939193/874850000000000000000000000 : ℝ)*base74 + (2875222196281119/3520750000000000000000000000 : ℝ)*base76 + (52257711031665353/770032034375000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (7899/10000000000000000 : ℝ)*base87 + (7899/10000000000000000 : ℝ)*base89 + (7899/10000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((14083/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14083/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17497/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(17497/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-59479/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-59479/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1439/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1439/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1451/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1451/4000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-23087/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-23087/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c322062_s1 p hpa hpb X hX hprev0

#print axioms solution
