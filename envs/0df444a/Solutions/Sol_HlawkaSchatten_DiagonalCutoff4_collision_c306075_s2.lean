-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c306075_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:59:07.918998+00:00
-- url     : https://prove2.me/submissions/50b010f8-2f98-4808-bcf4-ec4d99f24ee4

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
theorem collision_support_c306075_s2_s2_0 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-736599789/5000000000 : ℝ)*x 0 + (-1507431299/2500000000 : ℝ)*x 1 + (500317997/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (736599789/5000000000 : ℝ)^135 ≤ (8125637023387/100000000000000 : ℝ)^103 := by
    have hnat : (736599789 : ℕ)^135*100000000000000^103 ≤ 8125637023387^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      736599789 5000000000 8125637023387 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1507431299/2500000000 : ℝ)^135 ≤ (51527662123313/100000000000000 : ℝ)^103 := by
    have hnat : (1507431299 : ℕ)^135*100000000000000^103 ≤ 51527662123313^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1507431299 2500000000 51527662123313 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (500317997/1000000000 : ℝ)^135 ≤ (40346700846243/100000000000000 : ℝ)^103 := by
    have hnat : (500317997 : ℕ)^135*100000000000000^103 ≤ 40346700846243^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500317997 1000000000 40346700846243 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-736599789/5000000000 : ℝ), (-1507431299/2500000000 : ℝ), (500317997/1000000000 : ℝ)] ![(8125637023387/100000000000000 : ℝ), (51527662123313/100000000000000 : ℝ), (40346700846243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-736599789/5000000000 : ℝ)|^135 ≤ (8125637023387/100000000000000 : ℝ)^103
        have hw : |(-736599789/5000000000 : ℝ)|=(736599789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1507431299/2500000000 : ℝ)|^135 ≤ (51527662123313/100000000000000 : ℝ)^103
        have hw : |(-1507431299/2500000000 : ℝ)|=(1507431299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(500317997/1000000000 : ℝ)|^135 ≤ (40346700846243/100000000000000 : ℝ)^103
        have hw : |(500317997/1000000000 : ℝ)|=(500317997/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306075_s2_s2_2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2586208619/5000000000 : ℝ)*x 0 + (-4124495447/10000000000 : ℝ)*x 1 + (-908427843/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2586208619/5000000000 : ℝ)^135 ≤ (21072398865311/50000000000000 : ℝ)^103 := by
    have hnat : (2586208619 : ℕ)^135*50000000000000^103 ≤ 21072398865311^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586208619 5000000000 21072398865311 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4124495447/10000000000 : ℝ)^135 ≤ (7830948999877/25000000000000 : ℝ)^103 := by
    have hnat : (4124495447 : ℕ)^135*25000000000000^103 ≤ 7830948999877^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4124495447 10000000000 7830948999877 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (908427843/2500000000 : ℝ)^135 ≤ (13265703130583/50000000000000 : ℝ)^103 := by
    have hnat : (908427843 : ℕ)^135*50000000000000^103 ≤ 13265703130583^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      908427843 2500000000 13265703130583 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2586208619/5000000000 : ℝ), (-4124495447/10000000000 : ℝ), (-908427843/2500000000 : ℝ)] ![(21072398865311/50000000000000 : ℝ), (7830948999877/25000000000000 : ℝ), (13265703130583/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2586208619/5000000000 : ℝ)|^135 ≤ (21072398865311/50000000000000 : ℝ)^103
        have hw : |(2586208619/5000000000 : ℝ)|=(2586208619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4124495447/10000000000 : ℝ)|^135 ≤ (7830948999877/25000000000000 : ℝ)^103
        have hw : |(-4124495447/10000000000 : ℝ)|=(4124495447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-908427843/2500000000 : ℝ)|^135 ≤ (13265703130583/50000000000000 : ℝ)^103
        have hw : |(-908427843/2500000000 : ℝ)|=(908427843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306075_s2_s2_6 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3266920517/10000000000 : ℝ)*x 0 + (-2793545243/10000000000 : ℝ)*x 1 + (6610281887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3266920517/10000000000 : ℝ)^135 ≤ (23077636450229/100000000000000 : ℝ)^103 := by
    have hnat : (3266920517 : ℕ)^135*100000000000000^103 ≤ 23077636450229^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3266920517 10000000000 23077636450229 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2793545243/10000000000 : ℝ)^135 ≤ (9398479199857/50000000000000 : ℝ)^103 := by
    have hnat : (2793545243 : ℕ)^135*50000000000000^103 ≤ 9398479199857^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2793545243 10000000000 9398479199857 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6610281887/10000000000 : ℝ)^135 ≤ (11625081027259/20000000000000 : ℝ)^103 := by
    have hnat : (6610281887 : ℕ)^135*20000000000000^103 ≤ 11625081027259^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6610281887 10000000000 11625081027259 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3266920517/10000000000 : ℝ), (-2793545243/10000000000 : ℝ), (6610281887/10000000000 : ℝ)] ![(23077636450229/100000000000000 : ℝ), (9398479199857/50000000000000 : ℝ), (11625081027259/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3266920517/10000000000 : ℝ)|^135 ≤ (23077636450229/100000000000000 : ℝ)^103
        have hw : |(3266920517/10000000000 : ℝ)|=(3266920517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2793545243/10000000000 : ℝ)|^135 ≤ (9398479199857/50000000000000 : ℝ)^103
        have hw : |(-2793545243/10000000000 : ℝ)|=(2793545243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6610281887/10000000000 : ℝ)|^135 ≤ (11625081027259/20000000000000 : ℝ)^103
        have hw : |(6610281887/10000000000 : ℝ)|=(6610281887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306075_s2_s2_7 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-24219783/200000000 : ℝ)*x 0 + (-107045933/156250000 : ℝ)*x 1 + (2136025003/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (24219783/200000000 : ℝ)^135 ≤ (6284787841893/100000000000000 : ℝ)^103 := by
    have hnat : (24219783 : ℕ)^135*100000000000000^103 ≤ 6284787841893^103*200000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24219783 200000000 6284787841893 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107045933/156250000 : ℝ)^135 ≤ (15228638361971/25000000000000 : ℝ)^103 := by
    have hnat : (107045933 : ℕ)^135*25000000000000^103 ≤ 15228638361971^103*156250000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107045933 156250000 15228638361971 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2136025003/5000000000 : ℝ)^135 ≤ (16400329353163/50000000000000 : ℝ)^103 := by
    have hnat : (2136025003 : ℕ)^135*50000000000000^103 ≤ 16400329353163^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136025003 5000000000 16400329353163 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-24219783/200000000 : ℝ), (-107045933/156250000 : ℝ), (2136025003/5000000000 : ℝ)] ![(6284787841893/100000000000000 : ℝ), (15228638361971/25000000000000 : ℝ), (16400329353163/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-24219783/200000000 : ℝ)|^135 ≤ (6284787841893/100000000000000 : ℝ)^103
        have hw : |(-24219783/200000000 : ℝ)|=(24219783/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-107045933/156250000 : ℝ)|^135 ≤ (15228638361971/25000000000000 : ℝ)^103
        have hw : |(-107045933/156250000 : ℝ)|=(107045933/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2136025003/5000000000 : ℝ)|^135 ≤ (16400329353163/50000000000000 : ℝ)^103
        have hw : |(2136025003/5000000000 : ℝ)|=(2136025003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306075_s2_s2_8 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (32431751/50000000 : ℝ)*x 0 + (3195498203/10000000000 : ℝ)*x 1 + (1513392027/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (32431751/50000000 : ℝ)^135 ≤ (56701264946469/100000000000000 : ℝ)^103 := by
    have hnat : (32431751 : ℕ)^135*100000000000000^103 ≤ 56701264946469^103*50000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32431751 50000000 56701264946469 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3195498203/10000000000 : ℝ)^135 ≤ (5604654222007/25000000000000 : ℝ)^103 := by
    have hnat : (3195498203 : ℕ)^135*25000000000000^103 ≤ 5604654222007^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3195498203 10000000000 5604654222007 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1513392027/5000000000 : ℝ)^135 ≤ (10440059075557/50000000000000 : ℝ)^103 := by
    have hnat : (1513392027 : ℕ)^135*50000000000000^103 ≤ 10440059075557^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1513392027 5000000000 10440059075557 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(32431751/50000000 : ℝ), (3195498203/10000000000 : ℝ), (1513392027/5000000000 : ℝ)] ![(56701264946469/100000000000000 : ℝ), (5604654222007/25000000000000 : ℝ), (10440059075557/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(32431751/50000000 : ℝ)|^135 ≤ (56701264946469/100000000000000 : ℝ)^103
        have hw : |(32431751/50000000 : ℝ)|=(32431751/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3195498203/10000000000 : ℝ)|^135 ≤ (5604654222007/25000000000000 : ℝ)^103
        have hw : |(3195498203/10000000000 : ℝ)|=(3195498203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1513392027/5000000000 : ℝ)|^135 ≤ (10440059075557/50000000000000 : ℝ)^103
        have hw : |(1513392027/5000000000 : ℝ)|=(1513392027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306075_s2_s2_9 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1353921597/2500000000 : ℝ)*x 0 + (-1959155059/5000000000 : ℝ)*x 1 + (-3572894277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1353921597/2500000000 : ℝ)^135 ≤ (11190386610399/25000000000000 : ℝ)^103 := by
    have hnat : (1353921597 : ℕ)^135*25000000000000^103 ≤ 11190386610399^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353921597 2500000000 11190386610399 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1959155059/5000000000 : ℝ)^135 ≤ (3660942549123/12500000000000 : ℝ)^103 := by
    have hnat : (1959155059 : ℕ)^135*12500000000000^103 ≤ 3660942549123^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1959155059 5000000000 3660942549123 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3572894277/10000000000 : ℝ)^135 ≤ (12975456570851/50000000000000 : ℝ)^103 := by
    have hnat : (3572894277 : ℕ)^135*50000000000000^103 ≤ 12975456570851^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3572894277 10000000000 12975456570851 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1353921597/2500000000 : ℝ), (-1959155059/5000000000 : ℝ), (-3572894277/10000000000 : ℝ)] ![(11190386610399/25000000000000 : ℝ), (3660942549123/12500000000000 : ℝ), (12975456570851/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1353921597/2500000000 : ℝ)|^135 ≤ (11190386610399/25000000000000 : ℝ)^103
        have hw : |(1353921597/2500000000 : ℝ)|=(1353921597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1959155059/5000000000 : ℝ)|^135 ≤ (3660942549123/12500000000000 : ℝ)^103
        have hw : |(-1959155059/5000000000 : ℝ)|=(1959155059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3572894277/10000000000 : ℝ)|^135 ≤ (12975456570851/50000000000000 : ℝ)^103
        have hw : |(-3572894277/10000000000 : ℝ)|=(3572894277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306075_s2_s2_13 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1054849923/5000000000 : ℝ)*x 0 + (-1738574589/10000000000 : ℝ)*x 1 + (8183562093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054849923/5000000000 : ℝ)^135 ≤ (325244394543/2500000000000 : ℝ)^103 := by
    have hnat : (1054849923 : ℕ)^135*2500000000000^103 ≤ 325244394543^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054849923 5000000000 325244394543 2500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1738574589/10000000000 : ℝ)^135 ≤ (10095710438589/100000000000000 : ℝ)^103 := by
    have hnat : (1738574589 : ℕ)^135*100000000000000^103 ≤ 10095710438589^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1738574589 10000000000 10095710438589 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8183562093/10000000000 : ℝ)^135 ≤ (76894513759279/100000000000000 : ℝ)^103 := by
    have hnat : (8183562093 : ℕ)^135*100000000000000^103 ≤ 76894513759279^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8183562093 10000000000 76894513759279 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1054849923/5000000000 : ℝ), (-1738574589/10000000000 : ℝ), (8183562093/10000000000 : ℝ)] ![(325244394543/2500000000000 : ℝ), (10095710438589/100000000000000 : ℝ), (76894513759279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1054849923/5000000000 : ℝ)|^135 ≤ (325244394543/2500000000000 : ℝ)^103
        have hw : |(1054849923/5000000000 : ℝ)|=(1054849923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1738574589/10000000000 : ℝ)|^135 ≤ (10095710438589/100000000000000 : ℝ)^103
        have hw : |(-1738574589/10000000000 : ℝ)|=(1738574589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8183562093/10000000000 : ℝ)|^135 ≤ (76894513759279/100000000000000 : ℝ)^103
        have hw : |(8183562093/10000000000 : ℝ)|=(8183562093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306075_s2_s2_14 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-439744809/5000000000 : ℝ)*x 0 + (-2925478219/5000000000 : ℝ)*x 1 + (5560130287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (439744809/5000000000 : ℝ)^135 ≤ (4132612893919/100000000000000 : ℝ)^103 := by
    have hnat : (439744809 : ℕ)^135*100000000000000^103 ≤ 4132612893919^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      439744809 5000000000 4132612893919 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2925478219/5000000000 : ℝ)^135 ≤ (49534638443323/100000000000000 : ℝ)^103 := by
    have hnat : (2925478219 : ℕ)^135*100000000000000^103 ≤ 49534638443323^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2925478219 5000000000 49534638443323 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5560130287/10000000000 : ℝ)^135 ≤ (46332748657431/100000000000000 : ℝ)^103 := by
    have hnat : (5560130287 : ℕ)^135*100000000000000^103 ≤ 46332748657431^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5560130287 10000000000 46332748657431 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-439744809/5000000000 : ℝ), (-2925478219/5000000000 : ℝ), (5560130287/10000000000 : ℝ)] ![(4132612893919/100000000000000 : ℝ), (49534638443323/100000000000000 : ℝ), (46332748657431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-439744809/5000000000 : ℝ)|^135 ≤ (4132612893919/100000000000000 : ℝ)^103
        have hw : |(-439744809/5000000000 : ℝ)|=(439744809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2925478219/5000000000 : ℝ)|^135 ≤ (49534638443323/100000000000000 : ℝ)^103
        have hw : |(-2925478219/5000000000 : ℝ)|=(2925478219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5560130287/10000000000 : ℝ)|^135 ≤ (46332748657431/100000000000000 : ℝ)^103
        have hw : |(5560130287/10000000000 : ℝ)|=(5560130287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306075_s2_s2_15 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1788664353/2500000000 : ℝ)*x 0 + (735802883/2500000000 : ℝ)*x 1 + (95949239/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1788664353/2500000000 : ℝ)^135 ≤ (16119537247611/25000000000000 : ℝ)^103 := by
    have hnat : (1788664353 : ℕ)^135*25000000000000^103 ≤ 16119537247611^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1788664353 2500000000 16119537247611 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (735802883/2500000000 : ℝ)^135 ≤ (20127745804937/100000000000000 : ℝ)^103 := by
    have hnat : (735802883 : ℕ)^135*100000000000000^103 ≤ 20127745804937^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      735802883 2500000000 20127745804937 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (95949239/400000000 : ℝ)^135 ≤ (3848526298039/25000000000000 : ℝ)^103 := by
    have hnat : (95949239 : ℕ)^135*25000000000000^103 ≤ 3848526298039^103*400000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95949239 400000000 3848526298039 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1788664353/2500000000 : ℝ), (735802883/2500000000 : ℝ), (95949239/400000000 : ℝ)] ![(16119537247611/25000000000000 : ℝ), (20127745804937/100000000000000 : ℝ), (3848526298039/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1788664353/2500000000 : ℝ)|^135 ≤ (16119537247611/25000000000000 : ℝ)^103
        have hw : |(1788664353/2500000000 : ℝ)|=(1788664353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(735802883/2500000000 : ℝ)|^135 ≤ (20127745804937/100000000000000 : ℝ)^103
        have hw : |(735802883/2500000000 : ℝ)|=(735802883/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(95949239/400000000 : ℝ)|^135 ≤ (3848526298039/25000000000000 : ℝ)^103
        have hw : |(95949239/400000000 : ℝ)|=(95949239/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306075_s2_s2_16 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (282104233/500000000 : ℝ)*x 0 + (-2078976731/5000000000 : ℝ)*x 1 + (-305249021/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (282104233/500000000 : ℝ)^135 ≤ (23614945837101/50000000000000 : ℝ)^103 := by
    have hnat : (282104233 : ℕ)^135*50000000000000^103 ≤ 23614945837101^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282104233 500000000 23614945837101 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2078976731/5000000000 : ℝ)^135 ≤ (3165725786643/10000000000000 : ℝ)^103 := by
    have hnat : (2078976731 : ℕ)^135*10000000000000^103 ≤ 3165725786643^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078976731 5000000000 3165725786643 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (305249021/1000000000 : ℝ)^135 ≤ (263910630661/1250000000000 : ℝ)^103 := by
    have hnat : (305249021 : ℕ)^135*1250000000000^103 ≤ 263910630661^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      305249021 1000000000 263910630661 1250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(282104233/500000000 : ℝ), (-2078976731/5000000000 : ℝ), (-305249021/1000000000 : ℝ)] ![(23614945837101/50000000000000 : ℝ), (3165725786643/10000000000000 : ℝ), (263910630661/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(282104233/500000000 : ℝ)|^135 ≤ (23614945837101/50000000000000 : ℝ)^103
        have hw : |(282104233/500000000 : ℝ)|=(282104233/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2078976731/5000000000 : ℝ)|^135 ≤ (3165725786643/10000000000000 : ℝ)^103
        have hw : |(-2078976731/5000000000 : ℝ)|=(2078976731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-305249021/1000000000 : ℝ)|^135 ≤ (263910630661/1250000000000 : ℝ)^103
        have hw : |(-305249021/1000000000 : ℝ)|=(305249021/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306075_s2_s2_20 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2339758897/10000000000 : ℝ)*x 0 + (-1954307639/10000000000 : ℝ)*x 1 + (7892636379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2339758897/10000000000 : ℝ)^135 ≤ (14899971303549/100000000000000 : ℝ)^103 := by
    have hnat : (2339758897 : ℕ)^135*100000000000000^103 ≤ 14899971303549^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2339758897 10000000000 14899971303549 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1954307639/10000000000 : ℝ)^135 ≤ (147105496893/1250000000000 : ℝ)^103 := by
    have hnat : (1954307639 : ℕ)^135*1250000000000^103 ≤ 147105496893^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1954307639 10000000000 147105496893 1250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7892636379/10000000000 : ℝ)^135 ≤ (18332897232759/25000000000000 : ℝ)^103 := by
    have hnat : (7892636379 : ℕ)^135*25000000000000^103 ≤ 18332897232759^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7892636379 10000000000 18332897232759 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2339758897/10000000000 : ℝ), (-1954307639/10000000000 : ℝ), (7892636379/10000000000 : ℝ)] ![(14899971303549/100000000000000 : ℝ), (147105496893/1250000000000 : ℝ), (18332897232759/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2339758897/10000000000 : ℝ)|^135 ≤ (14899971303549/100000000000000 : ℝ)^103
        have hw : |(2339758897/10000000000 : ℝ)|=(2339758897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1954307639/10000000000 : ℝ)|^135 ≤ (147105496893/1250000000000 : ℝ)^103
        have hw : |(-1954307639/10000000000 : ℝ)|=(1954307639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7892636379/10000000000 : ℝ)|^135 ≤ (18332897232759/25000000000000 : ℝ)^103
        have hw : |(7892636379/10000000000 : ℝ)|=(7892636379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306075_s2_s2_21 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-12866967/156250000 : ℝ)*x 0 + (-1335391237/2000000000 : ℝ)*x 1 + (2356797763/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (12866967/156250000 : ℝ)^135 ≤ (236947786331/6250000000000 : ℝ)^103 := by
    have hnat : (12866967 : ℕ)^135*6250000000000^103 ≤ 236947786331^103*156250000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12866967 156250000 236947786331 6250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1335391237/2000000000 : ℝ)^135 ≤ (58895030501873/100000000000000 : ℝ)^103 := by
    have hnat : (1335391237 : ℕ)^135*100000000000000^103 ≤ 58895030501873^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1335391237 2000000000 58895030501873 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2356797763/5000000000 : ℝ)^135 ≤ (7462760979033/20000000000000 : ℝ)^103 := by
    have hnat : (2356797763 : ℕ)^135*20000000000000^103 ≤ 7462760979033^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2356797763 5000000000 7462760979033 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-12866967/156250000 : ℝ), (-1335391237/2000000000 : ℝ), (2356797763/5000000000 : ℝ)] ![(236947786331/6250000000000 : ℝ), (58895030501873/100000000000000 : ℝ), (7462760979033/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-12866967/156250000 : ℝ)|^135 ≤ (236947786331/6250000000000 : ℝ)^103
        have hw : |(-12866967/156250000 : ℝ)|=(12866967/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1335391237/2000000000 : ℝ)|^135 ≤ (58895030501873/100000000000000 : ℝ)^103
        have hw : |(-1335391237/2000000000 : ℝ)|=(1335391237/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2356797763/5000000000 : ℝ)|^135 ≤ (7462760979033/20000000000000 : ℝ)^103
        have hw : |(2356797763/5000000000 : ℝ)|=(2356797763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306075_s2_s2_22 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1442132067/2000000000 : ℝ)*x 0 + (2762147567/10000000000 : ℝ)*x 1 + (156891819/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1442132067/2000000000 : ℝ)^135 ≤ (16285113392379/25000000000000 : ℝ)^103 := by
    have hnat : (1442132067 : ℕ)^135*25000000000000^103 ≤ 16285113392379^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1442132067 2000000000 16285113392379 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2762147567/10000000000 : ℝ)^135 ≤ (148164329713/800000000000 : ℝ)^103 := by
    have hnat : (2762147567 : ℕ)^135*800000000000^103 ≤ 148164329713^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2762147567 10000000000 148164329713 800000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (156891819/625000000 : ℝ)^135 ≤ (4084751298921/25000000000000 : ℝ)^103 := by
    have hnat : (156891819 : ℕ)^135*25000000000000^103 ≤ 4084751298921^103*625000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156891819 625000000 4084751298921 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1442132067/2000000000 : ℝ), (2762147567/10000000000 : ℝ), (156891819/625000000 : ℝ)] ![(16285113392379/25000000000000 : ℝ), (148164329713/800000000000 : ℝ), (4084751298921/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1442132067/2000000000 : ℝ)|^135 ≤ (16285113392379/25000000000000 : ℝ)^103
        have hw : |(1442132067/2000000000 : ℝ)|=(1442132067/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2762147567/10000000000 : ℝ)|^135 ≤ (148164329713/800000000000 : ℝ)^103
        have hw : |(2762147567/10000000000 : ℝ)|=(2762147567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(156891819/625000000 : ℝ)|^135 ≤ (4084751298921/25000000000000 : ℝ)^103
        have hw : |(156891819/625000000 : ℝ)|=(156891819/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306075_s2_s2_23 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (614078489/1250000000 : ℝ)*x 0 + (-4293513699/10000000000 : ℝ)*x 1 + (-3743904241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (614078489/1250000000 : ℝ)^135 ≤ (9848076046637/25000000000000 : ℝ)^103 := by
    have hnat : (614078489 : ℕ)^135*25000000000000^103 ≤ 9848076046637^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      614078489 1250000000 9848076046637 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4293513699/10000000000 : ℝ)^135 ≤ (33016823845421/100000000000000 : ℝ)^103 := by
    have hnat : (4293513699 : ℕ)^135*100000000000000^103 ≤ 33016823845421^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4293513699 10000000000 33016823845421 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3743904241/10000000000 : ℝ)^135 ≤ (27590871947601/100000000000000 : ℝ)^103 := by
    have hnat : (3743904241 : ℕ)^135*100000000000000^103 ≤ 27590871947601^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3743904241 10000000000 27590871947601 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(614078489/1250000000 : ℝ), (-4293513699/10000000000 : ℝ), (-3743904241/10000000000 : ℝ)] ![(9848076046637/25000000000000 : ℝ), (33016823845421/100000000000000 : ℝ), (27590871947601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(614078489/1250000000 : ℝ)|^135 ≤ (9848076046637/25000000000000 : ℝ)^103
        have hw : |(614078489/1250000000 : ℝ)|=(614078489/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4293513699/10000000000 : ℝ)|^135 ≤ (33016823845421/100000000000000 : ℝ)^103
        have hw : |(-4293513699/10000000000 : ℝ)|=(4293513699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3743904241/10000000000 : ℝ)|^135 ≤ (27590871947601/100000000000000 : ℝ)^103
        have hw : |(-3743904241/10000000000 : ℝ)|=(3743904241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306075_s2_s2_27 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1929873957/5000000000 : ℝ)*x 0 + (-2222272203/10000000000 : ℝ)*x 1 + (1308713851/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1929873957/5000000000 : ℝ)^135 ≤ (28715159541593/100000000000000 : ℝ)^103 := by
    have hnat : (1929873957 : ℕ)^135*100000000000000^103 ≤ 28715159541593^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1929873957 5000000000 28715159541593 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2222272203/10000000000 : ℝ)^135 ≤ (13927093091729/100000000000000 : ℝ)^103 := by
    have hnat : (2222272203 : ℕ)^135*100000000000000^103 ≤ 13927093091729^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2222272203 10000000000 13927093091729 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1308713851/2000000000 : ℝ)^135 ≤ (14339436839907/25000000000000 : ℝ)^103 := by
    have hnat : (1308713851 : ℕ)^135*25000000000000^103 ≤ 14339436839907^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308713851 2000000000 14339436839907 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1929873957/5000000000 : ℝ), (-2222272203/10000000000 : ℝ), (1308713851/2000000000 : ℝ)] ![(28715159541593/100000000000000 : ℝ), (13927093091729/100000000000000 : ℝ), (14339436839907/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1929873957/5000000000 : ℝ)|^135 ≤ (28715159541593/100000000000000 : ℝ)^103
        have hw : |(1929873957/5000000000 : ℝ)|=(1929873957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2222272203/10000000000 : ℝ)|^135 ≤ (13927093091729/100000000000000 : ℝ)^103
        have hw : |(-2222272203/10000000000 : ℝ)|=(2222272203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1308713851/2000000000 : ℝ)|^135 ≤ (14339436839907/25000000000000 : ℝ)^103
        have hw : |(1308713851/2000000000 : ℝ)|=(1308713851/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c306075_s2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((59909/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(59909/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-81471/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-81471/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6263/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6263/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((21517/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(21517/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-39579/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-39579/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(26877/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(26877/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (38461/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (38461/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (38461/50000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (38461/50000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (38461/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (38461/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s2_pow0 : (59909/100000 : ℝ) ^ (67/16 : ℝ) ≤ (5850837674175690889/50000000000000000000 : ℝ) := by
    have hpowers : (59909/100000 : ℝ)^67 ≤ (5850837674175690889/50000000000000000000 : ℝ)^16 := by
      have hnat : (59909 : ℕ)^67*50000000000000000000^16 ≤ 5850837674175690889^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59909 100000 5850837674175690889 50000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (59909/100000 : ℝ)) (X := (5850837674175690889/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (55850837674175690889/50000000000000000000 : ℝ) ≤ (5133894555379907/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (55850837674175690889/50000000000000000000 : ℝ)^16 ≤ (5133894555379907/5000000000000000 : ℝ)^67 := by
      have hnat : (55850837674175690889 : ℕ)^16*5000000000000000^67 ≤ 5133894555379907^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55850837674175690889 50000000000000000000 5133894555379907 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5133894555379907/5000000000000000 : ℝ)) (X := (55850837674175690889/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (30850837674175690889/25000000000000000000 : ℝ) ≤ (10515003494937247/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (30850837674175690889/25000000000000000000 : ℝ)^16 ≤ (10515003494937247/10000000000000000 : ℝ)^67 := by
      have hnat : (30850837674175690889 : ℕ)^16*10000000000000000^67 ≤ 10515003494937247^67*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30850837674175690889 25000000000000000000 10515003494937247 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10515003494937247/10000000000000000 : ℝ)) (X := (30850837674175690889/25000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(133894555379907/2995450000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(247214384177433/5990900000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (59909/100000 : ℝ)) (alpha := (133894555379907/2995450000000000 : ℝ)) (beta := (247214384177433/5990900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (59909/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(133894555379907/2995450000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(247214384177433/5990900000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (81471/100000 : ℝ) ^ (67/16 : ℝ) ≤ (10599009172868932343/25000000000000000000 : ℝ) := by
    have hpowers : (81471/100000 : ℝ)^67 ≤ (10599009172868932343/25000000000000000000 : ℝ)^16 := by
      have hnat : (81471 : ℕ)^67*25000000000000000000^16 ≤ 10599009172868932343^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        81471 100000 10599009172868932343 25000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (81471/100000 : ℝ)) (X := (10599009172868932343/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (35599009172868932343/25000000000000000000 : ℝ) ≤ (10880684445143159/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (35599009172868932343/25000000000000000000 : ℝ)^16 ≤ (10880684445143159/10000000000000000 : ℝ)^67 := by
      have hnat : (35599009172868932343 : ℕ)^16*10000000000000000^67 ≤ 10880684445143159^67*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35599009172868932343 25000000000000000000 10880684445143159 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10880684445143159/10000000000000000 : ℝ)) (X := (35599009172868932343/25000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (23099009172868932343/12500000000000000000 : ℝ) ≤ (11579387117324597/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (23099009172868932343/12500000000000000000 : ℝ)^16 ≤ (11579387117324597/10000000000000000 : ℝ)^67 := by
      have hnat : (23099009172868932343 : ℕ)^16*10000000000000000^67 ≤ 11579387117324597^67*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23099009172868932343 12500000000000000000 11579387117324597 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11579387117324597/10000000000000000 : ℝ)) (X := (23099009172868932343/12500000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(880684445143159/8147100000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(116450445363573/1357850000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (81471/100000 : ℝ)) (alpha := (880684445143159/8147100000000000 : ℝ)) (beta := (116450445363573/1357850000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (81471/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(880684445143159/8147100000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(116450445363573/1357850000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (6263/10000 : ℝ) ^ (67/16 : ℝ) ≤ (563749721485041737/4000000000000000000 : ℝ) := by
    have hpowers : (6263/10000 : ℝ)^67 ≤ (563749721485041737/4000000000000000000 : ℝ)^16 := by
      have hnat : (6263 : ℕ)^67*4000000000000000000^16 ≤ 563749721485041737^16*10000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6263 10000 563749721485041737 4000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6263/10000 : ℝ)) (X := (563749721485041737/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (4563749721485041737/4000000000000000000 : ℝ) ≤ (161248057831173/156250000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (4563749721485041737/4000000000000000000 : ℝ)^16 ≤ (161248057831173/156250000000000 : ℝ)^67 := by
      have hnat : (4563749721485041737 : ℕ)^16*156250000000000^67 ≤ 161248057831173^67*4000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4563749721485041737 4000000000000000000 161248057831173 156250000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (161248057831173/156250000000000 : ℝ)) (X := (4563749721485041737/4000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (2563749721485041737/2000000000000000000 : ℝ) ≤ (5305473929012327/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (2563749721485041737/2000000000000000000 : ℝ)^16 ≤ (5305473929012327/5000000000000000 : ℝ)^67 := by
      have hnat : (2563749721485041737 : ℕ)^16*5000000000000000^67 ≤ 5305473929012327^67*2000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2563749721485041737 2000000000000000000 5305473929012327 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5305473929012327/5000000000000000 : ℝ)) (X := (2563749721485041737/2000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(4998057831173/97859375000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(145536078414791/3131500000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (6263/10000 : ℝ)) (alpha := (4998057831173/97859375000000 : ℝ)) (beta := (145536078414791/3131500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (6263/10000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(4998057831173/97859375000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(145536078414791/3131500000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-736599789/5000000000 : ℝ)*X 0 0+(-1507431299/2500000000 : ℝ)*X 0 1+(500317997/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306075_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((2586208619/5000000000 : ℝ)*X 2 0+(-4124495447/10000000000 : ℝ)*X 2 1+(-908427843/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306075_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((3266920517/10000000000 : ℝ)*X 0 0+(-2793545243/10000000000 : ℝ)*X 0 1+(6610281887/10000000000 : ℝ)*X 0 2+(3266920517/10000000000 : ℝ)*X 1 0+(-2793545243/10000000000 : ℝ)*X 1 1+(6610281887/10000000000 : ℝ)*X 1 2+(3266920517/10000000000 : ℝ)*X 2 0+(-2793545243/10000000000 : ℝ)*X 2 1+(6610281887/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306075_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-24219783/200000000 : ℝ)*X 0 0+(-107045933/156250000 : ℝ)*X 0 1+(2136025003/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306075_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((32431751/50000000 : ℝ)*X 1 0+(3195498203/10000000000 : ℝ)*X 1 1+(1513392027/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306075_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((1353921597/2500000000 : ℝ)*X 2 0+(-1959155059/5000000000 : ℝ)*X 2 1+(-3572894277/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306075_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((1054849923/5000000000 : ℝ)*X 0 0+(-1738574589/10000000000 : ℝ)*X 0 1+(8183562093/10000000000 : ℝ)*X 0 2+(1054849923/5000000000 : ℝ)*X 1 0+(-1738574589/10000000000 : ℝ)*X 1 1+(8183562093/10000000000 : ℝ)*X 1 2+(1054849923/5000000000 : ℝ)*X 2 0+(-1738574589/10000000000 : ℝ)*X 2 1+(8183562093/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306075_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-439744809/5000000000 : ℝ)*X 0 0+(-2925478219/5000000000 : ℝ)*X 0 1+(5560130287/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306075_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((1788664353/2500000000 : ℝ)*X 1 0+(735802883/2500000000 : ℝ)*X 1 1+(95949239/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306075_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((282104233/500000000 : ℝ)*X 2 0+(-2078976731/5000000000 : ℝ)*X 2 1+(-305249021/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306075_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((2339758897/10000000000 : ℝ)*X 0 0+(-1954307639/10000000000 : ℝ)*X 0 1+(7892636379/10000000000 : ℝ)*X 0 2+(2339758897/10000000000 : ℝ)*X 1 0+(-1954307639/10000000000 : ℝ)*X 1 1+(7892636379/10000000000 : ℝ)*X 1 2+(2339758897/10000000000 : ℝ)*X 2 0+(-1954307639/10000000000 : ℝ)*X 2 1+(7892636379/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306075_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-12866967/156250000 : ℝ)*X 0 0+(-1335391237/2000000000 : ℝ)*X 0 1+(2356797763/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306075_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((1442132067/2000000000 : ℝ)*X 1 0+(2762147567/10000000000 : ℝ)*X 1 1+(156891819/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306075_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((614078489/1250000000 : ℝ)*X 2 0+(-4293513699/10000000000 : ℝ)*X 2 1+(-3743904241/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306075_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((1929873957/5000000000 : ℝ)*X 0 0+(-2222272203/10000000000 : ℝ)*X 0 1+(1308713851/2000000000 : ℝ)*X 0 2+(1929873957/5000000000 : ℝ)*X 1 0+(-2222272203/10000000000 : ℝ)*X 1 1+(1308713851/2000000000 : ℝ)*X 1 2+(1929873957/5000000000 : ℝ)*X 2 0+(-2222272203/10000000000 : ℝ)*X 2 1+(1308713851/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306075_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((21517/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(21517/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (20971497881980413832725464126103/1273697473689875000000000000000000000 : ℝ) := by norm_num
    linear_combination (479585984301/1000000000000 : ℝ)*(base40) + (5902669/1000000000000 : ℝ)*(base49) + (37152026257/1000000000000 : ℝ)*(base60) + (4726999064909/1000000000000 : ℝ)*(major_s2_0) + (4726999064909/1000000000000 : ℝ)*(major_s2_1) + (4726999064909/1000000000000 : ℝ)*(major_s2_2) + (27812179/1000000000000 : ℝ)*(sp_s2_0) + (165825389/500000000000 : ℝ)*(sp_s2_2) + (1597044768443/250000000000 : ℝ)*(sp_s2_7) + (1277643110173/200000000000 : ℝ)*(sp_s2_8) + (6387791762363/1000000000000 : ℝ)*(sp_s2_9) + (1532888545299/500000000000 : ℝ)*(sp_s2_13) + (4332457/500000000000 : ℝ)*(sp_s2_21) + (23034431/250000000000 : ℝ)*(sp_s2_23) + (1532888545299/500000000000 : ℝ)*(f.failure) + (1277643110173/200000000000 : ℝ)*(f.sum) + (28955484214237458221/42521072750000000000000000000000 : ℝ)*base62 + (359461743569981/3131500000000000000000000000 : ℝ)*base65 + (2963907635936869/8147100000000000000000000000 : ℝ)*base66 + (179205941296997/391437500000000000000000000 : ℝ)*base68 + (102441412107614071131/187605033500000000000000000000000 : ℝ)*base70 + (87617912826563/5990900000000000000000000000 : ℝ)*base72 + (922543144769997/1357850000000000000000000000 : ℝ)*base74 + (360890848530127/2995450000000000000000000000 : ℝ)*base76 + (12484406073226633037/61010576737500000000000000000000 : ℝ)*base79 + (10807/25000000000000000 : ℝ)*base87 + (10807/25000000000000000 : ℝ)*base89 + (10807/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-39579/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-39579/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (338772797440942789403707107/81347435650000000000000000000000 : ℝ) := by norm_num
    linear_combination (944637/500000000000 : ℝ)*(base13) + (849221/1000000000000 : ℝ)*(base39) + (1322125063999/1000000000000 : ℝ)*(base40) + (2187131/1000000000000 : ℝ)*(base49) + (597619/250000000000 : ℝ)*(base59) + (435413007781/1000000000000 : ℝ)*(base60) + (6443034784891/1000000000000 : ℝ)*(major_s2_0) + (6443034784891/1000000000000 : ℝ)*(major_s2_1) + (6443034784891/1000000000000 : ℝ)*(major_s2_2) + (30077639/500000000000 : ℝ)*(sp_s2_0) + (2176816091861/250000000000 : ℝ)*(sp_s2_14) + (2176831602999/250000000000 : ℝ)*(sp_s2_15) + (2176831602999/250000000000 : ℝ)*(sp_s2_16) + (417874176961/100000000000 : ℝ)*(sp_s2_20) + (417874176961/100000000000 : ℝ)*(f.failure) + (2176831602999/250000000000 : ℝ)*(f.sum) + (762735278262118679/42521072750000000000000000000000 : ℝ)*base62 + (86949400010281/3131500000000000000000000000 : ℝ)*base64 + (1422784166721289/8147100000000000000000000000 : ℝ)*base67 + (439388011016069/782875000000000000000000000 : ℝ)*base69 + (152390509414100318681/187605033500000000000000000000000 : ℝ)*base71 + (2427250971791297/5990900000000000000000000000 : ℝ)*base72 + (112912790426593/1357850000000000000000000000 : ℝ)*base74 + (933655361856527/2995450000000000000000000000 : ℝ)*base77 + (138827340918333588683/244042306950000000000000000000000 : ℝ)*base78 + (627/5000000000000000 : ℝ)*base86 + (627/5000000000000000 : ℝ)*base88 + (627/5000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(26877/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(26877/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (12207477651829071548118235249671/2547394947379750000000000000000000000 : ℝ) := by norm_num
    linear_combination (332317214283/250000000000 : ℝ)*(base40) + (2026813/1000000000000 : ℝ)*(base49) + (2878056536153/500000000000 : ℝ)*(major_s2_0) + (2878056536153/500000000000 : ℝ)*(major_s2_1) + (2878056536153/500000000000 : ℝ)*(major_s2_2) + (7547649/200000000000 : ℝ)*(sp_s2_0) + (34529833/1000000000000 : ℝ)*(sp_s2_6) + (24835019/500000000000 : ℝ)*(sp_s2_7) + (12383629/200000000000 : ℝ)*(sp_s2_15) + (291089/500000000000 : ℝ)*(sp_s2_16) + (1555782067989/200000000000 : ℝ)*(sp_s2_21) + (1944733957521/250000000000 : ℝ)*(sp_s2_22) + (155579943321/20000000000 : ℝ)*(sp_s2_23) + (3733192269167/1000000000000 : ℝ)*(sp_s2_27) + (3733226799/1000000000 : ℝ)*(f.failure) + (1944749437057/250000000000 : ℝ)*(f.sum) + (2475794791650099811/42521072750000000000000000000000 : ℝ)*base63 + (153962946227737/391437500000000000000000000 : ℝ)*base64 + (783162069385907/4073550000000000000000000000 : ℝ)*base67 + (523191639557917/1565750000000000000000000000 : ℝ)*base68 + (29619007510596831577/93802516750000000000000000000000 : ℝ)*base70 + (111219683574117/1497725000000000000000000000 : ℝ)*base73 + (589835884048147/1357850000000000000000000000 : ℝ)*base75 + (83755956972793/187215625000000000000000000 : ℝ)*base76 + (1876313341448498387/61010576737500000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (7/50000000000000 : ℝ)*base87 + (7/50000000000000 : ℝ)*base89 + (7/50000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((59909/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(59909/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-81471/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-81471/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6263/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6263/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((21517/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(21517/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-39579/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-39579/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(26877/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(26877/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c306075_s2 p hpa hpb X hX hprev1

#print axioms solution
