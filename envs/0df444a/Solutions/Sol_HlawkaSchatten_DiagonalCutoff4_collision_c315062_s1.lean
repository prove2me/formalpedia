-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c315062_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:56:47.854045+00:00
-- url     : https://prove2.me/submissions/6038013c-ff0c-4914-866d-c69bf6f85634

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
theorem collision_support_c315062_s1_s1_0 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-130094583/1000000000 : ℝ)*x 0 + (5017521353/10000000000 : ℝ)*x 1 + (-2924771743/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (130094583/1000000000 : ℝ)^19 ≤ (755199459179/10000000000000 : ℝ)^15 := by
    have hnat : (130094583 : ℕ)^19*10000000000000^15 ≤ 755199459179^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130094583 1000000000 755199459179 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5017521353/10000000000 : ℝ)^19 ≤ (41746463489991/100000000000000 : ℝ)^15 := by
    have hnat : (5017521353 : ℕ)^19*100000000000000^15 ≤ 41746463489991^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5017521353 10000000000 41746463489991 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2924771743/5000000000 : ℝ)^19 ≤ (50701541893969/100000000000000 : ℝ)^15 := by
    have hnat : (2924771743 : ℕ)^19*100000000000000^15 ≤ 50701541893969^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2924771743 5000000000 50701541893969 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-130094583/1000000000 : ℝ), (5017521353/10000000000 : ℝ), (-2924771743/5000000000 : ℝ)] ![(755199459179/10000000000000 : ℝ), (41746463489991/100000000000000 : ℝ), (50701541893969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-130094583/1000000000 : ℝ)|^19 ≤ (755199459179/10000000000000 : ℝ)^15
        have hw : |(-130094583/1000000000 : ℝ)|=(130094583/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5017521353/10000000000 : ℝ)|^19 ≤ (41746463489991/100000000000000 : ℝ)^15
        have hw : |(5017521353/10000000000 : ℝ)|=(5017521353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2924771743/5000000000 : ℝ)|^19 ≤ (50701541893969/100000000000000 : ℝ)^15
        have hw : |(-2924771743/5000000000 : ℝ)|=(2924771743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315062_s1_s1_1 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (63024357/125000000 : ℝ)*x 0 + (-81884559/625000000 : ℝ)*x 1 + (-2909944057/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (63024357/125000000 : ℝ)^19 ≤ (21002032409087/50000000000000 : ℝ)^15 := by
    have hnat : (63024357 : ℕ)^19*50000000000000^15 ≤ 21002032409087^15*125000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63024357 125000000 21002032409087 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81884559/625000000 : ℝ)^19 ≤ (1904939577759/25000000000000 : ℝ)^15 := by
    have hnat : (81884559 : ℕ)^19*25000000000000^15 ≤ 1904939577759^15*625000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81884559 625000000 1904939577759 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2909944057/5000000000 : ℝ)^19 ≤ (25188088428803/50000000000000 : ℝ)^15 := by
    have hnat : (2909944057 : ℕ)^19*50000000000000^15 ≤ 25188088428803^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2909944057 5000000000 25188088428803 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(63024357/125000000 : ℝ), (-81884559/625000000 : ℝ), (-2909944057/5000000000 : ℝ)] ![(21002032409087/50000000000000 : ℝ), (1904939577759/25000000000000 : ℝ), (25188088428803/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(63024357/125000000 : ℝ)|^19 ≤ (21002032409087/50000000000000 : ℝ)^15
        have hw : |(63024357/125000000 : ℝ)|=(63024357/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-81884559/625000000 : ℝ)|^19 ≤ (1904939577759/25000000000000 : ℝ)^15
        have hw : |(-81884559/625000000 : ℝ)|=(81884559/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2909944057/5000000000 : ℝ)|^19 ≤ (25188088428803/50000000000000 : ℝ)^15
        have hw : |(-2909944057/5000000000 : ℝ)|=(2909944057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315062_s1_s1_2 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5252323299/10000000000 : ℝ)*x 0 + (528147667/1000000000 : ℝ)*x 1 + (444445727/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5252323299/10000000000 : ℝ)^19 ≤ (22118135200419/50000000000000 : ℝ)^15 := by
    have hnat : (5252323299 : ℕ)^19*50000000000000^15 ≤ 22118135200419^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252323299 10000000000 22118135200419 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528147667/1000000000 : ℝ)^19 ≤ (44547512998933/100000000000000 : ℝ)^15 := by
    have hnat : (528147667 : ℕ)^19*100000000000000^15 ≤ 44547512998933^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528147667 1000000000 44547512998933 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (444445727/2500000000 : ℝ)^19 ≤ (11216216583717/100000000000000 : ℝ)^15 := by
    have hnat : (444445727 : ℕ)^19*100000000000000^15 ≤ 11216216583717^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      444445727 2500000000 11216216583717 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5252323299/10000000000 : ℝ), (528147667/1000000000 : ℝ), (444445727/2500000000 : ℝ)] ![(22118135200419/50000000000000 : ℝ), (44547512998933/100000000000000 : ℝ), (11216216583717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5252323299/10000000000 : ℝ)|^19 ≤ (22118135200419/50000000000000 : ℝ)^15
        have hw : |(5252323299/10000000000 : ℝ)|=(5252323299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(528147667/1000000000 : ℝ)|^19 ≤ (44547512998933/100000000000000 : ℝ)^15
        have hw : |(528147667/1000000000 : ℝ)|=(528147667/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(444445727/2500000000 : ℝ)|^19 ≤ (11216216583717/100000000000000 : ℝ)^15
        have hw : |(444445727/2500000000 : ℝ)|=(444445727/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315062_s1_s1_7 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-311578171/2500000000 : ℝ)*x 0 + (3907119159/10000000000 : ℝ)*x 1 + (-6894591873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (311578171/2500000000 : ℝ)^19 ≤ (447034357687/6250000000000 : ℝ)^15 := by
    have hnat : (311578171 : ℕ)^19*6250000000000^15 ≤ 447034357687^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      311578171 2500000000 447034357687 6250000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3907119159/10000000000 : ℝ)^19 ≤ (30410140843757/100000000000000 : ℝ)^15 := by
    have hnat : (3907119159 : ℕ)^19*100000000000000^15 ≤ 30410140843757^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3907119159 10000000000 30410140843757 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6894591873/10000000000 : ℝ)^19 ≤ (12487461883419/20000000000000 : ℝ)^15 := by
    have hnat : (6894591873 : ℕ)^19*20000000000000^15 ≤ 12487461883419^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6894591873 10000000000 12487461883419 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-311578171/2500000000 : ℝ), (3907119159/10000000000 : ℝ), (-6894591873/10000000000 : ℝ)] ![(447034357687/6250000000000 : ℝ), (30410140843757/100000000000000 : ℝ), (12487461883419/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-311578171/2500000000 : ℝ)|^19 ≤ (447034357687/6250000000000 : ℝ)^15
        have hw : |(-311578171/2500000000 : ℝ)|=(311578171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3907119159/10000000000 : ℝ)|^19 ≤ (30410140843757/100000000000000 : ℝ)^15
        have hw : |(3907119159/10000000000 : ℝ)|=(3907119159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6894591873/10000000000 : ℝ)|^19 ≤ (12487461883419/20000000000000 : ℝ)^15
        have hw : |(-6894591873/10000000000 : ℝ)|=(6894591873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315062_s1_s1_8 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4318907159/10000000000 : ℝ)*x 0 + (-16326947/250000000 : ℝ)*x 1 + (-6884345481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4318907159/10000000000 : ℝ)^19 ≤ (6905104078327/20000000000000 : ℝ)^15 := by
    have hnat : (4318907159 : ℕ)^19*20000000000000^15 ≤ 6905104078327^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4318907159 10000000000 6905104078327 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16326947/250000000 : ℝ)^19 ≤ (98583823011/3125000000000 : ℝ)^15 := by
    have hnat : (16326947 : ℕ)^19*3125000000000^15 ≤ 98583823011^15*250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16326947 250000000 98583823011 3125000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6884345481/10000000000 : ℝ)^19 ≤ (31159898625877/50000000000000 : ℝ)^15 := by
    have hnat : (6884345481 : ℕ)^19*50000000000000^15 ≤ 31159898625877^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6884345481 10000000000 31159898625877 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4318907159/10000000000 : ℝ), (-16326947/250000000 : ℝ), (-6884345481/10000000000 : ℝ)] ![(6905104078327/20000000000000 : ℝ), (98583823011/3125000000000 : ℝ), (31159898625877/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4318907159/10000000000 : ℝ)|^19 ≤ (6905104078327/20000000000000 : ℝ)^15
        have hw : |(4318907159/10000000000 : ℝ)|=(4318907159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-16326947/250000000 : ℝ)|^19 ≤ (98583823011/3125000000000 : ℝ)^15
        have hw : |(-16326947/250000000 : ℝ)|=(16326947/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6884345481/10000000000 : ℝ)|^19 ≤ (31159898625877/50000000000000 : ℝ)^15
        have hw : |(-6884345481/10000000000 : ℝ)|=(6884345481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315062_s1_s1_9 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2152578029/5000000000 : ℝ)*x 0 + (6679562037/10000000000 : ℝ)*x 1 + (516045257/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2152578029/5000000000 : ℝ)^19 ≤ (17193169427447/50000000000000 : ℝ)^15 := by
    have hnat : (2152578029 : ℕ)^19*50000000000000^15 ≤ 17193169427447^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152578029 5000000000 17193169427447 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6679562037/10000000000 : ℝ)^19 ≤ (59981057426981/100000000000000 : ℝ)^15 := by
    have hnat : (6679562037 : ℕ)^19*100000000000000^15 ≤ 59981057426981^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6679562037 10000000000 59981057426981 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (516045257/5000000000 : ℝ)^19 ≤ (2816301850277/50000000000000 : ℝ)^15 := by
    have hnat : (516045257 : ℕ)^19*50000000000000^15 ≤ 2816301850277^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516045257 5000000000 2816301850277 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2152578029/5000000000 : ℝ), (6679562037/10000000000 : ℝ), (516045257/5000000000 : ℝ)] ![(17193169427447/50000000000000 : ℝ), (59981057426981/100000000000000 : ℝ), (2816301850277/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2152578029/5000000000 : ℝ)|^19 ≤ (17193169427447/50000000000000 : ℝ)^15
        have hw : |(2152578029/5000000000 : ℝ)|=(2152578029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6679562037/10000000000 : ℝ)|^19 ≤ (59981057426981/100000000000000 : ℝ)^15
        have hw : |(6679562037/10000000000 : ℝ)|=(6679562037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(516045257/5000000000 : ℝ)|^19 ≤ (2816301850277/50000000000000 : ℝ)^15
        have hw : |(516045257/5000000000 : ℝ)|=(516045257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315062_s1_s1_13 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (291249473/625000000 : ℝ)*x 0 + (3418505601/5000000000 : ℝ)*x 1 + (-19045661/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (291249473/625000000 : ℝ)^19 ≤ (19007478303473/50000000000000 : ℝ)^15 := by
    have hnat : (291249473 : ℕ)^19*50000000000000^15 ≤ 19007478303473^15*625000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      291249473 625000000 19007478303473 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3418505601/5000000000 : ℝ)^19 ≤ (15444385899007/25000000000000 : ℝ)^15 := by
    have hnat : (3418505601 : ℕ)^19*25000000000000^15 ≤ 15444385899007^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3418505601 5000000000 15444385899007 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (19045661/2500000000 : ℝ)^19 ≤ (41499957113/20000000000000 : ℝ)^15 := by
    have hnat : (19045661 : ℕ)^19*20000000000000^15 ≤ 41499957113^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19045661 2500000000 41499957113 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(291249473/625000000 : ℝ), (3418505601/5000000000 : ℝ), (-19045661/2500000000 : ℝ)] ![(19007478303473/50000000000000 : ℝ), (15444385899007/25000000000000 : ℝ), (41499957113/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(291249473/625000000 : ℝ)|^19 ≤ (19007478303473/50000000000000 : ℝ)^15
        have hw : |(291249473/625000000 : ℝ)|=(291249473/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3418505601/5000000000 : ℝ)|^19 ≤ (15444385899007/25000000000000 : ℝ)^15
        have hw : |(3418505601/5000000000 : ℝ)|=(3418505601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-19045661/2500000000 : ℝ)|^19 ≤ (41499957113/20000000000000 : ℝ)^15
        have hw : |(-19045661/2500000000 : ℝ)|=(19045661/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315062_s1_s1_14 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-323782397/5000000000 : ℝ)*x 0 + (534541791/1250000000 : ℝ)*x 1 + (-3462399157/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (323782397/5000000000 : ℝ)^19 ≤ (3120987941903/100000000000000 : ℝ)^15 := by
    have hnat : (323782397 : ℕ)^19*100000000000000^15 ≤ 3120987941903^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323782397 5000000000 3120987941903 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (534541791/1250000000 : ℝ)^19 ≤ (6819001000161/20000000000000 : ℝ)^15 := by
    have hnat : (534541791 : ℕ)^19*20000000000000^15 ≤ 6819001000161^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534541791 1250000000 6819001000161 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3462399157/5000000000 : ℝ)^19 ≤ (62784007043599/100000000000000 : ℝ)^15 := by
    have hnat : (3462399157 : ℕ)^19*100000000000000^15 ≤ 62784007043599^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3462399157 5000000000 62784007043599 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-323782397/5000000000 : ℝ), (534541791/1250000000 : ℝ), (-3462399157/5000000000 : ℝ)] ![(3120987941903/100000000000000 : ℝ), (6819001000161/20000000000000 : ℝ), (62784007043599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-323782397/5000000000 : ℝ)|^19 ≤ (3120987941903/100000000000000 : ℝ)^15
        have hw : |(-323782397/5000000000 : ℝ)|=(323782397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(534541791/1250000000 : ℝ)|^19 ≤ (6819001000161/20000000000000 : ℝ)^15
        have hw : |(534541791/1250000000 : ℝ)|=(534541791/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3462399157/5000000000 : ℝ)|^19 ≤ (62784007043599/100000000000000 : ℝ)^15
        have hw : |(-3462399157/5000000000 : ℝ)|=(3462399157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315062_s1_s1_15 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3878813243/10000000000 : ℝ)*x 0 + (-62661981/500000000 : ℝ)*x 1 + (-6914495511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3878813243/10000000000 : ℝ)^19 ≤ (30131348482281/100000000000000 : ℝ)^15 := by
    have hnat : (3878813243 : ℕ)^19*100000000000000^15 ≤ 30131348482281^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3878813243 10000000000 30131348482281 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (62661981/500000000 : ℝ)^19 ≤ (112545959119/1562500000000 : ℝ)^15 := by
    have hnat : (62661981 : ℕ)^19*1562500000000^15 ≤ 112545959119^15*500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62661981 500000000 112545959119 1562500000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6914495511/10000000000 : ℝ)^19 ≤ (62665710121357/100000000000000 : ℝ)^15 := by
    have hnat : (6914495511 : ℕ)^19*100000000000000^15 ≤ 62665710121357^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6914495511 10000000000 62665710121357 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3878813243/10000000000 : ℝ), (-62661981/500000000 : ℝ), (-6914495511/10000000000 : ℝ)] ![(30131348482281/100000000000000 : ℝ), (112545959119/1562500000000 : ℝ), (62665710121357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3878813243/10000000000 : ℝ)|^19 ≤ (30131348482281/100000000000000 : ℝ)^15
        have hw : |(3878813243/10000000000 : ℝ)|=(3878813243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-62661981/500000000 : ℝ)|^19 ≤ (112545959119/1562500000000 : ℝ)^15
        have hw : |(-62661981/500000000 : ℝ)|=(62661981/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6914495511/10000000000 : ℝ)|^19 ≤ (62665710121357/100000000000000 : ℝ)^15
        have hw : |(-6914495511/10000000000 : ℝ)|=(6914495511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315062_s1_s1_16 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (257643749/400000000 : ℝ)*x 0 + (1140463343/2500000000 : ℝ)*x 1 + (1043934793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (257643749/400000000 : ℝ)^19 ≤ (7160206210871/12500000000000 : ℝ)^15 := by
    have hnat : (257643749 : ℕ)^19*12500000000000^15 ≤ 7160206210871^15*400000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257643749 400000000 7160206210871 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1140463343/2500000000 : ℝ)^19 ≤ (18501872288177/50000000000000 : ℝ)^15 := by
    have hnat : (1140463343 : ℕ)^19*50000000000000^15 ≤ 18501872288177^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1140463343 2500000000 18501872288177 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043934793/10000000000 : ℝ)^19 ≤ (1428651430079/25000000000000 : ℝ)^15 := by
    have hnat : (1043934793 : ℕ)^19*25000000000000^15 ≤ 1428651430079^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043934793 10000000000 1428651430079 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(257643749/400000000 : ℝ), (1140463343/2500000000 : ℝ), (1043934793/10000000000 : ℝ)] ![(7160206210871/12500000000000 : ℝ), (18501872288177/50000000000000 : ℝ), (1428651430079/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(257643749/400000000 : ℝ)|^19 ≤ (7160206210871/12500000000000 : ℝ)^15
        have hw : |(257643749/400000000 : ℝ)|=(257643749/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1140463343/2500000000 : ℝ)|^19 ≤ (18501872288177/50000000000000 : ℝ)^15
        have hw : |(1140463343/2500000000 : ℝ)|=(1140463343/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043934793/10000000000 : ℝ)|^19 ≤ (1428651430079/25000000000000 : ℝ)^15
        have hw : |(1043934793/10000000000 : ℝ)|=(1043934793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315062_s1_s1_20 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3668046577/5000000000 : ℝ)*x 0 + (2044350613/5000000000 : ℝ)*x 1 + (-43344759/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3668046577/5000000000 : ℝ)^19 ≤ (67544313813919/100000000000000 : ℝ)^15 := by
    have hnat : (3668046577 : ℕ)^19*100000000000000^15 ≤ 67544313813919^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3668046577 5000000000 67544313813919 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2044350613/5000000000 : ℝ)^19 ≤ (8052822976803/25000000000000 : ℝ)^15 := by
    have hnat : (2044350613 : ℕ)^19*25000000000000^15 ≤ 8052822976803^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2044350613 5000000000 8052822976803 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43344759/5000000000 : ℝ)^19 ≤ (122197132873/50000000000000 : ℝ)^15 := by
    have hnat : (43344759 : ℕ)^19*50000000000000^15 ≤ 122197132873^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43344759 5000000000 122197132873 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3668046577/5000000000 : ℝ), (2044350613/5000000000 : ℝ), (-43344759/5000000000 : ℝ)] ![(67544313813919/100000000000000 : ℝ), (8052822976803/25000000000000 : ℝ), (122197132873/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3668046577/5000000000 : ℝ)|^19 ≤ (67544313813919/100000000000000 : ℝ)^15
        have hw : |(3668046577/5000000000 : ℝ)|=(3668046577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2044350613/5000000000 : ℝ)|^19 ≤ (8052822976803/25000000000000 : ℝ)^15
        have hw : |(2044350613/5000000000 : ℝ)|=(2044350613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-43344759/5000000000 : ℝ)|^19 ≤ (122197132873/50000000000000 : ℝ)^15
        have hw : |(-43344759/5000000000 : ℝ)|=(43344759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315062_s1_s1_21 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-95236093/5000000000 : ℝ)*x 0 + (5862374453/10000000000 : ℝ)*x 1 + (-5647640719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (95236093/5000000000 : ℝ)^19 ≤ (662399481361/100000000000000 : ℝ)^15 := by
    have hnat : (95236093 : ℕ)^19*100000000000000^15 ≤ 662399481361^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95236093 5000000000 662399481361 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5862374453/10000000000 : ℝ)^19 ≤ (50842453853073/100000000000000 : ℝ)^15 := by
    have hnat : (5862374453 : ℕ)^19*100000000000000^15 ≤ 50842453853073^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5862374453 10000000000 50842453853073 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5647640719/10000000000 : ℝ)^19 ≤ (3030946665773/6250000000000 : ℝ)^15 := by
    have hnat : (5647640719 : ℕ)^19*6250000000000^15 ≤ 3030946665773^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5647640719 10000000000 3030946665773 6250000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-95236093/5000000000 : ℝ), (5862374453/10000000000 : ℝ), (-5647640719/10000000000 : ℝ)] ![(662399481361/100000000000000 : ℝ), (50842453853073/100000000000000 : ℝ), (3030946665773/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-95236093/5000000000 : ℝ)|^19 ≤ (662399481361/100000000000000 : ℝ)^15
        have hw : |(-95236093/5000000000 : ℝ)|=(95236093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5862374453/10000000000 : ℝ)|^19 ≤ (50842453853073/100000000000000 : ℝ)^15
        have hw : |(5862374453/10000000000 : ℝ)|=(5862374453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5647640719/10000000000 : ℝ)|^19 ≤ (3030946665773/6250000000000 : ℝ)^15
        have hw : |(-5647640719/10000000000 : ℝ)|=(5647640719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315062_s1_s1_22 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (784678831/1250000000 : ℝ)*x 0 + (-295004387/5000000000 : ℝ)*x 1 + (-2510436847/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (784678831/1250000000 : ℝ)^19 ≤ (27722162652769/50000000000000 : ℝ)^15 := by
    have hnat : (784678831 : ℕ)^19*50000000000000^15 ≤ 27722162652769^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      784678831 1250000000 27722162652769 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (295004387/5000000000 : ℝ)^19 ≤ (1386939125483/50000000000000 : ℝ)^15 := by
    have hnat : (295004387 : ℕ)^19*50000000000000^15 ≤ 1386939125483^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      295004387 5000000000 1386939125483 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2510436847/5000000000 : ℝ)^19 ≤ (41781796421549/100000000000000 : ℝ)^15 := by
    have hnat : (2510436847 : ℕ)^19*100000000000000^15 ≤ 41781796421549^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2510436847 5000000000 41781796421549 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(784678831/1250000000 : ℝ), (-295004387/5000000000 : ℝ), (-2510436847/5000000000 : ℝ)] ![(27722162652769/50000000000000 : ℝ), (1386939125483/50000000000000 : ℝ), (41781796421549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(784678831/1250000000 : ℝ)|^19 ≤ (27722162652769/50000000000000 : ℝ)^15
        have hw : |(784678831/1250000000 : ℝ)|=(784678831/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-295004387/5000000000 : ℝ)|^19 ≤ (1386939125483/50000000000000 : ℝ)^15
        have hw : |(-295004387/5000000000 : ℝ)|=(295004387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2510436847/5000000000 : ℝ)|^19 ≤ (41781796421549/100000000000000 : ℝ)^15
        have hw : |(-2510436847/5000000000 : ℝ)|=(2510436847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315062_s1_s1_23 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (891571011/2000000000 : ℝ)*x 0 + (6131529797/10000000000 : ℝ)*x 1 + (1655027837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (891571011/2000000000 : ℝ)^19 ≤ (449230817469/1250000000000 : ℝ)^15 := by
    have hnat : (891571011 : ℕ)^19*1250000000000^15 ≤ 449230817469^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      891571011 2000000000 449230817469 1250000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6131529797/10000000000 : ℝ)^19 ≤ (53817130117597/100000000000000 : ℝ)^15 := by
    have hnat : (6131529797 : ℕ)^19*100000000000000^15 ≤ 53817130117597^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6131529797 10000000000 53817130117597 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1655027837/10000000000 : ℝ)^19 ≤ (5122202234823/50000000000000 : ℝ)^15 := by
    have hnat : (1655027837 : ℕ)^19*50000000000000^15 ≤ 5122202234823^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1655027837 10000000000 5122202234823 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(891571011/2000000000 : ℝ), (6131529797/10000000000 : ℝ), (1655027837/10000000000 : ℝ)] ![(449230817469/1250000000000 : ℝ), (53817130117597/100000000000000 : ℝ), (5122202234823/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(891571011/2000000000 : ℝ)|^19 ≤ (449230817469/1250000000000 : ℝ)^15
        have hw : |(891571011/2000000000 : ℝ)|=(891571011/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6131529797/10000000000 : ℝ)|^19 ≤ (53817130117597/100000000000000 : ℝ)^15
        have hw : |(6131529797/10000000000 : ℝ)|=(6131529797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1655027837/10000000000 : ℝ)|^19 ≤ (5122202234823/50000000000000 : ℝ)^15
        have hw : |(1655027837/10000000000 : ℝ)|=(1655027837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315062_s1_s1_27 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1916651819/2500000000 : ℝ)*x 0 + (1814614601/5000000000 : ℝ)*x 1 + (-47725709/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1916651819/2500000000 : ℝ)^19 ≤ (71421791818219/100000000000000 : ℝ)^15 := by
    have hnat : (1916651819 : ℕ)^19*100000000000000^15 ≤ 71421791818219^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1916651819 2500000000 71421791818219 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1814614601/5000000000 : ℝ)^19 ≤ (27696925902713/100000000000000 : ℝ)^15 := by
    have hnat : (1814614601 : ℕ)^19*100000000000000^15 ≤ 27696925902713^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1814614601 5000000000 27696925902713 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (47725709/2000000000 : ℝ)^19 ≤ (220320566741/25000000000000 : ℝ)^15 := by
    have hnat : (47725709 : ℕ)^19*25000000000000^15 ≤ 220320566741^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47725709 2000000000 220320566741 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1916651819/2500000000 : ℝ), (1814614601/5000000000 : ℝ), (-47725709/2000000000 : ℝ)] ![(71421791818219/100000000000000 : ℝ), (27696925902713/100000000000000 : ℝ), (220320566741/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1916651819/2500000000 : ℝ)|^19 ≤ (71421791818219/100000000000000 : ℝ)^15
        have hw : |(1916651819/2500000000 : ℝ)|=(1916651819/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1814614601/5000000000 : ℝ)|^19 ≤ (27696925902713/100000000000000 : ℝ)^15
        have hw : |(1814614601/5000000000 : ℝ)|=(1814614601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-47725709/2000000000 : ℝ)|^19 ≤ (220320566741/25000000000000 : ℝ)^15
        have hw : |(-47725709/2000000000 : ℝ)|=(47725709/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c315062_s1 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((40027/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(40027/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79381/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(79381/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-68807/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-68807/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((14007/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14007/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(56327/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(56327/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-4063/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-4063/10000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (15821/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (15821/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (15821/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (15821/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15821/20000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15821/20000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (34911/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
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
  have s1_pow0 : (40027/50000 : ℝ) ^ (75/16 : ℝ) ≤ (7049169946996539227/20000000000000000000 : ℝ) := by
    have hpowers : (40027/50000 : ℝ)^75 ≤ (7049169946996539227/20000000000000000000 : ℝ)^16 := by
      have hnat : (40027 : ℕ)^75*20000000000000000000^16 ≤ 7049169946996539227^16*50000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        40027 50000 7049169946996539227 20000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (40027/50000 : ℝ)) (X := (7049169946996539227/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (27049169946996539227/20000000000000000000 : ℝ) ≤ (5332650400415769/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (27049169946996539227/20000000000000000000 : ℝ)^16 ≤ (5332650400415769/5000000000000000 : ℝ)^75 := by
      have hnat : (27049169946996539227 : ℕ)^16*5000000000000000^75 ≤ 5332650400415769^75*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27049169946996539227 20000000000000000000 5332650400415769 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5332650400415769/5000000000000000 : ℝ)) (X := (27049169946996539227/20000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (17049169946996539227/10000000000000000000 : ℝ) ≤ (2241093727990929/2000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (17049169946996539227/10000000000000000000 : ℝ)^16 ≤ (2241093727990929/2000000000000000 : ℝ)^75 := by
      have hnat : (17049169946996539227 : ℕ)^16*2000000000000000^75 ≤ 2241093727990929^75*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17049169946996539227 10000000000000000000 2241093727990929 2000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2241093727990929/2000000000000000 : ℝ)) (X := (17049169946996539227/10000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(332650400415769/4002700000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(41551372240239/615800000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (40027/50000 : ℝ)) (alpha := (332650400415769/4002700000000000 : ℝ)) (beta := (41551372240239/615800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (40027/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(332650400415769/4002700000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(41551372240239/615800000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (79381/100000 : ℝ) ^ (75/16 : ℝ) ≤ (33878283763563494527/100000000000000000000 : ℝ) := by
    have hpowers : (79381/100000 : ℝ)^75 ≤ (33878283763563494527/100000000000000000000 : ℝ)^16 := by
      have hnat : (79381 : ℕ)^75*100000000000000000000^16 ≤ 33878283763563494527^16*100000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        79381 100000 33878283763563494527 100000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (79381/100000 : ℝ)) (X := (33878283763563494527/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (133878283763563494527/100000000000000000000 : ℝ) ≤ (10642201944284427/10000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (133878283763563494527/100000000000000000000 : ℝ)^16 ≤ (10642201944284427/10000000000000000 : ℝ)^75 := by
      have hnat : (133878283763563494527 : ℕ)^16*10000000000000000^75 ≤ 10642201944284427^75*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        133878283763563494527 100000000000000000000 10642201944284427 10000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10642201944284427/10000000000000000 : ℝ)) (X := (133878283763563494527/100000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (83878283763563494527/50000000000000000000 : ℝ) ≤ (11166874450313833/10000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (83878283763563494527/50000000000000000000 : ℝ)^16 ≤ (11166874450313833/10000000000000000 : ℝ)^75 := by
      have hnat : (83878283763563494527 : ℕ)^16*10000000000000000^75 ≤ 11166874450313833^75*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        83878283763563494527 50000000000000000000 11166874450313833 10000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11166874450313833/10000000000000000 : ℝ)) (X := (83878283763563494527/50000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(642201944284427/7938100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(262336253014703/3969050000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (79381/100000 : ℝ)) (alpha := (642201944284427/7938100000000000 : ℝ)) (beta := (262336253014703/3969050000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (79381/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(642201944284427/7938100000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(262336253014703/3969050000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (68807/100000 : ℝ) ^ (75/16 : ℝ) ≤ (4333541187821854251/25000000000000000000 : ℝ) := by
    have hpowers : (68807/100000 : ℝ)^75 ≤ (4333541187821854251/25000000000000000000 : ℝ)^16 := by
      have hnat : (68807 : ℕ)^75*25000000000000000000^16 ≤ 4333541187821854251^16*100000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        68807 100000 4333541187821854251 25000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (68807/100000 : ℝ)) (X := (4333541187821854251/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (29333541187821854251/25000000000000000000 : ℝ) ≤ (5173453636520773/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (29333541187821854251/25000000000000000000 : ℝ)^16 ≤ (5173453636520773/5000000000000000 : ℝ)^75 := by
      have hnat : (29333541187821854251 : ℕ)^16*5000000000000000^75 ≤ 5173453636520773^75*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29333541187821854251 25000000000000000000 5173453636520773 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5173453636520773/5000000000000000 : ℝ)) (X := (29333541187821854251/25000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (16833541187821854251/12500000000000000000 : ℝ) ≤ (10655568718639593/10000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (16833541187821854251/12500000000000000000 : ℝ)^16 ≤ (10655568718639593/10000000000000000 : ℝ)^75 := by
      have hnat : (16833541187821854251 : ℕ)^16*10000000000000000^75 ≤ 10655568718639593^75*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16833541187821854251 12500000000000000000 10655568718639593 10000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10655568718639593/10000000000000000 : ℝ)) (X := (16833541187821854251/12500000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(173453636520773/3440350000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(308661445598047/6880700000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (68807/100000 : ℝ)) (alpha := (173453636520773/3440350000000000 : ℝ)) (beta := (308661445598047/6880700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (68807/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(173453636520773/3440350000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(308661445598047/6880700000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-130094583/1000000000 : ℝ)*X 0 0+(5017521353/10000000000 : ℝ)*X 0 1+(-2924771743/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315062_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((63024357/125000000 : ℝ)*X 1 0+(-81884559/625000000 : ℝ)*X 1 1+(-2909944057/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315062_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5252323299/10000000000 : ℝ)*X 2 0+(528147667/1000000000 : ℝ)*X 2 1+(444445727/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315062_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-311578171/2500000000 : ℝ)*X 0 0+(3907119159/10000000000 : ℝ)*X 0 1+(-6894591873/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315062_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((4318907159/10000000000 : ℝ)*X 1 0+(-16326947/250000000 : ℝ)*X 1 1+(-6884345481/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315062_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((2152578029/5000000000 : ℝ)*X 2 0+(6679562037/10000000000 : ℝ)*X 2 1+(516045257/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315062_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((291249473/625000000 : ℝ)*X 0 0+(3418505601/5000000000 : ℝ)*X 0 1+(-19045661/2500000000 : ℝ)*X 0 2+(291249473/625000000 : ℝ)*X 1 0+(3418505601/5000000000 : ℝ)*X 1 1+(-19045661/2500000000 : ℝ)*X 1 2+(291249473/625000000 : ℝ)*X 2 0+(3418505601/5000000000 : ℝ)*X 2 1+(-19045661/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315062_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-323782397/5000000000 : ℝ)*X 0 0+(534541791/1250000000 : ℝ)*X 0 1+(-3462399157/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315062_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((3878813243/10000000000 : ℝ)*X 1 0+(-62661981/500000000 : ℝ)*X 1 1+(-6914495511/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315062_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((257643749/400000000 : ℝ)*X 2 0+(1140463343/2500000000 : ℝ)*X 2 1+(1043934793/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315062_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((3668046577/5000000000 : ℝ)*X 0 0+(2044350613/5000000000 : ℝ)*X 0 1+(-43344759/5000000000 : ℝ)*X 0 2+(3668046577/5000000000 : ℝ)*X 1 0+(2044350613/5000000000 : ℝ)*X 1 1+(-43344759/5000000000 : ℝ)*X 1 2+(3668046577/5000000000 : ℝ)*X 2 0+(2044350613/5000000000 : ℝ)*X 2 1+(-43344759/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315062_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-95236093/5000000000 : ℝ)*X 0 0+(5862374453/10000000000 : ℝ)*X 0 1+(-5647640719/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315062_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((784678831/1250000000 : ℝ)*X 1 0+(-295004387/5000000000 : ℝ)*X 1 1+(-2510436847/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315062_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((891571011/2000000000 : ℝ)*X 2 0+(6131529797/10000000000 : ℝ)*X 2 1+(1655027837/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315062_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((1916651819/2500000000 : ℝ)*X 0 0+(1814614601/5000000000 : ℝ)*X 0 1+(-47725709/2000000000 : ℝ)*X 0 2+(1916651819/2500000000 : ℝ)*X 1 0+(1814614601/5000000000 : ℝ)*X 1 1+(-47725709/2000000000 : ℝ)*X 1 2+(1916651819/2500000000 : ℝ)*X 2 0+(1814614601/5000000000 : ℝ)*X 2 1+(-47725709/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315062_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((14007/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14007/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6988703261397622464719442460929/683206911964403125000000000000000000 : ℝ) := by norm_num
    linear_combination (45846706437/100000000000 : ℝ)*(base7) + (106797068977/1000000000000 : ℝ)*(base60) + (1651381388459/500000000000 : ℝ)*(major_s1_0) + (1651381388459/500000000000 : ℝ)*(major_s1_1) + (1651381388459/500000000000 : ℝ)*(major_s1_2) + (411551/125000000000 : ℝ)*(sp_s1_0) + (3535847/1000000000000 : ℝ)*(sp_s1_1) + (2223846808867/500000000000 : ℝ)*(sp_s1_7) + (1111945106553/250000000000 : ℝ)*(sp_s1_8) + (4447785099349/1000000000000 : ℝ)*(sp_s1_9) + (234944478491/100000000000 : ℝ)*(sp_s1_13) + (88451993/1000000000000 : ℝ)*(sp_s1_14) + (1400077/1000000000000 : ℝ)*(sp_s1_15) + (131393/500000000000 : ℝ)*(sp_s1_23) + (94548886027/50000000000 : ℝ)*(f.failure) + (889557072427/200000000000 : ℝ)*(f.sum) + (19097399058916154743/54619684670000000000000000000000 : ℝ)*base63 + (321868478269683/3440350000000000000000000000 : ℝ)*base65 + (159328937121143/1984525000000000000000000000 : ℝ)*base66 + (202637230059949/3440350000000000000000000000 : ℝ)*base69 + (1612694640621241857/34426722362500000000000000000000 : ℝ)*base71 + (170647248776131/307900000000000000000000000 : ℝ)*base73 + (1017453491677433/3969050000000000000000000000 : ℝ)*base75 + (296556962918173/1000675000000000000000000000 : ℝ)*base77 + (53017547189481293/24441409900000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (207/5000000000000000 : ℝ)*base86 + (207/5000000000000000 : ℝ)*base88 + (207/5000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(56327/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(56327/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (9698836947459236335024232545701/683206911964403125000000000000000000 : ℝ) := by norm_num
    linear_combination (482891343443/1000000000000 : ℝ)*(base7) + (1598709041303/500000000000 : ℝ)*(major_s1_0) + (1598709041303/500000000000 : ℝ)*(major_s1_1) + (1598709041303/500000000000 : ℝ)*(major_s1_2) + (3085587/200000000000 : ℝ)*(sp_s1_0) + (7367979/1000000000000 : ℝ)*(sp_s1_1) + (575251/50000000000 : ℝ)*(sp_s1_2) + (405001/250000000000 : ℝ)*(sp_s1_7) + (86979393/1000000000000 : ℝ)*(sp_s1_8) + (66924700497/15625000000 : ℝ)*(sp_s1_14) + (2141551766187/500000000000 : ℝ)*(sp_s1_15) + (4283186374727/1000000000000 : ℝ)*(sp_s1_16) + (2313512816943/1000000000000 : ℝ)*(sp_s1_20) + (521897/12500000000 : ℝ)*(sp_s1_27) + (1830663225259/1000000000000 : ℝ)*(f.failure) + (2141598939873/500000000000 : ℝ)*(f.sum) + (14534662057075051879/54619684670000000000000000000000 : ℝ)*base62 + (145506015342057/1720175000000000000000000000 : ℝ)*base64 + (133213535214829/1984525000000000000000000000 : ℝ)*base67 + (738454834954753/3440350000000000000000000000 : ℝ)*base69 + (14038658283441082517/68853444725000000000000000000000 : ℝ)*base70 + (173220895661253/307900000000000000000000000 : ℝ)*base72 + (153433811501513/496131250000000000000000000 : ℝ)*base74 + (206888105258063/2001350000000000000000000000 : ℝ)*base76 + (809782499236525309/24441409900000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (88319/100000000000000000 : ℝ)*base86 + (88319/100000000000000000 : ℝ)*base88 + (88319/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-4063/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-4063/10000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (36950263068568763875402797467433/10931310591430450000000000000000000000 : ℝ) := by norm_num
    linear_combination (19147694937/500000000000 : ℝ)*(base7) + (3725263/1000000000000 : ℝ)*(base11) + (30335412973/100000000000 : ℝ)*(base39) + (3459631028083/1000000000000 : ℝ)*(major_s1_0) + (3459631028083/1000000000000 : ℝ)*(major_s1_1) + (3459631028083/1000000000000 : ℝ)*(major_s1_2) + (74971/7812500000 : ℝ)*(sp_s1_0) + (2626893/1000000000000 : ℝ)*(sp_s1_1) + (10181583/500000000000 : ℝ)*(sp_s1_9) + (341541/500000000000 : ℝ)*(sp_s1_20) + (4916173705051/1000000000000 : ℝ)*(sp_s1_21) + (491618439971/100000000000 : ℝ)*(sp_s1_22) + (4916166663437/1000000000000 : ℝ)*(sp_s1_23) + (2019086437011/1000000000000 : ℝ)*(sp_s1_27) + (1980791730219/1000000000000 : ℝ)*(f.failure) + (4916187026603/1000000000000 : ℝ)*(f.sum) + (40879340081020776083/109239369340000000000000000000000 : ℝ)*base62 + (618821061240569/6880700000000000000000000000 : ℝ)*base64 + (216808847095089/3969050000000000000000000000 : ℝ)*base67 + (2954402266296681/3440350000000000000000000000 : ℝ)*base68 + (2441947059084978929/17213361181250000000000000000000 : ℝ)*base70 + (274947977792377/615800000000000000000000000 : ℝ)*base73 + (6684751979772429/7938100000000000000000000000 : ℝ)*base74 + (3000892404059123/4002700000000000000000000000 : ℝ)*base76 + (9128412906434796379/48882819800000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (20321/100000000000000000 : ℝ)*base87 + (20321/100000000000000000 : ℝ)*base89 + (20321/100000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((40027/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(40027/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79381/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(79381/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-68807/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-68807/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((14007/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14007/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(56327/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(56327/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-4063/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-4063/10000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c315062_s1 p hpa hpb X hX hprev0

#print axioms solution
