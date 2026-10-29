-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c313061_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:34:17.44238+00:00
-- url     : https://prove2.me/submissions/1294a706-7df5-4e81-b52f-5f63a4720d19

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
theorem collision_support_c313061_s2_s2_0 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-395630289/2000000000 : ℝ)*x 0 + (4511287453/10000000000 : ℝ)*x 1 + (2955532063/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (395630289/2000000000 : ℝ)^37 ≤ (1581372749413/12500000000000 : ℝ)^29 := by
    have hnat : (395630289 : ℕ)^37*12500000000000^29 ≤ 1581372749413^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      395630289 2000000000 1581372749413 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4511287453/10000000000 : ℝ)^37 ≤ (36218888759231/100000000000000 : ℝ)^29 := by
    have hnat : (4511287453 : ℕ)^37*100000000000000^29 ≤ 36218888759231^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4511287453 10000000000 36218888759231 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2955532063/5000000000 : ℝ)^37 ≤ (25565064611589/50000000000000 : ℝ)^29 := by
    have hnat : (2955532063 : ℕ)^37*50000000000000^29 ≤ 25565064611589^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2955532063 5000000000 25565064611589 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-395630289/2000000000 : ℝ), (4511287453/10000000000 : ℝ), (2955532063/5000000000 : ℝ)] ![(1581372749413/12500000000000 : ℝ), (36218888759231/100000000000000 : ℝ), (25565064611589/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-395630289/2000000000 : ℝ)|^37 ≤ (1581372749413/12500000000000 : ℝ)^29
        have hw : |(-395630289/2000000000 : ℝ)|=(395630289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4511287453/10000000000 : ℝ)|^37 ≤ (36218888759231/100000000000000 : ℝ)^29
        have hw : |(4511287453/10000000000 : ℝ)|=(4511287453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2955532063/5000000000 : ℝ)|^37 ≤ (25565064611589/50000000000000 : ℝ)^29
        have hw : |(2955532063/5000000000 : ℝ)|=(2955532063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313061_s2_s2_2 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4771785479/10000000000 : ℝ)*x 0 + (395965739/625000000 : ℝ)*x 1 + (-495124529/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4771785479/10000000000 : ℝ)^37 ≤ (38908202060541/100000000000000 : ℝ)^29 := by
    have hnat : (4771785479 : ℕ)^37*100000000000000^29 ≤ 38908202060541^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4771785479 10000000000 38908202060541 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (395965739/625000000 : ℝ)^37 ≤ (55859307768491/100000000000000 : ℝ)^29 := by
    have hnat : (395965739 : ℕ)^37*100000000000000^29 ≤ 55859307768491^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      395965739 625000000 55859307768491 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (495124529/5000000000 : ℝ)^37 ≤ (5232490166359/100000000000000 : ℝ)^29 := by
    have hnat : (495124529 : ℕ)^37*100000000000000^29 ≤ 5232490166359^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      495124529 5000000000 5232490166359 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4771785479/10000000000 : ℝ), (395965739/625000000 : ℝ), (-495124529/5000000000 : ℝ)] ![(38908202060541/100000000000000 : ℝ), (55859307768491/100000000000000 : ℝ), (5232490166359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4771785479/10000000000 : ℝ)|^37 ≤ (38908202060541/100000000000000 : ℝ)^29
        have hw : |(4771785479/10000000000 : ℝ)|=(4771785479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(395965739/625000000 : ℝ)|^37 ≤ (55859307768491/100000000000000 : ℝ)^29
        have hw : |(395965739/625000000 : ℝ)|=(395965739/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-495124529/5000000000 : ℝ)|^37 ≤ (5232490166359/100000000000000 : ℝ)^29
        have hw : |(-495124529/5000000000 : ℝ)|=(495124529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313061_s2_s2_6 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6240848611/10000000000 : ℝ)*x 0 + (1411393129/5000000000 : ℝ)*x 1 + (1702175719/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6240848611/10000000000 : ℝ)^37 ≤ (13699324258139/25000000000000 : ℝ)^29 := by
    have hnat : (6240848611 : ℕ)^37*25000000000000^29 ≤ 13699324258139^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6240848611 10000000000 13699324258139 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1411393129/5000000000 : ℝ)^37 ≤ (19913192384731/100000000000000 : ℝ)^29 := by
    have hnat : (1411393129 : ℕ)^37*100000000000000^29 ≤ 19913192384731^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1411393129 5000000000 19913192384731 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1702175719/5000000000 : ℝ)^37 ≤ (12644755286951/50000000000000 : ℝ)^29 := by
    have hnat : (1702175719 : ℕ)^37*50000000000000^29 ≤ 12644755286951^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1702175719 5000000000 12644755286951 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6240848611/10000000000 : ℝ), (1411393129/5000000000 : ℝ), (1702175719/5000000000 : ℝ)] ![(13699324258139/25000000000000 : ℝ), (19913192384731/100000000000000 : ℝ), (12644755286951/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6240848611/10000000000 : ℝ)|^37 ≤ (13699324258139/25000000000000 : ℝ)^29
        have hw : |(6240848611/10000000000 : ℝ)|=(6240848611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1411393129/5000000000 : ℝ)|^37 ≤ (19913192384731/100000000000000 : ℝ)^29
        have hw : |(1411393129/5000000000 : ℝ)|=(1411393129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1702175719/5000000000 : ℝ)|^37 ≤ (12644755286951/50000000000000 : ℝ)^29
        have hw : |(1702175719/5000000000 : ℝ)|=(1702175719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313061_s2_s2_7 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1935143621/10000000000 : ℝ)*x 0 + (151789479/400000000 : ℝ)*x 1 + (263297083/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1935143621/10000000000 : ℝ)^37 ≤ (12301113651339/100000000000000 : ℝ)^29 := by
    have hnat : (1935143621 : ℕ)^37*100000000000000^29 ≤ 12301113651339^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1935143621 10000000000 12301113651339 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (151789479/400000000 : ℝ)^37 ≤ (1815406489697/6250000000000 : ℝ)^29 := by
    have hnat : (151789479 : ℕ)^37*6250000000000^29 ≤ 1815406489697^29*400000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151789479 400000000 1815406489697 6250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263297083/400000000 : ℝ)^37 ≤ (58652382496813/100000000000000 : ℝ)^29 := by
    have hnat : (263297083 : ℕ)^37*100000000000000^29 ≤ 58652382496813^29*400000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263297083 400000000 58652382496813 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1935143621/10000000000 : ℝ), (151789479/400000000 : ℝ), (263297083/400000000 : ℝ)] ![(12301113651339/100000000000000 : ℝ), (1815406489697/6250000000000 : ℝ), (58652382496813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1935143621/10000000000 : ℝ)|^37 ≤ (12301113651339/100000000000000 : ℝ)^29
        have hw : |(-1935143621/10000000000 : ℝ)|=(1935143621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(151789479/400000000 : ℝ)|^37 ≤ (1815406489697/6250000000000 : ℝ)^29
        have hw : |(151789479/400000000 : ℝ)|=(151789479/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263297083/400000000 : ℝ)|^37 ≤ (58652382496813/100000000000000 : ℝ)^29
        have hw : |(263297083/400000000 : ℝ)|=(263297083/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313061_s2_s2_8 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (843868963/2000000000 : ℝ)*x 0 + (-356264307/2500000000 : ℝ)*x 1 + (82023621/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (843868963/2000000000 : ℝ)^37 ≤ (33255565238061/100000000000000 : ℝ)^29 := by
    have hnat : (843868963 : ℕ)^37*100000000000000^29 ≤ 33255565238061^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      843868963 2000000000 33255565238061 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (356264307/2500000000 : ℝ)^37 ≤ (208135779077/2500000000000 : ℝ)^29 := by
    have hnat : (356264307 : ℕ)^37*2500000000000^29 ≤ 208135779077^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      356264307 2500000000 208135779077 2500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82023621/125000000 : ℝ)^37 ≤ (5841900358831/10000000000000 : ℝ)^29 := by
    have hnat : (82023621 : ℕ)^37*10000000000000^29 ≤ 5841900358831^29*125000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82023621 125000000 5841900358831 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(843868963/2000000000 : ℝ), (-356264307/2500000000 : ℝ), (82023621/125000000 : ℝ)] ![(33255565238061/100000000000000 : ℝ), (208135779077/2500000000000 : ℝ), (5841900358831/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(843868963/2000000000 : ℝ)|^37 ≤ (33255565238061/100000000000000 : ℝ)^29
        have hw : |(843868963/2000000000 : ℝ)|=(843868963/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-356264307/2500000000 : ℝ)|^37 ≤ (208135779077/2500000000000 : ℝ)^29
        have hw : |(-356264307/2500000000 : ℝ)|=(356264307/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(82023621/125000000 : ℝ)|^37 ≤ (5841900358831/10000000000000 : ℝ)^29
        have hw : |(82023621/125000000 : ℝ)|=(82023621/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313061_s2_s2_9 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (429851719/1000000000 : ℝ)*x 0 + (3574921049/5000000000 : ℝ)*x 1 + (-44017299/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (429851719/1000000000 : ℝ)^37 ≤ (34053769877457/100000000000000 : ℝ)^29 := by
    have hnat : (429851719 : ℕ)^37*100000000000000^29 ≤ 34053769877457^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429851719 1000000000 34053769877457 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3574921049/5000000000 : ℝ)^37 ≤ (65178200827249/100000000000000 : ℝ)^29 := by
    have hnat : (3574921049 : ℕ)^37*100000000000000^29 ≤ 65178200827249^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3574921049 5000000000 65178200827249 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (44017299/2000000000 : ℝ)^37 ≤ (153605856521/20000000000000 : ℝ)^29 := by
    have hnat : (44017299 : ℕ)^37*20000000000000^29 ≤ 153605856521^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44017299 2000000000 153605856521 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(429851719/1000000000 : ℝ), (3574921049/5000000000 : ℝ), (-44017299/2000000000 : ℝ)] ![(34053769877457/100000000000000 : ℝ), (65178200827249/100000000000000 : ℝ), (153605856521/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(429851719/1000000000 : ℝ)|^37 ≤ (34053769877457/100000000000000 : ℝ)^29
        have hw : |(429851719/1000000000 : ℝ)|=(429851719/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3574921049/5000000000 : ℝ)|^37 ≤ (65178200827249/100000000000000 : ℝ)^29
        have hw : |(3574921049/5000000000 : ℝ)|=(3574921049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-44017299/2000000000 : ℝ)|^37 ≤ (153605856521/20000000000000 : ℝ)^29
        have hw : |(-44017299/2000000000 : ℝ)|=(44017299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313061_s2_s2_13 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1521133223/2500000000 : ℝ)*x 0 + (216859347/500000000 : ℝ)*x 1 + (39198979/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1521133223/2500000000 : ℝ)^37 ≤ (10610447961129/20000000000000 : ℝ)^29 := by
    have hnat : (1521133223 : ℕ)^37*20000000000000^29 ≤ 10610447961129^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1521133223 2500000000 10610447961129 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216859347/500000000 : ℝ)^37 ≤ (17222557087511/50000000000000 : ℝ)^29 := by
    have hnat : (216859347 : ℕ)^37*50000000000000^29 ≤ 17222557087511^29*500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216859347 500000000 17222557087511 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (39198979/200000000 : ℝ)^37 ≤ (6251322999139/50000000000000 : ℝ)^29 := by
    have hnat : (39198979 : ℕ)^37*50000000000000^29 ≤ 6251322999139^29*200000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39198979 200000000 6251322999139 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1521133223/2500000000 : ℝ), (216859347/500000000 : ℝ), (39198979/200000000 : ℝ)] ![(10610447961129/20000000000000 : ℝ), (17222557087511/50000000000000 : ℝ), (6251322999139/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1521133223/2500000000 : ℝ)|^37 ≤ (10610447961129/20000000000000 : ℝ)^29
        have hw : |(1521133223/2500000000 : ℝ)|=(1521133223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216859347/500000000 : ℝ)|^37 ≤ (17222557087511/50000000000000 : ℝ)^29
        have hw : |(216859347/500000000 : ℝ)|=(216859347/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(39198979/200000000 : ℝ)|^37 ≤ (6251322999139/50000000000000 : ℝ)^29
        have hw : |(39198979/200000000 : ℝ)|=(39198979/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313061_s2_s2_14 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-937372449/10000000000 : ℝ)*x 0 + (2273512281/5000000000 : ℝ)*x 1 + (3286092653/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (937372449/10000000000 : ℝ)^37 ≤ (2439336741617/50000000000000 : ℝ)^29 := by
    have hnat : (937372449 : ℕ)^37*50000000000000^29 ≤ 2439336741617^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      937372449 10000000000 2439336741617 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2273512281/5000000000 : ℝ)^37 ≤ (18292676301759/50000000000000 : ℝ)^29 := by
    have hnat : (2273512281 : ℕ)^37*50000000000000^29 ≤ 18292676301759^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2273512281 5000000000 18292676301759 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3286092653/5000000000 : ℝ)^37 ≤ (29267986949909/50000000000000 : ℝ)^29 := by
    have hnat : (3286092653 : ℕ)^37*50000000000000^29 ≤ 29267986949909^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3286092653 5000000000 29267986949909 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-937372449/10000000000 : ℝ), (2273512281/5000000000 : ℝ), (3286092653/5000000000 : ℝ)] ![(2439336741617/50000000000000 : ℝ), (18292676301759/50000000000000 : ℝ), (29267986949909/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-937372449/10000000000 : ℝ)|^37 ≤ (2439336741617/50000000000000 : ℝ)^29
        have hw : |(-937372449/10000000000 : ℝ)|=(937372449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2273512281/5000000000 : ℝ)|^37 ≤ (18292676301759/50000000000000 : ℝ)^29
        have hw : |(2273512281/5000000000 : ℝ)|=(2273512281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3286092653/5000000000 : ℝ)|^37 ≤ (29267986949909/50000000000000 : ℝ)^29
        have hw : |(3286092653/5000000000 : ℝ)|=(3286092653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313061_s2_s2_15 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4175183463/10000000000 : ℝ)*x 0 + (-749810861/5000000000 : ℝ)*x 1 + (6551647803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4175183463/10000000000 : ℝ)^37 ≤ (1640606184051/5000000000000 : ℝ)^29 := by
    have hnat : (4175183463 : ℕ)^37*5000000000000^29 ≤ 1640606184051^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4175183463 10000000000 1640606184051 5000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (749810861/5000000000 : ℝ)^37 ≤ (4442591077117/50000000000000 : ℝ)^29 := by
    have hnat : (749810861 : ℕ)^37*50000000000000^29 ≤ 4442591077117^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      749810861 5000000000 4442591077117 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6551647803/10000000000 : ℝ)^37 ≤ (58302694149449/100000000000000 : ℝ)^29 := by
    have hnat : (6551647803 : ℕ)^37*100000000000000^29 ≤ 58302694149449^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6551647803 10000000000 58302694149449 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4175183463/10000000000 : ℝ), (-749810861/5000000000 : ℝ), (6551647803/10000000000 : ℝ)] ![(1640606184051/5000000000000 : ℝ), (4442591077117/50000000000000 : ℝ), (58302694149449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4175183463/10000000000 : ℝ)|^37 ≤ (1640606184051/5000000000000 : ℝ)^29
        have hw : |(4175183463/10000000000 : ℝ)|=(4175183463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-749810861/5000000000 : ℝ)|^37 ≤ (4442591077117/50000000000000 : ℝ)^29
        have hw : |(-749810861/5000000000 : ℝ)|=(749810861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6551647803/10000000000 : ℝ)|^37 ≤ (58302694149449/100000000000000 : ℝ)^29
        have hw : |(6551647803/10000000000 : ℝ)|=(6551647803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313061_s2_s2_16 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5889010067/10000000000 : ℝ)*x 0 + (5652978771/10000000000 : ℝ)*x 1 + (-46065749/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5889010067/10000000000 : ℝ)^37 ≤ (50886864170529/100000000000000 : ℝ)^29 := by
    have hnat : (5889010067 : ℕ)^37*100000000000000^29 ≤ 50886864170529^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5889010067 10000000000 50886864170529 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5652978771/10000000000 : ℝ)^37 ≤ (24149607540849/50000000000000 : ℝ)^29 := by
    have hnat : (5652978771 : ℕ)^37*50000000000000^29 ≤ 24149607540849^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5652978771 10000000000 24149607540849 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (46065749/2000000000 : ℝ)^37 ≤ (813920732703/100000000000000 : ℝ)^29 := by
    have hnat : (46065749 : ℕ)^37*100000000000000^29 ≤ 813920732703^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46065749 2000000000 813920732703 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5889010067/10000000000 : ℝ), (5652978771/10000000000 : ℝ), (-46065749/2000000000 : ℝ)] ![(50886864170529/100000000000000 : ℝ), (24149607540849/50000000000000 : ℝ), (813920732703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5889010067/10000000000 : ℝ)|^37 ≤ (50886864170529/100000000000000 : ℝ)^29
        have hw : |(5889010067/10000000000 : ℝ)|=(5889010067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5652978771/10000000000 : ℝ)|^37 ≤ (24149607540849/50000000000000 : ℝ)^29
        have hw : |(5652978771/10000000000 : ℝ)|=(5652978771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-46065749/2000000000 : ℝ)|^37 ≤ (813920732703/100000000000000 : ℝ)^29
        have hw : |(-46065749/2000000000 : ℝ)|=(46065749/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313061_s2_s2_20 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7606517721/10000000000 : ℝ)*x 0 + (2466262407/10000000000 : ℝ)*x 1 + (1984425511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7606517721/10000000000 : ℝ)^37 ≤ (17633949043081/25000000000000 : ℝ)^29 := by
    have hnat : (7606517721 : ℕ)^37*25000000000000^29 ≤ 17633949043081^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7606517721 10000000000 17633949043081 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2466262407/10000000000 : ℝ)^37 ≤ (4190501404157/25000000000000 : ℝ)^29 := by
    have hnat : (2466262407 : ℕ)^37*25000000000000^29 ≤ 4190501404157^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2466262407 10000000000 4190501404157 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1984425511/10000000000 : ℝ)^37 ≤ (3175549547703/25000000000000 : ℝ)^29 := by
    have hnat : (1984425511 : ℕ)^37*25000000000000^29 ≤ 3175549547703^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1984425511 10000000000 3175549547703 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7606517721/10000000000 : ℝ), (2466262407/10000000000 : ℝ), (1984425511/10000000000 : ℝ)] ![(17633949043081/25000000000000 : ℝ), (4190501404157/25000000000000 : ℝ), (3175549547703/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7606517721/10000000000 : ℝ)|^37 ≤ (17633949043081/25000000000000 : ℝ)^29
        have hw : |(7606517721/10000000000 : ℝ)|=(7606517721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2466262407/10000000000 : ℝ)|^37 ≤ (4190501404157/25000000000000 : ℝ)^29
        have hw : |(2466262407/10000000000 : ℝ)|=(2466262407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1984425511/10000000000 : ℝ)|^37 ≤ (3175549547703/25000000000000 : ℝ)^29
        have hw : |(1984425511/10000000000 : ℝ)|=(1984425511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313061_s2_s2_21 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-218899473/2500000000 : ℝ)*x 0 + (5388707067/10000000000 : ℝ)*x 1 + (581665851/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218899473/2500000000 : ℝ)^37 ≤ (4472256413711/100000000000000 : ℝ)^29 := by
    have hnat : (218899473 : ℕ)^37*100000000000000^29 ≤ 4472256413711^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218899473 2500000000 4472256413711 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5388707067/10000000000 : ℝ)^37 ≤ (45437178500151/100000000000000 : ℝ)^29 := by
    have hnat : (5388707067 : ℕ)^37*100000000000000^29 ≤ 45437178500151^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388707067 10000000000 45437178500151 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (581665851/1000000000 : ℝ)^37 ≤ (5009056507639/10000000000000 : ℝ)^29 := by
    have hnat : (581665851 : ℕ)^37*10000000000000^29 ≤ 5009056507639^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      581665851 1000000000 5009056507639 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-218899473/2500000000 : ℝ), (5388707067/10000000000 : ℝ), (581665851/1000000000 : ℝ)] ![(4472256413711/100000000000000 : ℝ), (45437178500151/100000000000000 : ℝ), (5009056507639/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-218899473/2500000000 : ℝ)|^37 ≤ (4472256413711/100000000000000 : ℝ)^29
        have hw : |(-218899473/2500000000 : ℝ)|=(218899473/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5388707067/10000000000 : ℝ)|^37 ≤ (45437178500151/100000000000000 : ℝ)^29
        have hw : |(5388707067/10000000000 : ℝ)|=(5388707067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(581665851/1000000000 : ℝ)|^37 ≤ (5009056507639/10000000000000 : ℝ)^29
        have hw : |(581665851/1000000000 : ℝ)|=(581665851/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313061_s2_s2_22 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5871611891/10000000000 : ℝ)*x 0 + (-903605057/10000000000 : ℝ)*x 1 + (1328832991/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5871611891/10000000000 : ℝ)^37 ≤ (5069513256789/10000000000000 : ℝ)^29 := by
    have hnat : (5871611891 : ℕ)^37*10000000000000^29 ≤ 5069513256789^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5871611891 10000000000 5069513256789 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (903605057/10000000000 : ℝ)^37 ≤ (232778447957/5000000000000 : ℝ)^29 := by
    have hnat : (903605057 : ℕ)^37*5000000000000^29 ≤ 232778447957^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903605057 10000000000 232778447957 5000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1328832991/2500000000 : ℝ)^37 ≤ (8929859691973/20000000000000 : ℝ)^29 := by
    have hnat : (1328832991 : ℕ)^37*20000000000000^29 ≤ 8929859691973^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328832991 2500000000 8929859691973 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5871611891/10000000000 : ℝ), (-903605057/10000000000 : ℝ), (1328832991/2500000000 : ℝ)] ![(5069513256789/10000000000000 : ℝ), (232778447957/5000000000000 : ℝ), (8929859691973/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5871611891/10000000000 : ℝ)|^37 ≤ (5069513256789/10000000000000 : ℝ)^29
        have hw : |(5871611891/10000000000 : ℝ)|=(5871611891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-903605057/10000000000 : ℝ)|^37 ≤ (232778447957/5000000000000 : ℝ)^29
        have hw : |(-903605057/10000000000 : ℝ)|=(903605057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1328832991/2500000000 : ℝ)|^37 ≤ (8929859691973/20000000000000 : ℝ)^29
        have hw : |(1328832991/2500000000 : ℝ)|=(1328832991/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313061_s2_s2_23 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (8193899/20000000 : ℝ)*x 0 + (1418202803/2000000000 : ℝ)*x 1 + (-718578953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8193899/20000000 : ℝ)^37 ≤ (16014861877591/50000000000000 : ℝ)^29 := by
    have hnat : (8193899 : ℕ)^37*50000000000000^29 ≤ 16014861877591^29*20000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8193899 20000000 16014861877591 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1418202803/2000000000 : ℝ)^37 ≤ (64494761124817/100000000000000 : ℝ)^29 := by
    have hnat : (1418202803 : ℕ)^37*100000000000000^29 ≤ 64494761124817^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1418202803 2000000000 64494761124817 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (718578953/10000000000 : ℝ)^37 ≤ (695103020947/20000000000000 : ℝ)^29 := by
    have hnat : (718578953 : ℕ)^37*20000000000000^29 ≤ 695103020947^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      718578953 10000000000 695103020947 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8193899/20000000 : ℝ), (1418202803/2000000000 : ℝ), (-718578953/10000000000 : ℝ)] ![(16014861877591/50000000000000 : ℝ), (64494761124817/100000000000000 : ℝ), (695103020947/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8193899/20000000 : ℝ)|^37 ≤ (16014861877591/50000000000000 : ℝ)^29
        have hw : |(8193899/20000000 : ℝ)|=(8193899/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1418202803/2000000000 : ℝ)|^37 ≤ (64494761124817/100000000000000 : ℝ)^29
        have hw : |(1418202803/2000000000 : ℝ)|=(1418202803/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-718578953/10000000000 : ℝ)|^37 ≤ (695103020947/20000000000000 : ℝ)^29
        have hw : |(-718578953/10000000000 : ℝ)|=(718578953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313061_s2_s2_27 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3991338693/5000000000 : ℝ)*x 0 + (957364987/5000000000 : ℝ)*x 1 + (400451353/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3991338693/5000000000 : ℝ)^37 ≤ (9377025460407/12500000000000 : ℝ)^29 := by
    have hnat : (3991338693 : ℕ)^37*12500000000000^29 ≤ 9377025460407^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3991338693 5000000000 9377025460407 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (957364987/5000000000 : ℝ)^37 ≤ (2427159021723/20000000000000 : ℝ)^29 := by
    have hnat : (957364987 : ℕ)^37*20000000000000^29 ≤ 2427159021723^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      957364987 5000000000 2427159021723 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (400451353/2000000000 : ℝ)^37 ≤ (6424000595837/50000000000000 : ℝ)^29 := by
    have hnat : (400451353 : ℕ)^37*50000000000000^29 ≤ 6424000595837^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400451353 2000000000 6424000595837 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3991338693/5000000000 : ℝ), (957364987/5000000000 : ℝ), (400451353/2000000000 : ℝ)] ![(9377025460407/12500000000000 : ℝ), (2427159021723/20000000000000 : ℝ), (6424000595837/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3991338693/5000000000 : ℝ)|^37 ≤ (9377025460407/12500000000000 : ℝ)^29
        have hw : |(3991338693/5000000000 : ℝ)|=(3991338693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(957364987/5000000000 : ℝ)|^37 ≤ (2427159021723/20000000000000 : ℝ)^29
        have hw : |(957364987/5000000000 : ℝ)|=(957364987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(400451353/2000000000 : ℝ)|^37 ≤ (6424000595837/50000000000000 : ℝ)^29
        have hw : |(400451353/2000000000 : ℝ)|=(400451353/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c313061_s2 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((32533/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(32533/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6661/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(6661/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7703/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(7703/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((38159/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(38159/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22221/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(22221/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(40353/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(40353/100000 : ℝ)*X 1 2) := by
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
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  have s2_pow0 : (32533/50000 : ℝ) ^ (73/16 : ℝ) ≤ (14074342701684823789/100000000000000000000 : ℝ) := by
    have hpowers : (32533/50000 : ℝ)^73 ≤ (14074342701684823789/100000000000000000000 : ℝ)^16 := by
      have hnat : (32533 : ℕ)^73*100000000000000000000^16 ≤ 14074342701684823789^16*50000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32533 50000 14074342701684823789 100000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (32533/50000 : ℝ)) (X := (14074342701684823789/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (114074342701684823789/100000000000000000000 : ℝ) ≤ (1029281935436207/1000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (114074342701684823789/100000000000000000000 : ℝ)^16 ≤ (1029281935436207/1000000000000000 : ℝ)^73 := by
      have hnat : (114074342701684823789 : ℕ)^16*1000000000000000^73 ≤ 1029281935436207^73*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        114074342701684823789 100000000000000000000 1029281935436207 1000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1029281935436207/1000000000000000 : ℝ)) (X := (114074342701684823789/100000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (64074342701684823789/50000000000000000000 : ℝ) ≤ (2639663642405729/2500000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (64074342701684823789/50000000000000000000 : ℝ)^16 ≤ (2639663642405729/2500000000000000 : ℝ)^73 := by
      have hnat : (64074342701684823789 : ℕ)^16*2500000000000000^73 ≤ 2639663642405729^73*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64074342701684823789 50000000000000000000 2639663642405729 2500000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2639663642405729/2500000000000000 : ℝ)) (X := (64074342701684823789/50000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(29281935436207/650660000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(132917607630423/3253300000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (32533/50000 : ℝ)) (alpha := (29281935436207/650660000000000 : ℝ)) (beta := (132917607630423/3253300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (32533/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(29281935436207/650660000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(132917607630423/3253300000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (6661/10000 : ℝ) ^ (73/16 : ℝ) ≤ (1957981928367479431/12500000000000000000 : ℝ) := by
    have hpowers : (6661/10000 : ℝ)^73 ≤ (1957981928367479431/12500000000000000000 : ℝ)^16 := by
      have hnat : (6661 : ℕ)^73*12500000000000000000^16 ≤ 1957981928367479431^16*10000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6661 10000 1957981928367479431 12500000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6661/10000 : ℝ)) (X := (1957981928367479431/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (14457981928367479431/12500000000000000000 : ℝ) ≤ (10324084320315439/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (14457981928367479431/12500000000000000000 : ℝ)^16 ≤ (10324084320315439/10000000000000000 : ℝ)^73 := by
      have hnat : (14457981928367479431 : ℕ)^16*10000000000000000^73 ≤ 10324084320315439^73*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14457981928367479431 12500000000000000000 10324084320315439 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10324084320315439/10000000000000000 : ℝ)) (X := (14457981928367479431/12500000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (8207981928367479431/6250000000000000000 : ℝ) ≤ (1326939542400543/1250000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (8207981928367479431/6250000000000000000 : ℝ)^16 ≤ (1326939542400543/1250000000000000 : ℝ)^73 := by
      have hnat : (8207981928367479431 : ℕ)^16*1250000000000000^73 ≤ 1326939542400543^73*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8207981928367479431 6250000000000000000 1326939542400543 1250000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1326939542400543/1250000000000000 : ℝ)) (X := (8207981928367479431/6250000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(324084320315439/6661000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(58286403777781/1332200000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (6661/10000 : ℝ)) (alpha := (324084320315439/6661000000000000 : ℝ)) (beta := (58286403777781/1332200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (6661/10000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(324084320315439/6661000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(58286403777781/1332200000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (7703/12500 : ℝ) ^ (73/16 : ℝ) ≤ (2196665075579126871/20000000000000000000 : ℝ) := by
    have hpowers : (7703/12500 : ℝ)^73 ≤ (2196665075579126871/20000000000000000000 : ℝ)^16 := by
      have hnat : (7703 : ℕ)^73*20000000000000000000^16 ≤ 2196665075579126871^16*12500^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7703 12500 2196665075579126871 20000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7703/12500 : ℝ)) (X := (2196665075579126871/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (22196665075579126871/20000000000000000000 : ℝ) ≤ (10231033417668487/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (22196665075579126871/20000000000000000000 : ℝ)^16 ≤ (10231033417668487/10000000000000000 : ℝ)^73 := by
      have hnat : (22196665075579126871 : ℕ)^16*10000000000000000^73 ≤ 10231033417668487^73*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22196665075579126871 20000000000000000000 10231033417668487 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10231033417668487/10000000000000000 : ℝ)) (X := (22196665075579126871/20000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (12196665075579126871/10000000000000000000 : ℝ) ≤ (10444848823827439/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (12196665075579126871/10000000000000000000 : ℝ)^16 ≤ (10444848823827439/10000000000000000 : ℝ)^73 := by
      have hnat : (12196665075579126871 : ℕ)^16*10000000000000000^73 ≤ 10444848823827439^73*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12196665075579126871 10000000000000000000 10444848823827439 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10444848823827439/10000000000000000 : ℝ)) (X := (12196665075579126871/10000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(231033417668487/6162400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(26726925769869/770300000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (7703/12500 : ℝ)) (alpha := (231033417668487/6162400000000000 : ℝ)) (beta := (26726925769869/770300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (7703/12500 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(231033417668487/6162400000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(26726925769869/770300000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-395630289/2000000000 : ℝ)*X 0 0+(4511287453/10000000000 : ℝ)*X 0 1+(2955532063/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313061_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((4771785479/10000000000 : ℝ)*X 2 0+(395965739/625000000 : ℝ)*X 2 1+(-495124529/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313061_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((6240848611/10000000000 : ℝ)*X 0 0+(1411393129/5000000000 : ℝ)*X 0 1+(1702175719/5000000000 : ℝ)*X 0 2+(6240848611/10000000000 : ℝ)*X 1 0+(1411393129/5000000000 : ℝ)*X 1 1+(1702175719/5000000000 : ℝ)*X 1 2+(6240848611/10000000000 : ℝ)*X 2 0+(1411393129/5000000000 : ℝ)*X 2 1+(1702175719/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313061_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-1935143621/10000000000 : ℝ)*X 0 0+(151789479/400000000 : ℝ)*X 0 1+(263297083/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313061_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((843868963/2000000000 : ℝ)*X 1 0+(-356264307/2500000000 : ℝ)*X 1 1+(82023621/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313061_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((429851719/1000000000 : ℝ)*X 2 0+(3574921049/5000000000 : ℝ)*X 2 1+(-44017299/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313061_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((1521133223/2500000000 : ℝ)*X 0 0+(216859347/500000000 : ℝ)*X 0 1+(39198979/200000000 : ℝ)*X 0 2+(1521133223/2500000000 : ℝ)*X 1 0+(216859347/500000000 : ℝ)*X 1 1+(39198979/200000000 : ℝ)*X 1 2+(1521133223/2500000000 : ℝ)*X 2 0+(216859347/500000000 : ℝ)*X 2 1+(39198979/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313061_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-937372449/10000000000 : ℝ)*X 0 0+(2273512281/5000000000 : ℝ)*X 0 1+(3286092653/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313061_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((4175183463/10000000000 : ℝ)*X 1 0+(-749810861/5000000000 : ℝ)*X 1 1+(6551647803/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313061_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((5889010067/10000000000 : ℝ)*X 2 0+(5652978771/10000000000 : ℝ)*X 2 1+(-46065749/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313061_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((7606517721/10000000000 : ℝ)*X 0 0+(2466262407/10000000000 : ℝ)*X 0 1+(1984425511/10000000000 : ℝ)*X 0 2+(7606517721/10000000000 : ℝ)*X 1 0+(2466262407/10000000000 : ℝ)*X 1 1+(1984425511/10000000000 : ℝ)*X 1 2+(7606517721/10000000000 : ℝ)*X 2 0+(2466262407/10000000000 : ℝ)*X 2 1+(1984425511/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313061_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-218899473/2500000000 : ℝ)*X 0 0+(5388707067/10000000000 : ℝ)*X 0 1+(581665851/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313061_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((5871611891/10000000000 : ℝ)*X 1 0+(-903605057/10000000000 : ℝ)*X 1 1+(1328832991/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313061_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((8193899/20000000 : ℝ)*X 2 0+(1418202803/2000000000 : ℝ)*X 2 1+(-718578953/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313061_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((3991338693/5000000000 : ℝ)*X 0 0+(957364987/5000000000 : ℝ)*X 0 1+(400451353/2000000000 : ℝ)*X 0 2+(3991338693/5000000000 : ℝ)*X 1 0+(957364987/5000000000 : ℝ)*X 1 1+(400451353/2000000000 : ℝ)*X 1 2+(3991338693/5000000000 : ℝ)*X 2 0+(957364987/5000000000 : ℝ)*X 2 1+(400451353/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313061_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((38159/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(38159/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (15867050291287765920796290742167/3338515834078000000000000000000000000 : ℝ) := by norm_num
    linear_combination (449703/1000000000000 : ℝ)*(base23) + (222921/500000000000 : ℝ)*(base50) + (159214814779/200000000000 : ℝ)*(base59) + (4565933934171/1000000000000 : ℝ)*(major_s2_0) + (4565933934171/1000000000000 : ℝ)*(major_s2_1) + (4565933934171/1000000000000 : ℝ)*(major_s2_2) + (11142231/1000000000000 : ℝ)*(sp_s2_0) + (2294747/200000000000 : ℝ)*(sp_s2_6) + (6437882191627/1000000000000 : ℝ)*(sp_s2_7) + (6437545788809/1000000000000 : ℝ)*(sp_s2_8) + (321892517757/50000000000 : ℝ)*(sp_s2_9) + (336745184563/125000000000 : ℝ)*(sp_s2_13) + (43443131/125000000000 : ℝ)*(sp_s2_15) + (21264507/500000000000 : ℝ)*(sp_s2_23) + (2693972950239/1000000000000 : ℝ)*(f.failure) + (6437893333857/1000000000000 : ℝ)*(f.sum) + (80557008482993652687/205238732000000000000000000000000 : ℝ)*base62 + (380008626680339/770300000000000000000000000 : ℝ)*base64 + (285759215787869/1332200000000000000000000000 : ℝ)*base66 + (544017991793603/6162400000000000000000000000 : ℝ)*base68 + (775663445480843999/3132521237500000000000000000000 : ℝ)*base70 + (337469160944313/3253300000000000000000000000 : ℝ)*base73 + (3616217008657231/6661000000000000000000000000 : ℝ)*base74 + (108162798312277/650660000000000000000000000 : ℝ)*base77 + (10763392215489421029/43340462600000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (57393/100000000000000000 : ℝ)*base87 + (57393/100000000000000000 : ℝ)*base89 + (57393/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22221/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(22221/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (51800957369933704181716179/3132521237500000000000000000000 : ℝ) := by norm_num
    linear_combination (3025653/1000000000000 : ℝ)*(base19) + (957333/1000000000000 : ℝ)*(base39) + (82695258817/250000000000 : ℝ)*(base59) + (271169876827/62500000000 : ℝ)*(major_s2_0) + (271169876827/62500000000 : ℝ)*(major_s2_1) + (271169876827/62500000000 : ℝ)*(major_s2_2) + (7077277/200000000000 : ℝ)*(sp_s2_2) + (22322093/1000000000000 : ℝ)*(sp_s2_6) + (15475697/200000000000 : ℝ)*(sp_s2_7) + (1529360295227/250000000000 : ℝ)*(sp_s2_14) + (6117515533741/1000000000000 : ℝ)*(sp_s2_15) + (6117483173009/1000000000000 : ℝ)*(sp_s2_16) + (1279856998769/500000000000 : ℝ)*(sp_s2_20) + (87833633/500000000000 : ℝ)*(sp_s2_27) + (2559911986897/1000000000000 : ℝ)*(f.failure) + (3058759279697/500000000000 : ℝ)*(f.sum) + (2988330526304416519/12827420750000000000000000000000 : ℝ)*base62 + (409372718893971/385150000000000000000000000 : ℝ)*base65 + (251840177442223/333050000000000000000000000 : ℝ)*base67 + (102264577388549/385150000000000000000000000 : ℝ)*base69 + (2274430628857463929/6265042475000000000000000000000 : ℝ)*base71 + (80593904432157/1626650000000000000000000000 : ℝ)*base72 + (89653857495337/1665250000000000000000000000 : ℝ)*base75 + (59609454543653/325330000000000000000000000 : ℝ)*base77 + (1380611815306239923/10835115650000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (11839/100000000000000000 : ℝ)*base87 + (11839/100000000000000000 : ℝ)*base89 + (11839/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(40353/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(40353/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6853447237650420780662529776973/834628958519500000000000000000000000 : ℝ) := by norm_num
    linear_combination (215417/50000000000 : ℝ)*(base15) + (259353645951/1000000000000 : ℝ)*(base40) + (88497729709/250000000000 : ℝ)*(base59) + (956444727949/250000000000 : ℝ)*(major_s2_0) + (956444727949/250000000000 : ℝ)*(major_s2_1) + (956444727949/250000000000 : ℝ)*(major_s2_2) + (1103817/500000000000 : ℝ)*(sp_s2_0) + (44664069/250000000000 : ℝ)*(sp_s2_2) + (55603487/1000000000000 : ℝ)*(sp_s2_9) + (316699751/1000000000000 : ℝ)*(sp_s2_20) + (5394283051769/1000000000000 : ℝ)*(sp_s2_21) + (5394280951063/1000000000000 : ℝ)*(sp_s2_22) + (134851274991/25000000000 : ℝ)*(sp_s2_23) + (2256953127313/1000000000000 : ℝ)*(sp_s2_27) + (282158728383/125000000000 : ℝ)*(f.failure) + (5394285259403/1000000000000 : ℝ)*(f.sum) + (1742391097774393453/51309683000000000000000000000000 : ℝ)*base62 + (56099111877511/192575000000000000000000000 : ℝ)*base64 + (3275379915769/333050000000000000000000000 : ℝ)*base67 + (87125416830157/1540600000000000000000000000 : ℝ)*base68 + (84717930639647873/1566260618750000000000000000000 : ℝ)*base71 + (125162557437479/406662500000000000000000000 : ℝ)*base72 + (642202102351/26019531250000000000000000 : ℝ)*base74 + (111177166593509/325330000000000000000000000 : ℝ)*base77 + (1823220221504162387/5417557825000000000000000000000 : ℝ)*base78 + (479/12500000000000000 : ℝ)*base86 + (479/12500000000000000 : ℝ)*base88 + (479/12500000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((32533/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(32533/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6661/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(6661/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7703/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(7703/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((38159/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(38159/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22221/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(22221/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(40353/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(40353/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c313061_s2 p hpa hpb X hX hprev1

#print axioms solution
