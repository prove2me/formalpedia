-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c314054_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:46:52.59902+00:00
-- url     : https://prove2.me/submissions/b170f37f-f77b-4c16-831f-14bb74cbb662

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
theorem collision_support_c314054_s1_s1_0 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-535285069/10000000000 : ℝ)*x 0 + (4566457533/10000000000 : ℝ)*x 1 + (-3374326297/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535285069/10000000000 : ℝ)^75 ≤ (1209942301257/50000000000000 : ℝ)^59 := by
    have hnat : (535285069 : ℕ)^75*50000000000000^59 ≤ 1209942301257^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535285069 10000000000 1209942301257 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4566457533/10000000000 : ℝ)^75 ≤ (369200243341/1000000000000 : ℝ)^59 := by
    have hnat : (4566457533 : ℕ)^75*1000000000000^59 ≤ 369200243341^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4566457533 10000000000 369200243341 1000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3374326297/5000000000 : ℝ)^75 ≤ (15165022762809/25000000000000 : ℝ)^59 := by
    have hnat : (3374326297 : ℕ)^75*25000000000000^59 ≤ 15165022762809^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3374326297 5000000000 15165022762809 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-535285069/10000000000 : ℝ), (4566457533/10000000000 : ℝ), (-3374326297/5000000000 : ℝ)] ![(1209942301257/50000000000000 : ℝ), (369200243341/1000000000000 : ℝ), (15165022762809/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-535285069/10000000000 : ℝ)|^75 ≤ (1209942301257/50000000000000 : ℝ)^59
        have hw : |(-535285069/10000000000 : ℝ)|=(535285069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4566457533/10000000000 : ℝ)|^75 ≤ (369200243341/1000000000000 : ℝ)^59
        have hw : |(4566457533/10000000000 : ℝ)|=(4566457533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3374326297/5000000000 : ℝ)|^75 ≤ (15165022762809/25000000000000 : ℝ)^59
        have hw : |(-3374326297/5000000000 : ℝ)|=(3374326297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314054_s1_s1_1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (717892551/1250000000 : ℝ)*x 0 + (-1791107101/10000000000 : ℝ)*x 1 + (-4801532093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (717892551/1250000000 : ℝ)^75 ≤ (24706090653451/50000000000000 : ℝ)^59 := by
    have hnat : (717892551 : ℕ)^75*50000000000000^59 ≤ 24706090653451^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      717892551 1250000000 24706090653451 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1791107101/10000000000 : ℝ)^75 ≤ (2247026759623/20000000000000 : ℝ)^59 := by
    have hnat : (1791107101 : ℕ)^75*20000000000000^59 ≤ 2247026759623^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1791107101 10000000000 2247026759623 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4801532093/10000000000 : ℝ)^75 ≤ (39352684867919/100000000000000 : ℝ)^59 := by
    have hnat : (4801532093 : ℕ)^75*100000000000000^59 ≤ 39352684867919^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4801532093 10000000000 39352684867919 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(717892551/1250000000 : ℝ), (-1791107101/10000000000 : ℝ), (-4801532093/10000000000 : ℝ)] ![(24706090653451/50000000000000 : ℝ), (2247026759623/20000000000000 : ℝ), (39352684867919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(717892551/1250000000 : ℝ)|^75 ≤ (24706090653451/50000000000000 : ℝ)^59
        have hw : |(717892551/1250000000 : ℝ)|=(717892551/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1791107101/10000000000 : ℝ)|^75 ≤ (2247026759623/20000000000000 : ℝ)^59
        have hw : |(-1791107101/10000000000 : ℝ)|=(1791107101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4801532093/10000000000 : ℝ)|^75 ≤ (39352684867919/100000000000000 : ℝ)^59
        have hw : |(-4801532093/10000000000 : ℝ)|=(4801532093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314054_s1_s1_2 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2688713221/5000000000 : ℝ)*x 0 + (166158159/312500000 : ℝ)*x 1 + (801204271/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688713221/5000000000 : ℝ)^75 ≤ (22723746432443/50000000000000 : ℝ)^59 := by
    have hnat : (2688713221 : ℕ)^75*50000000000000^59 ≤ 22723746432443^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688713221 5000000000 22723746432443 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (166158159/312500000 : ℝ)^75 ≤ (44799949160417/100000000000000 : ℝ)^59 := by
    have hnat : (166158159 : ℕ)^75*100000000000000^59 ≤ 44799949160417^59*312500000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166158159 312500000 44799949160417 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (801204271/5000000000 : ℝ)^75 ≤ (2438139489341/25000000000000 : ℝ)^59 := by
    have hnat : (801204271 : ℕ)^75*25000000000000^59 ≤ 2438139489341^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      801204271 5000000000 2438139489341 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688713221/5000000000 : ℝ), (166158159/312500000 : ℝ), (801204271/5000000000 : ℝ)] ![(22723746432443/50000000000000 : ℝ), (44799949160417/100000000000000 : ℝ), (2438139489341/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688713221/5000000000 : ℝ)|^75 ≤ (22723746432443/50000000000000 : ℝ)^59
        have hw : |(2688713221/5000000000 : ℝ)|=(2688713221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(166158159/312500000 : ℝ)|^75 ≤ (44799949160417/100000000000000 : ℝ)^59
        have hw : |(166158159/312500000 : ℝ)|=(166158159/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(801204271/5000000000 : ℝ)|^75 ≤ (2438139489341/25000000000000 : ℝ)^59
        have hw : |(801204271/5000000000 : ℝ)|=(801204271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314054_s1_s1_6 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2680346083/5000000000 : ℝ)*x 0 + (5313898539/10000000000 : ℝ)*x 1 + (-407487647/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2680346083/5000000000 : ℝ)^75 ≤ (45267784538733/100000000000000 : ℝ)^59 := by
    have hnat : (2680346083 : ℕ)^75*100000000000000^59 ≤ 45267784538733^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2680346083 5000000000 45267784538733 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5313898539/10000000000 : ℝ)^75 ≤ (5595759874023/12500000000000 : ℝ)^59 := by
    have hnat : (5313898539 : ℕ)^75*12500000000000^59 ≤ 5595759874023^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5313898539 10000000000 5595759874023 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (407487647/2500000000 : ℝ)^75 ≤ (9966136455019/100000000000000 : ℝ)^59 := by
    have hnat : (407487647 : ℕ)^75*100000000000000^59 ≤ 9966136455019^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407487647 2500000000 9966136455019 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2680346083/5000000000 : ℝ), (5313898539/10000000000 : ℝ), (-407487647/2500000000 : ℝ)] ![(45267784538733/100000000000000 : ℝ), (5595759874023/12500000000000 : ℝ), (9966136455019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2680346083/5000000000 : ℝ)|^75 ≤ (45267784538733/100000000000000 : ℝ)^59
        have hw : |(2680346083/5000000000 : ℝ)|=(2680346083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5313898539/10000000000 : ℝ)|^75 ≤ (5595759874023/12500000000000 : ℝ)^59
        have hw : |(5313898539/10000000000 : ℝ)|=(5313898539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-407487647/2500000000 : ℝ)|^75 ≤ (9966136455019/100000000000000 : ℝ)^59
        have hw : |(-407487647/2500000000 : ℝ)|=(407487647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314054_s1_s1_7 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-241075417/5000000000 : ℝ)*x 0 + (3362795033/10000000000 : ℝ)*x 1 + (-7794966967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (241075417/5000000000 : ℝ)^75 ≤ (16552744683/781250000000 : ℝ)^59 := by
    have hnat : (241075417 : ℕ)^75*781250000000^59 ≤ 16552744683^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241075417 5000000000 16552744683 781250000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3362795033/10000000000 : ℝ)^75 ≤ (6255873687753/25000000000000 : ℝ)^59 := by
    have hnat : (3362795033 : ℕ)^75*25000000000000^59 ≤ 6255873687753^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3362795033 10000000000 6255873687753 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7794966967/10000000000 : ℝ)^75 ≤ (36428876957173/50000000000000 : ℝ)^59 := by
    have hnat : (7794966967 : ℕ)^75*50000000000000^59 ≤ 36428876957173^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7794966967 10000000000 36428876957173 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-241075417/5000000000 : ℝ), (3362795033/10000000000 : ℝ), (-7794966967/10000000000 : ℝ)] ![(16552744683/781250000000 : ℝ), (6255873687753/25000000000000 : ℝ), (36428876957173/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-241075417/5000000000 : ℝ)|^75 ≤ (16552744683/781250000000 : ℝ)^59
        have hw : |(-241075417/5000000000 : ℝ)|=(241075417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3362795033/10000000000 : ℝ)|^75 ≤ (6255873687753/25000000000000 : ℝ)^59
        have hw : |(3362795033/10000000000 : ℝ)|=(3362795033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7794966967/10000000000 : ℝ)|^75 ≤ (36428876957173/50000000000000 : ℝ)^59
        have hw : |(-7794966967/10000000000 : ℝ)|=(7794966967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314054_s1_s1_8 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4737676791/10000000000 : ℝ)*x 0 + (-734326213/10000000000 : ℝ)*x 1 + (-1297545109/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4737676791/10000000000 : ℝ)^75 ≤ (4836076764959/12500000000000 : ℝ)^59 := by
    have hnat : (4737676791 : ℕ)^75*12500000000000^59 ≤ 4836076764959^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4737676791 10000000000 4836076764959 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (734326213/10000000000 : ℝ)^75 ≤ (723375024521/20000000000000 : ℝ)^59 := by
    have hnat : (734326213 : ℕ)^75*20000000000000^59 ≤ 723375024521^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      734326213 10000000000 723375024521 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1297545109/2000000000 : ℝ)^75 ≤ (57694510751229/100000000000000 : ℝ)^59 := by
    have hnat : (1297545109 : ℕ)^75*100000000000000^59 ≤ 57694510751229^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1297545109 2000000000 57694510751229 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4737676791/10000000000 : ℝ), (-734326213/10000000000 : ℝ), (-1297545109/2000000000 : ℝ)] ![(4836076764959/12500000000000 : ℝ), (723375024521/20000000000000 : ℝ), (57694510751229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4737676791/10000000000 : ℝ)|^75 ≤ (4836076764959/12500000000000 : ℝ)^59
        have hw : |(4737676791/10000000000 : ℝ)|=(4737676791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-734326213/10000000000 : ℝ)|^75 ≤ (723375024521/20000000000000 : ℝ)^59
        have hw : |(-734326213/10000000000 : ℝ)|=(734326213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1297545109/2000000000 : ℝ)|^75 ≤ (57694510751229/100000000000000 : ℝ)^59
        have hw : |(-1297545109/2000000000 : ℝ)|=(1297545109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314054_s1_s1_9 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (167370381/400000000 : ℝ)*x 0 + (1425259631/2000000000 : ℝ)*x 1 + (226307193/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167370381/400000000 : ℝ)^75 ≤ (16518732345399/50000000000000 : ℝ)^59 := by
    have hnat : (167370381 : ℕ)^75*50000000000000^59 ≤ 16518732345399^59*400000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167370381 400000000 16518732345399 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1425259631/2000000000 : ℝ)^75 ≤ (65007385170083/100000000000000 : ℝ)^59 := by
    have hnat : (1425259631 : ℕ)^75*100000000000000^59 ≤ 65007385170083^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1425259631 2000000000 65007385170083 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (226307193/5000000000 : ℝ)^75 ≤ (391030025363/20000000000000 : ℝ)^59 := by
    have hnat : (226307193 : ℕ)^75*20000000000000^59 ≤ 391030025363^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226307193 5000000000 391030025363 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167370381/400000000 : ℝ), (1425259631/2000000000 : ℝ), (226307193/5000000000 : ℝ)] ![(16518732345399/50000000000000 : ℝ), (65007385170083/100000000000000 : ℝ), (391030025363/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167370381/400000000 : ℝ)|^75 ≤ (16518732345399/50000000000000 : ℝ)^59
        have hw : |(167370381/400000000 : ℝ)|=(167370381/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1425259631/2000000000 : ℝ)|^75 ≤ (65007385170083/100000000000000 : ℝ)^59
        have hw : |(1425259631/2000000000 : ℝ)|=(1425259631/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(226307193/5000000000 : ℝ)|^75 ≤ (391030025363/20000000000000 : ℝ)^59
        have hw : |(226307193/5000000000 : ℝ)|=(226307193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314054_s1_s1_13 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (885502881/2000000000 : ℝ)*x 0 + (3463919013/5000000000 : ℝ)*x 1 + (-421747379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (885502881/2000000000 : ℝ)^75 ≤ (35497957738477/100000000000000 : ℝ)^59 := by
    have hnat : (885502881 : ℕ)^75*100000000000000^59 ≤ 35497957738477^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      885502881 2000000000 35497957738477 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3463919013/5000000000 : ℝ)^75 ≤ (7839349063167/12500000000000 : ℝ)^59 := by
    have hnat : (3463919013 : ℕ)^75*12500000000000^59 ≤ 7839349063167^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3463919013 5000000000 7839349063167 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (421747379/10000000000 : ℝ)^75 ≤ (1787249747747/100000000000000 : ℝ)^59 := by
    have hnat : (421747379 : ℕ)^75*100000000000000^59 ≤ 1787249747747^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421747379 10000000000 1787249747747 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(885502881/2000000000 : ℝ), (3463919013/5000000000 : ℝ), (-421747379/10000000000 : ℝ)] ![(35497957738477/100000000000000 : ℝ), (7839349063167/12500000000000 : ℝ), (1787249747747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(885502881/2000000000 : ℝ)|^75 ≤ (35497957738477/100000000000000 : ℝ)^59
        have hw : |(885502881/2000000000 : ℝ)|=(885502881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3463919013/5000000000 : ℝ)|^75 ≤ (7839349063167/12500000000000 : ℝ)^59
        have hw : |(3463919013/5000000000 : ℝ)|=(3463919013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-421747379/10000000000 : ℝ)|^75 ≤ (1787249747747/100000000000000 : ℝ)^59
        have hw : |(-421747379/10000000000 : ℝ)|=(421747379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314054_s1_s1_14 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-5567213/10000000000 : ℝ)*x 0 + (3658806463/10000000000 : ℝ)*x 1 + (-773419273/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5567213/10000000000 : ℝ)^75 ≤ (7296237229/100000000000000 : ℝ)^59 := by
    have hnat : (5567213 : ℕ)^75*100000000000000^59 ≤ 7296237229^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5567213 10000000000 7296237229 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3658806463/10000000000 : ℝ)^75 ≤ (27856273246071/100000000000000 : ℝ)^59 := by
    have hnat : (3658806463 : ℕ)^75*100000000000000^59 ≤ 27856273246071^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3658806463 10000000000 27856273246071 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (773419273/1000000000 : ℝ)^75 ≤ (2885457220077/4000000000000 : ℝ)^59 := by
    have hnat : (773419273 : ℕ)^75*4000000000000^59 ≤ 2885457220077^59*1000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      773419273 1000000000 2885457220077 4000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5567213/10000000000 : ℝ), (3658806463/10000000000 : ℝ), (-773419273/1000000000 : ℝ)] ![(7296237229/100000000000000 : ℝ), (27856273246071/100000000000000 : ℝ), (2885457220077/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5567213/10000000000 : ℝ)|^75 ≤ (7296237229/100000000000000 : ℝ)^59
        have hw : |(-5567213/10000000000 : ℝ)|=(5567213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3658806463/10000000000 : ℝ)|^75 ≤ (27856273246071/100000000000000 : ℝ)^59
        have hw : |(3658806463/10000000000 : ℝ)|=(3658806463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-773419273/1000000000 : ℝ)|^75 ≤ (2885457220077/4000000000000 : ℝ)^59
        have hw : |(-773419273/1000000000 : ℝ)|=(773419273/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314054_s1_s1_15 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1956998247/5000000000 : ℝ)*x 0 + (-408879267/2500000000 : ℝ)*x 1 + (-3329675343/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1956998247/5000000000 : ℝ)^75 ≤ (3034901619087/10000000000000 : ℝ)^59 := by
    have hnat : (1956998247 : ℕ)^75*10000000000000^59 ≤ 3034901619087^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1956998247 5000000000 3034901619087 10000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (408879267/2500000000 : ℝ)^75 ≤ (625588876867/6250000000000 : ℝ)^59 := by
    have hnat : (408879267 : ℕ)^75*6250000000000^59 ≤ 625588876867^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408879267 2500000000 625588876867 6250000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3329675343/5000000000 : ℝ)^75 ≤ (29820780882409/50000000000000 : ℝ)^59 := by
    have hnat : (3329675343 : ℕ)^75*50000000000000^59 ≤ 29820780882409^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3329675343 5000000000 29820780882409 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1956998247/5000000000 : ℝ), (-408879267/2500000000 : ℝ), (-3329675343/5000000000 : ℝ)] ![(3034901619087/10000000000000 : ℝ), (625588876867/6250000000000 : ℝ), (29820780882409/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1956998247/5000000000 : ℝ)|^75 ≤ (3034901619087/10000000000000 : ℝ)^59
        have hw : |(1956998247/5000000000 : ℝ)|=(1956998247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-408879267/2500000000 : ℝ)|^75 ≤ (625588876867/6250000000000 : ℝ)^59
        have hw : |(-408879267/2500000000 : ℝ)|=(408879267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3329675343/5000000000 : ℝ)|^75 ≤ (29820780882409/50000000000000 : ℝ)^59
        have hw : |(-3329675343/5000000000 : ℝ)|=(3329675343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314054_s1_s1_16 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3666336691/5000000000 : ℝ)*x 0 + (3863475213/10000000000 : ℝ)*x 1 + (9217883/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3666336691/5000000000 : ℝ)^75 ≤ (2696393712709/4000000000000 : ℝ)^59 := by
    have hnat : (3666336691 : ℕ)^75*4000000000000^59 ≤ 2696393712709^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3666336691 5000000000 2696393712709 4000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3863475213/10000000000 : ℝ)^75 ≤ (5970383043409/20000000000000 : ℝ)^59 := by
    have hnat : (3863475213 : ℕ)^75*20000000000000^59 ≤ 5970383043409^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3863475213 10000000000 5970383043409 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9217883/156250000 : ℝ)^75 ≤ (2738241955519/100000000000000 : ℝ)^59 := by
    have hnat : (9217883 : ℕ)^75*100000000000000^59 ≤ 2738241955519^59*156250000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9217883 156250000 2738241955519 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3666336691/5000000000 : ℝ), (3863475213/10000000000 : ℝ), (9217883/156250000 : ℝ)] ![(2696393712709/4000000000000 : ℝ), (5970383043409/20000000000000 : ℝ), (2738241955519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3666336691/5000000000 : ℝ)|^75 ≤ (2696393712709/4000000000000 : ℝ)^59
        have hw : |(3666336691/5000000000 : ℝ)|=(3666336691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3863475213/10000000000 : ℝ)|^75 ≤ (5970383043409/20000000000000 : ℝ)^59
        have hw : |(3863475213/10000000000 : ℝ)|=(3863475213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9217883/156250000 : ℝ)|^75 ≤ (2738241955519/100000000000000 : ℝ)^59
        have hw : |(9217883/156250000 : ℝ)|=(9217883/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314054_s1_s1_20 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (684082333/1000000000 : ℝ)*x 0 + (1041837913/2500000000 : ℝ)*x 1 + (-1008992639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (684082333/1000000000 : ℝ)^75 ≤ (12343036043853/20000000000000 : ℝ)^59 := by
    have hnat : (684082333 : ℕ)^75*20000000000000^59 ≤ 12343036043853^59*1000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684082333 1000000000 12343036043853 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1041837913/2500000000 : ℝ)^75 ≤ (16433928005399/50000000000000 : ℝ)^59 := by
    have hnat : (1041837913 : ℕ)^75*50000000000000^59 ≤ 16433928005399^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041837913 2500000000 16433928005399 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1008992639/10000000000 : ℝ)^75 ≤ (1354240938149/25000000000000 : ℝ)^59 := by
    have hnat : (1008992639 : ℕ)^75*25000000000000^59 ≤ 1354240938149^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008992639 10000000000 1354240938149 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(684082333/1000000000 : ℝ), (1041837913/2500000000 : ℝ), (-1008992639/10000000000 : ℝ)] ![(12343036043853/20000000000000 : ℝ), (16433928005399/50000000000000 : ℝ), (1354240938149/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(684082333/1000000000 : ℝ)|^75 ≤ (12343036043853/20000000000000 : ℝ)^59
        have hw : |(684082333/1000000000 : ℝ)|=(684082333/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1041837913/2500000000 : ℝ)|^75 ≤ (16433928005399/50000000000000 : ℝ)^59
        have hw : |(1041837913/2500000000 : ℝ)|=(1041837913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1008992639/10000000000 : ℝ)|^75 ≤ (1354240938149/25000000000000 : ℝ)^59
        have hw : |(-1008992639/10000000000 : ℝ)|=(1008992639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314054_s1_s1_21 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (14649/1000000000 : ℝ)*x 0 + (5657902309/10000000000 : ℝ)*x 1 + (-1483708007/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (14649/1000000000 : ℝ)^75 ≤ (7158807/10000000000000 : ℝ)^59 := by
    have hnat : (14649 : ℕ)^75*10000000000000^59 ≤ 7158807^59*1000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14649 1000000000 7158807 10000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5657902309/10000000000 : ℝ)^75 ≤ (48481824476407/100000000000000 : ℝ)^59 := by
    have hnat : (5657902309 : ℕ)^75*100000000000000^59 ≤ 48481824476407^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5657902309 10000000000 48481824476407 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1483708007/2500000000 : ℝ)^75 ≤ (6439762990753/12500000000000 : ℝ)^59 := by
    have hnat : (1483708007 : ℕ)^75*12500000000000^59 ≤ 6439762990753^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1483708007 2500000000 6439762990753 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(14649/1000000000 : ℝ), (5657902309/10000000000 : ℝ), (-1483708007/2500000000 : ℝ)] ![(7158807/10000000000000 : ℝ), (48481824476407/100000000000000 : ℝ), (6439762990753/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(14649/1000000000 : ℝ)|^75 ≤ (7158807/10000000000000 : ℝ)^59
        have hw : |(14649/1000000000 : ℝ)|=(14649/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5657902309/10000000000 : ℝ)|^75 ≤ (48481824476407/100000000000000 : ℝ)^59
        have hw : |(5657902309/10000000000 : ℝ)|=(5657902309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1483708007/2500000000 : ℝ)|^75 ≤ (6439762990753/12500000000000 : ℝ)^59
        have hw : |(-1483708007/2500000000 : ℝ)|=(1483708007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314054_s1_s1_22 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1409097197/2000000000 : ℝ)*x 0 + (-738121397/5000000000 : ℝ)*x 1 + (-3584715319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1409097197/2000000000 : ℝ)^75 ≤ (64071732672451/100000000000000 : ℝ)^59 := by
    have hnat : (1409097197 : ℕ)^75*100000000000000^59 ≤ 64071732672451^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1409097197 2000000000 64071732672451 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (738121397/5000000000 : ℝ)^75 ≤ (2196770348207/25000000000000 : ℝ)^59 := by
    have hnat : (738121397 : ℕ)^75*25000000000000^59 ≤ 2196770348207^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      738121397 5000000000 2196770348207 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3584715319/10000000000 : ℝ)^75 ≤ (27141185922783/100000000000000 : ℝ)^59 := by
    have hnat : (3584715319 : ℕ)^75*100000000000000^59 ≤ 27141185922783^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3584715319 10000000000 27141185922783 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1409097197/2000000000 : ℝ), (-738121397/5000000000 : ℝ), (-3584715319/10000000000 : ℝ)] ![(64071732672451/100000000000000 : ℝ), (2196770348207/25000000000000 : ℝ), (27141185922783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1409097197/2000000000 : ℝ)|^75 ≤ (64071732672451/100000000000000 : ℝ)^59
        have hw : |(1409097197/2000000000 : ℝ)|=(1409097197/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-738121397/5000000000 : ℝ)|^75 ≤ (2196770348207/25000000000000 : ℝ)^59
        have hw : |(-738121397/5000000000 : ℝ)|=(738121397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3584715319/10000000000 : ℝ)|^75 ≤ (27141185922783/100000000000000 : ℝ)^59
        have hw : |(-3584715319/10000000000 : ℝ)|=(3584715319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314054_s1_s1_23 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2177218593/5000000000 : ℝ)*x 0 + (2930394407/5000000000 : ℝ)*x 1 + (274278097/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177218593/5000000000 : ℝ)^75 ≤ (34754839921097/100000000000000 : ℝ)^59 := by
    have hnat : (2177218593 : ℕ)^75*100000000000000^59 ≤ 34754839921097^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177218593 5000000000 34754839921097 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2930394407/5000000000 : ℝ)^75 ≤ (50702445350537/100000000000000 : ℝ)^59 := by
    have hnat : (2930394407 : ℕ)^75*100000000000000^59 ≤ 50702445350537^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2930394407 5000000000 50702445350537 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (274278097/1250000000 : ℝ)^75 ≤ (116341717717/800000000000 : ℝ)^59 := by
    have hnat : (274278097 : ℕ)^75*800000000000^59 ≤ 116341717717^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274278097 1250000000 116341717717 800000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2177218593/5000000000 : ℝ), (2930394407/5000000000 : ℝ), (274278097/1250000000 : ℝ)] ![(34754839921097/100000000000000 : ℝ), (50702445350537/100000000000000 : ℝ), (116341717717/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2177218593/5000000000 : ℝ)|^75 ≤ (34754839921097/100000000000000 : ℝ)^59
        have hw : |(2177218593/5000000000 : ℝ)|=(2177218593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2930394407/5000000000 : ℝ)|^75 ≤ (50702445350537/100000000000000 : ℝ)^59
        have hw : |(2930394407/5000000000 : ℝ)|=(2930394407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(274278097/1250000000 : ℝ)|^75 ≤ (116341717717/800000000000 : ℝ)^59
        have hw : |(274278097/1250000000 : ℝ)|=(274278097/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314054_s1_s1_27 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6608602011/10000000000 : ℝ)*x 0 + (63018419/156250000 : ℝ)*x 1 + (-778787761/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6608602011/10000000000 : ℝ)^75 ≤ (14766098770413/25000000000000 : ℝ)^59 := by
    have hnat : (6608602011 : ℕ)^75*25000000000000^59 ≤ 14766098770413^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6608602011 10000000000 14766098770413 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (63018419/156250000 : ℝ)^75 ≤ (31528580670381/100000000000000 : ℝ)^59 := by
    have hnat : (63018419 : ℕ)^75*100000000000000^59 ≤ 31528580670381^59*156250000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63018419 156250000 31528580670381 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (778787761/5000000000 : ℝ)^75 ≤ (9407024233987/100000000000000 : ℝ)^59 := by
    have hnat : (778787761 : ℕ)^75*100000000000000^59 ≤ 9407024233987^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      778787761 5000000000 9407024233987 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6608602011/10000000000 : ℝ), (63018419/156250000 : ℝ), (-778787761/5000000000 : ℝ)] ![(14766098770413/25000000000000 : ℝ), (31528580670381/100000000000000 : ℝ), (9407024233987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6608602011/10000000000 : ℝ)|^75 ≤ (14766098770413/25000000000000 : ℝ)^59
        have hw : |(6608602011/10000000000 : ℝ)|=(6608602011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(63018419/156250000 : ℝ)|^75 ≤ (31528580670381/100000000000000 : ℝ)^59
        have hw : |(63018419/156250000 : ℝ)|=(63018419/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-778787761/5000000000 : ℝ)|^75 ≤ (9407024233987/100000000000000 : ℝ)^59
        have hw : |(-778787761/5000000000 : ℝ)|=(778787761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c314054_s1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((19533/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(19533/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16319/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(16319/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-72081/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-72081/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((14183/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14183/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(59683/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(59683/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-48193/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-48193/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (15771/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (15771/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (15771/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (15771/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15771/20000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15771/20000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (87867/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have s1_pow0 : (19533/25000 : ℝ) ^ (37/8 : ℝ) ≤ (1996245137547971441/6250000000000000000 : ℝ) := by
    have hpowers : (19533/25000 : ℝ)^37 ≤ (1996245137547971441/6250000000000000000 : ℝ)^8 := by
      have hnat : (19533 : ℕ)^37*6250000000000000000^8 ≤ 1996245137547971441^8*25000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19533 25000 1996245137547971441 6250000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19533/25000 : ℝ)) (X := (1996245137547971441/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (8246245137547971441/6250000000000000000 : ℝ) ≤ (2123524555112921/2000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (8246245137547971441/6250000000000000000 : ℝ)^8 ≤ (2123524555112921/2000000000000000 : ℝ)^37 := by
      have hnat : (8246245137547971441 : ℕ)^8*2000000000000000^37 ≤ 2123524555112921^37*6250000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8246245137547971441 6250000000000000000 2123524555112921 2000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2123524555112921/2000000000000000 : ℝ)) (X := (8246245137547971441/6250000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (5121245137547971441/3125000000000000000 : ℝ) ≤ (11127148938321079/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (5121245137547971441/3125000000000000000 : ℝ)^8 ≤ (11127148938321079/10000000000000000 : ℝ)^37 := by
      have hnat : (5121245137547971441 : ℕ)^8*10000000000000000^37 ≤ 11127148938321079^37*3125000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5121245137547971441 3125000000000000000 11127148938321079 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11127148938321079/10000000000000000 : ℝ)) (X := (5121245137547971441/3125000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(41174851704307/520880000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(84921027126079/1302200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (19533/25000 : ℝ)) (alpha := (41174851704307/520880000000000 : ℝ)) (beta := (84921027126079/1302200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (19533/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(41174851704307/520880000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(84921027126079/1302200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (16319/20000 : ℝ) ^ (37/8 : ℝ) ≤ (9758519008650057773/25000000000000000000 : ℝ) := by
    have hpowers : (16319/20000 : ℝ)^37 ≤ (9758519008650057773/25000000000000000000 : ℝ)^8 := by
      have hnat : (16319 : ℕ)^37*25000000000000000000^8 ≤ 9758519008650057773^8*20000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16319 20000 9758519008650057773 25000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16319/20000 : ℝ)) (X := (9758519008650057773/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (34758519008650057773/25000000000000000000 : ℝ) ≤ (10738537454463191/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (34758519008650057773/25000000000000000000 : ℝ)^8 ≤ (10738537454463191/10000000000000000 : ℝ)^37 := by
      have hnat : (34758519008650057773 : ℕ)^8*10000000000000000^37 ≤ 10738537454463191^37*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        34758519008650057773 25000000000000000000 10738537454463191 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10738537454463191/10000000000000000 : ℝ)) (X := (34758519008650057773/25000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (22258519008650057773/12500000000000000000 : ℝ) ≤ (11328719172068387/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (22258519008650057773/12500000000000000000 : ℝ)^8 ≤ (11328719172068387/10000000000000000 : ℝ)^37 := by
      have hnat : (22258519008650057773 : ℕ)^8*10000000000000000^37 ≤ 11328719172068387^37*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22258519008650057773 12500000000000000000 11328719172068387 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11328719172068387/10000000000000000 : ℝ)) (X := (22258519008650057773/12500000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(738537454463191/8159500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(147545429401299/2039875000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (16319/20000 : ℝ)) (alpha := (738537454463191/8159500000000000 : ℝ)) (beta := (147545429401299/2039875000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (16319/20000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(738537454463191/8159500000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(147545429401299/2039875000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (72081/100000 : ℝ) ^ (37/8 : ℝ) ≤ (21999925713154733649/100000000000000000000 : ℝ) := by
    have hpowers : (72081/100000 : ℝ)^37 ≤ (21999925713154733649/100000000000000000000 : ℝ)^8 := by
      have hnat : (72081 : ℕ)^37*100000000000000000000^8 ≤ 21999925713154733649^8*100000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        72081 100000 21999925713154733649 100000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (72081/100000 : ℝ)) (X := (21999925713154733649/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (121999925713154733649/100000000000000000000 : ℝ) ≤ (2609830770875429/2500000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (121999925713154733649/100000000000000000000 : ℝ)^8 ≤ (2609830770875429/2500000000000000 : ℝ)^37 := by
      have hnat : (121999925713154733649 : ℕ)^8*2500000000000000^37 ≤ 2609830770875429^37*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        121999925713154733649 100000000000000000000 2609830770875429 2500000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2609830770875429/2500000000000000 : ℝ)) (X := (121999925713154733649/100000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (71999925713154733649/50000000000000000000 : ℝ) ≤ (5410164200218371/5000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (71999925713154733649/50000000000000000000 : ℝ)^8 ≤ (5410164200218371/5000000000000000 : ℝ)^37 := by
      have hnat : (71999925713154733649 : ℕ)^8*5000000000000000^37 ≤ 5410164200218371^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        71999925713154733649 50000000000000000000 5410164200218371 5000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5410164200218371/5000000000000000 : ℝ)) (X := (71999925713154733649/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(109830770875429/1802025000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(190502658467513/3604050000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (72081/100000 : ℝ)) (alpha := (109830770875429/1802025000000000 : ℝ)) (beta := (190502658467513/3604050000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (72081/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(109830770875429/1802025000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(190502658467513/3604050000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-535285069/10000000000 : ℝ)*X 0 0+(4566457533/10000000000 : ℝ)*X 0 1+(-3374326297/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314054_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((717892551/1250000000 : ℝ)*X 1 0+(-1791107101/10000000000 : ℝ)*X 1 1+(-4801532093/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314054_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2688713221/5000000000 : ℝ)*X 2 0+(166158159/312500000 : ℝ)*X 2 1+(801204271/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314054_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((2680346083/5000000000 : ℝ)*X 0 0+(5313898539/10000000000 : ℝ)*X 0 1+(-407487647/2500000000 : ℝ)*X 0 2+(2680346083/5000000000 : ℝ)*X 1 0+(5313898539/10000000000 : ℝ)*X 1 1+(-407487647/2500000000 : ℝ)*X 1 2+(2680346083/5000000000 : ℝ)*X 2 0+(5313898539/10000000000 : ℝ)*X 2 1+(-407487647/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314054_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-241075417/5000000000 : ℝ)*X 0 0+(3362795033/10000000000 : ℝ)*X 0 1+(-7794966967/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314054_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((4737676791/10000000000 : ℝ)*X 1 0+(-734326213/10000000000 : ℝ)*X 1 1+(-1297545109/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314054_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((167370381/400000000 : ℝ)*X 2 0+(1425259631/2000000000 : ℝ)*X 2 1+(226307193/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314054_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((885502881/2000000000 : ℝ)*X 0 0+(3463919013/5000000000 : ℝ)*X 0 1+(-421747379/10000000000 : ℝ)*X 0 2+(885502881/2000000000 : ℝ)*X 1 0+(3463919013/5000000000 : ℝ)*X 1 1+(-421747379/10000000000 : ℝ)*X 1 2+(885502881/2000000000 : ℝ)*X 2 0+(3463919013/5000000000 : ℝ)*X 2 1+(-421747379/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314054_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-5567213/10000000000 : ℝ)*X 0 0+(3658806463/10000000000 : ℝ)*X 0 1+(-773419273/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314054_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((1956998247/5000000000 : ℝ)*X 1 0+(-408879267/2500000000 : ℝ)*X 1 1+(-3329675343/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314054_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((3666336691/5000000000 : ℝ)*X 2 0+(3863475213/10000000000 : ℝ)*X 2 1+(9217883/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314054_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((684082333/1000000000 : ℝ)*X 0 0+(1041837913/2500000000 : ℝ)*X 0 1+(-1008992639/10000000000 : ℝ)*X 0 2+(684082333/1000000000 : ℝ)*X 1 0+(1041837913/2500000000 : ℝ)*X 1 1+(-1008992639/10000000000 : ℝ)*X 1 2+(684082333/1000000000 : ℝ)*X 2 0+(1041837913/2500000000 : ℝ)*X 2 1+(-1008992639/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314054_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((14649/1000000000 : ℝ)*X 0 0+(5657902309/10000000000 : ℝ)*X 0 1+(-1483708007/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314054_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((1409097197/2000000000 : ℝ)*X 1 0+(-738121397/5000000000 : ℝ)*X 1 1+(-3584715319/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314054_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((2177218593/5000000000 : ℝ)*X 2 0+(2930394407/5000000000 : ℝ)*X 2 1+(274278097/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314054_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((6608602011/10000000000 : ℝ)*X 0 0+(63018419/156250000 : ℝ)*X 0 1+(-778787761/5000000000 : ℝ)*X 0 2+(6608602011/10000000000 : ℝ)*X 1 0+(63018419/156250000 : ℝ)*X 1 1+(-778787761/5000000000 : ℝ)*X 1 2+(6608602011/10000000000 : ℝ)*X 2 0+(63018419/156250000 : ℝ)*X 2 1+(-778787761/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314054_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((14183/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14183/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (103523954604502984065742291/10429319800000000000000000000000 : ℝ) := by norm_num
    linear_combination (93975067717/250000000000 : ℝ)*(base7) + (24903023961/250000000000 : ℝ)*(base39) + (277343429527/1000000000000 : ℝ)*(base60) + (2678707798219/1000000000000 : ℝ)*(major_s1_0) + (2678707798219/1000000000000 : ℝ)*(major_s1_1) + (2678707798219/1000000000000 : ℝ)*(major_s1_2) + (2894171/1000000000000 : ℝ)*(sp_s1_0) + (3580333009987/1000000000000 : ℝ)*(sp_s1_7) + (358044711767/100000000000 : ℝ)*(sp_s1_8) + (716090126883/200000000000 : ℝ)*(sp_s1_9) + (1932664009961/1000000000000 : ℝ)*(sp_s1_13) + (29445941/250000000000 : ℝ)*(sp_s1_14) + (1642563/250000000000 : ℝ)*(sp_s1_22) + (3053507/1000000000000 : ℝ)*(sp_s1_23) + (389190934773/250000000000 : ℝ)*(f.failure) + (1790226843961/500000000000 : ℝ)*(f.sum) + (368089847231253267671/588144919500000000000000000000000 : ℝ)*base62 + (1424762313974387/3604050000000000000000000000 : ℝ)*base65 + (66698830300657/254984375000000000000000000 : ℝ)*base66 + (1798870648953073/3604050000000000000000000000 : ℝ)*base68 + (36989818345027205581/187727756400000000000000000000000 : ℝ)*base71 + (214491297869841/1302200000000000000000000000 : ℝ)*base73 + (391533249763929/8159500000000000000000000000 : ℝ)*base75 + (97399384441/520880000000000000000000000 : ℝ)*base77 + (43493434526839110067/106253009000000000000000000000000 : ℝ)*base79 + (19663/25000000000000000 : ℝ)*base86 + (19663/25000000000000000 : ℝ)*base88 + (19663/25000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(59683/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(59683/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (15371342372047251070791587943839/2552941047243000000000000000000000000 : ℝ) := by norm_num
    linear_combination (72802945483/125000000000 : ℝ)*(base7) + (339091/500000000000 : ℝ)*(base39) + (2451511065527/1000000000000 : ℝ)*(major_s1_0) + (2451511065527/1000000000000 : ℝ)*(major_s1_1) + (2451511065527/1000000000000 : ℝ)*(major_s1_2) + (2348717/500000000000 : ℝ)*(sp_s1_1) + (1105027/250000000000 : ℝ)*(sp_s1_2) + (14960571/500000000000 : ℝ)*(sp_s1_8) + (3137117646393/1000000000000 : ℝ)*(sp_s1_14) + (627417569199/200000000000 : ℝ)*(sp_s1_15) + (3137118044463/1000000000000 : ℝ)*(sp_s1_16) + (2007141720193/1000000000000 : ℝ)*(sp_s1_20) + (2409089/500000000000 : ℝ)*(sp_s1_21) + (74279/10000000000 : ℝ)*(sp_s1_27) + (1424725584229/1000000000000 : ℝ)*(f.failure) + (3137122464571/1000000000000 : ℝ)*(f.sum) + (183017348308435835807/588144919500000000000000000000000 : ℝ)*base63 + (518374448947283/1802025000000000000000000000 : ℝ)*base65 + (801113048706171/4079750000000000000000000000 : ℝ)*base66 + (391334443807249/901012500000000000000000000 : ℝ)*base69 + (34375700120557736993/187727756400000000000000000000000 : ℝ)*base71 + (466102705612587/1302200000000000000000000000 : ℝ)*base72 + (3857584844304257/8159500000000000000000000000 : ℝ)*base75 + (133822847161197/520880000000000000000000000 : ℝ)*base77 + (23957457549909477289/106253009000000000000000000000000 : ℝ)*base78 + (199/100000000000000000 : ℝ)*base86 + (199/100000000000000000 : ℝ)*base88 + (199/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-48193/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-48193/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1748732443229789865203102340493/150173002779000000000000000000000000 : ℝ) := by norm_num
    linear_combination (289682168143/500000000000 : ℝ)*(base7) + (110101/1000000000000 : ℝ)*(base15) + (219967084441/500000000000 : ℝ)*(base39) + (2652859307789/1000000000000 : ℝ)*(major_s1_0) + (2652859307789/1000000000000 : ℝ)*(major_s1_1) + (2652859307789/1000000000000 : ℝ)*(major_s1_2) + (2646611/62500000000 : ℝ)*(sp_s1_2) + (12439203/1000000000000 : ℝ)*(sp_s1_6) + (8502903/500000000000 : ℝ)*(sp_s1_9) + (16673727/200000000000 : ℝ)*(sp_s1_20) + (856148279939/250000000000 : ℝ)*(sp_s1_21) + (684918601931/200000000000 : ℝ)*(sp_s1_22) + (1712266884087/500000000000 : ℝ)*(sp_s1_23) + (530252525441/250000000000 : ℝ)*(sp_s1_27) + (385435393329/250000000000 : ℝ)*(f.failure) + (856148279939/250000000000 : ℝ)*(f.sum) + (137514993385273092001/588144919500000000000000000000000 : ℝ)*base62 + (10857627758071/450506250000000000000000000 : ℝ)*base64 + (657248030623447/4079750000000000000000000000 : ℝ)*base66 + (33454286428027/3604050000000000000000000000 : ℝ)*base69 + (2869293783069450077/11042809200000000000000000000000 : ℝ)*base70 + (13263699208037/76600000000000000000000000 : ℝ)*base72 + (588203788075401/8159500000000000000000000000 : ℝ)*base74 + (1531904207041/30640000000000000000000000 : ℝ)*base76 + (278428539536858781/6250177000000000000000000000000 : ℝ)*base79 + (2701/25000000000000000 : ℝ)*base87 + (2701/25000000000000000 : ℝ)*base89 + (2701/25000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((19533/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(19533/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16319/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(16319/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-72081/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-72081/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((14183/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14183/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(59683/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(59683/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-48193/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-48193/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c314054_s1 p hpa hpb X hX hprev0

#print axioms solution
