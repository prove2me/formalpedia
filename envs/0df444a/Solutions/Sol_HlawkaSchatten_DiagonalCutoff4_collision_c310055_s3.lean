-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c310055_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:27:05.551819+00:00
-- url     : https://prove2.me/submissions/a56acf0a-1111-4ae6-bb36-63be596b7da6

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
theorem collision_support_c310055_s3_s3_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2055769073/10000000000 : ℝ)*x 0 + (5686308747/10000000000 : ℝ)*x 1 + (4800213763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2055769073/10000000000 : ℝ)^71 ≤ (6487573915571/50000000000000 : ℝ)^55 := by
    have hnat : (2055769073 : ℕ)^71*50000000000000^55 ≤ 6487573915571^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2055769073 10000000000 6487573915571 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5686308747/10000000000 : ℝ)^71 ≤ (24125614624317/50000000000000 : ℝ)^55 := by
    have hnat : (5686308747 : ℕ)^71*50000000000000^55 ≤ 24125614624317^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5686308747 10000000000 24125614624317 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4800213763/10000000000 : ℝ)^71 ≤ (38773622906251/100000000000000 : ℝ)^55 := by
    have hnat : (4800213763 : ℕ)^71*100000000000000^55 ≤ 38773622906251^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4800213763 10000000000 38773622906251 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2055769073/10000000000 : ℝ), (5686308747/10000000000 : ℝ), (4800213763/10000000000 : ℝ)] ![(6487573915571/50000000000000 : ℝ), (24125614624317/50000000000000 : ℝ), (38773622906251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2055769073/10000000000 : ℝ)|^71 ≤ (6487573915571/50000000000000 : ℝ)^55
        have hw : |(-2055769073/10000000000 : ℝ)|=(2055769073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5686308747/10000000000 : ℝ)|^71 ≤ (24125614624317/50000000000000 : ℝ)^55
        have hw : |(5686308747/10000000000 : ℝ)|=(5686308747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4800213763/10000000000 : ℝ)|^71 ≤ (38773622906251/100000000000000 : ℝ)^55
        have hw : |(4800213763/10000000000 : ℝ)|=(4800213763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s3_s3_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4794961179/10000000000 : ℝ)*x 0 + (-1152474063/10000000000 : ℝ)*x 1 + (3152557791/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4794961179/10000000000 : ℝ)^71 ≤ (1935943070389/5000000000000 : ℝ)^55 := by
    have hnat : (4794961179 : ℕ)^71*5000000000000^55 ≤ 1935943070389^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4794961179 10000000000 1935943070389 5000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1152474063/10000000000 : ℝ)^71 ≤ (6146829034949/100000000000000 : ℝ)^55 := by
    have hnat : (1152474063 : ℕ)^71*100000000000000^55 ≤ 6146829034949^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1152474063 10000000000 6146829034949 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3152557791/5000000000 : ℝ)^71 ≤ (13783577384589/25000000000000 : ℝ)^55 := by
    have hnat : (3152557791 : ℕ)^71*25000000000000^55 ≤ 13783577384589^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3152557791 5000000000 13783577384589 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4794961179/10000000000 : ℝ), (-1152474063/10000000000 : ℝ), (3152557791/5000000000 : ℝ)] ![(1935943070389/5000000000000 : ℝ), (6146829034949/100000000000000 : ℝ), (13783577384589/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4794961179/10000000000 : ℝ)|^71 ≤ (1935943070389/5000000000000 : ℝ)^55
        have hw : |(4794961179/10000000000 : ℝ)|=(4794961179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1152474063/10000000000 : ℝ)|^71 ≤ (6146829034949/100000000000000 : ℝ)^55
        have hw : |(-1152474063/10000000000 : ℝ)|=(1152474063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3152557791/5000000000 : ℝ)|^71 ≤ (13783577384589/25000000000000 : ℝ)^55
        have hw : |(3152557791/5000000000 : ℝ)|=(3152557791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s3_s3_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4774327187/10000000000 : ℝ)*x 0 + (5704722783/10000000000 : ℝ)*x 1 + (-82563973/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4774327187/10000000000 : ℝ)^71 ≤ (1925195403349/5000000000000 : ℝ)^55 := by
    have hnat : (4774327187 : ℕ)^71*5000000000000^55 ≤ 1925195403349^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4774327187 10000000000 1925195403349 5000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5704722783/10000000000 : ℝ)^71 ≤ (12113257984809/25000000000000 : ℝ)^55 := by
    have hnat : (5704722783 : ℕ)^71*25000000000000^55 ≤ 12113257984809^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5704722783 10000000000 12113257984809 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82563973/400000000 : ℝ)^71 ≤ (13043059974743/100000000000000 : ℝ)^55 := by
    have hnat : (82563973 : ℕ)^71*100000000000000^55 ≤ 13043059974743^55*400000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82563973 400000000 13043059974743 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4774327187/10000000000 : ℝ), (5704722783/10000000000 : ℝ), (-82563973/400000000 : ℝ)] ![(1925195403349/5000000000000 : ℝ), (12113257984809/25000000000000 : ℝ), (13043059974743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4774327187/10000000000 : ℝ)|^71 ≤ (1925195403349/5000000000000 : ℝ)^55
        have hw : |(4774327187/10000000000 : ℝ)|=(4774327187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5704722783/10000000000 : ℝ)|^71 ≤ (12113257984809/25000000000000 : ℝ)^55
        have hw : |(5704722783/10000000000 : ℝ)|=(5704722783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-82563973/400000000 : ℝ)|^71 ≤ (13043059974743/100000000000000 : ℝ)^55
        have hw : |(-82563973/400000000 : ℝ)|=(82563973/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s3_s3_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6056048619/10000000000 : ℝ)*x 0 + (3977988879/10000000000 : ℝ)*x 1 + (2561793867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6056048619/10000000000 : ℝ)^71 ≤ (52339100648797/100000000000000 : ℝ)^55 := by
    have hnat : (6056048619 : ℕ)^71*100000000000000^55 ≤ 52339100648797^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6056048619 10000000000 52339100648797 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3977988879/10000000000 : ℝ)^71 ≤ (30423001314449/100000000000000 : ℝ)^55 := by
    have hnat : (3977988879 : ℕ)^71*100000000000000^55 ≤ 30423001314449^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3977988879 10000000000 30423001314449 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2561793867/10000000000 : ℝ)^71 ≤ (8618949011593/50000000000000 : ℝ)^55 := by
    have hnat : (2561793867 : ℕ)^71*50000000000000^55 ≤ 8618949011593^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2561793867 10000000000 8618949011593 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6056048619/10000000000 : ℝ), (3977988879/10000000000 : ℝ), (2561793867/10000000000 : ℝ)] ![(52339100648797/100000000000000 : ℝ), (30423001314449/100000000000000 : ℝ), (8618949011593/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6056048619/10000000000 : ℝ)|^71 ≤ (52339100648797/100000000000000 : ℝ)^55
        have hw : |(6056048619/10000000000 : ℝ)|=(6056048619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3977988879/10000000000 : ℝ)|^71 ≤ (30423001314449/100000000000000 : ℝ)^55
        have hw : |(3977988879/10000000000 : ℝ)|=(3977988879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2561793867/10000000000 : ℝ)|^71 ≤ (8618949011593/50000000000000 : ℝ)^55
        have hw : |(2561793867/10000000000 : ℝ)|=(2561793867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s3_s3_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1668926661/10000000000 : ℝ)*x 0 + (4888354281/10000000000 : ℝ)*x 1 + (2940351577/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1668926661/10000000000 : ℝ)^71 ≤ (9913732141577/100000000000000 : ℝ)^55 := by
    have hnat : (1668926661 : ℕ)^71*100000000000000^55 ≤ 9913732141577^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1668926661 10000000000 9913732141577 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4888354281/10000000000 : ℝ)^71 ≤ (39695133750907/100000000000000 : ℝ)^55 := by
    have hnat : (4888354281 : ℕ)^71*100000000000000^55 ≤ 39695133750907^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4888354281 10000000000 39695133750907 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2940351577/5000000000 : ℝ)^71 ≤ (10078226818327/20000000000000 : ℝ)^55 := by
    have hnat : (2940351577 : ℕ)^71*20000000000000^55 ≤ 10078226818327^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2940351577 5000000000 10078226818327 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1668926661/10000000000 : ℝ), (4888354281/10000000000 : ℝ), (2940351577/5000000000 : ℝ)] ![(9913732141577/100000000000000 : ℝ), (39695133750907/100000000000000 : ℝ), (10078226818327/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1668926661/10000000000 : ℝ)|^71 ≤ (9913732141577/100000000000000 : ℝ)^55
        have hw : |(-1668926661/10000000000 : ℝ)|=(1668926661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4888354281/10000000000 : ℝ)|^71 ≤ (39695133750907/100000000000000 : ℝ)^55
        have hw : |(4888354281/10000000000 : ℝ)|=(4888354281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2940351577/5000000000 : ℝ)|^71 ≤ (10078226818327/20000000000000 : ℝ)^55
        have hw : |(2940351577/5000000000 : ℝ)|=(2940351577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s3_s3_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4543081441/10000000000 : ℝ)*x 0 + (-83479343/2500000000 : ℝ)*x 1 + (435045683/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4543081441/10000000000 : ℝ)^71 ≤ (3611359091187/10000000000000 : ℝ)^55 := by
    have hnat : (4543081441 : ℕ)^71*10000000000000^55 ≤ 3611359091187^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4543081441 10000000000 3611359091187 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (83479343/2500000000 : ℝ)^71 ≤ (19407616749/1562500000000 : ℝ)^55 := by
    have hnat : (83479343 : ℕ)^71*1562500000000^55 ≤ 19407616749^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83479343 2500000000 19407616749 1562500000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (435045683/625000000 : ℝ)^71 ≤ (12528864319921/20000000000000 : ℝ)^55 := by
    have hnat : (435045683 : ℕ)^71*20000000000000^55 ≤ 12528864319921^55*625000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435045683 625000000 12528864319921 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4543081441/10000000000 : ℝ), (-83479343/2500000000 : ℝ), (435045683/625000000 : ℝ)] ![(3611359091187/10000000000000 : ℝ), (19407616749/1562500000000 : ℝ), (12528864319921/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4543081441/10000000000 : ℝ)|^71 ≤ (3611359091187/10000000000000 : ℝ)^55
        have hw : |(4543081441/10000000000 : ℝ)|=(4543081441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-83479343/2500000000 : ℝ)|^71 ≤ (19407616749/1562500000000 : ℝ)^55
        have hw : |(-83479343/2500000000 : ℝ)|=(83479343/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(435045683/625000000 : ℝ)|^71 ≤ (12528864319921/20000000000000 : ℝ)^55
        have hw : |(435045683/625000000 : ℝ)|=(435045683/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s3_s3_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4522200777/10000000000 : ℝ)*x 0 + (825651133/1250000000 : ℝ)*x 1 + (-213124587/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4522200777/10000000000 : ℝ)^71 ≤ (8974866232947/25000000000000 : ℝ)^55 := by
    have hnat : (4522200777 : ℕ)^71*25000000000000^55 ≤ 8974866232947^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4522200777 10000000000 8974866232947 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (825651133/1250000000 : ℝ)^71 ≤ (58545016600323/100000000000000 : ℝ)^55 := by
    have hnat : (825651133 : ℕ)^71*100000000000000^55 ≤ 58545016600323^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      825651133 1250000000 58545016600323 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (213124587/2000000000 : ℝ)^71 ≤ (2777759226397/50000000000000 : ℝ)^55 := by
    have hnat : (213124587 : ℕ)^71*50000000000000^55 ≤ 2777759226397^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213124587 2000000000 2777759226397 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4522200777/10000000000 : ℝ), (825651133/1250000000 : ℝ), (-213124587/2000000000 : ℝ)] ![(8974866232947/25000000000000 : ℝ), (58545016600323/100000000000000 : ℝ), (2777759226397/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4522200777/10000000000 : ℝ)|^71 ≤ (8974866232947/25000000000000 : ℝ)^55
        have hw : |(4522200777/10000000000 : ℝ)|=(4522200777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(825651133/1250000000 : ℝ)|^71 ≤ (58545016600323/100000000000000 : ℝ)^55
        have hw : |(825651133/1250000000 : ℝ)|=(825651133/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-213124587/2000000000 : ℝ)|^71 ≤ (2777759226397/50000000000000 : ℝ)^55
        have hw : |(-213124587/2000000000 : ℝ)|=(213124587/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s3_s3_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1027240869/2000000000 : ℝ)*x 0 + (2957007773/5000000000 : ℝ)*x 1 + (632184163/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1027240869/2000000000 : ℝ)^71 ≤ (42312190242741/100000000000000 : ℝ)^55 := by
    have hnat : (1027240869 : ℕ)^71*100000000000000^55 ≤ 42312190242741^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027240869 2000000000 42312190242741 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2957007773/5000000000 : ℝ)^71 ≤ (50759927854079/100000000000000 : ℝ)^55 := by
    have hnat : (2957007773 : ℕ)^71*100000000000000^55 ≤ 50759927854079^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2957007773 5000000000 50759927854079 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (632184163/5000000000 : ℝ)^71 ≤ (6927881895977/100000000000000 : ℝ)^55 := by
    have hnat : (632184163 : ℕ)^71*100000000000000^55 ≤ 6927881895977^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      632184163 5000000000 6927881895977 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1027240869/2000000000 : ℝ), (2957007773/5000000000 : ℝ), (632184163/5000000000 : ℝ)] ![(42312190242741/100000000000000 : ℝ), (50759927854079/100000000000000 : ℝ), (6927881895977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1027240869/2000000000 : ℝ)|^71 ≤ (42312190242741/100000000000000 : ℝ)^55
        have hw : |(1027240869/2000000000 : ℝ)|=(1027240869/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2957007773/5000000000 : ℝ)|^71 ≤ (50759927854079/100000000000000 : ℝ)^55
        have hw : |(2957007773/5000000000 : ℝ)|=(2957007773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(632184163/5000000000 : ℝ)|^71 ≤ (6927881895977/100000000000000 : ℝ)^55
        have hw : |(632184163/5000000000 : ℝ)|=(632184163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s3_s3_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-37177041/400000000 : ℝ)*x 0 + (164155613/312500000 : ℝ)*x 1 + (6006357433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (37177041/400000000 : ℝ)^71 ≤ (4656495021531/100000000000000 : ℝ)^55 := by
    have hnat : (37177041 : ℕ)^71*100000000000000^55 ≤ 4656495021531^55*400000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37177041 400000000 4656495021531 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164155613/312500000 : ℝ)^71 ≤ (43558126960883/100000000000000 : ℝ)^55 := by
    have hnat : (164155613 : ℕ)^71*100000000000000^55 ≤ 43558126960883^55*312500000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164155613 312500000 43558126960883 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6006357433/10000000000 : ℝ)^71 ≤ (51785378009349/100000000000000 : ℝ)^55 := by
    have hnat : (6006357433 : ℕ)^71*100000000000000^55 ≤ 51785378009349^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6006357433 10000000000 51785378009349 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-37177041/400000000 : ℝ), (164155613/312500000 : ℝ), (6006357433/10000000000 : ℝ)] ![(4656495021531/100000000000000 : ℝ), (43558126960883/100000000000000 : ℝ), (51785378009349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-37177041/400000000 : ℝ)|^71 ≤ (4656495021531/100000000000000 : ℝ)^55
        have hw : |(-37177041/400000000 : ℝ)|=(37177041/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164155613/312500000 : ℝ)|^71 ≤ (43558126960883/100000000000000 : ℝ)^55
        have hw : |(164155613/312500000 : ℝ)|=(164155613/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6006357433/10000000000 : ℝ)|^71 ≤ (51785378009349/100000000000000 : ℝ)^55
        have hw : |(6006357433/10000000000 : ℝ)|=(6006357433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s3_s3_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4221884843/10000000000 : ℝ)*x 0 + (-895769667/10000000000 : ℝ)*x 1 + (6966207057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4221884843/10000000000 : ℝ)^71 ≤ (513313648221/1562500000000 : ℝ)^55 := by
    have hnat : (4221884843 : ℕ)^71*1562500000000^55 ≤ 513313648221^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4221884843 10000000000 513313648221 1562500000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (895769667/10000000000 : ℝ)^71 ≤ (4439977255613/100000000000000 : ℝ)^55 := by
    have hnat : (895769667 : ℕ)^71*100000000000000^55 ≤ 4439977255613^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895769667 10000000000 4439977255613 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6966207057/10000000000 : ℝ)^71 ≤ (62707949248903/100000000000000 : ℝ)^55 := by
    have hnat : (6966207057 : ℕ)^71*100000000000000^55 ≤ 62707949248903^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6966207057 10000000000 62707949248903 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4221884843/10000000000 : ℝ), (-895769667/10000000000 : ℝ), (6966207057/10000000000 : ℝ)] ![(513313648221/1562500000000 : ℝ), (4439977255613/100000000000000 : ℝ), (62707949248903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4221884843/10000000000 : ℝ)|^71 ≤ (513313648221/1562500000000 : ℝ)^55
        have hw : |(4221884843/10000000000 : ℝ)|=(4221884843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-895769667/10000000000 : ℝ)|^71 ≤ (4439977255613/100000000000000 : ℝ)^55
        have hw : |(-895769667/10000000000 : ℝ)|=(895769667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6966207057/10000000000 : ℝ)|^71 ≤ (62707949248903/100000000000000 : ℝ)^55
        have hw : |(6966207057/10000000000 : ℝ)|=(6966207057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s3_s3_16 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5982275769/10000000000 : ℝ)*x 0 + (2635806693/5000000000 : ℝ)*x 1 + (-939969947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5982275769/10000000000 : ℝ)^71 ≤ (51517507722253/100000000000000 : ℝ)^55 := by
    have hnat : (5982275769 : ℕ)^71*100000000000000^55 ≤ 51517507722253^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5982275769 10000000000 51517507722253 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2635806693/5000000000 : ℝ)^71 ≤ (8751538330677/20000000000000 : ℝ)^55 := by
    have hnat : (2635806693 : ℕ)^71*20000000000000^55 ≤ 8751538330677^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635806693 5000000000 8751538330677 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (939969947/10000000000 : ℝ)^71 ≤ (4724800618987/100000000000000 : ℝ)^55 := by
    have hnat : (939969947 : ℕ)^71*100000000000000^55 ≤ 4724800618987^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      939969947 10000000000 4724800618987 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5982275769/10000000000 : ℝ), (2635806693/5000000000 : ℝ), (-939969947/10000000000 : ℝ)] ![(51517507722253/100000000000000 : ℝ), (8751538330677/20000000000000 : ℝ), (4724800618987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5982275769/10000000000 : ℝ)|^71 ≤ (51517507722253/100000000000000 : ℝ)^55
        have hw : |(5982275769/10000000000 : ℝ)|=(5982275769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2635806693/5000000000 : ℝ)|^71 ≤ (8751538330677/20000000000000 : ℝ)^55
        have hw : |(2635806693/5000000000 : ℝ)|=(2635806693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-939969947/10000000000 : ℝ)|^71 ≤ (4724800618987/100000000000000 : ℝ)^55
        have hw : |(-939969947/10000000000 : ℝ)|=(939969947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s3_s3_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3732728691/5000000000 : ℝ)*x 0 + (1686623147/5000000000 : ℝ)*x 1 + (1252122451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3732728691/5000000000 : ℝ)^71 ≤ (34284465536157/50000000000000 : ℝ)^55 := by
    have hnat : (3732728691 : ℕ)^71*50000000000000^55 ≤ 34284465536157^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3732728691 5000000000 34284465536157 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1686623147/5000000000 : ℝ)^71 ≤ (24589683548773/100000000000000 : ℝ)^55 := by
    have hnat : (1686623147 : ℕ)^71*100000000000000^55 ≤ 24589683548773^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1686623147 5000000000 24589683548773 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1252122451/10000000000 : ℝ)^71 ≤ (6841385366341/100000000000000 : ℝ)^55 := by
    have hnat : (1252122451 : ℕ)^71*100000000000000^55 ≤ 6841385366341^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1252122451 10000000000 6841385366341 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3732728691/5000000000 : ℝ), (1686623147/5000000000 : ℝ), (1252122451/10000000000 : ℝ)] ![(34284465536157/50000000000000 : ℝ), (24589683548773/100000000000000 : ℝ), (6841385366341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3732728691/5000000000 : ℝ)|^71 ≤ (34284465536157/50000000000000 : ℝ)^55
        have hw : |(3732728691/5000000000 : ℝ)|=(3732728691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1686623147/5000000000 : ℝ)|^71 ≤ (24589683548773/100000000000000 : ℝ)^55
        have hw : |(1686623147/5000000000 : ℝ)|=(1686623147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1252122451/10000000000 : ℝ)|^71 ≤ (6841385366341/100000000000000 : ℝ)^55
        have hw : |(1252122451/10000000000 : ℝ)|=(1252122451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s3_s3_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-453116569/5000000000 : ℝ)*x 0 + (639806467/1000000000 : ℝ)*x 1 + (4851304101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (453116569/5000000000 : ℝ)^71 ≤ (8802815439/195312500000 : ℝ)^55 := by
    have hnat : (453116569 : ℕ)^71*195312500000^55 ≤ 8802815439^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453116569 5000000000 8802815439 195312500000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (639806467/1000000000 : ℝ)^71 ≤ (28092889555713/50000000000000 : ℝ)^55 := by
    have hnat : (639806467 : ℕ)^71*50000000000000^55 ≤ 28092889555713^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      639806467 1000000000 28092889555713 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4851304101/10000000000 : ℝ)^71 ≤ (39307179362989/100000000000000 : ℝ)^55 := by
    have hnat : (4851304101 : ℕ)^71*100000000000000^55 ≤ 39307179362989^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4851304101 10000000000 39307179362989 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-453116569/5000000000 : ℝ), (639806467/1000000000 : ℝ), (4851304101/10000000000 : ℝ)] ![(8802815439/195312500000 : ℝ), (28092889555713/50000000000000 : ℝ), (39307179362989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-453116569/5000000000 : ℝ)|^71 ≤ (8802815439/195312500000 : ℝ)^55
        have hw : |(-453116569/5000000000 : ℝ)|=(453116569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(639806467/1000000000 : ℝ)|^71 ≤ (28092889555713/50000000000000 : ℝ)^55
        have hw : |(639806467/1000000000 : ℝ)|=(639806467/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4851304101/10000000000 : ℝ)|^71 ≤ (39307179362989/100000000000000 : ℝ)^55
        have hw : |(4851304101/10000000000 : ℝ)|=(4851304101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s3_s3_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3013176117/5000000000 : ℝ)*x 0 + (-156017441/5000000000 : ℝ)*x 1 + (694791069/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3013176117/5000000000 : ℝ)^71 ≤ (52008026008379/100000000000000 : ℝ)^55 := by
    have hnat : (3013176117 : ℕ)^71*100000000000000^55 ≤ 52008026008379^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3013176117 5000000000 52008026008379 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (156017441/5000000000 : ℝ)^71 ≤ (1138028535959/100000000000000 : ℝ)^55 := by
    have hnat : (156017441 : ℕ)^71*100000000000000^55 ≤ 1138028535959^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156017441 5000000000 1138028535959 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (694791069/1250000000 : ℝ)^71 ≤ (9370789088877/20000000000000 : ℝ)^55 := by
    have hnat : (694791069 : ℕ)^71*20000000000000^55 ≤ 9370789088877^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      694791069 1250000000 9370789088877 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3013176117/5000000000 : ℝ), (-156017441/5000000000 : ℝ), (694791069/1250000000 : ℝ)] ![(52008026008379/100000000000000 : ℝ), (1138028535959/100000000000000 : ℝ), (9370789088877/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3013176117/5000000000 : ℝ)|^71 ≤ (52008026008379/100000000000000 : ℝ)^55
        have hw : |(3013176117/5000000000 : ℝ)|=(3013176117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-156017441/5000000000 : ℝ)|^71 ≤ (1138028535959/100000000000000 : ℝ)^55
        have hw : |(-156017441/5000000000 : ℝ)|=(156017441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(694791069/1250000000 : ℝ)|^71 ≤ (9370789088877/20000000000000 : ℝ)^55
        have hw : |(694791069/1250000000 : ℝ)|=(694791069/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s3_s3_23 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2090667017/5000000000 : ℝ)*x 0 + (6627087829/10000000000 : ℝ)*x 1 + (-189536583/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2090667017/5000000000 : ℝ)^71 ≤ (32445308996421/100000000000000 : ℝ)^55 := by
    have hnat : (2090667017 : ℕ)^71*100000000000000^55 ≤ 32445308996421^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2090667017 5000000000 32445308996421 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6627087829/10000000000 : ℝ)^71 ≤ (29397736131603/50000000000000 : ℝ)^55 := by
    have hnat : (6627087829 : ℕ)^71*50000000000000^55 ≤ 29397736131603^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6627087829 10000000000 29397736131603 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (189536583/1250000000 : ℝ)^71 ≤ (2189804679973/25000000000000 : ℝ)^55 := by
    have hnat : (189536583 : ℕ)^71*25000000000000^55 ≤ 2189804679973^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      189536583 1250000000 2189804679973 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2090667017/5000000000 : ℝ), (6627087829/10000000000 : ℝ), (-189536583/1250000000 : ℝ)] ![(32445308996421/100000000000000 : ℝ), (29397736131603/50000000000000 : ℝ), (2189804679973/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2090667017/5000000000 : ℝ)|^71 ≤ (32445308996421/100000000000000 : ℝ)^55
        have hw : |(2090667017/5000000000 : ℝ)|=(2090667017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6627087829/10000000000 : ℝ)|^71 ≤ (29397736131603/50000000000000 : ℝ)^55
        have hw : |(6627087829/10000000000 : ℝ)|=(6627087829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-189536583/1250000000 : ℝ)|^71 ≤ (2189804679973/25000000000000 : ℝ)^55
        have hw : |(-189536583/1250000000 : ℝ)|=(189536583/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s3_s3_27 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (58667463/78125000 : ℝ)*x 0 + (507702211/2000000000 : ℝ)*x 1 + (541290599/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (58667463/78125000 : ℝ)^71 ≤ (34545406571819/50000000000000 : ℝ)^55 := by
    have hnat : (58667463 : ℕ)^71*50000000000000^55 ≤ 34545406571819^55*78125000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58667463 78125000 34545406571819 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (507702211/2000000000 : ℝ)^71 ≤ (17035924018629/100000000000000 : ℝ)^55 := by
    have hnat : (507702211 : ℕ)^71*100000000000000^55 ≤ 17035924018629^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507702211 2000000000 17035924018629 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541290599/2500000000 : ℝ)^71 ≤ (13873262832419/100000000000000 : ℝ)^55 := by
    have hnat : (541290599 : ℕ)^71*100000000000000^55 ≤ 13873262832419^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541290599 2500000000 13873262832419 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(58667463/78125000 : ℝ), (507702211/2000000000 : ℝ), (541290599/2500000000 : ℝ)] ![(34545406571819/50000000000000 : ℝ), (17035924018629/100000000000000 : ℝ), (13873262832419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(58667463/78125000 : ℝ)|^71 ≤ (34545406571819/50000000000000 : ℝ)^55
        have hw : |(58667463/78125000 : ℝ)|=(58667463/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(507702211/2000000000 : ℝ)|^71 ≤ (17035924018629/100000000000000 : ℝ)^55
        have hw : |(507702211/2000000000 : ℝ)|=(507702211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541290599/2500000000 : ℝ)|^71 ≤ (13873262832419/100000000000000 : ℝ)^55
        have hw : |(541290599/2500000000 : ℝ)|=(541290599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310055_s3 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((62057/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(62057/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(30651/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(30651/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12519/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(12519/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1326/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1326/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21663/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(21663/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43261/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(43261/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (62057/100000 : ℝ) ^ (35/8 : ℝ) ≤ (12401083979725758817/100000000000000000000 : ℝ) := by
    have hpowers : (62057/100000 : ℝ)^35 ≤ (12401083979725758817/100000000000000000000 : ℝ)^8 := by
      have hnat : (62057 : ℕ)^35*100000000000000000000^8 ≤ 12401083979725758817^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62057 100000 12401083979725758817 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (62057/100000 : ℝ)) (X := (12401083979725758817/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s3_corner0a : (112401083979725758817/100000000000000000000 : ℝ) ≤ (10270809771498077/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (112401083979725758817/100000000000000000000 : ℝ)^8 ≤ (10270809771498077/10000000000000000 : ℝ)^35 := by
      have hnat : (112401083979725758817 : ℕ)^8*10000000000000000^35 ≤ 10270809771498077^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        112401083979725758817 100000000000000000000 10270809771498077 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10270809771498077/10000000000000000 : ℝ)) (X := (112401083979725758817/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s3_corner0b : (62401083979725758817/50000000000000000000 : ℝ) ≤ (10519464434147377/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (62401083979725758817/50000000000000000000 : ℝ)^8 ≤ (10519464434147377/10000000000000000 : ℝ)^35 := by
      have hnat : (62401083979725758817 : ℕ)^8*10000000000000000^35 ≤ 10519464434147377^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62401083979725758817 50000000000000000000 10519464434147377 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10519464434147377/10000000000000000 : ℝ)) (X := (62401083979725758817/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(270809771498077/6205700000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(2486546626493/62057000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (62057/100000 : ℝ)) (alpha := (270809771498077/6205700000000000 : ℝ)) (beta := (2486546626493/62057000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (62057/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(270809771498077/6205700000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(2486546626493/62057000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (30651/50000 : ℝ) ^ (35/8 : ℝ) ≤ (11754429795960259701/100000000000000000000 : ℝ) := by
    have hpowers : (30651/50000 : ℝ)^35 ≤ (11754429795960259701/100000000000000000000 : ℝ)^8 := by
      have hnat : (30651 : ℕ)^35*100000000000000000000^8 ≤ 11754429795960259701^8*50000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30651 50000 11754429795960259701 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (30651/50000 : ℝ)) (X := (11754429795960259701/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s3_corner1a : (111754429795960259701/100000000000000000000 : ℝ) ≤ (1282159206599779/1250000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (111754429795960259701/100000000000000000000 : ℝ)^8 ≤ (1282159206599779/1250000000000000 : ℝ)^35 := by
      have hnat : (111754429795960259701 : ℕ)^8*1250000000000000^35 ≤ 1282159206599779^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        111754429795960259701 100000000000000000000 1282159206599779 1250000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1282159206599779/1250000000000000 : ℝ)) (X := (111754429795960259701/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s3_corner1b : (61754429795960259701/50000000000000000000 : ℝ) ≤ (10494447237209197/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (61754429795960259701/50000000000000000000 : ℝ)^8 ≤ (10494447237209197/10000000000000000 : ℝ)^35 := by
      have hnat : (61754429795960259701 : ℕ)^8*10000000000000000^35 ≤ 10494447237209197^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61754429795960259701 50000000000000000000 10494447237209197 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10494447237209197/10000000000000000 : ℝ)) (X := (61754429795960259701/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(32159206599779/766275000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(47434716882193/1226040000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (30651/50000 : ℝ)) (alpha := (32159206599779/766275000000000 : ℝ)) (beta := (47434716882193/1226040000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (30651/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(32159206599779/766275000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(47434716882193/1226040000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (12519/20000 : ℝ) ^ (35/8 : ℝ) ≤ (12878371278575684559/100000000000000000000 : ℝ) := by
    have hpowers : (12519/20000 : ℝ)^35 ≤ (12878371278575684559/100000000000000000000 : ℝ)^8 := by
      have hnat : (12519 : ℕ)^35*100000000000000000000^8 ≤ 12878371278575684559^8*20000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12519 20000 12878371278575684559 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12519/20000 : ℝ)) (X := (12878371278575684559/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s3_corner2a : (112878371278575684559/100000000000000000000 : ℝ) ≤ (2570190531822187/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (112878371278575684559/100000000000000000000 : ℝ)^8 ≤ (2570190531822187/2500000000000000 : ℝ)^35 := by
      have hnat : (112878371278575684559 : ℕ)^8*2500000000000000^35 ≤ 2570190531822187^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        112878371278575684559 100000000000000000000 2570190531822187 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2570190531822187/2500000000000000 : ℝ)) (X := (112878371278575684559/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s3_corner2b : (62878371278575684559/50000000000000000000 : ℝ) ≤ (5268900667435369/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (62878371278575684559/50000000000000000000 : ℝ)^8 ≤ (5268900667435369/5000000000000000 : ℝ)^35 := by
      have hnat : (62878371278575684559 : ℕ)^8*5000000000000000^35 ≤ 5268900667435369^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62878371278575684559 50000000000000000000 5268900667435369 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5268900667435369/5000000000000000 : ℝ)) (X := (62878371278575684559/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(7798947980243/173875000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(25703920758199/625950000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (12519/20000 : ℝ)) (alpha := (7798947980243/173875000000000 : ℝ)) (beta := (25703920758199/625950000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (12519/20000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(7798947980243/173875000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(25703920758199/625950000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-2055769073/10000000000 : ℝ)*X 0 0+(5686308747/10000000000 : ℝ)*X 0 1+(4800213763/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_1 : ((4794961179/10000000000 : ℝ)*X 1 0+(-1152474063/10000000000 : ℝ)*X 1 1+(3152557791/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s3_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((4774327187/10000000000 : ℝ)*X 2 0+(5704722783/10000000000 : ℝ)*X 2 1+(-82563973/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_6 : ((6056048619/10000000000 : ℝ)*X 0 0+(3977988879/10000000000 : ℝ)*X 0 1+(2561793867/10000000000 : ℝ)*X 0 2+(6056048619/10000000000 : ℝ)*X 1 0+(3977988879/10000000000 : ℝ)*X 1 1+(2561793867/10000000000 : ℝ)*X 1 2+(6056048619/10000000000 : ℝ)*X 2 0+(3977988879/10000000000 : ℝ)*X 2 1+(2561793867/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s3_s3_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-1668926661/10000000000 : ℝ)*X 0 0+(4888354281/10000000000 : ℝ)*X 0 1+(2940351577/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((4543081441/10000000000 : ℝ)*X 1 0+(-83479343/2500000000 : ℝ)*X 1 1+(435045683/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((4522200777/10000000000 : ℝ)*X 2 0+(825651133/1250000000 : ℝ)*X 2 1+(-213124587/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((1027240869/2000000000 : ℝ)*X 0 0+(2957007773/5000000000 : ℝ)*X 0 1+(632184163/5000000000 : ℝ)*X 0 2+(1027240869/2000000000 : ℝ)*X 1 0+(2957007773/5000000000 : ℝ)*X 1 1+(632184163/5000000000 : ℝ)*X 1 2+(1027240869/2000000000 : ℝ)*X 2 0+(2957007773/5000000000 : ℝ)*X 2 1+(632184163/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-37177041/400000000 : ℝ)*X 0 0+(164155613/312500000 : ℝ)*X 0 1+(6006357433/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((4221884843/10000000000 : ℝ)*X 1 0+(-895769667/10000000000 : ℝ)*X 1 1+(6966207057/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((5982275769/10000000000 : ℝ)*X 2 0+(2635806693/5000000000 : ℝ)*X 2 1+(-939969947/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((3732728691/5000000000 : ℝ)*X 0 0+(1686623147/5000000000 : ℝ)*X 0 1+(1252122451/10000000000 : ℝ)*X 0 2+(3732728691/5000000000 : ℝ)*X 1 0+(1686623147/5000000000 : ℝ)*X 1 1+(1252122451/10000000000 : ℝ)*X 1 2+(3732728691/5000000000 : ℝ)*X 2 0+(1686623147/5000000000 : ℝ)*X 2 1+(1252122451/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-453116569/5000000000 : ℝ)*X 0 0+(639806467/1000000000 : ℝ)*X 0 1+(4851304101/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((3013176117/5000000000 : ℝ)*X 1 0+(-156017441/5000000000 : ℝ)*X 1 1+(694791069/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((2090667017/5000000000 : ℝ)*X 2 0+(6627087829/10000000000 : ℝ)*X 2 1+(-189536583/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((58667463/78125000 : ℝ)*X 0 0+(507702211/2000000000 : ℝ)*X 0 1+(541290599/2500000000 : ℝ)*X 0 2+(58667463/78125000 : ℝ)*X 1 0+(507702211/2000000000 : ℝ)*X 1 1+(541290599/2500000000 : ℝ)*X 1 2+(58667463/78125000 : ℝ)*X 2 0+(507702211/2000000000 : ℝ)*X 2 1+(541290599/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((1326/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1326/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (58763865801289340658605723/3552961750000000000000000000000 : ℝ) := by norm_num
    linear_combination (1534981/250000000000 : ℝ)*(base19) + (60077014153/200000000000 : ℝ)*(base49) + (22937/62500000000 : ℝ)*(base60) + (532637957747/125000000000 : ℝ)*(major_s3_0) + (532637957747/125000000000 : ℝ)*(major_s3_1) + (532637957747/125000000000 : ℝ)*(major_s3_2) + (23808499/1000000000000 : ℝ)*(sp_s3_0) + (896973/125000000000 : ℝ)*(sp_s3_6) + (5888501846991/1000000000000 : ℝ)*(sp_s3_7) + (235537838293/40000000000 : ℝ)*(sp_s3_8) + (294418312203/50000000000 : ℝ)*(sp_s3_9) + (526733795907/200000000000 : ℝ)*(sp_s3_13) + (36779121/500000000000 : ℝ)*(sp_s3_15) + (15941143/100000000000 : ℝ)*(sp_s3_23) + (2633676155319/1000000000000 : ℝ)*(f.failure) + (588852565549/100000000000 : ℝ)*(f.sum) + (4160934600057172051/10658885250000000000000000000000 : ℝ)*base63 + (114441113800787/312975000000000000000000000 : ℝ)*base65 + (232215926107319/306510000000000000000000000 : ℝ)*base67 + (113014842040393/173875000000000000000000000 : ℝ)*base69 + (557269559171026571/4855572393750000000000000000000 : ℝ)*base70 + (31999977553661/155142500000000000000000000 : ℝ)*base72 + (959663472520303/1532550000000000000000000000 : ℝ)*base75 + (137438694182601/193928125000000000000000000 : ℝ)*base77 + (13992057094803293/59440909593750000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (73033/100000000000000000 : ℝ)*base86 + (73033/100000000000000000 : ℝ)*base88 + (73033/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21663/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(21663/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (13813844488297846969660501/1776480875000000000000000000000 : ℝ) := by norm_num
    linear_combination (201033/100000000000 : ℝ)*(base39) + (218905594371/1000000000000 : ℝ)*(base49) + (332753/500000000000 : ℝ)*(base60) + (1015607273819/250000000000 : ℝ)*(major_s3_0) + (1015607273819/250000000000 : ℝ)*(major_s3_1) + (1015607273819/250000000000 : ℝ)*(major_s3_2) + (3296239/500000000000 : ℝ)*(sp_s3_1) + (15039357/1000000000000 : ℝ)*(sp_s3_7) + (50217323/1000000000000 : ℝ)*(sp_s3_8) + (5613959930697/1000000000000 : ℝ)*(sp_s3_14) + (1403479540063/250000000000 : ℝ)*(sp_s3_15) + (5613974970053/1000000000000 : ℝ)*(sp_s3_16) + (19615927001/7812500000 : ℝ)*(sp_s3_20) + (41972377/1000000000000 : ℝ)*(sp_s3_27) + (313860078563/125000000000 : ℝ)*(f.failure) + (5613974970053/1000000000000 : ℝ)*(f.sum) + (3182604627209122187/5329442625000000000000000000000 : ℝ)*base62 + (8466856410953/19560937500000000000000000 : ℝ)*base64 + (34962882532777/38313750000000000000000000 : ℝ)*base66 + (260024934391239/347750000000000000000000000 : ℝ)*base68 + (2899296204581612167/38844579150000000000000000000000 : ℝ)*base71 + (31143455941803/155142500000000000000000000 : ℝ)*base73 + (641653182826147/1532550000000000000000000000 : ℝ)*base74 + (592747016202999/3102850000000000000000000000 : ℝ)*base76 + (875857396678924421/9510545535000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (6541/12500000000000000 : ℝ)*base86 + (6541/12500000000000000 : ℝ)*base88 + (6541/12500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43261/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(43261/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (98847725066843804248138879051/8819445892790000000000000000000000 : ℝ) := by norm_num
    linear_combination (115342068277/1000000000000 : ℝ)*(base40) + (190505809271/1000000000000 : ℝ)*(base49) + (1262127/200000000000 : ℝ)*(base59) + (1586788599/400000000 : ℝ)*(major_s3_0) + (1586788599/400000000 : ℝ)*(major_s3_1) + (1586788599/400000000 : ℝ)*(major_s3_2) + (7732803/1000000000000 : ℝ)*(sp_s3_0) + (15932997/1000000000000 : ℝ)*(sp_s3_2) + (58645751/1000000000000 : ℝ)*(sp_s3_9) + (100606967/1000000000000 : ℝ)*(sp_s3_20) + (2741025364727/500000000000 : ℝ)*(sp_s3_21) + (5482058462257/1000000000000 : ℝ)*(sp_s3_22) + (5481983883509/1000000000000 : ℝ)*(sp_s3_23) + (2451780189793/1000000000000 : ℝ)*(sp_s3_27) + (2451880796759/1000000000000 : ℝ)*(f.failure) + (5482058462257/1000000000000 : ℝ)*(f.sum) + (3985133888957621/5684738800000000000000000000 : ℝ)*base62 + (12080813710541/20865000000000000000000000 : ℝ)*base64 + (69764962163421/102170000000000000000000000 : ℝ)*base66 + (4125725467561/3477500000000000000000000 : ℝ)*base68 + (1367668958347156529/2589638610000000000000000000000 : ℝ)*base70 + (152157144597513/620570000000000000000000000 : ℝ)*base72 + (59072551642453/51085000000000000000000000 : ℝ)*base74 + (712206502097823/620570000000000000000000000 : ℝ)*base76 + (138941107985137251/1585090922500000000000000000000 : ℝ)*base79 + (28887/100000000000000000 : ℝ)*base87 + (28887/100000000000000000 : ℝ)*base89 + (28887/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((62057/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(62057/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(30651/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(30651/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12519/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(12519/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1326/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1326/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21663/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(21663/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43261/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(43261/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c310055_s3 p hpa hpb X hX hprev2

#print axioms solution
