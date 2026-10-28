-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301083_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:44:14.977328+00:00
-- url     : https://prove2.me/submissions/b2eb7544-abb6-4821-a249-03f75378ea00

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
theorem collision_support_c301083_s3_s3_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-562522741/2000000000 : ℝ)*x 0 + (4943860081/10000000000 : ℝ)*x 1 + (1303041899/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (562522741/2000000000 : ℝ)^65 ≤ (4646946550717/25000000000000 : ℝ)^49 := by
    have hnat : (562522741 : ℕ)^65*25000000000000^49 ≤ 4646946550717^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562522741 2000000000 4646946550717 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4943860081/10000000000 : ℝ)^65 ≤ (19639906454537/50000000000000 : ℝ)^49 := by
    have hnat : (4943860081 : ℕ)^65*50000000000000^49 ≤ 19639906454537^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4943860081 10000000000 19639906454537 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1303041899/2500000000 : ℝ)^65 ≤ (5266550108531/12500000000000 : ℝ)^49 := by
    have hnat : (1303041899 : ℕ)^65*12500000000000^49 ≤ 5266550108531^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303041899 2500000000 5266550108531 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-562522741/2000000000 : ℝ), (4943860081/10000000000 : ℝ), (1303041899/2500000000 : ℝ)] ![(4646946550717/25000000000000 : ℝ), (19639906454537/50000000000000 : ℝ), (5266550108531/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-562522741/2000000000 : ℝ)|^65 ≤ (4646946550717/25000000000000 : ℝ)^49
        have hw : |(-562522741/2000000000 : ℝ)|=(562522741/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4943860081/10000000000 : ℝ)|^65 ≤ (19639906454537/50000000000000 : ℝ)^49
        have hw : |(4943860081/10000000000 : ℝ)|=(4943860081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1303041899/2500000000 : ℝ)|^65 ≤ (5266550108531/12500000000000 : ℝ)^49
        have hw : |(1303041899/2500000000 : ℝ)|=(1303041899/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301083_s3_s3_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (814403143/1250000000 : ℝ)*x 0 + (-203047431/1250000000 : ℝ)*x 1 + (4471461333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (814403143/1250000000 : ℝ)^65 ≤ (7080789818619/12500000000000 : ℝ)^49 := by
    have hnat : (814403143 : ℕ)^65*12500000000000^49 ≤ 7080789818619^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      814403143 1250000000 7080789818619 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (203047431/1250000000 : ℝ)^65 ≤ (8973312398863/100000000000000 : ℝ)^49 := by
    have hnat : (203047431 : ℕ)^65*100000000000000^49 ≤ 8973312398863^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203047431 1250000000 8973312398863 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4471461333/10000000000 : ℝ)^65 ≤ (3438036903807/10000000000000 : ℝ)^49 := by
    have hnat : (4471461333 : ℕ)^65*10000000000000^49 ≤ 3438036903807^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4471461333 10000000000 3438036903807 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(814403143/1250000000 : ℝ), (-203047431/1250000000 : ℝ), (4471461333/10000000000 : ℝ)] ![(7080789818619/12500000000000 : ℝ), (8973312398863/100000000000000 : ℝ), (3438036903807/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(814403143/1250000000 : ℝ)|^65 ≤ (7080789818619/12500000000000 : ℝ)^49
        have hw : |(814403143/1250000000 : ℝ)|=(814403143/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-203047431/1250000000 : ℝ)|^65 ≤ (8973312398863/100000000000000 : ℝ)^49
        have hw : |(-203047431/1250000000 : ℝ)|=(203047431/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4471461333/10000000000 : ℝ)|^65 ≤ (3438036903807/10000000000000 : ℝ)^49
        have hw : |(4471461333/10000000000 : ℝ)|=(4471461333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301083_s3_s3_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3973718623/10000000000 : ℝ)*x 0 + (189862389/312500000 : ℝ)*x 1 + (-571199167/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3973718623/10000000000 : ℝ)^65 ≤ (29398332611441/100000000000000 : ℝ)^49 := by
    have hnat : (3973718623 : ℕ)^65*100000000000000^49 ≤ 29398332611441^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3973718623 10000000000 29398332611441 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (189862389/312500000 : ℝ)^65 ≤ (5163260975987/10000000000000 : ℝ)^49 := by
    have hnat : (189862389 : ℕ)^65*10000000000000^49 ≤ 5163260975987^49*312500000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      189862389 312500000 5163260975987 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (571199167/2000000000 : ℝ)^65 ≤ (9484528811363/50000000000000 : ℝ)^49 := by
    have hnat : (571199167 : ℕ)^65*50000000000000^49 ≤ 9484528811363^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571199167 2000000000 9484528811363 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3973718623/10000000000 : ℝ), (189862389/312500000 : ℝ), (-571199167/2000000000 : ℝ)] ![(29398332611441/100000000000000 : ℝ), (5163260975987/10000000000000 : ℝ), (9484528811363/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3973718623/10000000000 : ℝ)|^65 ≤ (29398332611441/100000000000000 : ℝ)^49
        have hw : |(3973718623/10000000000 : ℝ)|=(3973718623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(189862389/312500000 : ℝ)|^65 ≤ (5163260975987/10000000000000 : ℝ)^49
        have hw : |(189862389/312500000 : ℝ)|=(189862389/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-571199167/2000000000 : ℝ)|^65 ≤ (9484528811363/50000000000000 : ℝ)^49
        have hw : |(-571199167/2000000000 : ℝ)|=(571199167/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301083_s3_s3_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2941000733/10000000000 : ℝ)*x 0 + (2432523233/5000000000 : ℝ)*x 1 + (1036733293/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2941000733/10000000000 : ℝ)^65 ≤ (19721617119057/100000000000000 : ℝ)^49 := by
    have hnat : (2941000733 : ℕ)^65*100000000000000^49 ≤ 19721617119057^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2941000733 10000000000 19721617119057 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2432523233/5000000000 : ℝ)^65 ≤ (38451325606861/100000000000000 : ℝ)^49 := by
    have hnat : (2432523233 : ℕ)^65*100000000000000^49 ≤ 38451325606861^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2432523233 5000000000 38451325606861 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036733293/2000000000 : ℝ)^65 ≤ (41827057260487/100000000000000 : ℝ)^49 := by
    have hnat : (1036733293 : ℕ)^65*100000000000000^49 ≤ 41827057260487^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036733293 2000000000 41827057260487 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2941000733/10000000000 : ℝ), (2432523233/5000000000 : ℝ), (1036733293/2000000000 : ℝ)] ![(19721617119057/100000000000000 : ℝ), (38451325606861/100000000000000 : ℝ), (41827057260487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2941000733/10000000000 : ℝ)|^65 ≤ (19721617119057/100000000000000 : ℝ)^49
        have hw : |(-2941000733/10000000000 : ℝ)|=(2941000733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2432523233/5000000000 : ℝ)|^65 ≤ (38451325606861/100000000000000 : ℝ)^49
        have hw : |(2432523233/5000000000 : ℝ)|=(2432523233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1036733293/2000000000 : ℝ)|^65 ≤ (41827057260487/100000000000000 : ℝ)^49
        have hw : |(1036733293/2000000000 : ℝ)|=(1036733293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301083_s3_s3_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6354724589/10000000000 : ℝ)*x 0 + (-153295353/2000000000 : ℝ)*x 1 + (1297248097/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6354724589/10000000000 : ℝ)^65 ≤ (27401339476743/50000000000000 : ℝ)^49 := by
    have hnat : (6354724589 : ℕ)^65*50000000000000^49 ≤ 27401339476743^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6354724589 10000000000 27401339476743 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (153295353/2000000000 : ℝ)^65 ≤ (3313246651927/100000000000000 : ℝ)^49 := by
    have hnat : (153295353 : ℕ)^65*100000000000000^49 ≤ 3313246651927^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153295353 2000000000 3313246651927 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1297248097/2500000000 : ℝ)^65 ≤ (41884074376867/100000000000000 : ℝ)^49 := by
    have hnat : (1297248097 : ℕ)^65*100000000000000^49 ≤ 41884074376867^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1297248097 2500000000 41884074376867 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6354724589/10000000000 : ℝ), (-153295353/2000000000 : ℝ), (1297248097/2500000000 : ℝ)] ![(27401339476743/50000000000000 : ℝ), (3313246651927/100000000000000 : ℝ), (41884074376867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6354724589/10000000000 : ℝ)|^65 ≤ (27401339476743/50000000000000 : ℝ)^49
        have hw : |(6354724589/10000000000 : ℝ)|=(6354724589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-153295353/2000000000 : ℝ)|^65 ≤ (3313246651927/100000000000000 : ℝ)^49
        have hw : |(-153295353/2000000000 : ℝ)|=(153295353/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1297248097/2500000000 : ℝ)|^65 ≤ (41884074376867/100000000000000 : ℝ)^49
        have hw : |(1297248097/2500000000 : ℝ)|=(1297248097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301083_s3_s3_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (881502183/2500000000 : ℝ)*x 0 + (1737900743/2500000000 : ℝ)*x 1 + (-54258361/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (881502183/2500000000 : ℝ)^65 ≤ (25087509474353/100000000000000 : ℝ)^49 := by
    have hnat : (881502183 : ℕ)^65*100000000000000^49 ≤ 25087509474353^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      881502183 2500000000 25087509474353 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1737900743/2500000000 : ℝ)^65 ≤ (61733495091859/100000000000000 : ℝ)^49 := by
    have hnat : (1737900743 : ℕ)^65*100000000000000^49 ≤ 61733495091859^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1737900743 2500000000 61733495091859 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54258361/250000000 : ℝ)^65 ≤ (6589497706641/50000000000000 : ℝ)^49 := by
    have hnat : (54258361 : ℕ)^65*50000000000000^49 ≤ 6589497706641^49*250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54258361 250000000 6589497706641 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(881502183/2500000000 : ℝ), (1737900743/2500000000 : ℝ), (-54258361/250000000 : ℝ)] ![(25087509474353/100000000000000 : ℝ), (61733495091859/100000000000000 : ℝ), (6589497706641/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(881502183/2500000000 : ℝ)|^65 ≤ (25087509474353/100000000000000 : ℝ)^49
        have hw : |(881502183/2500000000 : ℝ)|=(881502183/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1737900743/2500000000 : ℝ)|^65 ≤ (61733495091859/100000000000000 : ℝ)^49
        have hw : |(1737900743/2500000000 : ℝ)|=(1737900743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-54258361/250000000 : ℝ)|^65 ≤ (6589497706641/50000000000000 : ℝ)^49
        have hw : |(-54258361/250000000 : ℝ)|=(54258361/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301083_s3_s3_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (60940587/200000000 : ℝ)*x 0 + (1235249647/2500000000 : ℝ)*x 1 + (627449869/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (60940587/200000000 : ℝ)^65 ≤ (20670289535019/100000000000000 : ℝ)^49 := by
    have hnat : (60940587 : ℕ)^65*100000000000000^49 ≤ 20670289535019^49*200000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60940587 200000000 20670289535019 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1235249647/2500000000 : ℝ)^65 ≤ (39249657018623/100000000000000 : ℝ)^49 := by
    have hnat : (1235249647 : ℕ)^65*100000000000000^49 ≤ 39249657018623^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1235249647 2500000000 39249657018623 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (627449869/1250000000 : ℝ)^65 ≤ (801601068541/2000000000000 : ℝ)^49 := by
    have hnat : (627449869 : ℕ)^65*2000000000000^49 ≤ 801601068541^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      627449869 1250000000 801601068541 2000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(60940587/200000000 : ℝ), (1235249647/2500000000 : ℝ), (627449869/1250000000 : ℝ)] ![(20670289535019/100000000000000 : ℝ), (39249657018623/100000000000000 : ℝ), (801601068541/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(60940587/200000000 : ℝ)|^65 ≤ (20670289535019/100000000000000 : ℝ)^49
        have hw : |(60940587/200000000 : ℝ)|=(60940587/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1235249647/2500000000 : ℝ)|^65 ≤ (39249657018623/100000000000000 : ℝ)^49
        have hw : |(1235249647/2500000000 : ℝ)|=(1235249647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(627449869/1250000000 : ℝ)|^65 ≤ (801601068541/2000000000000 : ℝ)^49
        have hw : |(627449869/1250000000 : ℝ)|=(627449869/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301083_s3_s3_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1078667091/5000000000 : ℝ)*x 0 + (432510693/1000000000 : ℝ)*x 1 + (6287060333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078667091/5000000000 : ℝ)^65 ≤ (6537189552447/50000000000000 : ℝ)^49 := by
    have hnat : (1078667091 : ℕ)^65*50000000000000^49 ≤ 6537189552447^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078667091 5000000000 6537189552447 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (432510693/1000000000 : ℝ)^65 ≤ (32895665531653/100000000000000 : ℝ)^49 := by
    have hnat : (432510693 : ℕ)^65*100000000000000^49 ≤ 32895665531653^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432510693 1000000000 32895665531653 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6287060333/10000000000 : ℝ)^65 ≤ (6753744418153/12500000000000 : ℝ)^49 := by
    have hnat : (6287060333 : ℕ)^65*12500000000000^49 ≤ 6753744418153^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6287060333 10000000000 6753744418153 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1078667091/5000000000 : ℝ), (432510693/1000000000 : ℝ), (6287060333/10000000000 : ℝ)] ![(6537189552447/50000000000000 : ℝ), (32895665531653/100000000000000 : ℝ), (6753744418153/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1078667091/5000000000 : ℝ)|^65 ≤ (6537189552447/50000000000000 : ℝ)^49
        have hw : |(-1078667091/5000000000 : ℝ)|=(1078667091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(432510693/1000000000 : ℝ)|^65 ≤ (32895665531653/100000000000000 : ℝ)^49
        have hw : |(432510693/1000000000 : ℝ)|=(432510693/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6287060333/10000000000 : ℝ)|^65 ≤ (6753744418153/12500000000000 : ℝ)^49
        have hw : |(6287060333/10000000000 : ℝ)|=(6287060333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301083_s3_s3_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1815930329/2500000000 : ℝ)*x 0 + (-299159161/2000000000 : ℝ)*x 1 + (183834673/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1815930329/2500000000 : ℝ)^65 ≤ (16359250479511/25000000000000 : ℝ)^49 := by
    have hnat : (1815930329 : ℕ)^65*25000000000000^49 ≤ 16359250479511^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1815930329 2500000000 16359250479511 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (299159161/2000000000 : ℝ)^65 ≤ (8043459166149/100000000000000 : ℝ)^49 := by
    have hnat : (299159161 : ℕ)^65*100000000000000^49 ≤ 8043459166149^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299159161 2000000000 8043459166149 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (183834673/500000000 : ℝ)^65 ≤ (3314942363219/12500000000000 : ℝ)^49 := by
    have hnat : (183834673 : ℕ)^65*12500000000000^49 ≤ 3314942363219^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183834673 500000000 3314942363219 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1815930329/2500000000 : ℝ), (-299159161/2000000000 : ℝ), (183834673/500000000 : ℝ)] ![(16359250479511/25000000000000 : ℝ), (8043459166149/100000000000000 : ℝ), (3314942363219/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1815930329/2500000000 : ℝ)|^65 ≤ (16359250479511/25000000000000 : ℝ)^49
        have hw : |(1815930329/2500000000 : ℝ)|=(1815930329/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-299159161/2000000000 : ℝ)|^65 ≤ (8043459166149/100000000000000 : ℝ)^49
        have hw : |(-299159161/2000000000 : ℝ)|=(299159161/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(183834673/500000000 : ℝ)|^65 ≤ (3314942363219/12500000000000 : ℝ)^49
        have hw : |(183834673/500000000 : ℝ)|=(183834673/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301083_s3_s3_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (164900329/400000000 : ℝ)*x 0 + (6412436941/10000000000 : ℝ)*x 1 + (-1115428861/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (164900329/400000000 : ℝ)^65 ≤ (30867395734271/100000000000000 : ℝ)^49 := by
    have hnat : (164900329 : ℕ)^65*100000000000000^49 ≤ 30867395734271^49*400000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164900329 400000000 30867395734271 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6412436941/10000000000 : ℝ)^65 ≤ (3466492475089/6250000000000 : ℝ)^49 := by
    have hnat : (6412436941 : ℕ)^65*6250000000000^49 ≤ 3466492475089^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6412436941 10000000000 3466492475089 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1115428861/5000000000 : ℝ)^65 ≤ (13668724647689/100000000000000 : ℝ)^49 := by
    have hnat : (1115428861 : ℕ)^65*100000000000000^49 ≤ 13668724647689^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115428861 5000000000 13668724647689 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(164900329/400000000 : ℝ), (6412436941/10000000000 : ℝ), (-1115428861/5000000000 : ℝ)] ![(30867395734271/100000000000000 : ℝ), (3466492475089/6250000000000 : ℝ), (13668724647689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(164900329/400000000 : ℝ)|^65 ≤ (30867395734271/100000000000000 : ℝ)^49
        have hw : |(164900329/400000000 : ℝ)|=(164900329/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6412436941/10000000000 : ℝ)|^65 ≤ (3466492475089/6250000000000 : ℝ)^49
        have hw : |(6412436941/10000000000 : ℝ)|=(6412436941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1115428861/5000000000 : ℝ)|^65 ≤ (13668724647689/100000000000000 : ℝ)^49
        have hw : |(-1115428861/5000000000 : ℝ)|=(1115428861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301083_s3_s3_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (765000781/2500000000 : ℝ)*x 0 + (842216189/2000000000 : ℝ)*x 1 + (2850948243/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (765000781/2500000000 : ℝ)^65 ≤ (20787119712921/100000000000000 : ℝ)^49 := by
    have hnat : (765000781 : ℕ)^65*100000000000000^49 ≤ 20787119712921^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      765000781 2500000000 20787119712921 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (842216189/2000000000 : ℝ)^65 ≤ (31750209719007/100000000000000 : ℝ)^49 := by
    have hnat : (842216189 : ℕ)^65*100000000000000^49 ≤ 31750209719007^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      842216189 2000000000 31750209719007 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2850948243/5000000000 : ℝ)^65 ≤ (189850682217/400000000000 : ℝ)^49 := by
    have hnat : (2850948243 : ℕ)^65*400000000000^49 ≤ 189850682217^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2850948243 5000000000 189850682217 400000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(765000781/2500000000 : ℝ), (842216189/2000000000 : ℝ), (2850948243/5000000000 : ℝ)] ![(20787119712921/100000000000000 : ℝ), (31750209719007/100000000000000 : ℝ), (189850682217/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(765000781/2500000000 : ℝ)|^65 ≤ (20787119712921/100000000000000 : ℝ)^49
        have hw : |(765000781/2500000000 : ℝ)|=(765000781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(842216189/2000000000 : ℝ)|^65 ≤ (31750209719007/100000000000000 : ℝ)^49
        have hw : |(842216189/2000000000 : ℝ)|=(842216189/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2850948243/5000000000 : ℝ)|^65 ≤ (189850682217/400000000000 : ℝ)^49
        have hw : |(2850948243/5000000000 : ℝ)|=(2850948243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301083_s3_s3_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2320565407/10000000000 : ℝ)*x 0 + (5428413111/10000000000 : ℝ)*x 1 + (2559235047/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2320565407/10000000000 : ℝ)^65 ≤ (7201297913997/50000000000000 : ℝ)^49 := by
    have hnat : (2320565407 : ℕ)^65*50000000000000^49 ≤ 7201297913997^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2320565407 10000000000 7201297913997 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428413111/10000000000 : ℝ)^65 ≤ (22233379022571/50000000000000 : ℝ)^49 := by
    have hnat : (5428413111 : ℕ)^65*50000000000000^49 ≤ 22233379022571^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428413111 10000000000 22233379022571 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2559235047/5000000000 : ℝ)^65 ≤ (20565323057741/50000000000000 : ℝ)^49 := by
    have hnat : (2559235047 : ℕ)^65*50000000000000^49 ≤ 20565323057741^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2559235047 5000000000 20565323057741 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2320565407/10000000000 : ℝ), (5428413111/10000000000 : ℝ), (2559235047/5000000000 : ℝ)] ![(7201297913997/50000000000000 : ℝ), (22233379022571/50000000000000 : ℝ), (20565323057741/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2320565407/10000000000 : ℝ)|^65 ≤ (7201297913997/50000000000000 : ℝ)^49
        have hw : |(-2320565407/10000000000 : ℝ)|=(2320565407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428413111/10000000000 : ℝ)|^65 ≤ (22233379022571/50000000000000 : ℝ)^49
        have hw : |(5428413111/10000000000 : ℝ)|=(5428413111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2559235047/5000000000 : ℝ)|^65 ≤ (20565323057741/50000000000000 : ℝ)^49
        have hw : |(2559235047/5000000000 : ℝ)|=(2559235047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301083_s3_s3_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3635871083/5000000000 : ℝ)*x 0 + (-439399413/5000000000 : ℝ)*x 1 + (1021236671/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3635871083/5000000000 : ℝ)^65 ≤ (32766435675717/50000000000000 : ℝ)^49 := by
    have hnat : (3635871083 : ℕ)^65*50000000000000^49 ≤ 32766435675717^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3635871083 5000000000 32766435675717 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (439399413/5000000000 : ℝ)^65 ≤ (3972254351581/100000000000000 : ℝ)^49 := by
    have hnat : (439399413 : ℕ)^65*100000000000000^49 ≤ 3972254351581^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      439399413 5000000000 3972254351581 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1021236671/2500000000 : ℝ)^65 ≤ (6098974856547/20000000000000 : ℝ)^49 := by
    have hnat : (1021236671 : ℕ)^65*20000000000000^49 ≤ 6098974856547^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021236671 2500000000 6098974856547 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3635871083/5000000000 : ℝ), (-439399413/5000000000 : ℝ), (1021236671/2500000000 : ℝ)] ![(32766435675717/50000000000000 : ℝ), (3972254351581/100000000000000 : ℝ), (6098974856547/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3635871083/5000000000 : ℝ)|^65 ≤ (32766435675717/50000000000000 : ℝ)^49
        have hw : |(3635871083/5000000000 : ℝ)|=(3635871083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-439399413/5000000000 : ℝ)|^65 ≤ (3972254351581/100000000000000 : ℝ)^49
        have hw : |(-439399413/5000000000 : ℝ)|=(439399413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1021236671/2500000000 : ℝ)|^65 ≤ (6098974856547/20000000000000 : ℝ)^49
        have hw : |(1021236671/2500000000 : ℝ)|=(1021236671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301083_s3_s3_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (109759273/312500000 : ℝ)*x 0 + (6404141319/10000000000 : ℝ)*x 1 + (-293554573/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (109759273/312500000 : ℝ)^65 ≤ (6239543619557/25000000000000 : ℝ)^49 := by
    have hnat : (109759273 : ℕ)^65*25000000000000^49 ≤ 6239543619557^49*312500000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109759273 312500000 6239543619557 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6404141319/10000000000 : ℝ)^65 ≤ (27684359015157/50000000000000 : ℝ)^49 := by
    have hnat : (6404141319 : ℕ)^65*50000000000000^49 ≤ 27684359015157^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6404141319 10000000000 27684359015157 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (293554573/1000000000 : ℝ)^65 ≤ (9836553738499/50000000000000 : ℝ)^49 := by
    have hnat : (293554573 : ℕ)^65*50000000000000^49 ≤ 9836553738499^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      293554573 1000000000 9836553738499 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(109759273/312500000 : ℝ), (6404141319/10000000000 : ℝ), (-293554573/1000000000 : ℝ)] ![(6239543619557/25000000000000 : ℝ), (27684359015157/50000000000000 : ℝ), (9836553738499/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(109759273/312500000 : ℝ)|^65 ≤ (6239543619557/25000000000000 : ℝ)^49
        have hw : |(109759273/312500000 : ℝ)|=(109759273/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6404141319/10000000000 : ℝ)|^65 ≤ (27684359015157/50000000000000 : ℝ)^49
        have hw : |(6404141319/10000000000 : ℝ)|=(6404141319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-293554573/1000000000 : ℝ)|^65 ≤ (9836553738499/50000000000000 : ℝ)^49
        have hw : |(-293554573/1000000000 : ℝ)|=(293554573/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301083_s3_s3_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3919694409/10000000000 : ℝ)*x 0 + (4689869127/10000000000 : ℝ)*x 1 + (2241841841/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3919694409/10000000000 : ℝ)^65 ≤ (2886932331909/10000000000000 : ℝ)^49 := by
    have hnat : (3919694409 : ℕ)^65*10000000000000^49 ≤ 2886932331909^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3919694409 10000000000 2886932331909 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4689869127/10000000000 : ℝ)^65 ≤ (36625590339103/100000000000000 : ℝ)^49 := by
    have hnat : (4689869127 : ℕ)^65*100000000000000^49 ≤ 36625590339103^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4689869127 10000000000 36625590339103 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2241841841/5000000000 : ℝ)^65 ≤ (690101726547/2000000000000 : ℝ)^49 := by
    have hnat : (2241841841 : ℕ)^65*2000000000000^49 ≤ 690101726547^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241841841 5000000000 690101726547 2000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3919694409/10000000000 : ℝ), (4689869127/10000000000 : ℝ), (2241841841/5000000000 : ℝ)] ![(2886932331909/10000000000000 : ℝ), (36625590339103/100000000000000 : ℝ), (690101726547/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3919694409/10000000000 : ℝ)|^65 ≤ (2886932331909/10000000000000 : ℝ)^49
        have hw : |(3919694409/10000000000 : ℝ)|=(3919694409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4689869127/10000000000 : ℝ)|^65 ≤ (36625590339103/100000000000000 : ℝ)^49
        have hw : |(4689869127/10000000000 : ℝ)|=(4689869127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2241841841/5000000000 : ℝ)|^65 ≤ (690101726547/2000000000000 : ℝ)^49
        have hw : |(2241841841/5000000000 : ℝ)|=(2241841841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301083_s3 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((48667/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(48667/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((11897/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(11897/25000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27193/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(27193/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((5311/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5311/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((24883/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(24883/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(23637/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(23637/100000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (48667/100000 : ℝ) ^ (129/32 : ℝ) ≤ (342802831545711889/6250000000000000000 : ℝ) := by
    have hpowers : (48667/100000 : ℝ)^129 ≤ (342802831545711889/6250000000000000000 : ℝ)^32 := by
      have hnat : (48667 : ℕ)^129*6250000000000000000^32 ≤ 342802831545711889^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        48667 100000 342802831545711889 6250000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (48667/100000 : ℝ)) (X := (342802831545711889/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner0a : (6592802831545711889/6250000000000000000 : ℝ) ≤ (1266667386172257/1250000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (6592802831545711889/6250000000000000000 : ℝ)^32 ≤ (1266667386172257/1250000000000000 : ℝ)^129 := by
      have hnat : (6592802831545711889 : ℕ)^32*1250000000000000^129 ≤ 1266667386172257^129*6250000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6592802831545711889 6250000000000000000 1266667386172257 1250000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1266667386172257/1250000000000000 : ℝ)) (X := (6592802831545711889/6250000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner0b : (3467802831545711889/3125000000000000000 : ℝ) ≤ (10261562353015323/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (3467802831545711889/3125000000000000000 : ℝ)^32 ≤ (10261562353015323/10000000000000000 : ℝ)^129 := by
      have hnat : (3467802831545711889 : ℕ)^32*10000000000000000^129 ≤ 10261562353015323^129*3125000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3467802831545711889 3125000000000000000 10261562353015323 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10261562353015323/10000000000000000 : ℝ)) (X := (3467802831545711889/3125000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(16667386172257/608337500000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(128223263637267/4866700000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (48667/100000 : ℝ)) (alpha := (16667386172257/608337500000000 : ℝ)) (beta := (128223263637267/4866700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (48667/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(16667386172257/608337500000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(128223263637267/4866700000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (11897/25000 : ℝ) ^ (129/32 : ℝ) ≤ (5010852362316892147/100000000000000000000 : ℝ) := by
    have hpowers : (11897/25000 : ℝ)^129 ≤ (5010852362316892147/100000000000000000000 : ℝ)^32 := by
      have hnat : (11897 : ℕ)^129*100000000000000000000^32 ≤ 5010852362316892147^32*25000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11897 25000 5010852362316892147 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11897/25000 : ℝ)) (X := (5010852362316892147/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner1a : (105010852362316892147/100000000000000000000 : ℝ) ≤ (10122024738135787/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (105010852362316892147/100000000000000000000 : ℝ)^32 ≤ (10122024738135787/10000000000000000 : ℝ)^129 := by
      have hnat : (105010852362316892147 : ℕ)^32*10000000000000000^129 ≤ 10122024738135787^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        105010852362316892147 100000000000000000000 10122024738135787 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10122024738135787/10000000000000000 : ℝ)) (X := (105010852362316892147/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner1b : (55010852362316892147/50000000000000000000 : ℝ) ≤ (255993664175571/250000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (55010852362316892147/50000000000000000000 : ℝ)^32 ≤ (255993664175571/250000000000000 : ℝ)^129 := by
      have hnat : (55010852362316892147 : ℕ)^32*250000000000000^129 ≤ 255993664175571^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55010852362316892147 50000000000000000000 255993664175571 250000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (255993664175571/250000000000000 : ℝ)) (X := (55010852362316892147/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(122024738135787/4758800000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(117721828887053/4758800000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (11897/25000 : ℝ)) (alpha := (122024738135787/4758800000000000 : ℝ)) (beta := (117721828887053/4758800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (11897/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(122024738135787/4758800000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(117721828887053/4758800000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (27193/50000 : ℝ) ^ (129/32 : ℝ) ≤ (8583856443140001797/100000000000000000000 : ℝ) := by
    have hpowers : (27193/50000 : ℝ)^129 ≤ (8583856443140001797/100000000000000000000 : ℝ)^32 := by
      have hnat : (27193 : ℕ)^129*100000000000000000000^32 ≤ 8583856443140001797^32*50000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27193 50000 8583856443140001797 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27193/50000 : ℝ)) (X := (8583856443140001797/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner2a : (108583856443140001797/100000000000000000000 : ℝ) ≤ (637899145366051/625000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (108583856443140001797/100000000000000000000 : ℝ)^32 ≤ (637899145366051/625000000000000 : ℝ)^129 := by
      have hnat : (108583856443140001797 : ℕ)^32*625000000000000^129 ≤ 637899145366051^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        108583856443140001797 100000000000000000000 637899145366051 625000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (637899145366051/625000000000000 : ℝ)) (X := (108583856443140001797/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner2b : (58583856443140001797/50000000000000000000 : ℝ) ≤ (10400845361792487/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (58583856443140001797/50000000000000000000 : ℝ)^32 ≤ (10400845361792487/10000000000000000 : ℝ)^129 := by
      have hnat : (58583856443140001797 : ℕ)^32*10000000000000000^129 ≤ 10400845361792487^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        58583856443140001797 50000000000000000000 10400845361792487 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10400845361792487/10000000000000000 : ℝ)) (X := (58583856443140001797/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(12899145366051/339912500000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(194459035935671/5438600000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (27193/50000 : ℝ)) (alpha := (12899145366051/339912500000000 : ℝ)) (beta := (194459035935671/5438600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (27193/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(12899145366051/339912500000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(194459035935671/5438600000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-562522741/2000000000 : ℝ)*X 0 0+(4943860081/10000000000 : ℝ)*X 0 1+(1303041899/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301083_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_1 : ((814403143/1250000000 : ℝ)*X 1 0+(-203047431/1250000000 : ℝ)*X 1 1+(4471461333/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301083_s3_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((3973718623/10000000000 : ℝ)*X 2 0+(189862389/312500000 : ℝ)*X 2 1+(-571199167/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301083_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-2941000733/10000000000 : ℝ)*X 0 0+(2432523233/5000000000 : ℝ)*X 0 1+(1036733293/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301083_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((6354724589/10000000000 : ℝ)*X 1 0+(-153295353/2000000000 : ℝ)*X 1 1+(1297248097/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301083_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((881502183/2500000000 : ℝ)*X 2 0+(1737900743/2500000000 : ℝ)*X 2 1+(-54258361/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301083_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((60940587/200000000 : ℝ)*X 0 0+(1235249647/2500000000 : ℝ)*X 0 1+(627449869/1250000000 : ℝ)*X 0 2+(60940587/200000000 : ℝ)*X 1 0+(1235249647/2500000000 : ℝ)*X 1 1+(627449869/1250000000 : ℝ)*X 1 2+(60940587/200000000 : ℝ)*X 2 0+(1235249647/2500000000 : ℝ)*X 2 1+(627449869/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301083_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-1078667091/5000000000 : ℝ)*X 0 0+(432510693/1000000000 : ℝ)*X 0 1+(6287060333/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301083_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((1815930329/2500000000 : ℝ)*X 1 0+(-299159161/2000000000 : ℝ)*X 1 1+(183834673/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301083_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((164900329/400000000 : ℝ)*X 2 0+(6412436941/10000000000 : ℝ)*X 2 1+(-1115428861/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301083_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((765000781/2500000000 : ℝ)*X 0 0+(842216189/2000000000 : ℝ)*X 0 1+(2850948243/5000000000 : ℝ)*X 0 2+(765000781/2500000000 : ℝ)*X 1 0+(842216189/2000000000 : ℝ)*X 1 1+(2850948243/5000000000 : ℝ)*X 1 2+(765000781/2500000000 : ℝ)*X 2 0+(842216189/2000000000 : ℝ)*X 2 1+(2850948243/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301083_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-2320565407/10000000000 : ℝ)*X 0 0+(5428413111/10000000000 : ℝ)*X 0 1+(2559235047/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301083_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((3635871083/5000000000 : ℝ)*X 1 0+(-439399413/5000000000 : ℝ)*X 1 1+(1021236671/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301083_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((109759273/312500000 : ℝ)*X 2 0+(6404141319/10000000000 : ℝ)*X 2 1+(-293554573/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301083_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((3919694409/10000000000 : ℝ)*X 0 0+(4689869127/10000000000 : ℝ)*X 0 1+(2241841841/5000000000 : ℝ)*X 0 2+(3919694409/10000000000 : ℝ)*X 1 0+(4689869127/10000000000 : ℝ)*X 1 1+(2241841841/5000000000 : ℝ)*X 1 2+(3919694409/10000000000 : ℝ)*X 2 0+(4689869127/10000000000 : ℝ)*X 2 1+(2241841841/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301083_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((5311/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5311/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1479730740795119762421565081401/196806379921337500000000000000000000 : ℝ) := by norm_num
    linear_combination (27213/2500000000 : ℝ)*(base40) + (44796942683/40000000000 : ℝ)*(base49) + (10152066941/40000000000 : ℝ)*(base60) + (1101342131819/250000000000 : ℝ)*(major_s3_0) + (1101342131819/250000000000 : ℝ)*(major_s3_1) + (1101342131819/250000000000 : ℝ)*(major_s3_2) + (12995021/200000000000 : ℝ)*(sp_s3_0) + (289791/1953125000 : ℝ)*(sp_s3_1) + (583253990711/100000000000 : ℝ)*(sp_s3_7) + (5832456509223/1000000000000 : ℝ)*(sp_s3_8) + (1458110264719/250000000000 : ℝ)*(sp_s3_9) + (595623199157/200000000000 : ℝ)*(sp_s3_13) + (13670311/1000000000000 : ℝ)*(sp_s3_20) + (163823339/1000000000000 : ℝ)*(sp_s3_23) + (186133104131/62500000000 : ℝ)*(f.failure) + (1166520976443/200000000000 : ℝ)*(f.sum) + (4358644171226454687/6470302420000000000000000000000 : ℝ)*base63 + (555337511796051/1359650000000000000000000000 : ℝ)*base64 + (29401868228433/1189700000000000000000000000 : ℝ)*base67 + (587248963682119/1359650000000000000000000000 : ℝ)*base69 + (29792579418260650233/66170086550000000000000000000000 : ℝ)*base70 + (986225417481/9505273437500000000000000 : ℝ)*base73 + (236331106652093/1189700000000000000000000000 : ℝ)*base75 + (303758501271/4752636718750000000000000 : ℝ)*base76 + (1418408095708012627/11579825980000000000000000000000 : ℝ)*base79 + (239/1562500000000000 : ℝ)*base86 + (239/1562500000000000 : ℝ)*base88 + (239/1562500000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((24883/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(24883/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1464835068866287786089379204773/393612759842675000000000000000000000 : ℝ) := by norm_num
    linear_combination (801723495653/1000000000000 : ℝ)*(base40) + (7237808013/6250000000 : ℝ)*(base49) + (679538245237/1000000000000 : ℝ)*(base60) + (162582509603/31250000000 : ℝ)*(major_s3_0) + (162582509603/31250000000 : ℝ)*(major_s3_1) + (162582509603/31250000000 : ℝ)*(major_s3_2) + (527693/12500000000 : ℝ)*(sp_s3_1) + (44631737/500000000000 : ℝ)*(sp_s3_2) + (35227789/500000000000 : ℝ)*(sp_s3_7) + (6888105333357/1000000000000 : ℝ)*(sp_s3_14) + (1722029617199/250000000000 : ℝ)*(sp_s3_15) + (6888086525461/1000000000000 : ℝ)*(sp_s3_16) + (3517103585149/1000000000000 : ℝ)*(sp_s3_20) + (15104699/1000000000000 : ℝ)*(sp_s3_22) + (3517103585149/1000000000000 : ℝ)*(f.failure) + (1377635157787/200000000000 : ℝ)*(f.sum) + (43120367542131327/202196950625000000000000000000 : ℝ)*base63 + (549517580121609/1359650000000000000000000000 : ℝ)*base65 + (159419252573719/594850000000000000000000000 : ℝ)*base67 + (79503055550297/679825000000000000000000000 : ℝ)*base69 + (18999081432075770747/66170086550000000000000000000000 : ℝ)*base71 + (95699096674833/1216675000000000000000000000 : ℝ)*base73 + (364420918069209/594850000000000000000000000 : ℝ)*base75 + (563837020816679/1216675000000000000000000000 : ℝ)*base77 + (579722616917488899/2894956495000000000000000000000 : ℝ)*base78 + (4831/25000000000000000 : ℝ)*base86 + (4831/25000000000000000 : ℝ)*base88 + (4831/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(23637/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(23637/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (34205165362530228913360023/6617008655000000000000000000000 : ℝ) := by norm_num
    linear_combination (18117201073/25000000000 : ℝ)*(base40) + (1292257081489/1000000000000 : ℝ)*(base49) + (1112047/500000000000 : ℝ)*(base50) + (854851/1000000000000 : ℝ)*(base60) + (263444188553/50000000000 : ℝ)*(major_s3_0) + (263444188553/50000000000 : ℝ)*(major_s3_1) + (263444188553/50000000000 : ℝ)*(major_s3_2) + (9561/40000000000 : ℝ)*(sp_s3_9) + (16659397/500000000000 : ℝ)*(sp_s3_15) + (38277013/1000000000000 : ℝ)*(sp_s3_16) + (1743970035131/250000000000 : ℝ)*(sp_s3_21) + (697584682173/100000000000 : ℝ)*(sp_s3_22) + (3487920812243/500000000000 : ℝ)*(sp_s3_23) + (3561885678497/1000000000000 : ℝ)*(sp_s3_27) + (3561885678497/1000000000000 : ℝ)*(f.failure) + (1743970035131/250000000000 : ℝ)*(f.sum) + (81691538476165387/1294060484000000000000000000000 : ℝ)*base62 + (72678015245611/67982500000000000000000000 : ℝ)*base65 + (186856327099471/237940000000000000000000000 : ℝ)*base67 + (60073980840347/271930000000000000000000000 : ℝ)*base69 + (886385629901940133/1323401731000000000000000000000 : ℝ)*base71 + (327619619619/1901054687500000000000000 : ℝ)*base73 + (54264672534731/47588000000000000000000000 : ℝ)*base75 + (245754000647187/243335000000000000000000000 : ℝ)*base77 + (3544516364725654699/11579825980000000000000000000000 : ℝ)*base78 + (2443/25000000000000000 : ℝ)*base86 + (2443/25000000000000000 : ℝ)*base88 + (2443/25000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((48667/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(48667/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((11897/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(11897/25000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27193/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(27193/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((5311/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5311/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((24883/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(24883/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(23637/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(23637/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301083_s3 p hpa hpb X hX hprev2

#print axioms solution
