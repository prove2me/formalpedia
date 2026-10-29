-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c309054_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:02:34.513536+00:00
-- url     : https://prove2.me/submissions/b0ea1d0a-1100-4738-b5a6-a9fa5176bf46

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
theorem collision_support_c309054_s3_s3_0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-721658647/5000000000 : ℝ)*x 0 + (1128379633/2500000000 : ℝ)*x 1 + (-3205997123/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (721658647/5000000000 : ℝ)^35 ≤ (406680959131/5000000000000 : ℝ)^27 := by
    have hnat : (721658647 : ℕ)^35*5000000000000^27 ≤ 406680959131^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      721658647 5000000000 406680959131 5000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1128379633/2500000000 : ℝ)^35 ≤ (8914343826979/25000000000000 : ℝ)^27 := by
    have hnat : (1128379633 : ℕ)^35*25000000000000^27 ≤ 8914343826979^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128379633 2500000000 8914343826979 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3205997123/5000000000 : ℝ)^35 ≤ (439132855457/781250000000 : ℝ)^27 := by
    have hnat : (3205997123 : ℕ)^35*781250000000^27 ≤ 439132855457^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3205997123 5000000000 439132855457 781250000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-721658647/5000000000 : ℝ), (1128379633/2500000000 : ℝ), (-3205997123/5000000000 : ℝ)] ![(406680959131/5000000000000 : ℝ), (8914343826979/25000000000000 : ℝ), (439132855457/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-721658647/5000000000 : ℝ)|^35 ≤ (406680959131/5000000000000 : ℝ)^27
        have hw : |(-721658647/5000000000 : ℝ)|=(721658647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1128379633/2500000000 : ℝ)|^35 ≤ (8914343826979/25000000000000 : ℝ)^27
        have hw : |(1128379633/2500000000 : ℝ)|=(1128379633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3205997123/5000000000 : ℝ)|^35 ≤ (439132855457/781250000000 : ℝ)^27
        have hw : |(-3205997123/5000000000 : ℝ)|=(3205997123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309054_s3_s3_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5175538873/10000000000 : ℝ)*x 0 + (513912317/1000000000 : ℝ)*x 1 + (2341443267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5175538873/10000000000 : ℝ)^35 ≤ (42579609201881/100000000000000 : ℝ)^27 := by
    have hnat : (5175538873 : ℕ)^35*100000000000000^27 ≤ 42579609201881^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175538873 10000000000 42579609201881 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (513912317/1000000000 : ℝ)^35 ≤ (4219165060031/10000000000000 : ℝ)^27 := by
    have hnat : (513912317 : ℕ)^35*10000000000000^27 ≤ 4219165060031^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513912317 1000000000 4219165060031 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2341443267/10000000000 : ℝ)^35 ≤ (15228740170479/100000000000000 : ℝ)^27 := by
    have hnat : (2341443267 : ℕ)^35*100000000000000^27 ≤ 15228740170479^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2341443267 10000000000 15228740170479 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5175538873/10000000000 : ℝ), (513912317/1000000000 : ℝ), (2341443267/10000000000 : ℝ)] ![(42579609201881/100000000000000 : ℝ), (4219165060031/10000000000000 : ℝ), (15228740170479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5175538873/10000000000 : ℝ)|^35 ≤ (42579609201881/100000000000000 : ℝ)^27
        have hw : |(5175538873/10000000000 : ℝ)|=(5175538873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(513912317/1000000000 : ℝ)|^35 ≤ (4219165060031/10000000000000 : ℝ)^27
        have hw : |(513912317/1000000000 : ℝ)|=(513912317/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2341443267/10000000000 : ℝ)|^35 ≤ (15228740170479/100000000000000 : ℝ)^27
        have hw : |(2341443267/10000000000 : ℝ)|=(2341443267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309054_s3_s3_7 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-643921299/5000000000 : ℝ)*x 0 + (504301087/1250000000 : ℝ)*x 1 + (-3464523297/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (643921299/5000000000 : ℝ)^35 ≤ (7016466023197/100000000000000 : ℝ)^27 := by
    have hnat : (643921299 : ℕ)^35*100000000000000^27 ≤ 7016466023197^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643921299 5000000000 7016466023197 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (504301087/1250000000 : ℝ)^35 ≤ (30830028990579/100000000000000 : ℝ)^27 := by
    have hnat : (504301087 : ℕ)^35*100000000000000^27 ≤ 30830028990579^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504301087 1250000000 30830028990579 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3464523297/5000000000 : ℝ)^35 ≤ (62153504969913/100000000000000 : ℝ)^27 := by
    have hnat : (3464523297 : ℕ)^35*100000000000000^27 ≤ 62153504969913^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3464523297 5000000000 62153504969913 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-643921299/5000000000 : ℝ), (504301087/1250000000 : ℝ), (-3464523297/5000000000 : ℝ)] ![(7016466023197/100000000000000 : ℝ), (30830028990579/100000000000000 : ℝ), (62153504969913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-643921299/5000000000 : ℝ)|^35 ≤ (7016466023197/100000000000000 : ℝ)^27
        have hw : |(-643921299/5000000000 : ℝ)|=(643921299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(504301087/1250000000 : ℝ)|^35 ≤ (30830028990579/100000000000000 : ℝ)^27
        have hw : |(504301087/1250000000 : ℝ)|=(504301087/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3464523297/5000000000 : ℝ)|^35 ≤ (62153504969913/100000000000000 : ℝ)^27
        have hw : |(-3464523297/5000000000 : ℝ)|=(3464523297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309054_s3_s3_8 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (131618157/250000000 : ℝ)*x 0 + (-839375687/5000000000 : ℝ)*x 1 + (-55461427/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131618157/250000000 : ℝ)^35 ≤ (10883297117389/25000000000000 : ℝ)^27 := by
    have hnat : (131618157 : ℕ)^35*25000000000000^27 ≤ 10883297117389^27*250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131618157 250000000 10883297117389 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (839375687/5000000000 : ℝ)^35 ≤ (4946781416573/50000000000000 : ℝ)^27 := by
    have hnat : (839375687 : ℕ)^35*50000000000000^27 ≤ 4946781416573^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      839375687 5000000000 4946781416573 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (55461427/100000000 : ℝ)^35 ≤ (2910828042277/6250000000000 : ℝ)^27 := by
    have hnat : (55461427 : ℕ)^35*6250000000000^27 ≤ 2910828042277^27*100000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55461427 100000000 2910828042277 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(131618157/250000000 : ℝ), (-839375687/5000000000 : ℝ), (-55461427/100000000 : ℝ)] ![(10883297117389/25000000000000 : ℝ), (4946781416573/50000000000000 : ℝ), (2910828042277/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(131618157/250000000 : ℝ)|^35 ≤ (10883297117389/25000000000000 : ℝ)^27
        have hw : |(131618157/250000000 : ℝ)|=(131618157/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-839375687/5000000000 : ℝ)|^35 ≤ (4946781416573/50000000000000 : ℝ)^27
        have hw : |(-839375687/5000000000 : ℝ)|=(839375687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-55461427/100000000 : ℝ)|^35 ≤ (2910828042277/6250000000000 : ℝ)^27
        have hw : |(-55461427/100000000 : ℝ)|=(55461427/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309054_s3_s3_9 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (482921811/1000000000 : ℝ)*x 0 + (3047934979/5000000000 : ℝ)*x 1 + (371045101/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (482921811/1000000000 : ℝ)^35 ≤ (38923393192567/100000000000000 : ℝ)^27 := by
    have hnat : (482921811 : ℕ)^35*100000000000000^27 ≤ 38923393192567^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482921811 1000000000 38923393192567 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3047934979/5000000000 : ℝ)^35 ≤ (658040432191/1250000000000 : ℝ)^27 := by
    have hnat : (3047934979 : ℕ)^35*1250000000000^27 ≤ 658040432191^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3047934979 5000000000 658040432191 1250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (371045101/2500000000 : ℝ)^35 ≤ (67466977751/800000000000 : ℝ)^27 := by
    have hnat : (371045101 : ℕ)^35*800000000000^27 ≤ 67466977751^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      371045101 2500000000 67466977751 800000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(482921811/1000000000 : ℝ), (3047934979/5000000000 : ℝ), (371045101/2500000000 : ℝ)] ![(38923393192567/100000000000000 : ℝ), (658040432191/1250000000000 : ℝ), (67466977751/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(482921811/1000000000 : ℝ)|^35 ≤ (38923393192567/100000000000000 : ℝ)^27
        have hw : |(482921811/1000000000 : ℝ)|=(482921811/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3047934979/5000000000 : ℝ)|^35 ≤ (658040432191/1250000000000 : ℝ)^27
        have hw : |(3047934979/5000000000 : ℝ)|=(3047934979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(371045101/2500000000 : ℝ)|^35 ≤ (67466977751/800000000000 : ℝ)^27
        have hw : |(371045101/2500000000 : ℝ)|=(371045101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309054_s3_s3_13 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4974446419/10000000000 : ℝ)*x 0 + (48379029/80000000 : ℝ)*x 1 + (-1349014313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4974446419/10000000000 : ℝ)^35 ≤ (40447469118549/100000000000000 : ℝ)^27 := by
    have hnat : (4974446419 : ℕ)^35*100000000000000^27 ≤ 40447469118549^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4974446419 10000000000 40447469118549 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (48379029/80000000 : ℝ)^35 ≤ (52101031216269/100000000000000 : ℝ)^27 := by
    have hnat : (48379029 : ℕ)^35*100000000000000^27 ≤ 52101031216269^27*80000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48379029 80000000 52101031216269 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1349014313/10000000000 : ℝ)^35 ≤ (7451499655489/100000000000000 : ℝ)^27 := by
    have hnat : (1349014313 : ℕ)^35*100000000000000^27 ≤ 7451499655489^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349014313 10000000000 7451499655489 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4974446419/10000000000 : ℝ), (48379029/80000000 : ℝ), (-1349014313/10000000000 : ℝ)] ![(40447469118549/100000000000000 : ℝ), (52101031216269/100000000000000 : ℝ), (7451499655489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4974446419/10000000000 : ℝ)|^35 ≤ (40447469118549/100000000000000 : ℝ)^27
        have hw : |(4974446419/10000000000 : ℝ)|=(4974446419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(48379029/80000000 : ℝ)|^35 ≤ (52101031216269/100000000000000 : ℝ)^27
        have hw : |(48379029/80000000 : ℝ)|=(48379029/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1349014313/10000000000 : ℝ)|^35 ≤ (7451499655489/100000000000000 : ℝ)^27
        have hw : |(-1349014313/10000000000 : ℝ)|=(1349014313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309054_s3_s3_14 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-784237829/10000000000 : ℝ)*x 0 + (443560149/1000000000 : ℝ)*x 1 + (-3434223759/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (784237829/10000000000 : ℝ)^35 ≤ (368872909637/10000000000000 : ℝ)^27 := by
    have hnat : (784237829 : ℕ)^35*10000000000000^27 ≤ 368872909637^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      784237829 10000000000 368872909637 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (443560149/1000000000 : ℝ)^35 ≤ (34861483176001/100000000000000 : ℝ)^27 := by
    have hnat : (443560149 : ℕ)^35*100000000000000^27 ≤ 34861483176001^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443560149 1000000000 34861483176001 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3434223759/5000000000 : ℝ)^35 ≤ (2457991508263/4000000000000 : ℝ)^27 := by
    have hnat : (3434223759 : ℕ)^35*4000000000000^27 ≤ 2457991508263^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3434223759 5000000000 2457991508263 4000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-784237829/10000000000 : ℝ), (443560149/1000000000 : ℝ), (-3434223759/5000000000 : ℝ)] ![(368872909637/10000000000000 : ℝ), (34861483176001/100000000000000 : ℝ), (2457991508263/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-784237829/10000000000 : ℝ)|^35 ≤ (368872909637/10000000000000 : ℝ)^27
        have hw : |(-784237829/10000000000 : ℝ)|=(784237829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(443560149/1000000000 : ℝ)|^35 ≤ (34861483176001/100000000000000 : ℝ)^27
        have hw : |(443560149/1000000000 : ℝ)|=(443560149/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3434223759/5000000000 : ℝ)|^35 ≤ (2457991508263/4000000000000 : ℝ)^27
        have hw : |(-3434223759/5000000000 : ℝ)|=(3434223759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309054_s3_s3_15 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2442782297/5000000000 : ℝ)*x 0 + (-2148129639/10000000000 : ℝ)*x 1 + (-5573168337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2442782297/5000000000 : ℝ)^35 ≤ (39513122881967/100000000000000 : ℝ)^27 := by
    have hnat : (2442782297 : ℕ)^35*100000000000000^27 ≤ 39513122881967^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2442782297 5000000000 39513122881967 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2148129639/10000000000 : ℝ)^35 ≤ (13619227784851/100000000000000 : ℝ)^27 := by
    have hnat : (2148129639 : ℕ)^35*100000000000000^27 ≤ 13619227784851^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148129639 10000000000 13619227784851 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5573168337/10000000000 : ℝ)^35 ≤ (4686764932487/10000000000000 : ℝ)^27 := by
    have hnat : (5573168337 : ℕ)^35*10000000000000^27 ≤ 4686764932487^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5573168337 10000000000 4686764932487 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2442782297/5000000000 : ℝ), (-2148129639/10000000000 : ℝ), (-5573168337/10000000000 : ℝ)] ![(39513122881967/100000000000000 : ℝ), (13619227784851/100000000000000 : ℝ), (4686764932487/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2442782297/5000000000 : ℝ)|^35 ≤ (39513122881967/100000000000000 : ℝ)^27
        have hw : |(2442782297/5000000000 : ℝ)|=(2442782297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2148129639/10000000000 : ℝ)|^35 ≤ (13619227784851/100000000000000 : ℝ)^27
        have hw : |(-2148129639/10000000000 : ℝ)|=(2148129639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5573168337/10000000000 : ℝ)|^35 ≤ (4686764932487/10000000000000 : ℝ)^27
        have hw : |(-5573168337/10000000000 : ℝ)|=(5573168337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309054_s3_s3_16 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3074741813/5000000000 : ℝ)*x 0 + (2395326713/5000000000 : ℝ)*x 1 + (364288997/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3074741813/5000000000 : ℝ)^35 ≤ (13311050529807/25000000000000 : ℝ)^27 := by
    have hnat : (3074741813 : ℕ)^35*25000000000000^27 ≤ 13311050529807^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3074741813 5000000000 13311050529807 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2395326713/5000000000 : ℝ)^35 ≤ (38520942332611/100000000000000 : ℝ)^27 := by
    have hnat : (2395326713 : ℕ)^35*100000000000000^27 ≤ 38520942332611^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2395326713 5000000000 38520942332611 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (364288997/2500000000 : ℝ)^35 ≤ (411742776729/5000000000000 : ℝ)^27 := by
    have hnat : (364288997 : ℕ)^35*5000000000000^27 ≤ 411742776729^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      364288997 2500000000 411742776729 5000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3074741813/5000000000 : ℝ), (2395326713/5000000000 : ℝ), (364288997/2500000000 : ℝ)] ![(13311050529807/25000000000000 : ℝ), (38520942332611/100000000000000 : ℝ), (411742776729/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3074741813/5000000000 : ℝ)|^35 ≤ (13311050529807/25000000000000 : ℝ)^27
        have hw : |(3074741813/5000000000 : ℝ)|=(3074741813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2395326713/5000000000 : ℝ)|^35 ≤ (38520942332611/100000000000000 : ℝ)^27
        have hw : |(2395326713/5000000000 : ℝ)|=(2395326713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(364288997/2500000000 : ℝ)|^35 ≤ (411742776729/5000000000000 : ℝ)^27
        have hw : |(364288997/2500000000 : ℝ)|=(364288997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309054_s3_s3_20 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (301248199/500000000 : ℝ)*x 0 + (4906820271/10000000000 : ℝ)*x 1 + (-7407103/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (301248199/500000000 : ℝ)^35 ≤ (810169334531/1562500000000 : ℝ)^27 := by
    have hnat : (301248199 : ℕ)^35*1562500000000^27 ≤ 810169334531^27*500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      301248199 500000000 810169334531 1562500000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4906820271/10000000000 : ℝ)^35 ≤ (19868056435669/50000000000000 : ℝ)^27 := by
    have hnat : (4906820271 : ℕ)^35*50000000000000^27 ≤ 19868056435669^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4906820271 10000000000 19868056435669 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7407103/50000000 : ℝ)^35 ≤ (4206524853449/50000000000000 : ℝ)^27 := by
    have hnat : (7407103 : ℕ)^35*50000000000000^27 ≤ 4206524853449^27*50000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7407103 50000000 4206524853449 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(301248199/500000000 : ℝ), (4906820271/10000000000 : ℝ), (-7407103/50000000 : ℝ)] ![(810169334531/1562500000000 : ℝ), (19868056435669/50000000000000 : ℝ), (4206524853449/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(301248199/500000000 : ℝ)|^35 ≤ (810169334531/1562500000000 : ℝ)^27
        have hw : |(301248199/500000000 : ℝ)|=(301248199/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4906820271/10000000000 : ℝ)|^35 ≤ (19868056435669/50000000000000 : ℝ)^27
        have hw : |(4906820271/10000000000 : ℝ)|=(4906820271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7407103/50000000 : ℝ)|^35 ≤ (4206524853449/50000000000000 : ℝ)^27
        have hw : |(-7407103/50000000 : ℝ)|=(7407103/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309054_s3_s3_21 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-284591691/5000000000 : ℝ)*x 0 + (5198363559/10000000000 : ℝ)*x 1 + (-6282522077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (284591691/5000000000 : ℝ)^35 ≤ (608664624089/25000000000000 : ℝ)^27 := by
    have hnat : (284591691 : ℕ)^35*25000000000000^27 ≤ 608664624089^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284591691 5000000000 608664624089 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5198363559/10000000000 : ℝ)^35 ≤ (42823187475851/100000000000000 : ℝ)^27 := by
    have hnat : (5198363559 : ℕ)^35*100000000000000^27 ≤ 42823187475851^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5198363559 10000000000 42823187475851 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6282522077/10000000000 : ℝ)^35 ≤ (54742154012767/100000000000000 : ℝ)^27 := by
    have hnat : (6282522077 : ℕ)^35*100000000000000^27 ≤ 54742154012767^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6282522077 10000000000 54742154012767 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-284591691/5000000000 : ℝ), (5198363559/10000000000 : ℝ), (-6282522077/10000000000 : ℝ)] ![(608664624089/25000000000000 : ℝ), (42823187475851/100000000000000 : ℝ), (54742154012767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-284591691/5000000000 : ℝ)|^35 ≤ (608664624089/25000000000000 : ℝ)^27
        have hw : |(-284591691/5000000000 : ℝ)|=(284591691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5198363559/10000000000 : ℝ)|^35 ≤ (42823187475851/100000000000000 : ℝ)^27
        have hw : |(5198363559/10000000000 : ℝ)|=(5198363559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6282522077/10000000000 : ℝ)|^35 ≤ (54742154012767/100000000000000 : ℝ)^27
        have hw : |(-6282522077/10000000000 : ℝ)|=(6282522077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309054_s3_s3_22 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6442535243/10000000000 : ℝ)*x 0 + (-116480921/625000000 : ℝ)*x 1 + (-1040873057/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6442535243/10000000000 : ℝ)^35 ≤ (56556306692363/100000000000000 : ℝ)^27 := by
    have hnat : (6442535243 : ℕ)^35*100000000000000^27 ≤ 56556306692363^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6442535243 10000000000 56556306692363 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (116480921/625000000 : ℝ)^35 ≤ (566447327437/5000000000000 : ℝ)^27 := by
    have hnat : (116480921 : ℕ)^35*5000000000000^27 ≤ 566447327437^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116480921 625000000 566447327437 5000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1040873057/2500000000 : ℝ)^35 ≤ (32114746741501/100000000000000 : ℝ)^27 := by
    have hnat : (1040873057 : ℕ)^35*100000000000000^27 ≤ 32114746741501^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040873057 2500000000 32114746741501 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6442535243/10000000000 : ℝ), (-116480921/625000000 : ℝ), (-1040873057/2500000000 : ℝ)] ![(56556306692363/100000000000000 : ℝ), (566447327437/5000000000000 : ℝ), (32114746741501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6442535243/10000000000 : ℝ)|^35 ≤ (56556306692363/100000000000000 : ℝ)^27
        have hw : |(6442535243/10000000000 : ℝ)|=(6442535243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-116480921/625000000 : ℝ)|^35 ≤ (566447327437/5000000000000 : ℝ)^27
        have hw : |(-116480921/625000000 : ℝ)|=(116480921/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1040873057/2500000000 : ℝ)|^35 ≤ (32114746741501/100000000000000 : ℝ)^27
        have hw : |(-1040873057/2500000000 : ℝ)|=(1040873057/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309054_s3_s3_23 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4896386187/10000000000 : ℝ)*x 0 + (1062600669/2000000000 : ℝ)*x 1 + (2470081567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4896386187/10000000000 : ℝ)^35 ≤ (2476663417691/6250000000000 : ℝ)^27 := by
    have hnat : (4896386187 : ℕ)^35*6250000000000^27 ≤ 2476663417691^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4896386187 10000000000 2476663417691 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1062600669/2000000000 : ℝ)^35 ≤ (44051365488843/100000000000000 : ℝ)^27 := by
    have hnat : (1062600669 : ℕ)^35*100000000000000^27 ≤ 44051365488843^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062600669 2000000000 44051365488843 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2470081567/10000000000 : ℝ)^35 ≤ (3264403961971/20000000000000 : ℝ)^27 := by
    have hnat : (2470081567 : ℕ)^35*20000000000000^27 ≤ 3264403961971^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2470081567 10000000000 3264403961971 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4896386187/10000000000 : ℝ), (1062600669/2000000000 : ℝ), (2470081567/10000000000 : ℝ)] ![(2476663417691/6250000000000 : ℝ), (44051365488843/100000000000000 : ℝ), (3264403961971/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4896386187/10000000000 : ℝ)|^35 ≤ (2476663417691/6250000000000 : ℝ)^27
        have hw : |(4896386187/10000000000 : ℝ)|=(4896386187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1062600669/2000000000 : ℝ)|^35 ≤ (44051365488843/100000000000000 : ℝ)^27
        have hw : |(1062600669/2000000000 : ℝ)|=(1062600669/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2470081567/10000000000 : ℝ)|^35 ≤ (3264403961971/20000000000000 : ℝ)^27
        have hw : |(2470081567/10000000000 : ℝ)|=(2470081567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309054_s3_s3_27 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5830906099/10000000000 : ℝ)*x 0 + (769701/1600000 : ℝ)*x 1 + (-189476041/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5830906099/10000000000 : ℝ)^35 ≤ (9939270307649/20000000000000 : ℝ)^27 := by
    have hnat : (5830906099 : ℕ)^35*20000000000000^27 ≤ 9939270307649^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5830906099 10000000000 9939270307649 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (769701/1600000 : ℝ)^35 ≤ (38729306279653/100000000000000 : ℝ)^27 := by
    have hnat : (769701 : ℕ)^35*100000000000000^27 ≤ 38729306279653^27*1600000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      769701 1600000 38729306279653 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (189476041/1000000000 : ℝ)^35 ≤ (11574342169197/100000000000000 : ℝ)^27 := by
    have hnat : (189476041 : ℕ)^35*100000000000000^27 ≤ 11574342169197^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      189476041 1000000000 11574342169197 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5830906099/10000000000 : ℝ), (769701/1600000 : ℝ), (-189476041/1000000000 : ℝ)] ![(9939270307649/20000000000000 : ℝ), (38729306279653/100000000000000 : ℝ), (11574342169197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5830906099/10000000000 : ℝ)|^35 ≤ (9939270307649/20000000000000 : ℝ)^27
        have hw : |(5830906099/10000000000 : ℝ)|=(5830906099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(769701/1600000 : ℝ)|^35 ≤ (38729306279653/100000000000000 : ℝ)^27
        have hw : |(769701/1600000 : ℝ)|=(769701/1600000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-189476041/1000000000 : ℝ)|^35 ≤ (11574342169197/100000000000000 : ℝ)^27
        have hw : |(-189476041/1000000000 : ℝ)|=(189476041/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c309054_s3 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev2 : (0 : ℝ) ≤ ((6871/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6871/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29277/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(29277/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-22247/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-22247/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((851/2500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(851/2500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17823/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(17823/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-11611/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-11611/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (77509/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (77509/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (77509/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (77509/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (77509/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (77509/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s3_pow0 : (6871/12500 : ℝ) ^ (69/16 : ℝ) ≤ (151444704673696353/2000000000000000000 : ℝ) := by
    have hpowers : (6871/12500 : ℝ)^69 ≤ (151444704673696353/2000000000000000000 : ℝ)^16 := by
      have hnat : (6871 : ℕ)^69*2000000000000000000^16 ≤ 151444704673696353^16*12500^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6871 12500 151444704673696353 2000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6871/12500 : ℝ)) (X := (151444704673696353/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s3_corner0a : (2151444704673696353/2000000000000000000 : ℝ) ≤ (10170698244243867/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (2151444704673696353/2000000000000000000 : ℝ)^16 ≤ (10170698244243867/10000000000000000 : ℝ)^69 := by
      have hnat : (2151444704673696353 : ℕ)^16*10000000000000000^69 ≤ 10170698244243867^69*2000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2151444704673696353 2000000000000000000 10170698244243867 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10170698244243867/10000000000000000 : ℝ)) (X := (2151444704673696353/2000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s3_corner0b : (1151444704673696353/1000000000000000000 : ℝ) ≤ (10332402016561871/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (1151444704673696353/1000000000000000000 : ℝ)^16 ≤ (10332402016561871/10000000000000000 : ℝ)^69 := by
      have hnat : (1151444704673696353 : ℕ)^16*10000000000000000^69 ≤ 10332402016561871^69*1000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1151444704673696353 1000000000000000000 10332402016561871 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10332402016561871/10000000000000000 : ℝ)) (X := (1151444704673696353/1000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(170698244243867/5496800000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(40425943079501/1374200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (6871/12500 : ℝ)) (alpha := (170698244243867/5496800000000000 : ℝ)) (beta := (40425943079501/1374200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (6871/12500 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(170698244243867/5496800000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(40425943079501/1374200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (29277/50000 : ℝ) ^ (69/16 : ℝ) ≤ (4972304372479305891/50000000000000000000 : ℝ) := by
    have hpowers : (29277/50000 : ℝ)^69 ≤ (4972304372479305891/50000000000000000000 : ℝ)^16 := by
      have hnat : (29277 : ℕ)^69*50000000000000000000^16 ≤ 4972304372479305891^16*50000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29277 50000 4972304372479305891 50000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (29277/50000 : ℝ)) (X := (4972304372479305891/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s3_corner1a : (54972304372479305891/50000000000000000000 : ℝ) ≤ (10222275462984889/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (54972304372479305891/50000000000000000000 : ℝ)^16 ≤ (10222275462984889/10000000000000000 : ℝ)^69 := by
      have hnat : (54972304372479305891 : ℕ)^16*10000000000000000^69 ≤ 10222275462984889^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54972304372479305891 50000000000000000000 10222275462984889 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10222275462984889/10000000000000000 : ℝ)) (X := (54972304372479305891/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s3_corner1b : (29972304372479305891/25000000000000000000 : ℝ) ≤ (5214802433820471/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (29972304372479305891/25000000000000000000 : ℝ)^16 ≤ (5214802433820471/5000000000000000 : ℝ)^69 := by
      have hnat : (29972304372479305891 : ℕ)^16*5000000000000000^69 ≤ 5214802433820471^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29972304372479305891 25000000000000000000 5214802433820471 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5214802433820471/5000000000000000 : ℝ)) (X := (29972304372479305891/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(74091820994963/1951800000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(207329404656053/5855400000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (29277/50000 : ℝ)) (alpha := (74091820994963/1951800000000000 : ℝ)) (beta := (207329404656053/5855400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (29277/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(74091820994963/1951800000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(207329404656053/5855400000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (22247/50000 : ℝ) ^ (69/16 : ℝ) ≤ (760746589129810013/25000000000000000000 : ℝ) := by
    have hpowers : (22247/50000 : ℝ)^69 ≤ (760746589129810013/25000000000000000000 : ℝ)^16 := by
      have hnat : (22247 : ℕ)^69*25000000000000000000^16 ≤ 760746589129810013^16*50000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22247 50000 760746589129810013 25000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (22247/50000 : ℝ)) (X := (760746589129810013/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s3_corner2a : (25760746589129810013/25000000000000000000 : ℝ) ≤ (1006975184137977/1000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (25760746589129810013/25000000000000000000 : ℝ)^16 ≤ (1006975184137977/1000000000000000 : ℝ)^69 := by
      have hnat : (25760746589129810013 : ℕ)^16*1000000000000000^69 ≤ 1006975184137977^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25760746589129810013 25000000000000000000 1006975184137977 1000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1006975184137977/1000000000000000 : ℝ)) (X := (25760746589129810013/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s3_corner2b : (13260746589129810013/12500000000000000000 : ℝ) ≤ (10137938971870723/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (13260746589129810013/12500000000000000000 : ℝ)^16 ≤ (10137938971870723/10000000000000000 : ℝ)^69 := by
      have hnat : (13260746589129810013 : ℕ)^16*10000000000000000^69 ≤ 10137938971870723^69*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13260746589129810013 12500000000000000000 10137938971870723 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10137938971870723/10000000000000000 : ℝ)) (X := (13260746589129810013/12500000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(6975184137977/444940000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(68187130490953/4449400000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (22247/50000 : ℝ)) (alpha := (6975184137977/444940000000000 : ℝ)) (beta := (68187130490953/4449400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (22247/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(6975184137977/444940000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(68187130490953/4449400000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-721658647/5000000000 : ℝ)*X 0 0+(1128379633/2500000000 : ℝ)*X 0 1+(-3205997123/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((5175538873/10000000000 : ℝ)*X 2 0+(513912317/1000000000 : ℝ)*X 2 1+(2341443267/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-643921299/5000000000 : ℝ)*X 0 0+(504301087/1250000000 : ℝ)*X 0 1+(-3464523297/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((131618157/250000000 : ℝ)*X 1 0+(-839375687/5000000000 : ℝ)*X 1 1+(-55461427/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((482921811/1000000000 : ℝ)*X 2 0+(3047934979/5000000000 : ℝ)*X 2 1+(371045101/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((4974446419/10000000000 : ℝ)*X 0 0+(48379029/80000000 : ℝ)*X 0 1+(-1349014313/10000000000 : ℝ)*X 0 2+(4974446419/10000000000 : ℝ)*X 1 0+(48379029/80000000 : ℝ)*X 1 1+(-1349014313/10000000000 : ℝ)*X 1 2+(4974446419/10000000000 : ℝ)*X 2 0+(48379029/80000000 : ℝ)*X 2 1+(-1349014313/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-784237829/10000000000 : ℝ)*X 0 0+(443560149/1000000000 : ℝ)*X 0 1+(-3434223759/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((2442782297/5000000000 : ℝ)*X 1 0+(-2148129639/10000000000 : ℝ)*X 1 1+(-5573168337/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((3074741813/5000000000 : ℝ)*X 2 0+(2395326713/5000000000 : ℝ)*X 2 1+(364288997/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((301248199/500000000 : ℝ)*X 0 0+(4906820271/10000000000 : ℝ)*X 0 1+(-7407103/50000000 : ℝ)*X 0 2+(301248199/500000000 : ℝ)*X 1 0+(4906820271/10000000000 : ℝ)*X 1 1+(-7407103/50000000 : ℝ)*X 1 2+(301248199/500000000 : ℝ)*X 2 0+(4906820271/10000000000 : ℝ)*X 2 1+(-7407103/50000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-284591691/5000000000 : ℝ)*X 0 0+(5198363559/10000000000 : ℝ)*X 0 1+(-6282522077/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((6442535243/10000000000 : ℝ)*X 1 0+(-116480921/625000000 : ℝ)*X 1 1+(-1040873057/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((4896386187/10000000000 : ℝ)*X 2 0+(1062600669/2000000000 : ℝ)*X 2 1+(2470081567/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((5830906099/10000000000 : ℝ)*X 0 0+(769701/1600000 : ℝ)*X 0 1+(-189476041/1000000000 : ℝ)*X 0 2+(5830906099/10000000000 : ℝ)*X 1 0+(769701/1600000 : ℝ)*X 1 1+(-189476041/1000000000 : ℝ)*X 1 2+(5830906099/10000000000 : ℝ)*X 2 0+(769701/1600000 : ℝ)*X 2 1+(-189476041/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309054_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((851/2500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(851/2500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (300387228834554138277444001077/19890030906440000000000000000000000 : ℝ) := by norm_num
    linear_combination (337474958023/500000000000 : ℝ)*(base39) + (5668273/1000000000000 : ℝ)*(base50) + (443270369517/1000000000000 : ℝ)*(base60) + (2701636955829/500000000000 : ℝ)*(major_s3_0) + (2701636955829/500000000000 : ℝ)*(major_s3_1) + (2701636955829/500000000000 : ℝ)*(major_s3_2) + (33297071/1000000000000 : ℝ)*(sp_s3_0) + (463339442593/62500000000 : ℝ)*(sp_s3_7) + (115833535467/15625000000 : ℝ)*(sp_s3_8) + (3706719481207/500000000000 : ℝ)*(sp_s3_9) + (848253642401/250000000000 : ℝ)*(sp_s3_13) + (63841011/1000000000000 : ℝ)*(sp_s3_14) + (181949683/1000000000000 : ℝ)*(sp_s3_15) + (22314289/250000000000 : ℝ)*(sp_s3_23) + (848253642401/250000000000 : ℝ)*(f.failure) + (741352821957/100000000000 : ℝ)*(f.sum) + (6734438330489454723/7236949100000000000000000000000 : ℝ)*base63 + (304953545949337/2224700000000000000000000000 : ℝ)*base65 + (3347978284353/325300000000000000000000000 : ℝ)*base66 + (78726582002687/222470000000000000000000000 : ℝ)*base69 + (162307275333844949/61143654800000000000000000000000 : ℝ)*base71 + (155451884569659/687100000000000000000000000 : ℝ)*base73 + (295292841959469/325300000000000000000000000 : ℝ)*base75 + (1578789903439863/2748400000000000000000000000 : ℝ)*base77 + (554551103020876527/1117568150000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (17953/25000000000000000 : ℝ)*base86 + (17953/25000000000000000 : ℝ)*base88 + (17953/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17823/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(17823/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (95352123835890398191702083/7236949100000000000000000000000 : ℝ) := by norm_num
    linear_combination (613149505317/1000000000000 : ℝ)*(base39) + (106273/40000000000 : ℝ)*(base49) + (89576819593/500000000000 : ℝ)*(base60) + (5431387628967/1000000000000 : ℝ)*(major_s3_0) + (5431387628967/1000000000000 : ℝ)*(major_s3_1) + (5431387628967/1000000000000 : ℝ)*(major_s3_2) + (26085461/200000000000 : ℝ)*(sp_s3_0) + (72978871/500000000000 : ℝ)*(sp_s3_8) + (232872944179/31250000000 : ℝ)*(sp_s3_14) + (7451956180467/1000000000000 : ℝ)*(sp_s3_15) + (7452102138209/1000000000000 : ℝ)*(sp_s3_16) + (3410340316161/1000000000000 : ℝ)*(sp_s3_20) + (4687147/125000000000 : ℝ)*(sp_s3_21) + (328411643/1000000000000 : ℝ)*(sp_s3_27) + (852667181951/250000000000 : ℝ)*(f.failure) + (7452102138209/1000000000000 : ℝ)*(f.sum) + (8260522861635696939/14473898200000000000000000000000 : ℝ)*base63 + (1207537171135251/4449400000000000000000000000 : ℝ)*base65 + (152837661937537/1951800000000000000000000000 : ℝ)*base66 + (461863169321829/444940000000000000000000000 : ℝ)*base69 + (27282160432018078833/122287309600000000000000000000000 : ℝ)*base70 + (493906160917753/1374200000000000000000000000 : ℝ)*base72 + (464631057913147/650600000000000000000000000 : ℝ)*base75 + (3551483586218189/5496800000000000000000000000 : ℝ)*base77 + (4012156481670779443/6705408900000000000000000000000 : ℝ)*base79 + (24103/25000000000000000 : ℝ)*base86 + (24103/25000000000000000 : ℝ)*base88 + (24103/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-11611/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-11611/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3239866546145618490435565101467/298350463596600000000000000000000000 : ℝ) := by norm_num
    linear_combination (859191/1000000000000 : ℝ)*(base11) + (963706269691/1000000000000 : ℝ)*(base39) + (1856451/1000000000000 : ℝ)*(base40) + (38077/12500000000 : ℝ)*(base50) + (2132894143807/500000000000 : ℝ)*(major_s3_0) + (2132894143807/500000000000 : ℝ)*(major_s3_1) + (2132894143807/500000000000 : ℝ)*(major_s3_2) + (695979/500000000000 : ℝ)*(sp_s3_2) + (30061053/1000000000000 : ℝ)*(sp_s3_9) + (224390593/1000000000000 : ℝ)*(sp_s3_20) + (5852847669681/1000000000000 : ℝ)*(sp_s3_21) + (5852848528873/1000000000000 : ℝ)*(sp_s3_22) + (2926408537931/500000000000 : ℝ)*(sp_s3_23) + (2678500035999/1000000000000 : ℝ)*(sp_s3_27) + (2678724426591/1000000000000 : ℝ)*(f.failure) + (5852848528873/1000000000000 : ℝ)*(f.sum) + (16021678890848785433/21710847300000000000000000000000 : ℝ)*base62 + (614126341132031/2224700000000000000000000000 : ℝ)*base65 + (1496206113152981/2927700000000000000000000000 : ℝ)*base66 + (114662560989021/222470000000000000000000000 : ℝ)*base68 + (16433293733123655393/61143654800000000000000000000000 : ℝ)*base70 + (66666824560447/687100000000000000000000000 : ℝ)*base73 + (816417106004269/975900000000000000000000000 : ℝ)*base74 + (1064472205317011/2748400000000000000000000000 : ℝ)*base76 + (4457658488233106521/10058113350000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (63023/100000000000000000 : ℝ)*base86 + (63023/100000000000000000 : ℝ)*base88 + (63023/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev2 : (0 : ℝ) ≤ ((6871/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6871/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29277/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(29277/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-22247/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-22247/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((851/2500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(851/2500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17823/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(17823/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-11611/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-11611/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c309054_s3 p hpa hpb X hX hprev2

#print axioms solution
