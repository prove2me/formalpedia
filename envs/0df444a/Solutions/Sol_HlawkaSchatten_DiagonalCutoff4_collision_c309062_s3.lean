-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c309062_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:05:19.803643+00:00
-- url     : https://prove2.me/submissions/b97f300c-5088-4bcf-8ee6-b542077e03a2

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
theorem collision_support_c309062_s3_s3_0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2074698391/10000000000 : ℝ)*x 0 + (2438166241/5000000000 : ℝ)*x 1 + (-2818507363/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2074698391/10000000000 : ℝ)^35 ≤ (2603761812619/20000000000000 : ℝ)^27 := by
    have hnat : (2074698391 : ℕ)^35*20000000000000^27 ≤ 2603761812619^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074698391 10000000000 2603761812619 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2438166241/5000000000 : ℝ)^35 ≤ (39416359667343/100000000000000 : ℝ)^27 := by
    have hnat : (2438166241 : ℕ)^35*100000000000000^27 ≤ 39416359667343^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2438166241 5000000000 39416359667343 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2818507363/5000000000 : ℝ)^35 ≤ (11891207812059/25000000000000 : ℝ)^27 := by
    have hnat : (2818507363 : ℕ)^35*25000000000000^27 ≤ 11891207812059^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2818507363 5000000000 11891207812059 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2074698391/10000000000 : ℝ), (2438166241/5000000000 : ℝ), (-2818507363/5000000000 : ℝ)] ![(2603761812619/20000000000000 : ℝ), (39416359667343/100000000000000 : ℝ), (11891207812059/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2074698391/10000000000 : ℝ)|^35 ≤ (2603761812619/20000000000000 : ℝ)^27
        have hw : |(-2074698391/10000000000 : ℝ)|=(2074698391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2438166241/5000000000 : ℝ)|^35 ≤ (39416359667343/100000000000000 : ℝ)^27
        have hw : |(2438166241/5000000000 : ℝ)|=(2438166241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2818507363/5000000000 : ℝ)|^35 ≤ (11891207812059/25000000000000 : ℝ)^27
        have hw : |(-2818507363/5000000000 : ℝ)|=(2818507363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309062_s3_s3_1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4874417273/10000000000 : ℝ)*x 0 + (-1039515197/5000000000 : ℝ)*x 1 + (-5635626687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4874417273/10000000000 : ℝ)^35 ≤ (157585171421/400000000000 : ℝ)^27 := by
    have hnat : (4874417273 : ℕ)^35*400000000000^27 ≤ 157585171421^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4874417273 10000000000 157585171421 400000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1039515197/5000000000 : ℝ)^35 ≤ (1305405780109/10000000000000 : ℝ)^27 := by
    have hnat : (1039515197 : ℕ)^35*10000000000000^27 ≤ 1305405780109^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039515197 5000000000 1305405780109 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5635626687/10000000000 : ℝ)^35 ≤ (23774824660671/50000000000000 : ℝ)^27 := by
    have hnat : (5635626687 : ℕ)^35*50000000000000^27 ≤ 23774824660671^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5635626687 10000000000 23774824660671 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4874417273/10000000000 : ℝ), (-1039515197/5000000000 : ℝ), (-5635626687/10000000000 : ℝ)] ![(157585171421/400000000000 : ℝ), (1305405780109/10000000000000 : ℝ), (23774824660671/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4874417273/10000000000 : ℝ)|^35 ≤ (157585171421/400000000000 : ℝ)^27
        have hw : |(4874417273/10000000000 : ℝ)|=(4874417273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1039515197/5000000000 : ℝ)|^35 ≤ (1305405780109/10000000000000 : ℝ)^27
        have hw : |(-1039515197/5000000000 : ℝ)|=(1039515197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5635626687/10000000000 : ℝ)|^35 ≤ (23774824660671/50000000000000 : ℝ)^27
        have hw : |(-5635626687/10000000000 : ℝ)|=(5635626687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309062_s3_s3_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (101690609/200000000 : ℝ)*x 0 + (635256477/1250000000 : ℝ)*x 1 + (2526064623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (101690609/200000000 : ℝ)^35 ≤ (20805783378283/50000000000000 : ℝ)^27 := by
    have hnat : (101690609 : ℕ)^35*50000000000000^27 ≤ 20805783378283^27*200000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101690609 200000000 20805783378283 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (635256477/1250000000 : ℝ)^35 ≤ (41585273248761/100000000000000 : ℝ)^27 := by
    have hnat : (635256477 : ℕ)^35*100000000000000^27 ≤ 41585273248761^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      635256477 1250000000 41585273248761 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2526064623/10000000000 : ℝ)^35 ≤ (16803159984911/100000000000000 : ℝ)^27 := by
    have hnat : (2526064623 : ℕ)^35*100000000000000^27 ≤ 16803159984911^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2526064623 10000000000 16803159984911 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(101690609/200000000 : ℝ), (635256477/1250000000 : ℝ), (2526064623/10000000000 : ℝ)] ![(20805783378283/50000000000000 : ℝ), (41585273248761/100000000000000 : ℝ), (16803159984911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(101690609/200000000 : ℝ)|^35 ≤ (20805783378283/50000000000000 : ℝ)^27
        have hw : |(101690609/200000000 : ℝ)|=(101690609/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(635256477/1250000000 : ℝ)|^35 ≤ (41585273248761/100000000000000 : ℝ)^27
        have hw : |(635256477/1250000000 : ℝ)|=(635256477/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2526064623/10000000000 : ℝ)|^35 ≤ (16803159984911/100000000000000 : ℝ)^27
        have hw : |(2526064623/10000000000 : ℝ)|=(2526064623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309062_s3_s3_7 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-438626703/2500000000 : ℝ)*x 0 + (551082781/1250000000 : ℝ)*x 1 + (-1259946001/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (438626703/2500000000 : ℝ)^35 ≤ (2095226593627/20000000000000 : ℝ)^27 := by
    have hnat : (438626703 : ℕ)^35*20000000000000^27 ≤ 2095226593627^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438626703 2500000000 2095226593627 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (551082781/1250000000 : ℝ)^35 ≤ (17293633997681/50000000000000 : ℝ)^27 := by
    have hnat : (551082781 : ℕ)^35*50000000000000^27 ≤ 17293633997681^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551082781 1250000000 17293633997681 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1259946001/2000000000 : ℝ)^35 ≤ (54936599021011/100000000000000 : ℝ)^27 := by
    have hnat : (1259946001 : ℕ)^35*100000000000000^27 ≤ 54936599021011^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1259946001 2000000000 54936599021011 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-438626703/2500000000 : ℝ), (551082781/1250000000 : ℝ), (-1259946001/2000000000 : ℝ)] ![(2095226593627/20000000000000 : ℝ), (17293633997681/50000000000000 : ℝ), (54936599021011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-438626703/2500000000 : ℝ)|^35 ≤ (2095226593627/20000000000000 : ℝ)^27
        have hw : |(-438626703/2500000000 : ℝ)|=(438626703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(551082781/1250000000 : ℝ)|^35 ≤ (17293633997681/50000000000000 : ℝ)^27
        have hw : |(551082781/1250000000 : ℝ)|=(551082781/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1259946001/2000000000 : ℝ)|^35 ≤ (54936599021011/100000000000000 : ℝ)^27
        have hw : |(-1259946001/2000000000 : ℝ)|=(1259946001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309062_s3_s3_8 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4830887911/10000000000 : ℝ)*x 0 + (-90319071/625000000 : ℝ)*x 1 + (-1223981389/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4830887911/10000000000 : ℝ)^35 ≤ (4867605045931/12500000000000 : ℝ)^27 := by
    have hnat : (4830887911 : ℕ)^35*12500000000000^27 ≤ 4867605045931^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4830887911 10000000000 4867605045931 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (90319071/625000000 : ℝ)^35 ≤ (8146681947283/100000000000000 : ℝ)^27 := by
    have hnat : (90319071 : ℕ)^35*100000000000000^27 ≤ 8146681947283^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90319071 625000000 8146681947283 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1223981389/2000000000 : ℝ)^35 ≤ (3307029854437/6250000000000 : ℝ)^27 := by
    have hnat : (1223981389 : ℕ)^35*6250000000000^27 ≤ 3307029854437^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1223981389 2000000000 3307029854437 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4830887911/10000000000 : ℝ), (-90319071/625000000 : ℝ), (-1223981389/2000000000 : ℝ)] ![(4867605045931/12500000000000 : ℝ), (8146681947283/100000000000000 : ℝ), (3307029854437/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4830887911/10000000000 : ℝ)|^35 ≤ (4867605045931/12500000000000 : ℝ)^27
        have hw : |(4830887911/10000000000 : ℝ)|=(4830887911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-90319071/625000000 : ℝ)|^35 ≤ (8146681947283/100000000000000 : ℝ)^27
        have hw : |(-90319071/625000000 : ℝ)|=(90319071/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1223981389/2000000000 : ℝ)|^35 ≤ (3307029854437/6250000000000 : ℝ)^27
        have hw : |(-1223981389/2000000000 : ℝ)|=(1223981389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309062_s3_s3_9 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (970847703/2000000000 : ℝ)*x 0 + (370846303/625000000 : ℝ)*x 1 + (845142289/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (970847703/2000000000 : ℝ)^35 ≤ (39185009796999/100000000000000 : ℝ)^27 := by
    have hnat : (970847703 : ℕ)^35*100000000000000^27 ≤ 39185009796999^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      970847703 2000000000 39185009796999 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (370846303/625000000 : ℝ)^35 ≤ (12708307187921/25000000000000 : ℝ)^27 := by
    have hnat : (370846303 : ℕ)^35*25000000000000^27 ≤ 12708307187921^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      370846303 625000000 12708307187921 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (845142289/5000000000 : ℝ)^35 ≤ (9981761430239/100000000000000 : ℝ)^27 := by
    have hnat : (845142289 : ℕ)^35*100000000000000^27 ≤ 9981761430239^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845142289 5000000000 9981761430239 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(970847703/2000000000 : ℝ), (370846303/625000000 : ℝ), (845142289/5000000000 : ℝ)] ![(39185009796999/100000000000000 : ℝ), (12708307187921/25000000000000 : ℝ), (9981761430239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(970847703/2000000000 : ℝ)|^35 ≤ (39185009796999/100000000000000 : ℝ)^27
        have hw : |(970847703/2000000000 : ℝ)|=(970847703/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(370846303/625000000 : ℝ)|^35 ≤ (12708307187921/25000000000000 : ℝ)^27
        have hw : |(370846303/625000000 : ℝ)|=(370846303/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(845142289/5000000000 : ℝ)|^35 ≤ (9981761430239/100000000000000 : ℝ)^27
        have hw : |(845142289/5000000000 : ℝ)|=(845142289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309062_s3_s3_13 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1284545171/2500000000 : ℝ)*x 0 + (3047419917/5000000000 : ℝ)*x 1 + (-1020067197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1284545171/2500000000 : ℝ)^35 ≤ (21090810254611/50000000000000 : ℝ)^27 := by
    have hnat : (1284545171 : ℕ)^35*50000000000000^27 ≤ 21090810254611^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284545171 2500000000 21090810254611 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3047419917/5000000000 : ℝ)^35 ≤ (13157925742391/25000000000000 : ℝ)^27 := by
    have hnat : (3047419917 : ℕ)^35*25000000000000^27 ≤ 13157925742391^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3047419917 5000000000 13157925742391 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1020067197/10000000000 : ℝ)^35 ≤ (2593338252363/50000000000000 : ℝ)^27 := by
    have hnat : (1020067197 : ℕ)^35*50000000000000^27 ≤ 2593338252363^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020067197 10000000000 2593338252363 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1284545171/2500000000 : ℝ), (3047419917/5000000000 : ℝ), (-1020067197/10000000000 : ℝ)] ![(21090810254611/50000000000000 : ℝ), (13157925742391/25000000000000 : ℝ), (2593338252363/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1284545171/2500000000 : ℝ)|^35 ≤ (21090810254611/50000000000000 : ℝ)^27
        have hw : |(1284545171/2500000000 : ℝ)|=(1284545171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3047419917/5000000000 : ℝ)|^35 ≤ (13157925742391/25000000000000 : ℝ)^27
        have hw : |(3047419917/5000000000 : ℝ)|=(3047419917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1020067197/10000000000 : ℝ)|^35 ≤ (2593338252363/50000000000000 : ℝ)^27
        have hw : |(-1020067197/10000000000 : ℝ)|=(1020067197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309062_s3_s3_14 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-681210817/5000000000 : ℝ)*x 0 + (4746837841/10000000000 : ℝ)*x 1 + (-6251100041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (681210817/5000000000 : ℝ)^35 ≤ (7547641159613/100000000000000 : ℝ)^27 := by
    have hnat : (681210817 : ℕ)^35*100000000000000^27 ≤ 7547641159613^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681210817 5000000000 7547641159613 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4746837841/10000000000 : ℝ)^35 ≤ (3806485824621/10000000000000 : ℝ)^27 := by
    have hnat : (4746837841 : ℕ)^35*10000000000000^27 ≤ 3806485824621^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4746837841 10000000000 3806485824621 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6251100041/10000000000 : ℝ)^35 ≤ (27193750290427/50000000000000 : ℝ)^27 := by
    have hnat : (6251100041 : ℕ)^35*50000000000000^27 ≤ 27193750290427^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6251100041 10000000000 27193750290427 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-681210817/5000000000 : ℝ), (4746837841/10000000000 : ℝ), (-6251100041/10000000000 : ℝ)] ![(7547641159613/100000000000000 : ℝ), (3806485824621/10000000000000 : ℝ), (27193750290427/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-681210817/5000000000 : ℝ)|^35 ≤ (7547641159613/100000000000000 : ℝ)^27
        have hw : |(-681210817/5000000000 : ℝ)|=(681210817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4746837841/10000000000 : ℝ)|^35 ≤ (3806485824621/10000000000000 : ℝ)^27
        have hw : |(4746837841/10000000000 : ℝ)|=(4746837841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6251100041/10000000000 : ℝ)|^35 ≤ (27193750290427/50000000000000 : ℝ)^27
        have hw : |(-6251100041/10000000000 : ℝ)|=(6251100041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309062_s3_s3_15 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1125920687/2500000000 : ℝ)*x 0 + (-924376623/5000000000 : ℝ)*x 1 + (-307419687/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1125920687/2500000000 : ℝ)^35 ≤ (35556680494313/100000000000000 : ℝ)^27 := by
    have hnat : (1125920687 : ℕ)^35*100000000000000^27 ≤ 35556680494313^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125920687 2500000000 35556680494313 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (924376623/5000000000 : ℝ)^35 ≤ (11211349659119/100000000000000 : ℝ)^27 := by
    have hnat : (924376623 : ℕ)^35*100000000000000^27 ≤ 11211349659119^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      924376623 5000000000 11211349659119 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (307419687/500000000 : ℝ)^35 ≤ (26615984916647/50000000000000 : ℝ)^27 := by
    have hnat : (307419687 : ℕ)^35*50000000000000^27 ≤ 26615984916647^27*500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      307419687 500000000 26615984916647 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1125920687/2500000000 : ℝ), (-924376623/5000000000 : ℝ), (-307419687/500000000 : ℝ)] ![(35556680494313/100000000000000 : ℝ), (11211349659119/100000000000000 : ℝ), (26615984916647/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1125920687/2500000000 : ℝ)|^35 ≤ (35556680494313/100000000000000 : ℝ)^27
        have hw : |(1125920687/2500000000 : ℝ)|=(1125920687/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-924376623/5000000000 : ℝ)|^35 ≤ (11211349659119/100000000000000 : ℝ)^27
        have hw : |(-924376623/5000000000 : ℝ)|=(924376623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-307419687/500000000 : ℝ)|^35 ≤ (26615984916647/50000000000000 : ℝ)^27
        have hw : |(-307419687/500000000 : ℝ)|=(307419687/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309062_s3_s3_16 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5826722451/10000000000 : ℝ)*x 0 + (4953416813/10000000000 : ℝ)*x 1 + (427206059/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5826722451/10000000000 : ℝ)^35 ≤ (12412533635877/25000000000000 : ℝ)^27 := by
    have hnat : (5826722451 : ℕ)^35*25000000000000^27 ≤ 12412533635877^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5826722451 10000000000 12412533635877 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4953416813/10000000000 : ℝ)^35 ≤ (40225950794673/100000000000000 : ℝ)^27 := by
    have hnat : (4953416813 : ℕ)^35*100000000000000^27 ≤ 40225950794673^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4953416813 10000000000 40225950794673 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (427206059/2500000000 : ℝ)^35 ≤ (2024782928773/20000000000000 : ℝ)^27 := by
    have hnat : (427206059 : ℕ)^35*20000000000000^27 ≤ 2024782928773^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427206059 2500000000 2024782928773 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5826722451/10000000000 : ℝ), (4953416813/10000000000 : ℝ), (427206059/2500000000 : ℝ)] ![(12412533635877/25000000000000 : ℝ), (40225950794673/100000000000000 : ℝ), (2024782928773/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5826722451/10000000000 : ℝ)|^35 ≤ (12412533635877/25000000000000 : ℝ)^27
        have hw : |(5826722451/10000000000 : ℝ)|=(5826722451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4953416813/10000000000 : ℝ)|^35 ≤ (40225950794673/100000000000000 : ℝ)^27
        have hw : |(4953416813/10000000000 : ℝ)|=(4953416813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(427206059/2500000000 : ℝ)|^35 ≤ (2024782928773/20000000000000 : ℝ)^27
        have hw : |(427206059/2500000000 : ℝ)|=(427206059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309062_s3_s3_20 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6301274791/10000000000 : ℝ)*x 0 + (4916346883/10000000000 : ℝ)*x 1 + (-1023572061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6301274791/10000000000 : ℝ)^35 ≤ (10990812479477/20000000000000 : ℝ)^27 := by
    have hnat : (6301274791 : ℕ)^35*20000000000000^27 ≤ 10990812479477^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6301274791 10000000000 10990812479477 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4916346883/10000000000 : ℝ)^35 ≤ (19918074033867/50000000000000 : ℝ)^27 := by
    have hnat : (4916346883 : ℕ)^35*50000000000000^27 ≤ 19918074033867^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4916346883 10000000000 19918074033867 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1023572061/10000000000 : ℝ)^35 ≤ (5209789523021/100000000000000 : ℝ)^27 := by
    have hnat : (1023572061 : ℕ)^35*100000000000000^27 ≤ 5209789523021^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023572061 10000000000 5209789523021 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6301274791/10000000000 : ℝ), (4916346883/10000000000 : ℝ), (-1023572061/10000000000 : ℝ)] ![(10990812479477/20000000000000 : ℝ), (19918074033867/50000000000000 : ℝ), (5209789523021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6301274791/10000000000 : ℝ)|^35 ≤ (10990812479477/20000000000000 : ℝ)^27
        have hw : |(6301274791/10000000000 : ℝ)|=(6301274791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4916346883/10000000000 : ℝ)|^35 ≤ (19918074033867/50000000000000 : ℝ)^27
        have hw : |(4916346883/10000000000 : ℝ)|=(4916346883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1023572061/10000000000 : ℝ)|^35 ≤ (5209789523021/100000000000000 : ℝ)^27
        have hw : |(-1023572061/10000000000 : ℝ)|=(1023572061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309062_s3_s3_21 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-113531763/1000000000 : ℝ)*x 0 + (2628393259/5000000000 : ℝ)*x 1 + (-5911914661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (113531763/1000000000 : ℝ)^35 ≤ (2979354397527/50000000000000 : ℝ)^27 := by
    have hnat : (113531763 : ℕ)^35*50000000000000^27 ≤ 2979354397527^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113531763 1000000000 2979354397527 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2628393259/5000000000 : ℝ)^35 ≤ (21724051111251/50000000000000 : ℝ)^27 := by
    have hnat : (2628393259 : ℕ)^35*50000000000000^27 ≤ 21724051111251^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628393259 5000000000 21724051111251 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5911914661/10000000000 : ℝ)^35 ≤ (1581037155247/3125000000000 : ℝ)^27 := by
    have hnat : (5911914661 : ℕ)^35*3125000000000^27 ≤ 1581037155247^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5911914661 10000000000 1581037155247 3125000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-113531763/1000000000 : ℝ), (2628393259/5000000000 : ℝ), (-5911914661/10000000000 : ℝ)] ![(2979354397527/50000000000000 : ℝ), (21724051111251/50000000000000 : ℝ), (1581037155247/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-113531763/1000000000 : ℝ)|^35 ≤ (2979354397527/50000000000000 : ℝ)^27
        have hw : |(-113531763/1000000000 : ℝ)|=(113531763/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2628393259/5000000000 : ℝ)|^35 ≤ (21724051111251/50000000000000 : ℝ)^27
        have hw : |(2628393259/5000000000 : ℝ)|=(2628393259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5911914661/10000000000 : ℝ)|^35 ≤ (1581037155247/3125000000000 : ℝ)^27
        have hw : |(-5911914661/10000000000 : ℝ)|=(5911914661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309062_s3_s3_22 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1168567069/2000000000 : ℝ)*x 0 + (-1727639413/10000000000 : ℝ)*x 1 + (-4922725841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1168567069/2000000000 : ℝ)^35 ≤ (49828188528857/100000000000000 : ℝ)^27 := by
    have hnat : (1168567069 : ℕ)^35*100000000000000^27 ≤ 49828188528857^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1168567069 2000000000 49828188528857 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1727639413/10000000000 : ℝ)^35 ≤ (10268648353681/100000000000000 : ℝ)^27 := by
    have hnat : (1727639413 : ℕ)^35*100000000000000^27 ≤ 10268648353681^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1727639413 10000000000 10268648353681 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4922725841/10000000000 : ℝ)^35 ≤ (19951581554597/50000000000000 : ℝ)^27 := by
    have hnat : (4922725841 : ℕ)^35*50000000000000^27 ≤ 19951581554597^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4922725841 10000000000 19951581554597 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1168567069/2000000000 : ℝ), (-1727639413/10000000000 : ℝ), (-4922725841/10000000000 : ℝ)] ![(49828188528857/100000000000000 : ℝ), (10268648353681/100000000000000 : ℝ), (19951581554597/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1168567069/2000000000 : ℝ)|^35 ≤ (49828188528857/100000000000000 : ℝ)^27
        have hw : |(1168567069/2000000000 : ℝ)|=(1168567069/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1727639413/10000000000 : ℝ)|^35 ≤ (10268648353681/100000000000000 : ℝ)^27
        have hw : |(-1727639413/10000000000 : ℝ)|=(1727639413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4922725841/10000000000 : ℝ)|^35 ≤ (19951581554597/50000000000000 : ℝ)^27
        have hw : |(-4922725841/10000000000 : ℝ)|=(4922725841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309062_s3_s3_23 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (931961313/2000000000 : ℝ)*x 0 + (2731683453/5000000000 : ℝ)*x 1 + (2567714421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (931961313/2000000000 : ℝ)^35 ≤ (3716263694931/10000000000000 : ℝ)^27 := by
    have hnat : (931961313 : ℕ)^35*10000000000000^27 ≤ 3716263694931^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      931961313 2000000000 3716263694931 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2731683453/5000000000 : ℝ)^35 ≤ (9134837847157/20000000000000 : ℝ)^27 := by
    have hnat : (2731683453 : ℕ)^35*20000000000000^27 ≤ 9134837847157^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731683453 5000000000 9134837847157 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2567714421/10000000000 : ℝ)^35 ≤ (858158689941/5000000000000 : ℝ)^27 := by
    have hnat : (2567714421 : ℕ)^35*5000000000000^27 ≤ 858158689941^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2567714421 10000000000 858158689941 5000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(931961313/2000000000 : ℝ), (2731683453/5000000000 : ℝ), (2567714421/10000000000 : ℝ)] ![(3716263694931/10000000000000 : ℝ), (9134837847157/20000000000000 : ℝ), (858158689941/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(931961313/2000000000 : ℝ)|^35 ≤ (3716263694931/10000000000000 : ℝ)^27
        have hw : |(931961313/2000000000 : ℝ)|=(931961313/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2731683453/5000000000 : ℝ)|^35 ≤ (9134837847157/20000000000000 : ℝ)^27
        have hw : |(2731683453/5000000000 : ℝ)|=(2731683453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2567714421/10000000000 : ℝ)|^35 ≤ (858158689941/5000000000000 : ℝ)^27
        have hw : |(2567714421/10000000000 : ℝ)|=(2567714421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309062_s3_s3_27 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1284231293/2000000000 : ℝ)*x 0 + (581464839/1250000000 : ℝ)*x 1 + (-1229585547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1284231293/2000000000 : ℝ)^35 ≤ (28156571795921/50000000000000 : ℝ)^27 := by
    have hnat : (1284231293 : ℕ)^35*50000000000000^27 ≤ 28156571795921^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284231293 2000000000 28156571795921 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (581464839/1250000000 : ℝ)^35 ≤ (37079045004231/100000000000000 : ℝ)^27 := by
    have hnat : (581464839 : ℕ)^35*100000000000000^27 ≤ 37079045004231^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      581464839 1250000000 37079045004231 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1229585547/10000000000 : ℝ)^35 ≤ (6607811393737/100000000000000 : ℝ)^27 := by
    have hnat : (1229585547 : ℕ)^35*100000000000000^27 ≤ 6607811393737^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1229585547 10000000000 6607811393737 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1284231293/2000000000 : ℝ), (581464839/1250000000 : ℝ), (-1229585547/10000000000 : ℝ)] ![(28156571795921/50000000000000 : ℝ), (37079045004231/100000000000000 : ℝ), (6607811393737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1284231293/2000000000 : ℝ)|^35 ≤ (28156571795921/50000000000000 : ℝ)^27
        have hw : |(1284231293/2000000000 : ℝ)|=(1284231293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(581464839/1250000000 : ℝ)|^35 ≤ (37079045004231/100000000000000 : ℝ)^27
        have hw : |(581464839/1250000000 : ℝ)|=(581464839/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1229585547/10000000000 : ℝ)|^35 ≤ (6607811393737/100000000000000 : ℝ)^27
        have hw : |(-1229585547/10000000000 : ℝ)|=(1229585547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c309062_s3 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev2 : (0 : ℝ) ≤ ((60329/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(60329/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(60723/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(60723/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-42617/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-42617/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((17369/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17369/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17483/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(17483/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-1097/5000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-1097/5000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
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
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (60329/100000 : ℝ) ^ (69/16 : ℝ) ≤ (5655733345795724039/50000000000000000000 : ℝ) := by
    have hpowers : (60329/100000 : ℝ)^69 ≤ (5655733345795724039/50000000000000000000 : ℝ)^16 := by
      have hnat : (60329 : ℕ)^69*50000000000000000000^16 ≤ 5655733345795724039^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60329 100000 5655733345795724039 50000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (60329/100000 : ℝ)) (X := (5655733345795724039/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s3_corner0a : (55655733345795724039/50000000000000000000 : ℝ) ≤ (10251604949474569/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (55655733345795724039/50000000000000000000 : ℝ)^16 ≤ (10251604949474569/10000000000000000 : ℝ)^69 := by
      have hnat : (55655733345795724039 : ℕ)^16*10000000000000000^69 ≤ 10251604949474569^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55655733345795724039 50000000000000000000 10251604949474569 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10251604949474569/10000000000000000 : ℝ)) (X := (55655733345795724039/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s3_corner0b : (30655733345795724039/25000000000000000000 : ℝ) ≤ (1310534259150343/1250000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (30655733345795724039/25000000000000000000 : ℝ)^16 ≤ (1310534259150343/1250000000000000 : ℝ)^69 := by
      have hnat : (30655733345795724039 : ℕ)^16*1250000000000000^69 ≤ 1310534259150343^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30655733345795724039 25000000000000000000 1310534259150343 1250000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1310534259150343/1250000000000000 : ℝ)) (X := (30655733345795724039/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(251604949474569/6032900000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(9306764949127/241316000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (60329/100000 : ℝ)) (alpha := (251604949474569/6032900000000000 : ℝ)) (beta := (9306764949127/241316000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (60329/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(251604949474569/6032900000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(9306764949127/241316000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (60723/100000 : ℝ) ^ (69/16 : ℝ) ≤ (2908377446488236653/25000000000000000000 : ℝ) := by
    have hpowers : (60723/100000 : ℝ)^69 ≤ (2908377446488236653/25000000000000000000 : ℝ)^16 := by
      have hnat : (60723 : ℕ)^69*25000000000000000000^16 ≤ 2908377446488236653^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60723 100000 2908377446488236653 25000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (60723/100000 : ℝ)) (X := (2908377446488236653/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s3_corner1a : (27908377446488236653/25000000000000000000 : ℝ) ≤ (2051694983858941/2000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (27908377446488236653/25000000000000000000 : ℝ)^16 ≤ (2051694983858941/2000000000000000 : ℝ)^69 := by
      have hnat : (27908377446488236653 : ℕ)^16*2000000000000000^69 ≤ 2051694983858941^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27908377446488236653 25000000000000000000 2051694983858941 2000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2051694983858941/2000000000000000 : ℝ)) (X := (27908377446488236653/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s3_corner1b : (15408377446488236653/12500000000000000000 : ℝ) ≤ (10497018117325267/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (15408377446488236653/12500000000000000000 : ℝ)^16 ≤ (10497018117325267/10000000000000000 : ℝ)^69 := by
      have hnat : (15408377446488236653 : ℕ)^16*10000000000000000^69 ≤ 10497018117325267^69*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15408377446488236653 12500000000000000000 10497018117325267 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10497018117325267/10000000000000000 : ℝ)) (X := (15408377446488236653/12500000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(51694983858941/1214460000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(119271599015281/3036150000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (60723/100000 : ℝ)) (alpha := (51694983858941/1214460000000000 : ℝ)) (beta := (119271599015281/3036150000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (60723/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(51694983858941/1214460000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(119271599015281/3036150000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (42617/100000 : ℝ) ^ (69/16 : ℝ) ≤ (1263415354869737441/50000000000000000000 : ℝ) := by
    have hpowers : (42617/100000 : ℝ)^69 ≤ (1263415354869737441/50000000000000000000 : ℝ)^16 := by
      have hnat : (42617 : ℕ)^69*50000000000000000000^16 ≤ 1263415354869737441^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        42617 100000 1263415354869737441 50000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (42617/100000 : ℝ)) (X := (1263415354869737441/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s3_corner2a : (51263415354869737441/50000000000000000000 : ℝ) ≤ (5029016440745261/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (51263415354869737441/50000000000000000000 : ℝ)^16 ≤ (5029016440745261/5000000000000000 : ℝ)^69 := by
      have hnat : (51263415354869737441 : ℕ)^16*5000000000000000^69 ≤ 5029016440745261^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51263415354869737441 50000000000000000000 5029016440745261 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5029016440745261/5000000000000000 : ℝ)) (X := (51263415354869737441/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s3_corner2b : (26263415354869737441/25000000000000000000 : ℝ) ≤ (10114977345355819/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (26263415354869737441/25000000000000000000 : ℝ)^16 ≤ (10114977345355819/10000000000000000 : ℝ)^69 := by
      have hnat : (26263415354869737441 : ℕ)^16*10000000000000000^69 ≤ 10114977345355819^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26263415354869737441 25000000000000000000 10114977345355819 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10114977345355819/10000000000000000 : ℝ)) (X := (26263415354869737441/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(29016440745261/2130850000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(56944463865297/4261700000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (42617/100000 : ℝ)) (alpha := (29016440745261/2130850000000000 : ℝ)) (beta := (56944463865297/4261700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (42617/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(29016440745261/2130850000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(56944463865297/4261700000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-2074698391/10000000000 : ℝ)*X 0 0+(2438166241/5000000000 : ℝ)*X 0 1+(-2818507363/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309062_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_1 : ((4874417273/10000000000 : ℝ)*X 1 0+(-1039515197/5000000000 : ℝ)*X 1 1+(-5635626687/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309062_s3_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((101690609/200000000 : ℝ)*X 2 0+(635256477/1250000000 : ℝ)*X 2 1+(2526064623/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309062_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-438626703/2500000000 : ℝ)*X 0 0+(551082781/1250000000 : ℝ)*X 0 1+(-1259946001/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309062_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((4830887911/10000000000 : ℝ)*X 1 0+(-90319071/625000000 : ℝ)*X 1 1+(-1223981389/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309062_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((970847703/2000000000 : ℝ)*X 2 0+(370846303/625000000 : ℝ)*X 2 1+(845142289/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309062_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((1284545171/2500000000 : ℝ)*X 0 0+(3047419917/5000000000 : ℝ)*X 0 1+(-1020067197/10000000000 : ℝ)*X 0 2+(1284545171/2500000000 : ℝ)*X 1 0+(3047419917/5000000000 : ℝ)*X 1 1+(-1020067197/10000000000 : ℝ)*X 1 2+(1284545171/2500000000 : ℝ)*X 2 0+(3047419917/5000000000 : ℝ)*X 2 1+(-1020067197/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309062_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-681210817/5000000000 : ℝ)*X 0 0+(4746837841/10000000000 : ℝ)*X 0 1+(-6251100041/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309062_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((1125920687/2500000000 : ℝ)*X 1 0+(-924376623/5000000000 : ℝ)*X 1 1+(-307419687/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309062_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((5826722451/10000000000 : ℝ)*X 2 0+(4953416813/10000000000 : ℝ)*X 2 1+(427206059/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309062_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((6301274791/10000000000 : ℝ)*X 0 0+(4916346883/10000000000 : ℝ)*X 0 1+(-1023572061/10000000000 : ℝ)*X 0 2+(6301274791/10000000000 : ℝ)*X 1 0+(4916346883/10000000000 : ℝ)*X 1 1+(-1023572061/10000000000 : ℝ)*X 1 2+(6301274791/10000000000 : ℝ)*X 2 0+(4916346883/10000000000 : ℝ)*X 2 1+(-1023572061/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309062_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-113531763/1000000000 : ℝ)*X 0 0+(2628393259/5000000000 : ℝ)*X 0 1+(-5911914661/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309062_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((1168567069/2000000000 : ℝ)*X 1 0+(-1727639413/10000000000 : ℝ)*X 1 1+(-4922725841/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309062_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((931961313/2000000000 : ℝ)*X 2 0+(2731683453/5000000000 : ℝ)*X 2 1+(2567714421/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309062_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((1284231293/2000000000 : ℝ)*X 0 0+(581464839/1250000000 : ℝ)*X 0 1+(-1229585547/10000000000 : ℝ)*X 0 2+(1284231293/2000000000 : ℝ)*X 1 0+(581464839/1250000000 : ℝ)*X 1 1+(-1229585547/10000000000 : ℝ)*X 1 2+(1284231293/2000000000 : ℝ)*X 2 0+(581464839/1250000000 : ℝ)*X 2 1+(-1229585547/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309062_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((17369/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17369/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1827887598049369817771673489/128552049650000000000000000000000 : ℝ) := by norm_num
    linear_combination (74388933397/200000000000 : ℝ)*(base39) + (208280908521/1000000000000 : ℝ)*(base49) + (165956578861/1000000000000 : ℝ)*(base60) + (6446207139083/1000000000000 : ℝ)*(major_s3_0) + (6446207139083/1000000000000 : ℝ)*(major_s3_1) + (6446207139083/1000000000000 : ℝ)*(major_s3_2) + (72853837/1000000000000 : ℝ)*(sp_s3_0) + (45507441/1000000000000 : ℝ)*(sp_s3_1) + (4422203325999/500000000000 : ℝ)*(sp_s3_7) + (8844281345073/1000000000000 : ℝ)*(sp_s3_8) + (1768864826913/200000000000 : ℝ)*(sp_s3_9) + (4047930032643/1000000000000 : ℝ)*(sp_s3_13) + (152653321/1000000000000 : ℝ)*(sp_s3_15) + (15537127/100000000000 : ℝ)*(sp_s3_23) + (4047930032643/1000000000000 : ℝ)*(f.failure) + (4422239752917/500000000000 : ℝ)*(f.sum) + (128443050288653467663/258783209100000000000000000000000 : ℝ)*base63 + (3181252251151349/4261700000000000000000000000 : ℝ)*base64 + (38881986878749/94879687500000000000000000 : ℝ)*base67 + (276226573931697/2130850000000000000000000000 : ℝ)*base68 + (17472948823877525391/128552049650000000000000000000000 : ℝ)*base70 + (650953200875959/1206580000000000000000000000 : ℝ)*base73 + (555153143632199/1214460000000000000000000000 : ℝ)*base74 + (2926292645596353/6032900000000000000000000000 : ℝ)*base76 + (130441224466497966121/366335786700000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (179/100000000000000000 : ℝ)*base86 + (179/100000000000000000 : ℝ)*base88 + (179/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17483/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(17483/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (699240258803325651060120687/128552049650000000000000000000000 : ℝ) := by norm_num
    linear_combination (351101557533/1000000000000 : ℝ)*(base39) + (25404359031/100000000000 : ℝ)*(base49) + (862233/1000000000000 : ℝ)*(base60) + (819253421329/125000000000 : ℝ)*(major_s3_0) + (819253421329/125000000000 : ℝ)*(major_s3_1) + (819253421329/125000000000 : ℝ)*(major_s3_2) + (3526619/500000000000 : ℝ)*(sp_s3_2) + (2437699/100000000000 : ℝ)*(sp_s3_7) + (11162621/500000000000 : ℝ)*(sp_s3_8) + (359695689243/40000000000 : ℝ)*(sp_s3_14) + (8992394282823/1000000000000 : ℝ)*(sp_s3_15) + (8992409554827/1000000000000 : ℝ)*(sp_s3_16) + (4115551371407/1000000000000 : ℝ)*(sp_s3_20) + (84948669/1000000000000 : ℝ)*(sp_s3_27) + (1028909080019/250000000000 : ℝ)*(f.failure) + (1798483321613/200000000000 : ℝ)*(f.sum) + (956817052135783951/32347901137500000000000000000000 : ℝ)*base62 + (232282867816503/532712500000000000000000000 : ℝ)*base65 + (281980732423483/3036150000000000000000000000 : ℝ)*base66 + (23436647216441/266356250000000000000000000 : ℝ)*base68 + (58324543898737339241/128552049650000000000000000000000 : ℝ)*base71 + (6425045193679/30164500000000000000000000 : ℝ)*base73 + (101527362276779/607230000000000000000000000 : ℝ)*base75 + (27477663150809/188528125000000000000000000 : ℝ)*base77 + (2630363902880831651/22895986668750000000000000000000 : ℝ)*base79 + (14307/25000000000000000 : ℝ)*base86 + (14307/25000000000000000 : ℝ)*base88 + (14307/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-1097/5000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-1097/5000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (8284712989823824770657986625029/867340678988550000000000000000000000 : ℝ) := by norm_num
    linear_combination (4002049/500000000000 : ℝ)*(base11) + (872282867563/1000000000000 : ℝ)*(base39) + (26733/250000000000 : ℝ)*(base40) + (39735884989/250000000000 : ℝ)*(base49) + (1307084379249/250000000000 : ℝ)*(major_s3_0) + (1307084379249/250000000000 : ℝ)*(major_s3_1) + (1307084379249/250000000000 : ℝ)*(major_s3_2) + (3330331/100000000000 : ℝ)*(sp_s3_0) + (14675951/1000000000000 : ℝ)*(sp_s3_2) + (48031661/1000000000000 : ℝ)*(sp_s3_9) + (1434693642357/200000000000 : ℝ)*(sp_s3_21) + (3586754759597/500000000000 : ℝ)*(sp_s3_22) + (3586723405791/500000000000 : ℝ)*(sp_s3_23) + (1641581165421/500000000000 : ℝ)*(sp_s3_27) + (1641581165421/500000000000 : ℝ)*(f.failure) + (3586754759597/500000000000 : ℝ)*(f.sum) + (153156687011725307/5391316856250000000000000000000 : ℝ)*base63 + (94330625958727/266356250000000000000000000 : ℝ)*base65 + (464561548654313/1012050000000000000000000000 : ℝ)*base66 + (37051728436759/133178125000000000000000000 : ℝ)*base68 + (20143146062254117399/64276024825000000000000000000000 : ℝ)*base71 + (30726795848129/301645000000000000000000000 : ℝ)*base72 + (51732310724519/202410000000000000000000000 : ℝ)*base74 + (220831274695969/1508225000000000000000000000 : ℝ)*base76 + (59151192671103461437/61055964450000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (2013/50000000000000000 : ℝ)*base86 + (2013/50000000000000000 : ℝ)*base88 + (2013/50000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev2 : (0 : ℝ) ≤ ((60329/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(60329/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(60723/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(60723/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-42617/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-42617/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((17369/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17369/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17483/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(17483/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-1097/5000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-1097/5000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c309062_s3 p hpa hpb X hX hprev2

#print axioms solution
