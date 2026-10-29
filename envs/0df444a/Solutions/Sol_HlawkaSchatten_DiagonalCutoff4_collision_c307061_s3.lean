-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c307061_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:15:04.520997+00:00
-- url     : https://prove2.me/submissions/c8054639-600f-4a29-903f-7365165acacf

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
theorem collision_support_c307061_s3_s3_0 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1692972503/10000000000 : ℝ)*x 0 + (4665890137/10000000000 : ℝ)*x 1 + (6180057803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1692972503/10000000000 : ℝ)^17 ≤ (9801925864757/100000000000000 : ℝ)^13 := by
    have hnat : (1692972503 : ℕ)^17*100000000000000^13 ≤ 9801925864757^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1692972503 10000000000 9801925864757 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4665890137/10000000000 : ℝ)^17 ≤ (7380710982243/20000000000000 : ℝ)^13 := by
    have hnat : (4665890137 : ℕ)^17*20000000000000^13 ≤ 7380710982243^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4665890137 10000000000 7380710982243 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6180057803/10000000000 : ℝ)^17 ≤ (10658903840157/20000000000000 : ℝ)^13 := by
    have hnat : (6180057803 : ℕ)^17*20000000000000^13 ≤ 10658903840157^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6180057803 10000000000 10658903840157 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1692972503/10000000000 : ℝ), (4665890137/10000000000 : ℝ), (6180057803/10000000000 : ℝ)] ![(9801925864757/100000000000000 : ℝ), (7380710982243/20000000000000 : ℝ), (10658903840157/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1692972503/10000000000 : ℝ)|^17 ≤ (9801925864757/100000000000000 : ℝ)^13
        have hw : |(-1692972503/10000000000 : ℝ)|=(1692972503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4665890137/10000000000 : ℝ)|^17 ≤ (7380710982243/20000000000000 : ℝ)^13
        have hw : |(4665890137/10000000000 : ℝ)|=(4665890137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6180057803/10000000000 : ℝ)|^17 ≤ (10658903840157/20000000000000 : ℝ)^13
        have hw : |(6180057803/10000000000 : ℝ)|=(6180057803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307061_s3_s3_1 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2394712049/5000000000 : ℝ)*x 0 + (-1726300329/10000000000 : ℝ)*x 1 + (6043388423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2394712049/5000000000 : ℝ)^17 ≤ (9546604546059/25000000000000 : ℝ)^13 := by
    have hnat : (2394712049 : ℕ)^17*25000000000000^13 ≤ 9546604546059^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2394712049 5000000000 9546604546059 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1726300329/10000000000 : ℝ)^17 ≤ (2513754911909/25000000000000 : ℝ)^13 := by
    have hnat : (1726300329 : ℕ)^17*25000000000000^13 ≤ 2513754911909^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1726300329 10000000000 2513754911909 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6043388423/10000000000 : ℝ)^17 ≤ (51758562149417/100000000000000 : ℝ)^13 := by
    have hnat : (6043388423 : ℕ)^17*100000000000000^13 ≤ 51758562149417^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6043388423 10000000000 51758562149417 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2394712049/5000000000 : ℝ), (-1726300329/10000000000 : ℝ), (6043388423/10000000000 : ℝ)] ![(9546604546059/25000000000000 : ℝ), (2513754911909/25000000000000 : ℝ), (51758562149417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2394712049/5000000000 : ℝ)|^17 ≤ (9546604546059/25000000000000 : ℝ)^13
        have hw : |(2394712049/5000000000 : ℝ)|=(2394712049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1726300329/10000000000 : ℝ)|^17 ≤ (2513754911909/25000000000000 : ℝ)^13
        have hw : |(-1726300329/10000000000 : ℝ)|=(1726300329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6043388423/10000000000 : ℝ)|^17 ≤ (51758562149417/100000000000000 : ℝ)^13
        have hw : |(6043388423/10000000000 : ℝ)|=(6043388423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307061_s3_s3_7 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1705474143/10000000000 : ℝ)*x 0 + (334119219/1000000000 : ℝ)*x 1 + (7299583647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1705474143/10000000000 : ℝ)^17 ≤ (4948343072557/50000000000000 : ℝ)^13 := by
    have hnat : (1705474143 : ℕ)^17*50000000000000^13 ≤ 4948343072557^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1705474143 10000000000 4948343072557 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (334119219/1000000000 : ℝ)^17 ≤ (2980709222927/12500000000000 : ℝ)^13 := by
    have hnat : (334119219 : ℕ)^17*12500000000000^13 ≤ 2980709222927^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334119219 1000000000 2980709222927 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7299583647/10000000000 : ℝ)^17 ≤ (66257640061689/100000000000000 : ℝ)^13 := by
    have hnat : (7299583647 : ℕ)^17*100000000000000^13 ≤ 66257640061689^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7299583647 10000000000 66257640061689 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1705474143/10000000000 : ℝ), (334119219/1000000000 : ℝ), (7299583647/10000000000 : ℝ)] ![(4948343072557/50000000000000 : ℝ), (2980709222927/12500000000000 : ℝ), (66257640061689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1705474143/10000000000 : ℝ)|^17 ≤ (4948343072557/50000000000000 : ℝ)^13
        have hw : |(-1705474143/10000000000 : ℝ)|=(1705474143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(334119219/1000000000 : ℝ)|^17 ≤ (2980709222927/12500000000000 : ℝ)^13
        have hw : |(334119219/1000000000 : ℝ)|=(334119219/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7299583647/10000000000 : ℝ)|^17 ≤ (66257640061689/100000000000000 : ℝ)^13
        have hw : |(7299583647/10000000000 : ℝ)|=(7299583647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307061_s3_s3_8 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (469236869/1250000000 : ℝ)*x 0 + (-1193888323/10000000000 : ℝ)*x 1 + (1819960683/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (469236869/1250000000 : ℝ)^17 ≤ (1110742850961/4000000000000 : ℝ)^13 := by
    have hnat : (469236869 : ℕ)^17*4000000000000^13 ≤ 1110742850961^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469236869 1250000000 1110742850961 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1193888323/10000000000 : ℝ)^17 ≤ (1552002960573/25000000000000 : ℝ)^13 := by
    have hnat : (1193888323 : ℕ)^17*25000000000000^13 ≤ 1552002960573^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1193888323 10000000000 1552002960573 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1819960683/2500000000 : ℝ)^17 ≤ (257903972183/390625000000 : ℝ)^13 := by
    have hnat : (1819960683 : ℕ)^17*390625000000^13 ≤ 257903972183^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1819960683 2500000000 257903972183 390625000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(469236869/1250000000 : ℝ), (-1193888323/10000000000 : ℝ), (1819960683/2500000000 : ℝ)] ![(1110742850961/4000000000000 : ℝ), (1552002960573/25000000000000 : ℝ), (257903972183/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(469236869/1250000000 : ℝ)|^17 ≤ (1110742850961/4000000000000 : ℝ)^13
        have hw : |(469236869/1250000000 : ℝ)|=(469236869/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1193888323/10000000000 : ℝ)|^17 ≤ (1552002960573/25000000000000 : ℝ)^13
        have hw : |(-1193888323/10000000000 : ℝ)|=(1193888323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1819960683/2500000000 : ℝ)|^17 ≤ (257903972183/390625000000 : ℝ)^13
        have hw : |(1819960683/2500000000 : ℝ)|=(1819960683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307061_s3_s3_9 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3850282453/10000000000 : ℝ)*x 0 + (1544060649/2000000000 : ℝ)*x 1 + (-392307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3850282453/10000000000 : ℝ)^17 ≤ (5740924616883/20000000000000 : ℝ)^13 := by
    have hnat : (3850282453 : ℕ)^17*20000000000000^13 ≤ 5740924616883^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3850282453 10000000000 5740924616883 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1544060649/2000000000 : ℝ)^17 ≤ (7129520399393/10000000000000 : ℝ)^13 := by
    have hnat : (1544060649 : ℕ)^17*10000000000000^13 ≤ 7129520399393^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1544060649 2000000000 7129520399393 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (392307/10000000000 : ℝ)^17 ≤ (34581887/20000000000000 : ℝ)^13 := by
    have hnat : (392307 : ℕ)^17*20000000000000^13 ≤ 34581887^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      392307 10000000000 34581887 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3850282453/10000000000 : ℝ), (1544060649/2000000000 : ℝ), (-392307/10000000000 : ℝ)] ![(5740924616883/20000000000000 : ℝ), (7129520399393/10000000000000 : ℝ), (34581887/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3850282453/10000000000 : ℝ)|^17 ≤ (5740924616883/20000000000000 : ℝ)^13
        have hw : |(3850282453/10000000000 : ℝ)|=(3850282453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1544060649/2000000000 : ℝ)|^17 ≤ (7129520399393/10000000000000 : ℝ)^13
        have hw : |(1544060649/2000000000 : ℝ)|=(1544060649/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-392307/10000000000 : ℝ)|^17 ≤ (34581887/20000000000000 : ℝ)^13
        have hw : |(-392307/10000000000 : ℝ)|=(392307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307061_s3_s3_13 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5011604903/10000000000 : ℝ)*x 0 + (1418754683/2500000000 : ℝ)*x 1 + (1952101933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5011604903/10000000000 : ℝ)^17 ≤ (40519306391509/100000000000000 : ℝ)^13 := by
    have hnat : (5011604903 : ℕ)^17*100000000000000^13 ≤ 40519306391509^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5011604903 10000000000 40519306391509 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1418754683/2500000000 : ℝ)^17 ≤ (47672170969701/100000000000000 : ℝ)^13 := by
    have hnat : (1418754683 : ℕ)^17*100000000000000^13 ≤ 47672170969701^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1418754683 2500000000 47672170969701 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1952101933/10000000000 : ℝ)^17 ≤ (11808522618773/100000000000000 : ℝ)^13 := by
    have hnat : (1952101933 : ℕ)^17*100000000000000^13 ≤ 11808522618773^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1952101933 10000000000 11808522618773 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5011604903/10000000000 : ℝ), (1418754683/2500000000 : ℝ), (1952101933/10000000000 : ℝ)] ![(40519306391509/100000000000000 : ℝ), (47672170969701/100000000000000 : ℝ), (11808522618773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5011604903/10000000000 : ℝ)|^17 ≤ (40519306391509/100000000000000 : ℝ)^13
        have hw : |(5011604903/10000000000 : ℝ)|=(5011604903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1418754683/2500000000 : ℝ)|^17 ≤ (47672170969701/100000000000000 : ℝ)^13
        have hw : |(1418754683/2500000000 : ℝ)|=(1418754683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1952101933/10000000000 : ℝ)|^17 ≤ (11808522618773/100000000000000 : ℝ)^13
        have hw : |(1952101933/10000000000 : ℝ)|=(1952101933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307061_s3_s3_14 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-795710767/10000000000 : ℝ)*x 0 + (354981371/1000000000 : ℝ)*x 1 + (7657430763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (795710767/10000000000 : ℝ)^17 ≤ (1825980269317/50000000000000 : ℝ)^13 := by
    have hnat : (795710767 : ℕ)^17*50000000000000^13 ≤ 1825980269317^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      795710767 10000000000 1825980269317 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (354981371/1000000000 : ℝ)^17 ≤ (2581114519797/10000000000000 : ℝ)^13 := by
    have hnat : (354981371 : ℕ)^17*10000000000000^13 ≤ 2581114519797^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      354981371 1000000000 2581114519797 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7657430763/10000000000 : ℝ)^17 ≤ (70536894245163/100000000000000 : ℝ)^13 := by
    have hnat : (7657430763 : ℕ)^17*100000000000000^13 ≤ 70536894245163^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7657430763 10000000000 70536894245163 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-795710767/10000000000 : ℝ), (354981371/1000000000 : ℝ), (7657430763/10000000000 : ℝ)] ![(1825980269317/50000000000000 : ℝ), (2581114519797/10000000000000 : ℝ), (70536894245163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-795710767/10000000000 : ℝ)|^17 ≤ (1825980269317/50000000000000 : ℝ)^13
        have hw : |(-795710767/10000000000 : ℝ)|=(795710767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(354981371/1000000000 : ℝ)|^17 ≤ (2581114519797/10000000000000 : ℝ)^13
        have hw : |(354981371/1000000000 : ℝ)|=(354981371/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7657430763/10000000000 : ℝ)|^17 ≤ (70536894245163/100000000000000 : ℝ)^13
        have hw : |(7657430763/10000000000 : ℝ)|=(7657430763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307061_s3_s3_15 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (76329723/250000000 : ℝ)*x 0 + (-380192099/2500000000 : ℝ)*x 1 + (7636660509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (76329723/250000000 : ℝ)^17 ≤ (10597083394167/50000000000000 : ℝ)^13 := by
    have hnat : (76329723 : ℕ)^17*50000000000000^13 ≤ 10597083394167^13*250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76329723 250000000 10597083394167 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (380192099/2500000000 : ℝ)^17 ≤ (4259515314863/50000000000000 : ℝ)^13 := by
    have hnat : (380192099 : ℕ)^17*50000000000000^13 ≤ 4259515314863^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      380192099 2500000000 4259515314863 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7636660509/10000000000 : ℝ)^17 ≤ (35143401280739/50000000000000 : ℝ)^13 := by
    have hnat : (7636660509 : ℕ)^17*50000000000000^13 ≤ 35143401280739^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7636660509 10000000000 35143401280739 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(76329723/250000000 : ℝ), (-380192099/2500000000 : ℝ), (7636660509/10000000000 : ℝ)] ![(10597083394167/50000000000000 : ℝ), (4259515314863/50000000000000 : ℝ), (35143401280739/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(76329723/250000000 : ℝ)|^17 ≤ (10597083394167/50000000000000 : ℝ)^13
        have hw : |(76329723/250000000 : ℝ)|=(76329723/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-380192099/2500000000 : ℝ)|^17 ≤ (4259515314863/50000000000000 : ℝ)^13
        have hw : |(-380192099/2500000000 : ℝ)|=(380192099/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7636660509/10000000000 : ℝ)|^17 ≤ (35143401280739/50000000000000 : ℝ)^13
        have hw : |(7636660509/10000000000 : ℝ)|=(7636660509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307061_s3_s3_16 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1363495793/2000000000 : ℝ)*x 0 + (980498909/2000000000 : ℝ)*x 1 + (-5839767/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1363495793/2000000000 : ℝ)^17 ≤ (6059421056149/10000000000000 : ℝ)^13 := by
    have hnat : (1363495793 : ℕ)^17*10000000000000^13 ≤ 6059421056149^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1363495793 2000000000 6059421056149 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (980498909/2000000000 : ℝ)^17 ≤ (4921198251873/12500000000000 : ℝ)^13 := by
    have hnat : (980498909 : ℕ)^17*12500000000000^13 ≤ 4921198251873^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      980498909 2000000000 4921198251873 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5839767/2500000000 : ℝ)^17 ≤ (36203412971/100000000000000 : ℝ)^13 := by
    have hnat : (5839767 : ℕ)^17*100000000000000^13 ≤ 36203412971^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5839767 2500000000 36203412971 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1363495793/2000000000 : ℝ), (980498909/2000000000 : ℝ), (-5839767/2500000000 : ℝ)] ![(6059421056149/10000000000000 : ℝ), (4921198251873/12500000000000 : ℝ), (36203412971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1363495793/2000000000 : ℝ)|^17 ≤ (6059421056149/10000000000000 : ℝ)^13
        have hw : |(1363495793/2000000000 : ℝ)|=(1363495793/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(980498909/2000000000 : ℝ)|^17 ≤ (4921198251873/12500000000000 : ℝ)^13
        have hw : |(980498909/2000000000 : ℝ)|=(980498909/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5839767/2500000000 : ℝ)|^17 ≤ (36203412971/100000000000000 : ℝ)^13
        have hw : |(-5839767/2500000000 : ℝ)|=(5839767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307061_s3_s3_20 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (8033253801/10000000000 : ℝ)*x 0 + (458868903/2000000000 : ℝ)*x 1 + (880237661/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8033253801/10000000000 : ℝ)^17 ≤ (75097820099599/100000000000000 : ℝ)^13 := by
    have hnat : (8033253801 : ℕ)^17*100000000000000^13 ≤ 75097820099599^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8033253801 10000000000 75097820099599 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (458868903/2000000000 : ℝ)^17 ≤ (455814600227/3125000000000 : ℝ)^13 := by
    have hnat : (458868903 : ℕ)^17*3125000000000^13 ≤ 455814600227^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458868903 2000000000 455814600227 3125000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (880237661/5000000000 : ℝ)^17 ≤ (5158056343563/50000000000000 : ℝ)^13 := by
    have hnat : (880237661 : ℕ)^17*50000000000000^13 ≤ 5158056343563^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880237661 5000000000 5158056343563 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8033253801/10000000000 : ℝ), (458868903/2000000000 : ℝ), (880237661/5000000000 : ℝ)] ![(75097820099599/100000000000000 : ℝ), (455814600227/3125000000000 : ℝ), (5158056343563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8033253801/10000000000 : ℝ)|^17 ≤ (75097820099599/100000000000000 : ℝ)^13
        have hw : |(8033253801/10000000000 : ℝ)|=(8033253801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(458868903/2000000000 : ℝ)|^17 ≤ (455814600227/3125000000000 : ℝ)^13
        have hw : |(458868903/2000000000 : ℝ)|=(458868903/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(880237661/5000000000 : ℝ)|^17 ≤ (5158056343563/50000000000000 : ℝ)^13
        have hw : |(880237661/5000000000 : ℝ)|=(880237661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307061_s3_s3_21 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-450025117/10000000000 : ℝ)*x 0 + (3125432399/5000000000 : ℝ)*x 1 + (5353585821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (450025117/10000000000 : ℝ)^17 ≤ (866598766611/50000000000000 : ℝ)^13 := by
    have hnat : (450025117 : ℕ)^17*50000000000000^13 ≤ 866598766611^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450025117 10000000000 866598766611 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3125432399/5000000000 : ℝ)^17 ≤ (6761802142069/12500000000000 : ℝ)^13 := by
    have hnat : (3125432399 : ℕ)^17*12500000000000^13 ≤ 6761802142069^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3125432399 5000000000 6761802142069 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5353585821/10000000000 : ℝ)^17 ≤ (11043096328331/25000000000000 : ℝ)^13 := by
    have hnat : (5353585821 : ℕ)^17*25000000000000^13 ≤ 11043096328331^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353585821 10000000000 11043096328331 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-450025117/10000000000 : ℝ), (3125432399/5000000000 : ℝ), (5353585821/10000000000 : ℝ)] ![(866598766611/50000000000000 : ℝ), (6761802142069/12500000000000 : ℝ), (11043096328331/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-450025117/10000000000 : ℝ)|^17 ≤ (866598766611/50000000000000 : ℝ)^13
        have hw : |(-450025117/10000000000 : ℝ)|=(450025117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3125432399/5000000000 : ℝ)|^17 ≤ (6761802142069/12500000000000 : ℝ)^13
        have hw : |(3125432399/5000000000 : ℝ)|=(3125432399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5353585821/10000000000 : ℝ)|^17 ≤ (11043096328331/25000000000000 : ℝ)^13
        have hw : |(5353585821/10000000000 : ℝ)|=(5353585821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307061_s3_s3_22 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (335721509/500000000 : ℝ)*x 0 + (-460777423/10000000000 : ℝ)*x 1 + (484942103/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335721509/500000000 : ℝ)^17 ≤ (59399284281119/100000000000000 : ℝ)^13 := by
    have hnat : (335721509 : ℕ)^17*100000000000000^13 ≤ 59399284281119^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335721509 500000000 59399284281119 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (460777423/10000000000 : ℝ)^17 ≤ (446886999507/25000000000000 : ℝ)^13 := by
    have hnat : (460777423 : ℕ)^17*25000000000000^13 ≤ 446886999507^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      460777423 10000000000 446886999507 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (484942103/1000000000 : ℝ)^17 ≤ (19406583856873/50000000000000 : ℝ)^13 := by
    have hnat : (484942103 : ℕ)^17*50000000000000^13 ≤ 19406583856873^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      484942103 1000000000 19406583856873 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335721509/500000000 : ℝ), (-460777423/10000000000 : ℝ), (484942103/1000000000 : ℝ)] ![(59399284281119/100000000000000 : ℝ), (446886999507/25000000000000 : ℝ), (19406583856873/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335721509/500000000 : ℝ)|^17 ≤ (59399284281119/100000000000000 : ℝ)^13
        have hw : |(335721509/500000000 : ℝ)|=(335721509/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-460777423/10000000000 : ℝ)|^17 ≤ (446886999507/25000000000000 : ℝ)^13
        have hw : |(-460777423/10000000000 : ℝ)|=(460777423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(484942103/1000000000 : ℝ)|^17 ≤ (19406583856873/50000000000000 : ℝ)^13
        have hw : |(484942103/1000000000 : ℝ)|=(484942103/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307061_s3_s3_23 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3352231849/10000000000 : ℝ)*x 0 + (8025357763/10000000000 : ℝ)*x 1 + (-6134813/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3352231849/10000000000 : ℝ)^17 ≤ (23948757461737/100000000000000 : ℝ)^13 := by
    have hnat : (3352231849 : ℕ)^17*100000000000000^13 ≤ 23948757461737^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3352231849 10000000000 23948757461737 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8025357763/10000000000 : ℝ)^17 ≤ (37500653646161/50000000000000 : ℝ)^13 := by
    have hnat : (8025357763 : ℕ)^17*50000000000000^13 ≤ 37500653646161^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8025357763 10000000000 37500653646161 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6134813/200000000 : ℝ)^17 ≤ (104993524113/10000000000000 : ℝ)^13 := by
    have hnat : (6134813 : ℕ)^17*10000000000000^13 ≤ 104993524113^13*200000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6134813 200000000 104993524113 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3352231849/10000000000 : ℝ), (8025357763/10000000000 : ℝ), (-6134813/200000000 : ℝ)] ![(23948757461737/100000000000000 : ℝ), (37500653646161/50000000000000 : ℝ), (104993524113/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3352231849/10000000000 : ℝ)|^17 ≤ (23948757461737/100000000000000 : ℝ)^13
        have hw : |(3352231849/10000000000 : ℝ)|=(3352231849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8025357763/10000000000 : ℝ)|^17 ≤ (37500653646161/50000000000000 : ℝ)^13
        have hw : |(8025357763/10000000000 : ℝ)|=(8025357763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6134813/200000000 : ℝ)|^17 ≤ (104993524113/10000000000000 : ℝ)^13
        have hw : |(-6134813/200000000 : ℝ)|=(6134813/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307061_s3_s3_27 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (844202807/1000000000 : ℝ)*x 0 + (883508791/5000000000 : ℝ)*x 1 + (51654861/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (844202807/1000000000 : ℝ)^17 ≤ (20033417605691/25000000000000 : ℝ)^13 := by
    have hnat : (844202807 : ℕ)^17*25000000000000^13 ≤ 20033417605691^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844202807 1000000000 20033417605691 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (883508791/5000000000 : ℝ)^17 ≤ (1036627384083/10000000000000 : ℝ)^13 := by
    have hnat : (883508791 : ℕ)^17*10000000000000^13 ≤ 1036627384083^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      883508791 5000000000 1036627384083 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51654861/312500000 : ℝ)^17 ≤ (4750027861101/50000000000000 : ℝ)^13 := by
    have hnat : (51654861 : ℕ)^17*50000000000000^13 ≤ 4750027861101^13*312500000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51654861 312500000 4750027861101 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(844202807/1000000000 : ℝ), (883508791/5000000000 : ℝ), (51654861/312500000 : ℝ)] ![(20033417605691/25000000000000 : ℝ), (1036627384083/10000000000000 : ℝ), (4750027861101/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(844202807/1000000000 : ℝ)|^17 ≤ (20033417605691/25000000000000 : ℝ)^13
        have hw : |(844202807/1000000000 : ℝ)|=(844202807/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(883508791/5000000000 : ℝ)|^17 ≤ (1036627384083/10000000000000 : ℝ)^13
        have hw : |(883508791/5000000000 : ℝ)|=(883508791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(51654861/312500000 : ℝ)|^17 ≤ (4750027861101/50000000000000 : ℝ)^13
        have hw : |(51654861/312500000 : ℝ)|=(51654861/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c307061_s3 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((38637/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(38637/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39229/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(39229/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(299/400 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(299/400 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3187/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3187/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1351/2000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1351/2000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1243/2000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1243/2000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4817/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4817/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4817/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4817/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4817/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4817/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (92559/50000 : ℝ) := by
    linarith only [f.Tcap]
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
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (38637/50000 : ℝ) ^ (135/32 : ℝ) ≤ (33700851895658995779/100000000000000000000 : ℝ) := by
    have hpowers : (38637/50000 : ℝ)^135 ≤ (33700851895658995779/100000000000000000000 : ℝ)^32 := by
      have hnat : (38637 : ℕ)^135*100000000000000000000^32 ≤ 33700851895658995779^32*50000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        38637 50000 33700851895658995779 100000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (38637/50000 : ℝ)) (X := (33700851895658995779/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s3_corner0a : (133700851895658995779/100000000000000000000 : ℝ) ≤ (10712688355806167/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (133700851895658995779/100000000000000000000 : ℝ)^32 ≤ (10712688355806167/10000000000000000 : ℝ)^135 := by
      have hnat : (133700851895658995779 : ℕ)^32*10000000000000000^135 ≤ 10712688355806167^135*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        133700851895658995779 100000000000000000000 10712688355806167 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10712688355806167/10000000000000000 : ℝ)) (X := (133700851895658995779/100000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s3_corner0b : (83700851895658995779/50000000000000000000 : ℝ) ≤ (11298983579878921/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (83700851895658995779/50000000000000000000 : ℝ)^32 ≤ (11298983579878921/10000000000000000 : ℝ)^135 := by
      have hnat : (83700851895658995779 : ℕ)^32*10000000000000000^135 ≤ 11298983579878921^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        83700851895658995779 50000000000000000000 11298983579878921 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11298983579878921/10000000000000000 : ℝ)) (X := (83700851895658995779/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(712688355806167/7727400000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(293147612036377/3863700000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (38637/50000 : ℝ)) (alpha := (712688355806167/7727400000000000 : ℝ)) (beta := (293147612036377/3863700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (38637/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(712688355806167/7727400000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(293147612036377/3863700000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (39229/50000 : ℝ) ^ (135/32 : ℝ) ≤ (7186721628503073719/20000000000000000000 : ℝ) := by
    have hpowers : (39229/50000 : ℝ)^135 ≤ (7186721628503073719/20000000000000000000 : ℝ)^32 := by
      have hnat : (39229 : ℕ)^135*20000000000000000000^32 ≤ 7186721628503073719^32*50000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39229 50000 7186721628503073719 20000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (39229/50000 : ℝ)) (X := (7186721628503073719/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s3_corner1a : (27186721628503073719/20000000000000000000 : ℝ) ≤ (5377413146155999/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (27186721628503073719/20000000000000000000 : ℝ)^32 ≤ (5377413146155999/5000000000000000 : ℝ)^135 := by
      have hnat : (27186721628503073719 : ℕ)^32*5000000000000000^135 ≤ 5377413146155999^135*20000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27186721628503073719 20000000000000000000 5377413146155999 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5377413146155999/5000000000000000 : ℝ)) (X := (27186721628503073719/20000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s3_corner1b : (17186721628503073719/10000000000000000000 : ℝ) ≤ (56848559744589/50000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (17186721628503073719/10000000000000000000 : ℝ)^32 ≤ (56848559744589/50000000000000 : ℝ)^135 := by
      have hnat : (17186721628503073719 : ℕ)^32*50000000000000^135 ≤ 56848559744589^135*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17186721628503073719 10000000000000000000 56848559744589 50000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (56848559744589/50000000000000 : ℝ)) (X := (17186721628503073719/10000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(377413146155999/3922900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(307442828302901/3922900000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (39229/50000 : ℝ)) (alpha := (377413146155999/3922900000000000 : ℝ)) (beta := (307442828302901/3922900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (39229/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(377413146155999/3922900000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(307442828302901/3922900000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (299/400 : ℝ) ^ (135/32 : ℝ) ≤ (29295251941642669473/100000000000000000000 : ℝ) := by
    have hpowers : (299/400 : ℝ)^135 ≤ (29295251941642669473/100000000000000000000 : ℝ)^32 := by
      have hnat : (299 : ℕ)^135*100000000000000000000^32 ≤ 29295251941642669473^32*400^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        299 400 29295251941642669473 100000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (299/400 : ℝ)) (X := (29295251941642669473/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s3_corner2a : (129295251941642669473/100000000000000000000 : ℝ) ≤ (265698566954927/250000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (129295251941642669473/100000000000000000000 : ℝ)^32 ≤ (265698566954927/250000000000000 : ℝ)^135 := by
      have hnat : (129295251941642669473 : ℕ)^32*250000000000000^135 ≤ 265698566954927^135*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        129295251941642669473 100000000000000000000 265698566954927 250000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (265698566954927/250000000000000 : ℝ)) (X := (129295251941642669473/100000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s3_corner2b : (79295251941642669473/50000000000000000000 : ℝ) ≤ (11155090784468679/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (79295251941642669473/50000000000000000000 : ℝ)^32 ≤ (11155090784468679/10000000000000000 : ℝ)^135 := by
      have hnat : (79295251941642669473 : ℕ)^32*10000000000000000^135 ≤ 11155090784468679^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        79295251941642669473 50000000000000000000 11155090784468679 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11155090784468679/10000000000000000 : ℝ)) (X := (79295251941642669473/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(15698566954927/186875000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(527148106271599/7475000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (299/400 : ℝ)) (alpha := (15698566954927/186875000000000 : ℝ)) (beta := (527148106271599/7475000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (299/400 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(15698566954927/186875000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(527148106271599/7475000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-1692972503/10000000000 : ℝ)*X 0 0+(4665890137/10000000000 : ℝ)*X 0 1+(6180057803/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307061_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_1 : ((2394712049/5000000000 : ℝ)*X 1 0+(-1726300329/10000000000 : ℝ)*X 1 1+(6043388423/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307061_s3_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-1705474143/10000000000 : ℝ)*X 0 0+(334119219/1000000000 : ℝ)*X 0 1+(7299583647/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307061_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((469236869/1250000000 : ℝ)*X 1 0+(-1193888323/10000000000 : ℝ)*X 1 1+(1819960683/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307061_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((3850282453/10000000000 : ℝ)*X 2 0+(1544060649/2000000000 : ℝ)*X 2 1+(-392307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307061_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((5011604903/10000000000 : ℝ)*X 0 0+(1418754683/2500000000 : ℝ)*X 0 1+(1952101933/10000000000 : ℝ)*X 0 2+(5011604903/10000000000 : ℝ)*X 1 0+(1418754683/2500000000 : ℝ)*X 1 1+(1952101933/10000000000 : ℝ)*X 1 2+(5011604903/10000000000 : ℝ)*X 2 0+(1418754683/2500000000 : ℝ)*X 2 1+(1952101933/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307061_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-795710767/10000000000 : ℝ)*X 0 0+(354981371/1000000000 : ℝ)*X 0 1+(7657430763/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307061_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((76329723/250000000 : ℝ)*X 1 0+(-380192099/2500000000 : ℝ)*X 1 1+(7636660509/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307061_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((1363495793/2000000000 : ℝ)*X 2 0+(980498909/2000000000 : ℝ)*X 2 1+(-5839767/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307061_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((8033253801/10000000000 : ℝ)*X 0 0+(458868903/2000000000 : ℝ)*X 0 1+(880237661/5000000000 : ℝ)*X 0 2+(8033253801/10000000000 : ℝ)*X 1 0+(458868903/2000000000 : ℝ)*X 1 1+(880237661/5000000000 : ℝ)*X 1 2+(8033253801/10000000000 : ℝ)*X 2 0+(458868903/2000000000 : ℝ)*X 2 1+(880237661/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307061_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-450025117/10000000000 : ℝ)*X 0 0+(3125432399/5000000000 : ℝ)*X 0 1+(5353585821/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307061_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((335721509/500000000 : ℝ)*X 1 0+(-460777423/10000000000 : ℝ)*X 1 1+(484942103/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307061_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((3352231849/10000000000 : ℝ)*X 2 0+(8025357763/10000000000 : ℝ)*X 2 1+(-6134813/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307061_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((844202807/1000000000 : ℝ)*X 0 0+(883508791/5000000000 : ℝ)*X 0 1+(51654861/312500000 : ℝ)*X 0 2+(844202807/1000000000 : ℝ)*X 1 0+(883508791/5000000000 : ℝ)*X 1 1+(51654861/312500000 : ℝ)*X 1 2+(844202807/1000000000 : ℝ)*X 2 0+(883508791/5000000000 : ℝ)*X 2 1+(51654861/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307061_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((3187/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3187/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (40730761253875026065643/3737500000000000000000000000 : ℝ) := by norm_num
    linear_combination (110210575879/250000000000 : ℝ)*(base7) + (107521/250000000000 : ℝ)*(base40) + (930757/1000000000000 : ℝ)*(base50) + (86848235163/500000000000 : ℝ)*(base59) + (2997070358099/1000000000000 : ℝ)*(major_s3_0) + (2997070358099/1000000000000 : ℝ)*(major_s3_1) + (2997070358099/1000000000000 : ℝ)*(major_s3_2) + (1046987/62500000000 : ℝ)*(sp_s3_0) + (118563214621/31250000000 : ℝ)*(sp_s3_7) + (3794077750199/1000000000000 : ℝ)*(sp_s3_8) + (3794089755491/1000000000000 : ℝ)*(sp_s3_9) + (2368863479793/1000000000000 : ℝ)*(sp_s3_13) + (50135827/1000000000000 : ℝ)*(sp_s3_14) + (3001323/250000000000 : ℝ)*(sp_s3_15) + (1928021176277/1000000000000 : ℝ)*(f.failure) + (3794089755491/1000000000000 : ℝ)*(f.sum) + (4019455848573364543/29323677500000000000000000000000 : ℝ)*base63 + (2372536608744699/7475000000000000000000000000 : ℝ)*base65 + (684446282543501/3922900000000000000000000000 : ℝ)*base66 + (10955456690921/373750000000000000000000000 : ℝ)*base69 + (68511273338858139319/144405787500000000000000000000000 : ℝ)*base71 + (586373238273727/3863700000000000000000000000 : ℝ)*base72 + (105504555803679/3922900000000000000000000000 : ℝ)*base74 + (488616012186007/7727400000000000000000000000 : ℝ)*base76 + (1877699192547605537/15156908730000000000000000000000 : ℝ)*base79 + (887/12500000000000000 : ℝ)*base87 + (887/12500000000000000 : ℝ)*base89 + (887/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1351/2000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1351/2000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1230853948778240354608403924377/377659642522500000000000000000000000 : ℝ) := by norm_num
    linear_combination (35285640073/62500000000 : ℝ)*(base7) + (745053/1000000000000 : ℝ)*(base40) + (310709/1000000000000 : ℝ)*(base49) + (561453/250000000000 : ℝ)*(base53) + (4823/31250000000 : ℝ)*(base59) + (2269094493223/1000000000000 : ℝ)*(major_s3_0) + (2269094493223/1000000000000 : ℝ)*(major_s3_1) + (2269092247411/1000000000000 : ℝ)*(major_s3_2) + (567739/1000000000000 : ℝ)*(sp_s3_7) + (16869797/500000000000 : ℝ)*(sp_s3_8) + (1365049241751/500000000000 : ℝ)*(sp_s3_14) + (2730065311647/1000000000000 : ℝ)*(sp_s3_15) + (2730101297053/1000000000000 : ℝ)*(sp_s3_16) + (126517695697/62500000000 : ℝ)*(sp_s3_20) + (11404006953/7812500000 : ℝ)*(f.failure) + (2730101297053/1000000000000 : ℝ)*(f.sum) + (2027645952883113577/29323677500000000000000000000000 : ℝ)*base63 + (12895447805189/7475000000000000000000000000 : ℝ)*base64 + (794697004904053/3922900000000000000000000000 : ℝ)*base67 + (76112366036497/186875000000000000000000000 : ℝ)*base69 + (12310707499477774991/144405787500000000000000000000000 : ℝ)*base71 + (686713611295321/3863700000000000000000000000 : ℝ)*base73 + (2324259283990647/3922900000000000000000000000 : ℝ)*base75 + (6820985460424141/7727400000000000000000000000 : ℝ)*base77 + (11663378321525888099/15156908730000000000000000000000 : ℝ)*base78 + (2099/3125000000000000 : ℝ)*base86 + (2099/3125000000000000 : ℝ)*base88 + (2099/3125000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1243/2000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1243/2000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (62759483472873162719010487231/4841790288750000000000000000000000 : ℝ) := by norm_num
    linear_combination (353579731327/1000000000000 : ℝ)*(base7) + (140027058347/1000000000000 : ℝ)*(base40) + (8078991/1000000000000 : ℝ)*(base43) + (686733/1000000000000 : ℝ)*(base49) + (572952583281/250000000000 : ℝ)*(major_s3_0) + (2291802254133/1000000000000 : ℝ)*(major_s3_1) + (572952583281/250000000000 : ℝ)*(major_s3_2) + (3473241/200000000000 : ℝ)*(sp_s3_0) + (2328537/125000000000 : ℝ)*(sp_s3_1) + (46688629/200000000000 : ℝ)*(sp_s3_9) + (2891084957491/1000000000000 : ℝ)*(sp_s3_21) + (2891091774391/1000000000000 : ℝ)*(sp_s3_22) + (2890868880551/1000000000000 : ℝ)*(sp_s3_23) + (1827905765193/1000000000000 : ℝ)*(sp_s3_27) + (737163016933/500000000000 : ℝ)*(f.failure) + (2891110402687/1000000000000 : ℝ)*(f.sum) + (403316150449330861/2255667500000000000000000000000 : ℝ)*base63 + (7840212799781/71875000000000000000000000 : ℝ)*base65 + (1287047754999853/3922900000000000000000000000 : ℝ)*base67 + (5000830313121/14375000000000000000000000 : ℝ)*base69 + (280853896942877627/1851356250000000000000000000000 : ℝ)*base70 + (11950362888983/40246875000000000000000000 : ℝ)*base73 + (1312736894257607/3922900000000000000000000000 : ℝ)*base75 + (58127357711029/643950000000000000000000000 : ℝ)*base77 + (11293668240696945361/50523029100000000000000000000000 : ℝ)*base79 + (123/6250000000000000 : ℝ)*base87 + (123/6250000000000000 : ℝ)*base89 + (123/6250000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((38637/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(38637/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39229/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(39229/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(299/400 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(299/400 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3187/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3187/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1351/2000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1351/2000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1243/2000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1243/2000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c307061_s3 p hpa hpb X hX hprev2

#print axioms solution
