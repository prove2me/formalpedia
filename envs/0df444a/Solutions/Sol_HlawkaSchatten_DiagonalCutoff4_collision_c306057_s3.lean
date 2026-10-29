-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c306057_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:56:22.856113+00:00
-- url     : https://prove2.me/submissions/24fe4ece-162f-4fb6-baa9-5577043532c0

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
theorem collision_support_c306057_s3_s3_0 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-3359502567/10000000000 : ℝ)*x 0 + (3359106649/10000000000 : ℝ)*x 1 + (1216624279/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3359502567/10000000000 : ℝ)^135 ≤ (23938573717963/100000000000000 : ℝ)^103 := by
    have hnat : (3359502567 : ℕ)^135*100000000000000^103 ≤ 23938573717963^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3359502567 10000000000 23938573717963 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3359106649/10000000000 : ℝ)^135 ≤ (11967438070877/50000000000000 : ℝ)^103 := by
    have hnat : (3359106649 : ℕ)^135*50000000000000^103 ≤ 11967438070877^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3359106649 10000000000 11967438070877 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1216624279/2000000000 : ℝ)^135 ≤ (10425310023159/20000000000000 : ℝ)^103 := by
    have hnat : (1216624279 : ℕ)^135*20000000000000^103 ≤ 10425310023159^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1216624279 2000000000 10425310023159 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3359502567/10000000000 : ℝ), (3359106649/10000000000 : ℝ), (1216624279/2000000000 : ℝ)] ![(23938573717963/100000000000000 : ℝ), (11967438070877/50000000000000 : ℝ), (10425310023159/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3359502567/10000000000 : ℝ)|^135 ≤ (23938573717963/100000000000000 : ℝ)^103
        have hw : |(-3359502567/10000000000 : ℝ)|=(3359502567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3359106649/10000000000 : ℝ)|^135 ≤ (11967438070877/50000000000000 : ℝ)^103
        have hw : |(3359106649/10000000000 : ℝ)|=(3359106649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1216624279/2000000000 : ℝ)|^135 ≤ (10425310023159/20000000000000 : ℝ)^103
        have hw : |(1216624279/2000000000 : ℝ)|=(1216624279/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306057_s3_s3_2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5746046853/10000000000 : ℝ)*x 0 + (5746617723/10000000000 : ℝ)*x 1 + (-11430033/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5746046853/10000000000 : ℝ)^135 ≤ (483737847587/1000000000000 : ℝ)^103 := by
    have hnat : (5746046853 : ℕ)^135*1000000000000^103 ≤ 483737847587^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5746046853 10000000000 483737847587 1000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5746617723/10000000000 : ℝ)^135 ≤ (6047510487539/12500000000000 : ℝ)^103 := by
    have hnat : (5746617723 : ℕ)^135*12500000000000^103 ≤ 6047510487539^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5746617723 10000000000 6047510487539 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11430033/156250000 : ℝ)^135 ≤ (25360401003/781250000000 : ℝ)^103 := by
    have hnat : (11430033 : ℕ)^135*781250000000^103 ≤ 25360401003^103*156250000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11430033 156250000 25360401003 781250000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5746046853/10000000000 : ℝ), (5746617723/10000000000 : ℝ), (-11430033/156250000 : ℝ)] ![(483737847587/1000000000000 : ℝ), (6047510487539/12500000000000 : ℝ), (25360401003/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5746046853/10000000000 : ℝ)|^135 ≤ (483737847587/1000000000000 : ℝ)^103
        have hw : |(5746046853/10000000000 : ℝ)|=(5746046853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5746617723/10000000000 : ℝ)|^135 ≤ (6047510487539/12500000000000 : ℝ)^103
        have hw : |(5746617723/10000000000 : ℝ)|=(5746617723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-11430033/156250000 : ℝ)|^135 ≤ (25360401003/781250000000 : ℝ)^103
        have hw : |(-11430033/156250000 : ℝ)|=(11430033/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306057_s3_s3_6 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1155477549/2500000000 : ℝ)*x 0 + (2311184691/5000000000 : ℝ)*x 1 + (371006379/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1155477549/2500000000 : ℝ)^135 ≤ (36365400719199/100000000000000 : ℝ)^103 := by
    have hnat : (1155477549 : ℕ)^135*100000000000000^103 ≤ 36365400719199^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1155477549 2500000000 36365400719199 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2311184691/5000000000 : ℝ)^135 ≤ (36370136141981/100000000000000 : ℝ)^103 := by
    have hnat : (2311184691 : ℕ)^135*100000000000000^103 ≤ 36370136141981^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2311184691 5000000000 36370136141981 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (371006379/1000000000 : ℝ)^135 ≤ (13632231561877/50000000000000 : ℝ)^103 := by
    have hnat : (371006379 : ℕ)^135*50000000000000^103 ≤ 13632231561877^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      371006379 1000000000 13632231561877 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1155477549/2500000000 : ℝ), (2311184691/5000000000 : ℝ), (371006379/1000000000 : ℝ)] ![(36365400719199/100000000000000 : ℝ), (36370136141981/100000000000000 : ℝ), (13632231561877/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1155477549/2500000000 : ℝ)|^135 ≤ (36365400719199/100000000000000 : ℝ)^103
        have hw : |(1155477549/2500000000 : ℝ)|=(1155477549/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2311184691/5000000000 : ℝ)|^135 ≤ (36370136141981/100000000000000 : ℝ)^103
        have hw : |(2311184691/5000000000 : ℝ)|=(2311184691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(371006379/1000000000 : ℝ)|^135 ≤ (13632231561877/50000000000000 : ℝ)^103
        have hw : |(371006379/1000000000 : ℝ)|=(371006379/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306057_s3_s3_7 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-3087367451/10000000000 : ℝ)*x 0 + (2738397679/10000000000 : ℝ)*x 1 + (1358911221/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3087367451/10000000000 : ℝ)^135 ≤ (2678698485277/12500000000000 : ℝ)^103 := by
    have hnat : (3087367451 : ℕ)^135*12500000000000^103 ≤ 2678698485277^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3087367451 10000000000 2678698485277 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2738397679/10000000000 : ℝ)^135 ≤ (18312100143529/100000000000000 : ℝ)^103 := by
    have hnat : (2738397679 : ℕ)^135*100000000000000^103 ≤ 18312100143529^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2738397679 10000000000 18312100143529 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358911221/2000000000 : ℝ)^135 ≤ (60258311961809/100000000000000 : ℝ)^103 := by
    have hnat : (1358911221 : ℕ)^135*100000000000000^103 ≤ 60258311961809^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358911221 2000000000 60258311961809 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3087367451/10000000000 : ℝ), (2738397679/10000000000 : ℝ), (1358911221/2000000000 : ℝ)] ![(2678698485277/12500000000000 : ℝ), (18312100143529/100000000000000 : ℝ), (60258311961809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3087367451/10000000000 : ℝ)|^135 ≤ (2678698485277/12500000000000 : ℝ)^103
        have hw : |(-3087367451/10000000000 : ℝ)|=(3087367451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2738397679/10000000000 : ℝ)|^135 ≤ (18312100143529/100000000000000 : ℝ)^103
        have hw : |(2738397679/10000000000 : ℝ)|=(2738397679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358911221/2000000000 : ℝ)|^135 ≤ (60258311961809/100000000000000 : ℝ)^103
        have hw : |(1358911221/2000000000 : ℝ)|=(1358911221/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306057_s3_s3_8 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (617399717/2000000000 : ℝ)*x 0 + (-1369035253/5000000000 : ℝ)*x 1 + (169877287/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (617399717/2000000000 : ℝ)^135 ≤ (10713116093119/50000000000000 : ℝ)^103 := by
    have hnat : (617399717 : ℕ)^135*50000000000000^103 ≤ 10713116093119^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      617399717 2000000000 10713116093119 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1369035253/5000000000 : ℝ)^135 ≤ (1830923261613/10000000000000 : ℝ)^103 := by
    have hnat : (1369035253 : ℕ)^135*10000000000000^103 ≤ 1830923261613^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369035253 5000000000 1830923261613 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169877287/250000000 : ℝ)^135 ≤ (60264535191337/100000000000000 : ℝ)^103 := by
    have hnat : (169877287 : ℕ)^135*100000000000000^103 ≤ 60264535191337^103*250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169877287 250000000 60264535191337 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(617399717/2000000000 : ℝ), (-1369035253/5000000000 : ℝ), (169877287/250000000 : ℝ)] ![(10713116093119/50000000000000 : ℝ), (1830923261613/10000000000000 : ℝ), (60264535191337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(617399717/2000000000 : ℝ)|^135 ≤ (10713116093119/50000000000000 : ℝ)^103
        have hw : |(617399717/2000000000 : ℝ)|=(617399717/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1369035253/5000000000 : ℝ)|^135 ≤ (1830923261613/10000000000000 : ℝ)^103
        have hw : |(-1369035253/5000000000 : ℝ)|=(1369035253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169877287/250000000 : ℝ)|^135 ≤ (60264535191337/100000000000000 : ℝ)^103
        have hw : |(169877287/250000000 : ℝ)|=(169877287/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306057_s3_s3_9 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1040292291/2000000000 : ℝ)*x 0 + (1308674779/2000000000 : ℝ)*x 1 + (-83653989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1040292291/2000000000 : ℝ)^135 ≤ (42455242829631/100000000000000 : ℝ)^103 := by
    have hnat : (1040292291 : ℕ)^135*100000000000000^103 ≤ 42455242829631^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040292291 2000000000 42455242829631 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1308674779/2000000000 : ℝ)^135 ≤ (57355502921903/100000000000000 : ℝ)^103 := by
    have hnat : (1308674779 : ℕ)^135*100000000000000^103 ≤ 57355502921903^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308674779 2000000000 57355502921903 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (83653989/10000000000 : ℝ)^135 ≤ (189254238941/100000000000000 : ℝ)^103 := by
    have hnat : (83653989 : ℕ)^135*100000000000000^103 ≤ 189254238941^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83653989 10000000000 189254238941 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1040292291/2000000000 : ℝ), (1308674779/2000000000 : ℝ), (-83653989/10000000000 : ℝ)] ![(42455242829631/100000000000000 : ℝ), (57355502921903/100000000000000 : ℝ), (189254238941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1040292291/2000000000 : ℝ)|^135 ≤ (42455242829631/100000000000000 : ℝ)^103
        have hw : |(1040292291/2000000000 : ℝ)|=(1040292291/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1308674779/2000000000 : ℝ)|^135 ≤ (57355502921903/100000000000000 : ℝ)^103
        have hw : |(1308674779/2000000000 : ℝ)|=(1308674779/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-83653989/10000000000 : ℝ)|^135 ≤ (189254238941/100000000000000 : ℝ)^103
        have hw : |(-83653989/10000000000 : ℝ)|=(83653989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306057_s3_s3_12 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2301777529/5000000000 : ℝ)*x 0 + (231648603/400000000 : ℝ)*x 1 + (2345868433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2301777529/5000000000 : ℝ)^135 ≤ (9044057618589/25000000000000 : ℝ)^103 := by
    have hnat : (2301777529 : ℕ)^135*25000000000000^103 ≤ 9044057618589^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2301777529 5000000000 9044057618589 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (231648603/400000000 : ℝ)^135 ≤ (48872783532483/100000000000000 : ℝ)^103 := by
    have hnat : (231648603 : ℕ)^135*100000000000000^103 ≤ 48872783532483^103*400000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      231648603 400000000 48872783532483 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2345868433/10000000000 : ℝ)^135 ≤ (14950985977359/100000000000000 : ℝ)^103 := by
    have hnat : (2345868433 : ℕ)^135*100000000000000^103 ≤ 14950985977359^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2345868433 10000000000 14950985977359 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2301777529/5000000000 : ℝ), (231648603/400000000 : ℝ), (2345868433/10000000000 : ℝ)] ![(9044057618589/25000000000000 : ℝ), (48872783532483/100000000000000 : ℝ), (14950985977359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2301777529/5000000000 : ℝ)|^135 ≤ (9044057618589/25000000000000 : ℝ)^103
        have hw : |(2301777529/5000000000 : ℝ)|=(2301777529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(231648603/400000000 : ℝ)|^135 ≤ (48872783532483/100000000000000 : ℝ)^103
        have hw : |(231648603/400000000 : ℝ)|=(231648603/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2345868433/10000000000 : ℝ)|^135 ≤ (14950985977359/100000000000000 : ℝ)^103
        have hw : |(2345868433/10000000000 : ℝ)|=(2345868433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306057_s3_s3_13 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2738788831/10000000000 : ℝ)*x 0 + (1543495043/5000000000 : ℝ)*x 1 + (13589113/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2738788831/10000000000 : ℝ)^135 ≤ (18315528558411/100000000000000 : ℝ)^103 := by
    have hnat : (2738788831 : ℕ)^135*100000000000000^103 ≤ 18315528558411^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2738788831 10000000000 18315528558411 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1543495043/5000000000 : ℝ)^135 ≤ (21426154869493/100000000000000 : ℝ)^103 := by
    have hnat : (1543495043 : ℕ)^135*100000000000000^103 ≤ 21426154869493^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1543495043 5000000000 21426154869493 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13589113/20000000 : ℝ)^135 ≤ (12051663310651/20000000000000 : ℝ)^103 := by
    have hnat : (13589113 : ℕ)^135*20000000000000^103 ≤ 12051663310651^103*20000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13589113 20000000 12051663310651 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2738788831/10000000000 : ℝ), (1543495043/5000000000 : ℝ), (13589113/20000000 : ℝ)] ![(18315528558411/100000000000000 : ℝ), (21426154869493/100000000000000 : ℝ), (12051663310651/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2738788831/10000000000 : ℝ)|^135 ≤ (18315528558411/100000000000000 : ℝ)^103
        have hw : |(-2738788831/10000000000 : ℝ)|=(2738788831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1543495043/5000000000 : ℝ)|^135 ≤ (21426154869493/100000000000000 : ℝ)^103
        have hw : |(1543495043/5000000000 : ℝ)|=(1543495043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(13589113/20000000 : ℝ)|^135 ≤ (12051663310651/20000000000000 : ℝ)^103
        have hw : |(13589113/20000000 : ℝ)|=(13589113/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306057_s3_s3_14 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3423077/12500000 : ℝ)*x 0 + (-771655313/2500000000 : ℝ)*x 1 + (3397545947/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3423077/12500000 : ℝ)^135 ≤ (91563301977/500000000000 : ℝ)^103 := by
    have hnat : (3423077 : ℕ)^135*500000000000^103 ≤ 91563301977^103*12500000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3423077 12500000 91563301977 500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (771655313/2500000000 : ℝ)^135 ≤ (4284559918411/20000000000000 : ℝ)^103 := by
    have hnat : (771655313 : ℕ)^135*20000000000000^103 ≤ 4284559918411^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      771655313 2500000000 4284559918411 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3397545947/5000000000 : ℝ)^135 ≤ (15066135000939/25000000000000 : ℝ)^103 := by
    have hnat : (3397545947 : ℕ)^135*25000000000000^103 ≤ 15066135000939^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3397545947 5000000000 15066135000939 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3423077/12500000 : ℝ), (-771655313/2500000000 : ℝ), (3397545947/5000000000 : ℝ)] ![(91563301977/500000000000 : ℝ), (4284559918411/20000000000000 : ℝ), (15066135000939/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3423077/12500000 : ℝ)|^135 ≤ (91563301977/500000000000 : ℝ)^103
        have hw : |(3423077/12500000 : ℝ)|=(3423077/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-771655313/2500000000 : ℝ)|^135 ≤ (4284559918411/20000000000000 : ℝ)^103
        have hw : |(-771655313/2500000000 : ℝ)|=(771655313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3397545947/5000000000 : ℝ)|^135 ≤ (15066135000939/25000000000000 : ℝ)^103
        have hw : |(3397545947/5000000000 : ℝ)|=(3397545947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306057_s3_s3_15 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6542824559/10000000000 : ℝ)*x 0 + (5202051521/10000000000 : ℝ)*x 1 + (-83653457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6542824559/10000000000 : ℝ)^135 ≤ (28674595931047/50000000000000 : ℝ)^103 := by
    have hnat : (6542824559 : ℕ)^135*50000000000000^103 ≤ 28674595931047^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6542824559 10000000000 28674595931047 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5202051521/10000000000 : ℝ)^135 ≤ (42461555465409/100000000000000 : ℝ)^103 := by
    have hnat : (5202051521 : ℕ)^135*100000000000000^103 ≤ 42461555465409^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5202051521 10000000000 42461555465409 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (83653457/10000000000 : ℝ)^135 ≤ (189252661451/100000000000000 : ℝ)^103 := by
    have hnat : (83653457 : ℕ)^135*100000000000000^103 ≤ 189252661451^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83653457 10000000000 189252661451 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6542824559/10000000000 : ℝ), (5202051521/10000000000 : ℝ), (-83653457/10000000000 : ℝ)] ![(28674595931047/50000000000000 : ℝ), (42461555465409/100000000000000 : ℝ), (189252661451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6542824559/10000000000 : ℝ)|^135 ≤ (28674595931047/50000000000000 : ℝ)^103
        have hw : |(6542824559/10000000000 : ℝ)|=(6542824559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5202051521/10000000000 : ℝ)|^135 ≤ (42461555465409/100000000000000 : ℝ)^103
        have hw : |(5202051521/10000000000 : ℝ)|=(5202051521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-83653457/10000000000 : ℝ)|^135 ≤ (189252661451/100000000000000 : ℝ)^103
        have hw : |(-83653457/10000000000 : ℝ)|=(83653457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306057_s3_s3_18 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (361920579/625000000 : ℝ)*x 0 + (2302038799/5000000000 : ℝ)*x 1 + (2345867399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (361920579/625000000 : ℝ)^135 ≤ (1954696402113/4000000000000 : ℝ)^103 := by
    have hnat : (361920579 : ℕ)^135*4000000000000^103 ≤ 1954696402113^103*625000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      361920579 625000000 1954696402113 4000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2302038799/5000000000 : ℝ)^135 ≤ (9045403149629/25000000000000 : ℝ)^103 := by
    have hnat : (2302038799 : ℕ)^135*25000000000000^103 ≤ 9045403149629^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2302038799 5000000000 9045403149629 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2345867399/10000000000 : ℝ)^135 ≤ (2990195467991/20000000000000 : ℝ)^103 := by
    have hnat : (2345867399 : ℕ)^135*20000000000000^103 ≤ 2990195467991^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2345867399 10000000000 2990195467991 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(361920579/625000000 : ℝ), (2302038799/5000000000 : ℝ), (2345867399/10000000000 : ℝ)] ![(1954696402113/4000000000000 : ℝ), (9045403149629/25000000000000 : ℝ), (2990195467991/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(361920579/625000000 : ℝ)|^135 ≤ (1954696402113/4000000000000 : ℝ)^103
        have hw : |(361920579/625000000 : ℝ)|=(361920579/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2302038799/5000000000 : ℝ)|^135 ≤ (9045403149629/25000000000000 : ℝ)^103
        have hw : |(2302038799/5000000000 : ℝ)|=(2302038799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2345867399/10000000000 : ℝ)|^135 ≤ (2990195467991/20000000000000 : ℝ)^103
        have hw : |(2345867399/10000000000 : ℝ)|=(2345867399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306057_s3_s3_19 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-3943372443/10000000000 : ℝ)*x 0 + (70947193/250000000 : ℝ)*x 1 + (1201479147/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3943372443/10000000000 : ℝ)^135 ≤ (14766656268727/50000000000000 : ℝ)^103 := by
    have hnat : (3943372443 : ℕ)^135*50000000000000^103 ≤ 14766656268727^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3943372443 10000000000 14766656268727 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (70947193/250000000 : ℝ)^135 ≤ (9594491821243/50000000000000 : ℝ)^103 := by
    have hnat : (70947193 : ℕ)^135*50000000000000^103 ≤ 9594491821243^103*250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70947193 250000000 9594491821243 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1201479147/2000000000 : ℝ)^135 ≤ (51277703809833/100000000000000 : ℝ)^103 := by
    have hnat : (1201479147 : ℕ)^135*100000000000000^103 ≤ 51277703809833^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1201479147 2000000000 51277703809833 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3943372443/10000000000 : ℝ), (70947193/250000000 : ℝ), (1201479147/2000000000 : ℝ)] ![(14766656268727/50000000000000 : ℝ), (9594491821243/50000000000000 : ℝ), (51277703809833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3943372443/10000000000 : ℝ)|^135 ≤ (14766656268727/50000000000000 : ℝ)^103
        have hw : |(-3943372443/10000000000 : ℝ)|=(3943372443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(70947193/250000000 : ℝ)|^135 ≤ (9594491821243/50000000000000 : ℝ)^103
        have hw : |(70947193/250000000 : ℝ)|=(70947193/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1201479147/2000000000 : ℝ)|^135 ≤ (51277703809833/100000000000000 : ℝ)^103
        have hw : |(1201479147/2000000000 : ℝ)|=(1201479147/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306057_s3_s3_20 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2837986703/10000000000 : ℝ)*x 0 + (-3942673167/10000000000 : ℝ)*x 1 + (6007930851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2837986703/10000000000 : ℝ)^135 ≤ (19189860878137/100000000000000 : ℝ)^103 := by
    have hnat : (2837986703 : ℕ)^135*100000000000000^103 ≤ 19189860878137^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2837986703 10000000000 19189860878137 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3942673167/10000000000 : ℝ)^135 ≤ (7381612133209/25000000000000 : ℝ)^103 := by
    have hnat : (3942673167 : ℕ)^135*25000000000000^103 ≤ 7381612133209^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3942673167 10000000000 7381612133209 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6007930851/10000000000 : ℝ)^135 ≤ (51283690583189/100000000000000 : ℝ)^103 := by
    have hnat : (6007930851 : ℕ)^135*100000000000000^103 ≤ 51283690583189^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6007930851 10000000000 51283690583189 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2837986703/10000000000 : ℝ), (-3942673167/10000000000 : ℝ), (6007930851/10000000000 : ℝ)] ![(19189860878137/100000000000000 : ℝ), (7381612133209/25000000000000 : ℝ), (51283690583189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2837986703/10000000000 : ℝ)|^135 ≤ (19189860878137/100000000000000 : ℝ)^103
        have hw : |(2837986703/10000000000 : ℝ)|=(2837986703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3942673167/10000000000 : ℝ)|^135 ≤ (7381612133209/25000000000000 : ℝ)^103
        have hw : |(-3942673167/10000000000 : ℝ)|=(3942673167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6007930851/10000000000 : ℝ)|^135 ≤ (51283690583189/100000000000000 : ℝ)^103
        have hw : |(6007930851/10000000000 : ℝ)|=(6007930851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306057_s3_s3_21 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3040635743/5000000000 : ℝ)*x 0 + (340569889/625000000 : ℝ)*x 1 + (-324085501/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3040635743/5000000000 : ℝ)^135 ≤ (6513221782687/12500000000000 : ℝ)^103 := by
    have hnat : (3040635743 : ℕ)^135*12500000000000^103 ≤ 6513221782687^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3040635743 5000000000 6513221782687 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (340569889/625000000 : ℝ)^135 ≤ (1128101495087/2500000000000 : ℝ)^103 := by
    have hnat : (340569889 : ℕ)^135*2500000000000^103 ≤ 1128101495087^103*625000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340569889 625000000 1128101495087 2500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (324085501/5000000000 : ℝ)^135 ≤ (2770165927537/100000000000000 : ℝ)^103 := by
    have hnat : (324085501 : ℕ)^135*100000000000000^103 ≤ 2770165927537^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324085501 5000000000 2770165927537 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3040635743/5000000000 : ℝ), (340569889/625000000 : ℝ), (-324085501/5000000000 : ℝ)] ![(6513221782687/12500000000000 : ℝ), (1128101495087/2500000000000 : ℝ), (2770165927537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3040635743/5000000000 : ℝ)|^135 ≤ (6513221782687/12500000000000 : ℝ)^103
        have hw : |(3040635743/5000000000 : ℝ)|=(3040635743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(340569889/625000000 : ℝ)|^135 ≤ (1128101495087/2500000000000 : ℝ)^103
        have hw : |(340569889/625000000 : ℝ)|=(340569889/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-324085501/5000000000 : ℝ)|^135 ≤ (2770165927537/100000000000000 : ℝ)^103
        have hw : |(-324085501/5000000000 : ℝ)|=(324085501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306057_s3_s3_25 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4035080347/10000000000 : ℝ)*x 0 + (107079469/200000000 : ℝ)*x 1 + (3522163841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4035080347/10000000000 : ℝ)^135 ≤ (30436765434097/100000000000000 : ℝ)^103 := by
    have hnat : (4035080347 : ℕ)^135*100000000000000^103 ≤ 30436765434097^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4035080347 10000000000 30436765434097 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107079469/200000000 : ℝ)^135 ≤ (4409419765399/10000000000000 : ℝ)^103 := by
    have hnat : (107079469 : ℕ)^135*10000000000000^103 ≤ 4409419765399^103*200000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107079469 200000000 4409419765399 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3522163841/10000000000 : ℝ)^135 ≤ (25469036895349/100000000000000 : ℝ)^103 := by
    have hnat : (3522163841 : ℕ)^135*100000000000000^103 ≤ 25469036895349^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3522163841 10000000000 25469036895349 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4035080347/10000000000 : ℝ), (107079469/200000000 : ℝ), (3522163841/10000000000 : ℝ)] ![(30436765434097/100000000000000 : ℝ), (4409419765399/10000000000000 : ℝ), (25469036895349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4035080347/10000000000 : ℝ)|^135 ≤ (30436765434097/100000000000000 : ℝ)^103
        have hw : |(4035080347/10000000000 : ℝ)|=(4035080347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(107079469/200000000 : ℝ)|^135 ≤ (4409419765399/10000000000000 : ℝ)^103
        have hw : |(107079469/200000000 : ℝ)|=(107079469/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3522163841/10000000000 : ℝ)|^135 ≤ (25469036895349/100000000000000 : ℝ)^103
        have hw : |(3522163841/10000000000 : ℝ)|=(3522163841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c306057_s3 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((9277/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9277/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(37091/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(37091/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1321/6250 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(1321/6250 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((23273/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(23273/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(23271/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(23271/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(4261/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(4261/50000 : ℝ)*X 1 2) := by
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
  have main1 : (38461/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (38461/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (38461/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (38461/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s3_pow0 : (9277/12500 : ℝ) ^ (67/16 : ℝ) ≤ (28688541111557180011/100000000000000000000 : ℝ) := by
    have hpowers : (9277/12500 : ℝ)^67 ≤ (28688541111557180011/100000000000000000000 : ℝ)^16 := by
      have hnat : (9277 : ℕ)^67*100000000000000000000^16 ≤ 28688541111557180011^16*12500^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9277 12500 28688541111557180011 100000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9277/12500 : ℝ)) (X := (28688541111557180011/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s3_corner0a : (128688541111557180011/100000000000000000000 : ℝ) ≤ (10620837807602893/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (128688541111557180011/100000000000000000000 : ℝ)^16 ≤ (10620837807602893/10000000000000000 : ℝ)^67 := by
      have hnat : (128688541111557180011 : ℕ)^16*10000000000000000^67 ≤ 10620837807602893^67*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        128688541111557180011 100000000000000000000 10620837807602893 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10620837807602893/10000000000000000 : ℝ)) (X := (128688541111557180011/100000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s3_corner0b : (78688541111557180011/50000000000000000000 : ℝ) ≤ (11143735704490497/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (78688541111557180011/50000000000000000000 : ℝ)^16 ≤ (11143735704490497/10000000000000000 : ℝ)^67 := by
      have hnat : (78688541111557180011 : ℕ)^16*10000000000000000^67 ≤ 11143735704490497^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        78688541111557180011 50000000000000000000 11143735704490497 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11143735704490497/10000000000000000 : ℝ)) (X := (78688541111557180011/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(620837807602893/7421600000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(130724474221901/1855400000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (9277/12500 : ℝ)) (alpha := (620837807602893/7421600000000000 : ℝ)) (beta := (130724474221901/1855400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (9277/12500 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(620837807602893/7421600000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(130724474221901/1855400000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (37091/50000 : ℝ) ^ (67/16 : ℝ) ≤ (5726709112176898011/20000000000000000000 : ℝ) := by
    have hpowers : (37091/50000 : ℝ)^67 ≤ (5726709112176898011/20000000000000000000 : ℝ)^16 := by
      have hnat : (37091 : ℕ)^67*20000000000000000000^16 ≤ 5726709112176898011^16*50000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37091 50000 5726709112176898011 20000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (37091/50000 : ℝ)) (X := (5726709112176898011/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s3_corner1a : (25726709112176898011/20000000000000000000 : ℝ) ≤ (1061975372522719/1000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (25726709112176898011/20000000000000000000 : ℝ)^16 ≤ (1061975372522719/1000000000000000 : ℝ)^67 := by
      have hnat : (25726709112176898011 : ℕ)^16*1000000000000000^67 ≤ 1061975372522719^67*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25726709112176898011 20000000000000000000 1061975372522719 1000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1061975372522719/1000000000000000 : ℝ)) (X := (25726709112176898011/20000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s3_corner1b : (15726709112176898011/10000000000000000000 : ℝ) ≤ (1392734412382179/1250000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (15726709112176898011/10000000000000000000 : ℝ)^16 ≤ (1392734412382179/1250000000000000 : ℝ)^67 := by
      have hnat : (15726709112176898011 : ℕ)^16*1250000000000000^67 ≤ 1392734412382179^67*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15726709112176898011 10000000000000000000 1392734412382179 1250000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1392734412382179/1250000000000000 : ℝ)) (X := (15726709112176898011/10000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(61975372522719/741820000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(261060786915121/3709100000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (37091/50000 : ℝ)) (alpha := (61975372522719/741820000000000 : ℝ)) (beta := (261060786915121/3709100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (37091/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(61975372522719/741820000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(261060786915121/3709100000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (1321/6250 : ℝ) ^ (67/16 : ℝ) ≤ (18639874721660183/12500000000000000000 : ℝ) := by
    have hpowers : (1321/6250 : ℝ)^67 ≤ (18639874721660183/12500000000000000000 : ℝ)^16 := by
      have hnat : (1321 : ℕ)^67*12500000000000000000^16 ≤ 18639874721660183^16*6250^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1321 6250 18639874721660183 12500000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1321/6250 : ℝ)) (X := (18639874721660183/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s3_corner2a : (12518639874721660183/12500000000000000000 : ℝ) ≤ (100035590314131/100000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (12518639874721660183/12500000000000000000 : ℝ)^16 ≤ (100035590314131/100000000000000 : ℝ)^67 := by
      have hnat : (12518639874721660183 : ℕ)^16*100000000000000^67 ≤ 100035590314131^67*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12518639874721660183 12500000000000000000 100035590314131 100000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100035590314131/100000000000000 : ℝ)) (X := (12518639874721660183/12500000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s3_corner2b : (6268639874721660183/6250000000000000000 : ℝ) ≤ (2501778507830379/2500000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (6268639874721660183/6250000000000000000 : ℝ)^16 ≤ (2501778507830379/2500000000000000 : ℝ)^67 := by
      have hnat : (6268639874721660183 : ℕ)^16*2500000000000000^67 ≤ 2501778507830379^67*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6268639874721660183 6250000000000000000 2501778507830379 2500000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501778507830379/2500000000000000 : ℝ)) (X := (6268639874721660183/6250000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(35590314131/21136000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(55546873569/33025000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (1321/6250 : ℝ)) (alpha := (35590314131/21136000000000 : ℝ)) (beta := (55546873569/33025000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1321/6250 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(35590314131/21136000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(55546873569/33025000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-3359502567/10000000000 : ℝ)*X 0 0+(3359106649/10000000000 : ℝ)*X 0 1+(1216624279/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306057_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((5746046853/10000000000 : ℝ)*X 2 0+(5746617723/10000000000 : ℝ)*X 2 1+(-11430033/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306057_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_6 : ((1155477549/2500000000 : ℝ)*X 0 0+(2311184691/5000000000 : ℝ)*X 0 1+(371006379/1000000000 : ℝ)*X 0 2+(1155477549/2500000000 : ℝ)*X 1 0+(2311184691/5000000000 : ℝ)*X 1 1+(371006379/1000000000 : ℝ)*X 1 2+(1155477549/2500000000 : ℝ)*X 2 0+(2311184691/5000000000 : ℝ)*X 2 1+(371006379/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306057_s3_s3_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-3087367451/10000000000 : ℝ)*X 0 0+(2738397679/10000000000 : ℝ)*X 0 1+(1358911221/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306057_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((617399717/2000000000 : ℝ)*X 1 0+(-1369035253/5000000000 : ℝ)*X 1 1+(169877287/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306057_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((1040292291/2000000000 : ℝ)*X 2 0+(1308674779/2000000000 : ℝ)*X 2 1+(-83653989/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306057_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_12 : ((2301777529/5000000000 : ℝ)*X 0 0+(231648603/400000000 : ℝ)*X 0 1+(2345868433/10000000000 : ℝ)*X 0 2+(2301777529/5000000000 : ℝ)*X 1 0+(231648603/400000000 : ℝ)*X 1 1+(2345868433/10000000000 : ℝ)*X 1 2+(2301777529/5000000000 : ℝ)*X 2 0+(231648603/400000000 : ℝ)*X 2 1+(2345868433/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306057_s3_s3_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((-2738788831/10000000000 : ℝ)*X 0 0+(1543495043/5000000000 : ℝ)*X 0 1+(13589113/20000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306057_s3_s3_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((3423077/12500000 : ℝ)*X 1 0+(-771655313/2500000000 : ℝ)*X 1 1+(3397545947/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306057_s3_s3_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((6542824559/10000000000 : ℝ)*X 2 0+(5202051521/10000000000 : ℝ)*X 2 1+(-83653457/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306057_s3_s3_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_18 : ((361920579/625000000 : ℝ)*X 0 0+(2302038799/5000000000 : ℝ)*X 0 1+(2345867399/10000000000 : ℝ)*X 0 2+(361920579/625000000 : ℝ)*X 1 0+(2302038799/5000000000 : ℝ)*X 1 1+(2345867399/10000000000 : ℝ)*X 1 2+(361920579/625000000 : ℝ)*X 2 0+(2302038799/5000000000 : ℝ)*X 2 1+(2345867399/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306057_s3_s3_18 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_19 : ((-3943372443/10000000000 : ℝ)*X 0 0+(70947193/250000000 : ℝ)*X 0 1+(1201479147/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306057_s3_s3_19 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((2837986703/10000000000 : ℝ)*X 1 0+(-3942673167/10000000000 : ℝ)*X 1 1+(6007930851/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306057_s3_s3_20 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((3040635743/5000000000 : ℝ)*X 2 0+(340569889/625000000 : ℝ)*X 2 1+(-324085501/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306057_s3_s3_21 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_25 : ((4035080347/10000000000 : ℝ)*X 0 0+(107079469/200000000 : ℝ)*X 0 1+(3522163841/10000000000 : ℝ)*X 0 2+(4035080347/10000000000 : ℝ)*X 1 0+(107079469/200000000 : ℝ)*X 1 1+(3522163841/10000000000 : ℝ)*X 1 2+(4035080347/10000000000 : ℝ)*X 2 0+(107079469/200000000 : ℝ)*X 2 1+(3522163841/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306057_s3_s3_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((23273/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(23273/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1008060107656541173427596840611/90909425289400000000000000000000000 : ℝ) := by norm_num
    linear_combination (2741951/250000000000 : ℝ)*(base23) + (36817/1000000000000 : ℝ)*(base49) + (1285663907587/500000000000 : ℝ)*(base59) + (568903160801/500000000000 : ℝ)*(base60) + (2837057778407/500000000000 : ℝ)*(major_s3_0) + (2837057778407/500000000000 : ℝ)*(major_s3_1) + (2837057778407/500000000000 : ℝ)*(major_s3_2) + (39288887/1000000000000 : ℝ)*(sp_s3_2) + (7668051201757/1000000000000 : ℝ)*(sp_s3_7) + (7668181526861/1000000000000 : ℝ)*(sp_s3_8) + (7668131270169/1000000000000 : ℝ)*(sp_s3_9) + (460003125143/125000000000 : ℝ)*(sp_s3_12) + (8145319/62500000000 : ℝ)*(sp_s3_13) + (20889413/1000000000000 : ℝ)*(sp_s3_25) + (3680045890557/1000000000000 : ℝ)*(f.failure) + (7668181526861/1000000000000 : ℝ)*(f.sum) + (645783028171706329/1959888440000000000000000000000 : ℝ)*base63 + (3226299296517/66050000000000000000000000 : ℝ)*base64 + (248367843039897/1854550000000000000000000000 : ℝ)*base67 + (6495763418583/52840000000000000000000000 : ℝ)*base69 + (710634358637265939/4901966800000000000000000000000 : ℝ)*base71 + (230794582651343/927700000000000000000000000 : ℝ)*base72 + (23488697579627/185455000000000000000000000 : ℝ)*base75 + (1952526357648971/3710800000000000000000000000 : ℝ)*base77 + (416744108382652447/1376372828000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (10801/50000000000000000 : ℝ)*base87 + (10801/50000000000000000 : ℝ)*base89 + (10801/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(23271/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(23271/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (13692586158054363642495607533/1567403884300000000000000000000000 : ℝ) := by norm_num
    linear_combination (2357767/250000000000 : ℝ)*(base21) + (5551/250000000000 : ℝ)*(base40) + (1285637290469/500000000000 : ℝ)*(base59) + (11468994381/8000000000 : ℝ)*(base60) + (5674046093389/1000000000000 : ℝ)*(major_s3_0) + (5674046093389/1000000000000 : ℝ)*(major_s3_1) + (5674046093389/1000000000000 : ℝ)*(major_s3_2) + (3601303/250000000000 : ℝ)*(sp_s3_6) + (105747353/1000000000000 : ℝ)*(sp_s3_8) + (7668088435979/1000000000000 : ℝ)*(sp_s3_13) + (3833991344313/500000000000 : ℝ)*(sp_s3_14) + (3834020722013/500000000000 : ℝ)*(sp_s3_15) + (1839993216819/500000000000 : ℝ)*(sp_s3_18) + (9390221/250000000000 : ℝ)*(sp_s3_21) + (73600016777/20000000000 : ℝ)*(f.failure) + (7668088435979/1000000000000 : ℝ)*(f.sum) + (12077796322688711/135164720000000000000000000000 : ℝ)*base63 + (663621166481/2064062500000000000000000 : ℝ)*base64 + (38056859894419/127900000000000000000000000 : ℝ)*base66 + (8966995648347/105680000000000000000000000 : ℝ)*base68 + (1567475646845402287/9803933600000000000000000000000 : ℝ)*base70 + (470876892405551/1855400000000000000000000000 : ℝ)*base72 + (8411589106443/25580000000000000000000000 : ℝ)*base75 + (1653064652783177/7421600000000000000000000000 : ℝ)*base77 + (16554498880661539/474611320000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (261/1000000000000000 : ℝ)*base87 + (261/1000000000000000 : ℝ)*base89 + (261/1000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(4261/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(4261/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (453418907332573288800972786669/181818850578800000000000000000000000 : ℝ) := by norm_num
    linear_combination (553103/1000000000000 : ℝ)*(base40) + (214153/500000000000 : ℝ)*(base50) + (47361078779/62500000000 : ℝ)*(base59) + (2832227483553/1000000000000 : ℝ)*(major_s3_0) + (2832227483553/1000000000000 : ℝ)*(major_s3_1) + (2832227483553/1000000000000 : ℝ)*(major_s3_2) + (30299/31250000000 : ℝ)*(sp_s3_0) + (258511/62500000000 : ℝ)*(sp_s3_9) + (15280823/1000000000000 : ℝ)*(sp_s3_12) + (928723/100000000000 : ℝ)*(sp_s3_15) + (3827562992353/1000000000000 : ℝ)*(sp_s3_19) + (3827563961921/1000000000000 : ℝ)*(sp_s3_20) + (765510107703/200000000000 : ℝ)*(sp_s3_21) + (459218723273/250000000000 : ℝ)*(sp_s3_25) + (367378034783/200000000000 : ℝ)*(f.failure) + (3827563961921/1000000000000 : ℝ)*(f.sum) + (571651104674626601/3919776880000000000000000000000 : ℝ)*base62 + (6046285858099/66050000000000000000000000 : ℝ)*base64 + (407626225108053/3709100000000000000000000000 : ℝ)*base67 + (12363205551943/105680000000000000000000000 : ℝ)*base68 + (7541952531148804981/9803933600000000000000000000000 : ℝ)*base71 + (1370288030586827/1855400000000000000000000000 : ℝ)*base72 + (501131108252229/741820000000000000000000000 : ℝ)*base74 + (1736611452935229/7421600000000000000000000000 : ℝ)*base77 + (1220127220819066409/13763728280000000000000000000000 : ℝ)*base79 + (4181/10000000000000000 : ℝ)*base86 + (4181/10000000000000000 : ℝ)*base88 + (4181/10000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((9277/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9277/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(37091/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(37091/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1321/6250 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(1321/6250 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((23273/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(23273/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(23271/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(23271/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(4261/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(4261/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c306057_s3 p hpa hpb X hX hprev2

#print axioms solution
