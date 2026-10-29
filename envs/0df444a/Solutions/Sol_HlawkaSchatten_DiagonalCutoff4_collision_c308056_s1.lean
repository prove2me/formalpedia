-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c308056_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:37:14.368509+00:00
-- url     : https://prove2.me/submissions/4dc3d5db-894d-404e-8faa-883ec877cc4c

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
theorem collision_support_c308056_s1_s1_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-316668271/1000000000 : ℝ)*x 0 + (3166685541/10000000000 : ℝ)*x 1 + (-3169574777/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (316668271/1000000000 : ℝ)^69 ≤ (22379153776933/100000000000000 : ℝ)^53 := by
    have hnat : (316668271 : ℕ)^69*100000000000000^53 ≤ 22379153776933^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      316668271 1000000000 22379153776933 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3166685541/10000000000 : ℝ)^69 ≤ (11189589911803/50000000000000 : ℝ)^53 := by
    have hnat : (3166685541 : ℕ)^69*50000000000000^53 ≤ 11189589911803^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3166685541 10000000000 11189589911803 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3169574777/5000000000 : ℝ)^69 ≤ (55241666384213/100000000000000 : ℝ)^53 := by
    have hnat : (3169574777 : ℕ)^69*100000000000000^53 ≤ 55241666384213^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3169574777 5000000000 55241666384213 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-316668271/1000000000 : ℝ), (3166685541/10000000000 : ℝ), (-3169574777/5000000000 : ℝ)] ![(22379153776933/100000000000000 : ℝ), (11189589911803/50000000000000 : ℝ), (55241666384213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-316668271/1000000000 : ℝ)|^69 ≤ (22379153776933/100000000000000 : ℝ)^53
        have hw : |(-316668271/1000000000 : ℝ)|=(316668271/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3166685541/10000000000 : ℝ)|^69 ≤ (11189589911803/50000000000000 : ℝ)^53
        have hw : |(3166685541/10000000000 : ℝ)|=(3166685541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3169574777/5000000000 : ℝ)|^69 ≤ (55241666384213/100000000000000 : ℝ)^53
        have hw : |(-3169574777/5000000000 : ℝ)|=(3169574777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308056_s1_s1_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (316668271/1000000000 : ℝ)*x 0 + (-3166685541/10000000000 : ℝ)*x 1 + (-3169574777/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (316668271/1000000000 : ℝ)^69 ≤ (22379153776933/100000000000000 : ℝ)^53 := by
    have hnat : (316668271 : ℕ)^69*100000000000000^53 ≤ 22379153776933^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      316668271 1000000000 22379153776933 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3166685541/10000000000 : ℝ)^69 ≤ (11189589911803/50000000000000 : ℝ)^53 := by
    have hnat : (3166685541 : ℕ)^69*50000000000000^53 ≤ 11189589911803^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3166685541 10000000000 11189589911803 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3169574777/5000000000 : ℝ)^69 ≤ (55241666384213/100000000000000 : ℝ)^53 := by
    have hnat : (3169574777 : ℕ)^69*100000000000000^53 ≤ 55241666384213^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3169574777 5000000000 55241666384213 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(316668271/1000000000 : ℝ), (-3166685541/10000000000 : ℝ), (-3169574777/5000000000 : ℝ)] ![(22379153776933/100000000000000 : ℝ), (11189589911803/50000000000000 : ℝ), (55241666384213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(316668271/1000000000 : ℝ)|^69 ≤ (22379153776933/100000000000000 : ℝ)^53
        have hw : |(316668271/1000000000 : ℝ)|=(316668271/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3166685541/10000000000 : ℝ)|^69 ≤ (11189589911803/50000000000000 : ℝ)^53
        have hw : |(-3166685541/10000000000 : ℝ)|=(3166685541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3169574777/5000000000 : ℝ)|^69 ≤ (55241666384213/100000000000000 : ℝ)^53
        have hw : |(-3169574777/5000000000 : ℝ)|=(3169574777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308056_s1_s1_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5573610017/10000000000 : ℝ)*x 0 + (5573612471/10000000000 : ℝ)*x 1 + (1233929459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5573610017/10000000000 : ℝ)^69 ≤ (46719540624863/100000000000000 : ℝ)^53 := by
    have hnat : (5573610017 : ℕ)^69*100000000000000^53 ≤ 46719540624863^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5573610017 10000000000 46719540624863 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5573612471/10000000000 : ℝ)^69 ≤ (9343913480963/20000000000000 : ℝ)^53 := by
    have hnat : (5573612471 : ℕ)^69*20000000000000^53 ≤ 9343913480963^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5573612471 10000000000 9343913480963 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1233929459/10000000000 : ℝ)^69 ≤ (820111494761/12500000000000 : ℝ)^53 := by
    have hnat : (1233929459 : ℕ)^69*12500000000000^53 ≤ 820111494761^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1233929459 10000000000 820111494761 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5573610017/10000000000 : ℝ), (5573612471/10000000000 : ℝ), (1233929459/10000000000 : ℝ)] ![(46719540624863/100000000000000 : ℝ), (9343913480963/20000000000000 : ℝ), (820111494761/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5573610017/10000000000 : ℝ)|^69 ≤ (46719540624863/100000000000000 : ℝ)^53
        have hw : |(5573610017/10000000000 : ℝ)|=(5573610017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5573612471/10000000000 : ℝ)|^69 ≤ (9343913480963/20000000000000 : ℝ)^53
        have hw : |(5573612471/10000000000 : ℝ)|=(5573612471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1233929459/10000000000 : ℝ)|^69 ≤ (820111494761/12500000000000 : ℝ)^53
        have hw : |(1233929459/10000000000 : ℝ)|=(1233929459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308056_s1_s1_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2712032083/10000000000 : ℝ)*x 0 + (2347291013/10000000000 : ℝ)*x 1 + (-3657239057/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2712032083/10000000000 : ℝ)^69 ≤ (3658002604429/20000000000000 : ℝ)^53 := by
    have hnat : (2712032083 : ℕ)^69*20000000000000^53 ≤ 3658002604429^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712032083 10000000000 3658002604429 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2347291013/10000000000 : ℝ)^69 ≤ (3788693003071/25000000000000 : ℝ)^53 := by
    have hnat : (2347291013 : ℕ)^69*25000000000000^53 ≤ 3788693003071^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2347291013 10000000000 3788693003071 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3657239057/5000000000 : ℝ)^69 ≤ (6655521494603/10000000000000 : ℝ)^53 := by
    have hnat : (3657239057 : ℕ)^69*10000000000000^53 ≤ 6655521494603^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3657239057 5000000000 6655521494603 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2712032083/10000000000 : ℝ), (2347291013/10000000000 : ℝ), (-3657239057/5000000000 : ℝ)] ![(3658002604429/20000000000000 : ℝ), (3788693003071/25000000000000 : ℝ), (6655521494603/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2712032083/10000000000 : ℝ)|^69 ≤ (3658002604429/20000000000000 : ℝ)^53
        have hw : |(-2712032083/10000000000 : ℝ)|=(2712032083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2347291013/10000000000 : ℝ)|^69 ≤ (3788693003071/25000000000000 : ℝ)^53
        have hw : |(2347291013/10000000000 : ℝ)|=(2347291013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3657239057/5000000000 : ℝ)|^69 ≤ (6655521494603/10000000000000 : ℝ)^53
        have hw : |(-3657239057/5000000000 : ℝ)|=(3657239057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308056_s1_s1_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (10848129/40000000 : ℝ)*x 0 + (-1173645579/5000000000 : ℝ)*x 1 + (-114288717/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10848129/40000000 : ℝ)^69 ≤ (9145007244199/50000000000000 : ℝ)^53 := by
    have hnat : (10848129 : ℕ)^69*50000000000000^53 ≤ 9145007244199^53*40000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10848129 40000000 9145007244199 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1173645579/5000000000 : ℝ)^69 ≤ (15154773231059/100000000000000 : ℝ)^53 := by
    have hnat : (1173645579 : ℕ)^69*100000000000000^53 ≤ 15154773231059^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1173645579 5000000000 15154773231059 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (114288717/156250000 : ℝ)^69 ≤ (2079850383401/3125000000000 : ℝ)^53 := by
    have hnat : (114288717 : ℕ)^69*3125000000000^53 ≤ 2079850383401^53*156250000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114288717 156250000 2079850383401 3125000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10848129/40000000 : ℝ), (-1173645579/5000000000 : ℝ), (-114288717/156250000 : ℝ)] ![(9145007244199/50000000000000 : ℝ), (15154773231059/100000000000000 : ℝ), (2079850383401/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10848129/40000000 : ℝ)|^69 ≤ (9145007244199/50000000000000 : ℝ)^53
        have hw : |(10848129/40000000 : ℝ)|=(10848129/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1173645579/5000000000 : ℝ)|^69 ≤ (15154773231059/100000000000000 : ℝ)^53
        have hw : |(-1173645579/5000000000 : ℝ)|=(1173645579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-114288717/156250000 : ℝ)|^69 ≤ (2079850383401/3125000000000 : ℝ)^53
        have hw : |(-114288717/156250000 : ℝ)|=(114288717/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308056_s1_s1_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4437307327/10000000000 : ℝ)*x 0 + (6828482427/10000000000 : ℝ)*x 1 + (911406371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4437307327/10000000000 : ℝ)^69 ≤ (34720786101533/100000000000000 : ℝ)^53 := by
    have hnat : (4437307327 : ℕ)^69*100000000000000^53 ≤ 34720786101533^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4437307327 10000000000 34720786101533 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6828482427/10000000000 : ℝ)^69 ≤ (15214191126957/25000000000000 : ℝ)^53 := by
    have hnat : (6828482427 : ℕ)^69*25000000000000^53 ≤ 15214191126957^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6828482427 10000000000 15214191126957 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (911406371/10000000000 : ℝ)^69 ≤ (4422449380907/100000000000000 : ℝ)^53 := by
    have hnat : (911406371 : ℕ)^69*100000000000000^53 ≤ 4422449380907^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      911406371 10000000000 4422449380907 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4437307327/10000000000 : ℝ), (6828482427/10000000000 : ℝ), (911406371/10000000000 : ℝ)] ![(34720786101533/100000000000000 : ℝ), (15214191126957/25000000000000 : ℝ), (4422449380907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4437307327/10000000000 : ℝ)|^69 ≤ (34720786101533/100000000000000 : ℝ)^53
        have hw : |(4437307327/10000000000 : ℝ)|=(4437307327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6828482427/10000000000 : ℝ)|^69 ≤ (15214191126957/25000000000000 : ℝ)^53
        have hw : |(6828482427/10000000000 : ℝ)|=(6828482427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(911406371/10000000000 : ℝ)|^69 ≤ (4422449380907/100000000000000 : ℝ)^53
        have hw : |(911406371/10000000000 : ℝ)|=(911406371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308056_s1_s1_12 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1148522483/2500000000 : ℝ)*x 0 + (1767438001/2500000000 : ℝ)*x 1 + (-1542353/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1148522483/2500000000 : ℝ)^69 ≤ (36326368218973/100000000000000 : ℝ)^53 := by
    have hnat : (1148522483 : ℕ)^69*100000000000000^53 ≤ 36326368218973^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1148522483 2500000000 36326368218973 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1767438001/2500000000 : ℝ)^69 ≤ (63670944244837/100000000000000 : ℝ)^53 := by
    have hnat : (1767438001 : ℕ)^69*100000000000000^53 ≤ 63670944244837^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1767438001 2500000000 63670944244837 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1542353/5000000000 : ℝ)^69 ≤ (671883221/25000000000000 : ℝ)^53 := by
    have hnat : (1542353 : ℕ)^69*25000000000000^53 ≤ 671883221^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1542353 5000000000 671883221 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1148522483/2500000000 : ℝ), (1767438001/2500000000 : ℝ), (-1542353/5000000000 : ℝ)] ![(36326368218973/100000000000000 : ℝ), (63670944244837/100000000000000 : ℝ), (671883221/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1148522483/2500000000 : ℝ)|^69 ≤ (36326368218973/100000000000000 : ℝ)^53
        have hw : |(1148522483/2500000000 : ℝ)|=(1148522483/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1767438001/2500000000 : ℝ)|^69 ≤ (63670944244837/100000000000000 : ℝ)^53
        have hw : |(1767438001/2500000000 : ℝ)|=(1767438001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1542353/5000000000 : ℝ)|^69 ≤ (671883221/25000000000000 : ℝ)^53
        have hw : |(-1542353/5000000000 : ℝ)|=(1542353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308056_s1_s1_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1173645531/5000000000 : ℝ)*x 0 + (542406371/2000000000 : ℝ)*x 1 + (-7314478249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1173645531/5000000000 : ℝ)^69 ≤ (7577386212073/50000000000000 : ℝ)^53 := by
    have hnat : (1173645531 : ℕ)^69*50000000000000^53 ≤ 7577386212073^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1173645531 5000000000 7577386212073 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542406371/2000000000 : ℝ)^69 ≤ (3658002204063/20000000000000 : ℝ)^53 := by
    have hnat : (542406371 : ℕ)^69*20000000000000^53 ≤ 3658002204063^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542406371 2000000000 3658002204063 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7314478249/10000000000 : ℝ)^69 ≤ (66555216545241/100000000000000 : ℝ)^53 := by
    have hnat : (7314478249 : ℕ)^69*100000000000000^53 ≤ 66555216545241^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7314478249 10000000000 66555216545241 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1173645531/5000000000 : ℝ), (542406371/2000000000 : ℝ), (-7314478249/10000000000 : ℝ)] ![(7577386212073/50000000000000 : ℝ), (3658002204063/20000000000000 : ℝ), (66555216545241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1173645531/5000000000 : ℝ)|^69 ≤ (7577386212073/50000000000000 : ℝ)^53
        have hw : |(-1173645531/5000000000 : ℝ)|=(1173645531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(542406371/2000000000 : ℝ)|^69 ≤ (3658002204063/20000000000000 : ℝ)^53
        have hw : |(542406371/2000000000 : ℝ)|=(542406371/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7314478249/10000000000 : ℝ)|^69 ≤ (66555216545241/100000000000000 : ℝ)^53
        have hw : |(-7314478249/10000000000 : ℝ)|=(7314478249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308056_s1_s1_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2347290789/10000000000 : ℝ)*x 0 + (-135601577/500000000 : ℝ)*x 1 + (-1828619669/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2347290789/10000000000 : ℝ)^69 ≤ (7577385064743/50000000000000 : ℝ)^53 := by
    have hnat : (2347290789 : ℕ)^69*50000000000000^53 ≤ 7577385064743^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2347290789 10000000000 7577385064743 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135601577/500000000 : ℝ)^69 ≤ (4572502063657/25000000000000 : ℝ)^53 := by
    have hnat : (135601577 : ℕ)^69*25000000000000^53 ≤ 4572502063657^53*500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135601577 500000000 4572502063657 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1828619669/2500000000 : ℝ)^69 ≤ (33277610801743/50000000000000 : ℝ)^53 := by
    have hnat : (1828619669 : ℕ)^69*50000000000000^53 ≤ 33277610801743^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1828619669 2500000000 33277610801743 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2347290789/10000000000 : ℝ), (-135601577/500000000 : ℝ), (-1828619669/2500000000 : ℝ)] ![(7577385064743/50000000000000 : ℝ), (4572502063657/25000000000000 : ℝ), (33277610801743/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2347290789/10000000000 : ℝ)|^69 ≤ (7577385064743/50000000000000 : ℝ)^53
        have hw : |(2347290789/10000000000 : ℝ)|=(2347290789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-135601577/500000000 : ℝ)|^69 ≤ (4572502063657/25000000000000 : ℝ)^53
        have hw : |(-135601577/500000000 : ℝ)|=(135601577/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1828619669/2500000000 : ℝ)|^69 ≤ (33277610801743/50000000000000 : ℝ)^53
        have hw : |(-1828619669/2500000000 : ℝ)|=(1828619669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308056_s1_s1_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (341424113/500000000 : ℝ)*x 0 + (443730747/1000000000 : ℝ)*x 1 + (455703223/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (341424113/500000000 : ℝ)^69 ≤ (30428381285091/50000000000000 : ℝ)^53 := by
    have hnat : (341424113 : ℕ)^69*50000000000000^53 ≤ 30428381285091^53*500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341424113 500000000 30428381285091 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (443730747/1000000000 : ℝ)^69 ≤ (4340098444783/12500000000000 : ℝ)^53 := by
    have hnat : (443730747 : ℕ)^69*12500000000000^53 ≤ 4340098444783^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443730747 1000000000 4340098444783 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (455703223/5000000000 : ℝ)^69 ≤ (552806231837/12500000000000 : ℝ)^53 := by
    have hnat : (455703223 : ℕ)^69*12500000000000^53 ≤ 552806231837^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      455703223 5000000000 552806231837 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(341424113/500000000 : ℝ), (443730747/1000000000 : ℝ), (455703223/5000000000 : ℝ)] ![(30428381285091/50000000000000 : ℝ), (4340098444783/12500000000000 : ℝ), (552806231837/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(341424113/500000000 : ℝ)|^69 ≤ (30428381285091/50000000000000 : ℝ)^53
        have hw : |(341424113/500000000 : ℝ)|=(341424113/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(443730747/1000000000 : ℝ)|^69 ≤ (4340098444783/12500000000000 : ℝ)^53
        have hw : |(443730747/1000000000 : ℝ)|=(443730747/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(455703223/5000000000 : ℝ)|^69 ≤ (552806231837/12500000000000 : ℝ)^53
        have hw : |(455703223/5000000000 : ℝ)|=(455703223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308056_s1_s1_19 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3703151463/10000000000 : ℝ)*x 0 + (2822645279/10000000000 : ℝ)*x 1 + (-6166973867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3703151463/10000000000 : ℝ)^69 ≤ (13718256106449/50000000000000 : ℝ)^53 := by
    have hnat : (3703151463 : ℕ)^69*50000000000000^53 ≤ 13718256106449^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3703151463 10000000000 13718256106449 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2822645279/10000000000 : ℝ)^69 ≤ (9633557677033/50000000000000 : ℝ)^53 := by
    have hnat : (2822645279 : ℕ)^69*50000000000000^53 ≤ 9633557677033^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2822645279 10000000000 9633557677033 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6166973867/10000000000 : ℝ)^69 ≤ (26648186213159/50000000000000 : ℝ)^53 := by
    have hnat : (6166973867 : ℕ)^69*50000000000000^53 ≤ 26648186213159^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6166973867 10000000000 26648186213159 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3703151463/10000000000 : ℝ), (2822645279/10000000000 : ℝ), (-6166973867/10000000000 : ℝ)] ![(13718256106449/50000000000000 : ℝ), (9633557677033/50000000000000 : ℝ), (26648186213159/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3703151463/10000000000 : ℝ)|^69 ≤ (13718256106449/50000000000000 : ℝ)^53
        have hw : |(-3703151463/10000000000 : ℝ)|=(3703151463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2822645279/10000000000 : ℝ)|^69 ≤ (9633557677033/50000000000000 : ℝ)^53
        have hw : |(2822645279/10000000000 : ℝ)|=(2822645279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6166973867/10000000000 : ℝ)|^69 ≤ (26648186213159/50000000000000 : ℝ)^53
        have hw : |(-6166973867/10000000000 : ℝ)|=(6166973867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308056_s1_s1_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2719060093/10000000000 : ℝ)*x 0 + (-359956513/1000000000 : ℝ)*x 1 + (-3168031607/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2719060093/10000000000 : ℝ)^69 ≤ (18351742773231/100000000000000 : ℝ)^53 := by
    have hnat : (2719060093 : ℕ)^69*100000000000000^53 ≤ 18351742773231^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719060093 10000000000 18351742773231 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (359956513/1000000000 : ℝ)^69 ≤ (13220801573289/50000000000000 : ℝ)^53 := by
    have hnat : (359956513 : ℕ)^69*50000000000000^53 ≤ 13220801573289^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      359956513 1000000000 13220801573289 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3168031607/5000000000 : ℝ)^69 ≤ (1725207939629/3125000000000 : ℝ)^53 := by
    have hnat : (3168031607 : ℕ)^69*3125000000000^53 ≤ 1725207939629^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3168031607 5000000000 1725207939629 3125000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2719060093/10000000000 : ℝ), (-359956513/1000000000 : ℝ), (-3168031607/5000000000 : ℝ)] ![(18351742773231/100000000000000 : ℝ), (13220801573289/50000000000000 : ℝ), (1725207939629/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2719060093/10000000000 : ℝ)|^69 ≤ (18351742773231/100000000000000 : ℝ)^53
        have hw : |(2719060093/10000000000 : ℝ)|=(2719060093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-359956513/1000000000 : ℝ)|^69 ≤ (13220801573289/50000000000000 : ℝ)^53
        have hw : |(-359956513/1000000000 : ℝ)|=(359956513/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3168031607/5000000000 : ℝ)|^69 ≤ (1725207939629/3125000000000 : ℝ)^53
        have hw : |(-3168031607/5000000000 : ℝ)|=(3168031607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308056_s1_s1_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5626851137/10000000000 : ℝ)*x 0 + (1125370131/2000000000 : ℝ)*x 1 + (26552207/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5626851137/10000000000 : ℝ)^69 ≤ (9460276975471/20000000000000 : ℝ)^53 := by
    have hnat : (5626851137 : ℕ)^69*20000000000000^53 ≤ 9460276975471^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5626851137 10000000000 9460276975471 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1125370131/2000000000 : ℝ)^69 ≤ (47301379602279/100000000000000 : ℝ)^53 := by
    have hnat : (1125370131 : ℕ)^69*100000000000000^53 ≤ 47301379602279^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125370131 2000000000 47301379602279 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26552207/250000000 : ℝ)^69 ≤ (2698617752403/50000000000000 : ℝ)^53 := by
    have hnat : (26552207 : ℕ)^69*50000000000000^53 ≤ 2698617752403^53*250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26552207 250000000 2698617752403 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5626851137/10000000000 : ℝ), (1125370131/2000000000 : ℝ), (26552207/250000000 : ℝ)] ![(9460276975471/20000000000000 : ℝ), (47301379602279/100000000000000 : ℝ), (2698617752403/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5626851137/10000000000 : ℝ)|^69 ≤ (9460276975471/20000000000000 : ℝ)^53
        have hw : |(5626851137/10000000000 : ℝ)|=(5626851137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1125370131/2000000000 : ℝ)|^69 ≤ (47301379602279/100000000000000 : ℝ)^53
        have hw : |(1125370131/2000000000 : ℝ)|=(1125370131/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(26552207/250000000 : ℝ)|^69 ≤ (2698617752403/50000000000000 : ℝ)^53
        have hw : |(26552207/250000000 : ℝ)|=(26552207/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308056_s1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((10871/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10871/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10871/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10871/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-31609/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-31609/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((69247/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(69247/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(69247/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(69247/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-1359/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-1359/20000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (3861/5000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (3861/5000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (11517/6250 : ℝ) := by
    linarith only [f.Tcap]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (10871/12500 : ℝ) ^ (17/4 : ℝ) ≤ (55243069514098494463/100000000000000000000 : ℝ) := by
    have hpowers : (10871/12500 : ℝ)^17 ≤ (55243069514098494463/100000000000000000000 : ℝ)^4 := by
      have hnat : (10871 : ℕ)^17*100000000000000000000^4 ≤ 55243069514098494463^4*12500^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10871 12500 55243069514098494463 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10871/12500 : ℝ)) (X := (55243069514098494463/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (155243069514098494463/100000000000000000000 : ℝ) ≤ (11090319350810959/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (155243069514098494463/100000000000000000000 : ℝ)^4 ≤ (11090319350810959/10000000000000000 : ℝ)^17 := by
      have hnat : (155243069514098494463 : ℕ)^4*10000000000000000^17 ≤ 11090319350810959^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        155243069514098494463 100000000000000000000 11090319350810959 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11090319350810959/10000000000000000 : ℝ)) (X := (155243069514098494463/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (105243069514098494463/50000000000000000000 : ℝ) ≤ (297846566034703/250000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (105243069514098494463/50000000000000000000 : ℝ)^4 ≤ (297846566034703/250000000000000 : ℝ)^17 := by
      have hnat : (105243069514098494463 : ℕ)^4*250000000000000^17 ≤ 297846566034703^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        105243069514098494463 50000000000000000000 297846566034703 250000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (297846566034703/250000000000000 : ℝ)) (X := (105243069514098494463/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1090319350810959/8696800000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(117649041511023/1242400000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (10871/12500 : ℝ)) (alpha := (1090319350810959/8696800000000000 : ℝ)) (beta := (117649041511023/1242400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (10871/12500 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1090319350810959/8696800000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(117649041511023/1242400000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (10871/12500 : ℝ) ^ (17/4 : ℝ) ≤ (55243069514098494463/100000000000000000000 : ℝ) := by
    have hpowers : (10871/12500 : ℝ)^17 ≤ (55243069514098494463/100000000000000000000 : ℝ)^4 := by
      have hnat : (10871 : ℕ)^17*100000000000000000000^4 ≤ 55243069514098494463^4*12500^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10871 12500 55243069514098494463 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10871/12500 : ℝ)) (X := (55243069514098494463/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (155243069514098494463/100000000000000000000 : ℝ) ≤ (11090319350810959/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (155243069514098494463/100000000000000000000 : ℝ)^4 ≤ (11090319350810959/10000000000000000 : ℝ)^17 := by
      have hnat : (155243069514098494463 : ℕ)^4*10000000000000000^17 ≤ 11090319350810959^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        155243069514098494463 100000000000000000000 11090319350810959 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11090319350810959/10000000000000000 : ℝ)) (X := (155243069514098494463/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (105243069514098494463/50000000000000000000 : ℝ) ≤ (297846566034703/250000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (105243069514098494463/50000000000000000000 : ℝ)^4 ≤ (297846566034703/250000000000000 : ℝ)^17 := by
      have hnat : (105243069514098494463 : ℕ)^4*250000000000000^17 ≤ 297846566034703^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        105243069514098494463 50000000000000000000 297846566034703 250000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (297846566034703/250000000000000 : ℝ)) (X := (105243069514098494463/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1090319350810959/8696800000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(117649041511023/1242400000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (10871/12500 : ℝ)) (alpha := (1090319350810959/8696800000000000 : ℝ)) (beta := (117649041511023/1242400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (10871/12500 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1090319350810959/8696800000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(117649041511023/1242400000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (31609/100000 : ℝ) ^ (17/4 : ℝ) ≤ (374253369716631023/50000000000000000000 : ℝ) := by
    have hpowers : (31609/100000 : ℝ)^17 ≤ (374253369716631023/50000000000000000000 : ℝ)^4 := by
      have hnat : (31609 : ℕ)^17*50000000000000000000^4 ≤ 374253369716631023^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31609 100000 374253369716631023 50000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (31609/100000 : ℝ)) (X := (374253369716631023/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (50374253369716631023/50000000000000000000 : ℝ) ≤ (10017561739843631/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (50374253369716631023/50000000000000000000 : ℝ)^4 ≤ (10017561739843631/10000000000000000 : ℝ)^17 := by
      have hnat : (50374253369716631023 : ℕ)^4*10000000000000000^17 ≤ 10017561739843631^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50374253369716631023 50000000000000000000 10017561739843631 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10017561739843631/10000000000000000 : ℝ)) (X := (50374253369716631023/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (25374253369716631023/25000000000000000000 : ℝ) ≤ (10035023986929399/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (25374253369716631023/25000000000000000000 : ℝ)^4 ≤ (10035023986929399/10000000000000000 : ℝ)^17 := by
      have hnat : (25374253369716631023 : ℕ)^4*10000000000000000^17 ≤ 10035023986929399^17*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25374253369716631023 25000000000000000000 10035023986929399 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10035023986929399/10000000000000000 : ℝ)) (X := (25374253369716631023/25000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(17561739843631/3160900000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(2182780885721/395112500000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (31609/100000 : ℝ)) (alpha := (17561739843631/3160900000000000 : ℝ)) (beta := (2182780885721/395112500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (31609/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(17561739843631/3160900000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(2182780885721/395112500000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-316668271/1000000000 : ℝ)*X 0 0+(3166685541/10000000000 : ℝ)*X 0 1+(-3169574777/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308056_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((316668271/1000000000 : ℝ)*X 1 0+(-3166685541/10000000000 : ℝ)*X 1 1+(-3169574777/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308056_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5573610017/10000000000 : ℝ)*X 2 0+(5573612471/10000000000 : ℝ)*X 2 1+(1233929459/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308056_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-2712032083/10000000000 : ℝ)*X 0 0+(2347291013/10000000000 : ℝ)*X 0 1+(-3657239057/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308056_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((10848129/40000000 : ℝ)*X 1 0+(-1173645579/5000000000 : ℝ)*X 1 1+(-114288717/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308056_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((4437307327/10000000000 : ℝ)*X 2 0+(6828482427/10000000000 : ℝ)*X 2 1+(911406371/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308056_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_12 : ((1148522483/2500000000 : ℝ)*X 0 0+(1767438001/2500000000 : ℝ)*X 0 1+(-1542353/5000000000 : ℝ)*X 0 2+(1148522483/2500000000 : ℝ)*X 1 0+(1767438001/2500000000 : ℝ)*X 1 1+(-1542353/5000000000 : ℝ)*X 1 2+(1148522483/2500000000 : ℝ)*X 2 0+(1767438001/2500000000 : ℝ)*X 2 1+(-1542353/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308056_s1_s1_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((-1173645531/5000000000 : ℝ)*X 0 0+(542406371/2000000000 : ℝ)*X 0 1+(-7314478249/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308056_s1_s1_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((2347290789/10000000000 : ℝ)*X 1 0+(-135601577/500000000 : ℝ)*X 1 1+(-1828619669/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308056_s1_s1_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((341424113/500000000 : ℝ)*X 2 0+(443730747/1000000000 : ℝ)*X 2 1+(455703223/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308056_s1_s1_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_19 : ((-3703151463/10000000000 : ℝ)*X 0 0+(2822645279/10000000000 : ℝ)*X 0 1+(-6166973867/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308056_s1_s1_19 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((2719060093/10000000000 : ℝ)*X 1 0+(-359956513/1000000000 : ℝ)*X 1 1+(-3168031607/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308056_s1_s1_20 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((5626851137/10000000000 : ℝ)*X 2 0+(1125370131/2000000000 : ℝ)*X 2 1+(26552207/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308056_s1_s1_21 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((69247/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(69247/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (602148191261101514600142771/137448575600000000000000000000000 : ℝ) := by norm_num
    linear_combination (114488819357/40000000000 : ℝ)*(base5) + (137737920597/200000000000 : ℝ)*(base7) + (3949217678869/1000000000000 : ℝ)*(base59) + (96964858209/62500000000 : ℝ)*(base60) + (3406161978831/1000000000000 : ℝ)*(major_s1_0) + (3406161978831/1000000000000 : ℝ)*(major_s1_1) + (3406161978831/1000000000000 : ℝ)*(major_s1_2) + (110993/12500000000 : ℝ)*(sp_s1_0) + (7902603/1000000000000 : ℝ)*(sp_s1_1) + (438863/62500000000 : ℝ)*(sp_s1_2) + (2107881017619/500000000000 : ℝ)*(sp_s1_7) + (105393267873/25000000000 : ℝ)*(sp_s1_8) + (1769496094199/250000000000 : ℝ)*(sp_s1_9) + (6459431/200000000000 : ℝ)*(sp_s1_14) + (2173530880941/1000000000000 : ℝ)*(f.failure) + (2107885457339/500000000000 : ℝ)*(f.sum) + (88574096913753470207/274897151200000000000000000000000 : ℝ)*base62 + (639719322974183/790225000000000000000000000 : ℝ)*base65 + (146899541976193/1242400000000000000000000000 : ℝ)*base67 + (1387686050723611/3160900000000000000000000000 : ℝ)*base68 + (258293281564469870377/274897151200000000000000000000000 : ℝ)*base71 + (151122945354593/1242400000000000000000000000 : ℝ)*base73 + (3422580166342111/8696800000000000000000000000 : ℝ)*base74 + (4157021823323871/8696800000000000000000000000 : ℝ)*base76 + (52674063604447/621200000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (45051/100000000000000000 : ℝ)*base87 + (45051/100000000000000000 : ℝ)*base89 + (45051/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(69247/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(69247/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (151116204715492925716961913/34362143900000000000000000000000 : ℝ) := by norm_num
    linear_combination (2862220234593/1000000000000 : ℝ)*(base5) + (344344805859/500000000000 : ℝ)*(base7) + (3949217001403/1000000000000 : ℝ)*(base59) + (2397672397571/1000000000000 : ℝ)*(base60) + (851540393603/250000000000 : ℝ)*(major_s1_0) + (851540393603/250000000000 : ℝ)*(major_s1_1) + (851540393603/250000000000 : ℝ)*(major_s1_2) + (1800787/200000000000 : ℝ)*(sp_s1_0) + (10849603/1000000000000 : ℝ)*(sp_s1_1) + (661637/125000000000 : ℝ)*(sp_s1_2) + (13314151/500000000000 : ℝ)*(sp_s1_7) + (4215734720689/1000000000000 : ℝ)*(sp_s1_13) + (4215759503323/1000000000000 : ℝ)*(sp_s1_14) + (3538992647211/500000000000 : ℝ)*(sp_s1_15) + (1086765311437/500000000000 : ℝ)*(f.failure) + (2107885176463/500000000000 : ℝ)*(f.sum) + (12172538848335834011/68724287800000000000000000000000 : ℝ)*base62 + (21694443661517/98778125000000000000000000 : ℝ)*base65 + (144282419793609/310600000000000000000000000 : ℝ)*base67 + (846061816269951/1580450000000000000000000000 : ℝ)*base68 + (39704415896261475561/68724287800000000000000000000000 : ℝ)*base71 + (142446662940469/310600000000000000000000000 : ℝ)*base73 + (285717610956563/2174200000000000000000000000 : ℝ)*base74 + (367301466430243/2174200000000000000000000000 : ℝ)*base76 + (3670356370411/155300000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (3707/50000000000000000 : ℝ)*base87 + (3707/50000000000000000 : ℝ)*base89 + (3707/50000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-1359/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-1359/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (406365008979479527802944281/137448575600000000000000000000000 : ℝ) := by norm_num
    linear_combination (20447698193/20000000000 : ℝ)*(base5) + (58713/100000000000 : ℝ)*(base7) + (468289/100000000000 : ℝ)*(base16) + (36892925073/1000000000000 : ℝ)*(base49) + (195488720181/200000000000 : ℝ)*(base59) + (1602220072069/1000000000000 : ℝ)*(major_s1_0) + (1602220072069/1000000000000 : ℝ)*(major_s1_1) + (1602220072069/1000000000000 : ℝ)*(major_s1_2) + (45658939/1000000000000 : ℝ)*(sp_s1_1) + (20021827/1000000000000 : ℝ)*(sp_s1_12) + (5020833/250000000000 : ℝ)*(sp_s1_15) + (2182034453651/1000000000000 : ℝ)*(sp_s1_19) + (2181984111823/1000000000000 : ℝ)*(sp_s1_20) + (3204399279969/1000000000000 : ℝ)*(sp_s1_21) + (1022404344347/1000000000000 : ℝ)*(f.failure) + (2182034453651/1000000000000 : ℝ)*(f.sum) + (36671894499955977733/274897151200000000000000000000000 : ℝ)*base62 + (168205312625161/1580450000000000000000000000 : ℝ)*base64 + (24545644419547/1242400000000000000000000000 : ℝ)*base67 + (2030552945729909/3160900000000000000000000000 : ℝ)*base68 + (182586468017384301603/274897151200000000000000000000000 : ℝ)*base71 + (972621570322187/1242400000000000000000000000 : ℝ)*base73 + (4650203297717989/8696800000000000000000000000 : ℝ)*base74 + (4724561116872069/8696800000000000000000000000 : ℝ)*base76 + (216789070167013/621200000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (62717/100000000000000000 : ℝ)*base87 + (62717/100000000000000000 : ℝ)*base89 + (62717/100000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((10871/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10871/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10871/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10871/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-31609/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-31609/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((69247/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(69247/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(69247/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(69247/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-1359/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-1359/20000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c308056_s1 p hpa hpb X hX hprev0

#print axioms solution
