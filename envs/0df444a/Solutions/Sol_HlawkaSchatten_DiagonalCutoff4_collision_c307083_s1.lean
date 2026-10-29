-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c307083_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:17:13.115725+00:00
-- url     : https://prove2.me/submissions/6d2e64f0-035b-4d69-b8cc-ef30f20e77da

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
theorem collision_support_c307083_s1_s1_0 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-949029949/5000000000 : ℝ)*x 0 + (5037027431/10000000000 : ℝ)*x 1 + (5689274801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (949029949/5000000000 : ℝ)^17 ≤ (11382860812519/100000000000000 : ℝ)^13 := by
    have hnat : (949029949 : ℕ)^17*100000000000000^13 ≤ 11382860812519^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      949029949 5000000000 11382860812519 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5037027431/10000000000 : ℝ)^17 ≤ (1274634489663/3125000000000 : ℝ)^13 := by
    have hnat : (5037027431 : ℕ)^17*3125000000000^13 ≤ 1274634489663^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5037027431 10000000000 1274634489663 3125000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5689274801/10000000000 : ℝ)^17 ≤ (47828835507533/100000000000000 : ℝ)^13 := by
    have hnat : (5689274801 : ℕ)^17*100000000000000^13 ≤ 47828835507533^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5689274801 10000000000 47828835507533 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-949029949/5000000000 : ℝ), (5037027431/10000000000 : ℝ), (5689274801/10000000000 : ℝ)] ![(11382860812519/100000000000000 : ℝ), (1274634489663/3125000000000 : ℝ), (47828835507533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-949029949/5000000000 : ℝ)|^17 ≤ (11382860812519/100000000000000 : ℝ)^13
        have hw : |(-949029949/5000000000 : ℝ)|=(949029949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5037027431/10000000000 : ℝ)|^17 ≤ (1274634489663/3125000000000 : ℝ)^13
        have hw : |(5037027431/10000000000 : ℝ)|=(5037027431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5689274801/10000000000 : ℝ)|^17 ≤ (47828835507533/100000000000000 : ℝ)^13
        have hw : |(5689274801/10000000000 : ℝ)|=(5689274801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307083_s1_s1_2 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3549999101/10000000000 : ℝ)*x 0 + (3461534639/5000000000 : ℝ)*x 1 + (-2021779997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3549999101/10000000000 : ℝ)^17 ≤ (25812907983257/100000000000000 : ℝ)^13 := by
    have hnat : (3549999101 : ℕ)^17*100000000000000^13 ≤ 25812907983257^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3549999101 10000000000 25812907983257 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3461534639/5000000000 : ℝ)^17 ≤ (30912192799037/50000000000000 : ℝ)^13 := by
    have hnat : (3461534639 : ℕ)^17*50000000000000^13 ≤ 30912192799037^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3461534639 5000000000 30912192799037 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2021779997/10000000000 : ℝ)^17 ≤ (193167287581/1562500000000 : ℝ)^13 := by
    have hnat : (2021779997 : ℕ)^17*1562500000000^13 ≤ 193167287581^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2021779997 10000000000 193167287581 1562500000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3549999101/10000000000 : ℝ), (3461534639/5000000000 : ℝ), (-2021779997/10000000000 : ℝ)] ![(25812907983257/100000000000000 : ℝ), (30912192799037/50000000000000 : ℝ), (193167287581/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3549999101/10000000000 : ℝ)|^17 ≤ (25812907983257/100000000000000 : ℝ)^13
        have hw : |(3549999101/10000000000 : ℝ)|=(3549999101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3461534639/5000000000 : ℝ)|^17 ≤ (30912192799037/50000000000000 : ℝ)^13
        have hw : |(3461534639/5000000000 : ℝ)|=(3461534639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2021779997/10000000000 : ℝ)|^17 ≤ (193167287581/1562500000000 : ℝ)^13
        have hw : |(-2021779997/10000000000 : ℝ)|=(2021779997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307083_s1_s1_6 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3157562891/10000000000 : ℝ)*x 0 + (932053713/2000000000 : ℝ)*x 1 + (5057762023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3157562891/10000000000 : ℝ)^17 ≤ (4429314004187/20000000000000 : ℝ)^13 := by
    have hnat : (3157562891 : ℕ)^17*20000000000000^13 ≤ 4429314004187^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3157562891 10000000000 4429314004187 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (932053713/2000000000 : ℝ)^17 ≤ (36845422744297/100000000000000 : ℝ)^13 := by
    have hnat : (932053713 : ℕ)^17*100000000000000^13 ≤ 36845422744297^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      932053713 2000000000 36845422744297 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5057762023/10000000000 : ℝ)^17 ≤ (205040036113/500000000000 : ℝ)^13 := by
    have hnat : (5057762023 : ℕ)^17*500000000000^13 ≤ 205040036113^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5057762023 10000000000 205040036113 500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3157562891/10000000000 : ℝ), (932053713/2000000000 : ℝ), (5057762023/10000000000 : ℝ)] ![(4429314004187/20000000000000 : ℝ), (36845422744297/100000000000000 : ℝ), (205040036113/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3157562891/10000000000 : ℝ)|^17 ≤ (4429314004187/20000000000000 : ℝ)^13
        have hw : |(3157562891/10000000000 : ℝ)|=(3157562891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(932053713/2000000000 : ℝ)|^17 ≤ (36845422744297/100000000000000 : ℝ)^13
        have hw : |(932053713/2000000000 : ℝ)|=(932053713/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5057762023/10000000000 : ℝ)|^17 ≤ (205040036113/500000000000 : ℝ)^13
        have hw : |(5057762023/10000000000 : ℝ)|=(5057762023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307083_s1_s1_7 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2105999/8000000 : ℝ)*x 0 + (1840458711/5000000000 : ℝ)*x 1 + (6372605427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2105999/8000000 : ℝ)^17 ≤ (8729511143669/50000000000000 : ℝ)^13 := by
    have hnat : (2105999 : ℕ)^17*50000000000000^13 ≤ 8729511143669^13*8000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105999 8000000 8729511143669 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1840458711/5000000000 : ℝ)^17 ≤ (27064754840837/100000000000000 : ℝ)^13 := by
    have hnat : (1840458711 : ℕ)^17*100000000000000^13 ≤ 27064754840837^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1840458711 5000000000 27064754840837 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6372605427/10000000000 : ℝ)^17 ≤ (27738111431911/50000000000000 : ℝ)^13 := by
    have hnat : (6372605427 : ℕ)^17*50000000000000^13 ≤ 27738111431911^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6372605427 10000000000 27738111431911 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2105999/8000000 : ℝ), (1840458711/5000000000 : ℝ), (6372605427/10000000000 : ℝ)] ![(8729511143669/50000000000000 : ℝ), (27064754840837/100000000000000 : ℝ), (27738111431911/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2105999/8000000 : ℝ)|^17 ≤ (8729511143669/50000000000000 : ℝ)^13
        have hw : |(-2105999/8000000 : ℝ)|=(2105999/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1840458711/5000000000 : ℝ)|^17 ≤ (27064754840837/100000000000000 : ℝ)^13
        have hw : |(1840458711/5000000000 : ℝ)|=(1840458711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6372605427/10000000000 : ℝ)|^17 ≤ (27738111431911/50000000000000 : ℝ)^13
        have hw : |(6372605427/10000000000 : ℝ)|=(6372605427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307083_s1_s1_8 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (179111537/312500000 : ℝ)*x 0 + (45073217/10000000000 : ℝ)*x 1 + (1206205229/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (179111537/312500000 : ℝ)^17 ≤ (12073583084777/25000000000000 : ℝ)^13 := by
    have hnat : (179111537 : ℕ)^17*25000000000000^13 ≤ 12073583084777^13*312500000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179111537 312500000 12073583084777 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (45073217/10000000000 : ℝ)^17 ≤ (85515992877/100000000000000 : ℝ)^13 := by
    have hnat : (45073217 : ℕ)^17*100000000000000^13 ≤ 85515992877^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45073217 10000000000 85515992877 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1206205229/2000000000 : ℝ)^17 ≤ (1032403033173/2000000000000 : ℝ)^13 := by
    have hnat : (1206205229 : ℕ)^17*2000000000000^13 ≤ 1032403033173^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1206205229 2000000000 1032403033173 2000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(179111537/312500000 : ℝ), (45073217/10000000000 : ℝ), (1206205229/2000000000 : ℝ)] ![(12073583084777/25000000000000 : ℝ), (85515992877/100000000000000 : ℝ), (1032403033173/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(179111537/312500000 : ℝ)|^17 ≤ (12073583084777/25000000000000 : ℝ)^13
        have hw : |(179111537/312500000 : ℝ)|=(179111537/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(45073217/10000000000 : ℝ)|^17 ≤ (85515992877/100000000000000 : ℝ)^13
        have hw : |(45073217/10000000000 : ℝ)|=(45073217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1206205229/2000000000 : ℝ)|^17 ≤ (1032403033173/2000000000000 : ℝ)^13
        have hw : |(1206205229/2000000000 : ℝ)|=(1206205229/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307083_s1_s1_9 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (726797093/5000000000 : ℝ)*x 0 + (8655583633/10000000000 : ℝ)*x 1 + (-402378703/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (726797093/5000000000 : ℝ)^17 ≤ (8030329870357/100000000000000 : ℝ)^13 := by
    have hnat : (726797093 : ℕ)^17*100000000000000^13 ≤ 8030329870357^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      726797093 5000000000 8030329870357 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8655583633/10000000000 : ℝ)^17 ≤ (41397387324133/50000000000000 : ℝ)^13 := by
    have hnat : (8655583633 : ℕ)^17*50000000000000^13 ≤ 41397387324133^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8655583633 10000000000 41397387324133 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (402378703/2500000000 : ℝ)^17 ≤ (2293723866123/25000000000000 : ℝ)^13 := by
    have hnat : (402378703 : ℕ)^17*25000000000000^13 ≤ 2293723866123^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402378703 2500000000 2293723866123 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(726797093/5000000000 : ℝ), (8655583633/10000000000 : ℝ), (-402378703/2500000000 : ℝ)] ![(8030329870357/100000000000000 : ℝ), (41397387324133/50000000000000 : ℝ), (2293723866123/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(726797093/5000000000 : ℝ)|^17 ≤ (8030329870357/100000000000000 : ℝ)^13
        have hw : |(726797093/5000000000 : ℝ)|=(726797093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8655583633/10000000000 : ℝ)|^17 ≤ (41397387324133/50000000000000 : ℝ)^13
        have hw : |(8655583633/10000000000 : ℝ)|=(8655583633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-402378703/2500000000 : ℝ)|^17 ≤ (2293723866123/25000000000000 : ℝ)^13
        have hw : |(-402378703/2500000000 : ℝ)|=(402378703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307083_s1_s1_13 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2768414407/10000000000 : ℝ)*x 0 + (3000614293/5000000000 : ℝ)*x 1 + (1994583151/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2768414407/10000000000 : ℝ)^17 ≤ (18647039933079/100000000000000 : ℝ)^13 := by
    have hnat : (2768414407 : ℕ)^17*100000000000000^13 ≤ 18647039933079^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2768414407 10000000000 18647039933079 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3000614293/5000000000 : ℝ)^17 ≤ (51286891261067/100000000000000 : ℝ)^13 := by
    have hnat : (3000614293 : ℕ)^17*100000000000000^13 ≤ 51286891261067^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3000614293 5000000000 51286891261067 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1994583151/5000000000 : ℝ)^17 ≤ (6013213759471/20000000000000 : ℝ)^13 := by
    have hnat : (1994583151 : ℕ)^17*20000000000000^13 ≤ 6013213759471^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1994583151 5000000000 6013213759471 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2768414407/10000000000 : ℝ), (3000614293/5000000000 : ℝ), (1994583151/5000000000 : ℝ)] ![(18647039933079/100000000000000 : ℝ), (51286891261067/100000000000000 : ℝ), (6013213759471/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2768414407/10000000000 : ℝ)|^17 ≤ (18647039933079/100000000000000 : ℝ)^13
        have hw : |(2768414407/10000000000 : ℝ)|=(2768414407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3000614293/5000000000 : ℝ)|^17 ≤ (51286891261067/100000000000000 : ℝ)^13
        have hw : |(3000614293/5000000000 : ℝ)|=(3000614293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1994583151/5000000000 : ℝ)|^17 ≤ (6013213759471/20000000000000 : ℝ)^13
        have hw : |(1994583151/5000000000 : ℝ)|=(1994583151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307083_s1_s1_14 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-247774877/5000000000 : ℝ)*x 0 + (2728959351/10000000000 : ℝ)*x 1 + (262805987/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (247774877/5000000000 : ℝ)^17 ≤ (491491105413/25000000000000 : ℝ)^13 := by
    have hnat : (247774877 : ℕ)^17*25000000000000^13 ≤ 491491105413^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      247774877 5000000000 491491105413 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2728959351/10000000000 : ℝ)^17 ≤ (2287534831499/12500000000000 : ℝ)^13 := by
    have hnat : (2728959351 : ℕ)^17*12500000000000^13 ≤ 2287534831499^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728959351 10000000000 2287534831499 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262805987/312500000 : ℝ)^17 ≤ (3986687845863/5000000000000 : ℝ)^13 := by
    have hnat : (262805987 : ℕ)^17*5000000000000^13 ≤ 3986687845863^13*312500000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262805987 312500000 3986687845863 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-247774877/5000000000 : ℝ), (2728959351/10000000000 : ℝ), (262805987/312500000 : ℝ)] ![(491491105413/25000000000000 : ℝ), (2287534831499/12500000000000 : ℝ), (3986687845863/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-247774877/5000000000 : ℝ)|^17 ≤ (491491105413/25000000000000 : ℝ)^13
        have hw : |(-247774877/5000000000 : ℝ)|=(247774877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2728959351/10000000000 : ℝ)|^17 ≤ (2287534831499/12500000000000 : ℝ)^13
        have hw : |(2728959351/10000000000 : ℝ)|=(2728959351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262805987/312500000 : ℝ)|^17 ≤ (3986687845863/5000000000000 : ℝ)^13
        have hw : |(262805987/312500000 : ℝ)|=(262805987/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307083_s1_s1_15 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (8862849263/10000000000 : ℝ)*x 0 + (27281/500000000 : ℝ)*x 1 + (2296361397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8862849263/10000000000 : ℝ)^17 ≤ (1067461211813/1250000000000 : ℝ)^13 := by
    have hnat : (8862849263 : ℕ)^17*1250000000000^13 ≤ 1067461211813^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8862849263 10000000000 1067461211813 1250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27281/500000000 : ℝ)^17 ≤ (66543283/25000000000000 : ℝ)^13 := by
    have hnat : (27281 : ℕ)^17*25000000000000^13 ≤ 66543283^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27281 500000000 66543283 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2296361397/10000000000 : ℝ)^17 ≤ (1460283687109/10000000000000 : ℝ)^13 := by
    have hnat : (2296361397 : ℕ)^17*10000000000000^13 ≤ 1460283687109^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2296361397 10000000000 1460283687109 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8862849263/10000000000 : ℝ), (27281/500000000 : ℝ), (2296361397/10000000000 : ℝ)] ![(1067461211813/1250000000000 : ℝ), (66543283/25000000000000 : ℝ), (1460283687109/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8862849263/10000000000 : ℝ)|^17 ≤ (1067461211813/1250000000000 : ℝ)^13
        have hw : |(8862849263/10000000000 : ℝ)|=(8862849263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(27281/500000000 : ℝ)|^17 ≤ (66543283/25000000000000 : ℝ)^13
        have hw : |(27281/500000000 : ℝ)|=(27281/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2296361397/10000000000 : ℝ)|^17 ≤ (1460283687109/10000000000000 : ℝ)^13
        have hw : |(2296361397/10000000000 : ℝ)|=(2296361397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307083_s1_s1_16 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4761369187/10000000000 : ℝ)*x 0 + (649891181/1000000000 : ℝ)*x 1 + (-1040668359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4761369187/10000000000 : ℝ)^17 ≤ (18947086283047/50000000000000 : ℝ)^13 := by
    have hnat : (4761369187 : ℕ)^17*50000000000000^13 ≤ 18947086283047^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4761369187 10000000000 18947086283047 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (649891181/1000000000 : ℝ)^17 ≤ (56918461073661/100000000000000 : ℝ)^13 := by
    have hnat : (649891181 : ℕ)^17*100000000000000^13 ≤ 56918461073661^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649891181 1000000000 56918461073661 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1040668359/10000000000 : ℝ)^17 ≤ (2593683169567/50000000000000 : ℝ)^13 := by
    have hnat : (1040668359 : ℕ)^17*50000000000000^13 ≤ 2593683169567^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040668359 10000000000 2593683169567 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4761369187/10000000000 : ℝ), (649891181/1000000000 : ℝ), (-1040668359/10000000000 : ℝ)] ![(18947086283047/50000000000000 : ℝ), (56918461073661/100000000000000 : ℝ), (2593683169567/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4761369187/10000000000 : ℝ)|^17 ≤ (18947086283047/50000000000000 : ℝ)^13
        have hw : |(4761369187/10000000000 : ℝ)|=(4761369187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(649891181/1000000000 : ℝ)|^17 ≤ (56918461073661/100000000000000 : ℝ)^13
        have hw : |(649891181/1000000000 : ℝ)|=(649891181/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1040668359/10000000000 : ℝ)|^17 ≤ (2593683169567/50000000000000 : ℝ)^13
        have hw : |(-1040668359/10000000000 : ℝ)|=(1040668359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307083_s1_s1_20 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1452251279/5000000000 : ℝ)*x 0 + (1626332501/5000000000 : ℝ)*x 1 + (6516716107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1452251279/5000000000 : ℝ)^17 ≤ (19854688375099/100000000000000 : ℝ)^13 := by
    have hnat : (1452251279 : ℕ)^17*100000000000000^13 ≤ 19854688375099^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1452251279 5000000000 19854688375099 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1626332501/5000000000 : ℝ)^17 ≤ (11511426292563/50000000000000 : ℝ)^13 := by
    have hnat : (1626332501 : ℕ)^17*50000000000000^13 ≤ 11511426292563^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1626332501 5000000000 11511426292563 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6516716107/10000000000 : ℝ)^17 ≤ (28561229509877/50000000000000 : ℝ)^13 := by
    have hnat : (6516716107 : ℕ)^17*50000000000000^13 ≤ 28561229509877^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6516716107 10000000000 28561229509877 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1452251279/5000000000 : ℝ), (1626332501/5000000000 : ℝ), (6516716107/10000000000 : ℝ)] ![(19854688375099/100000000000000 : ℝ), (11511426292563/50000000000000 : ℝ), (28561229509877/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1452251279/5000000000 : ℝ)|^17 ≤ (19854688375099/100000000000000 : ℝ)^13
        have hw : |(1452251279/5000000000 : ℝ)|=(1452251279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1626332501/5000000000 : ℝ)|^17 ≤ (11511426292563/50000000000000 : ℝ)^13
        have hw : |(1626332501/5000000000 : ℝ)|=(1626332501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6516716107/10000000000 : ℝ)|^17 ≤ (28561229509877/50000000000000 : ℝ)^13
        have hw : |(6516716107/10000000000 : ℝ)|=(6516716107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307083_s1_s1_21 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-37387421/250000000 : ℝ)*x 0 + (16285819/25000000 : ℝ)*x 1 + (4438598491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (37387421/250000000 : ℝ)^17 ≤ (1041797614777/12500000000000 : ℝ)^13 := by
    have hnat : (37387421 : ℕ)^17*12500000000000^13 ≤ 1041797614777^13*250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37387421 250000000 1041797614777 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16285819/25000000 : ℝ)^17 ≤ (11419016406059/20000000000000 : ℝ)^13 := by
    have hnat : (16285819 : ℕ)^17*20000000000000^13 ≤ 11419016406059^13*25000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16285819 25000000 11419016406059 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4438598491/10000000000 : ℝ)^17 ≤ (4321317129543/12500000000000 : ℝ)^13 := by
    have hnat : (4438598491 : ℕ)^17*12500000000000^13 ≤ 4321317129543^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4438598491 10000000000 4321317129543 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-37387421/250000000 : ℝ), (16285819/25000000 : ℝ), (4438598491/10000000000 : ℝ)] ![(1041797614777/12500000000000 : ℝ), (11419016406059/20000000000000 : ℝ), (4321317129543/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-37387421/250000000 : ℝ)|^17 ≤ (1041797614777/12500000000000 : ℝ)^13
        have hw : |(-37387421/250000000 : ℝ)|=(37387421/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(16285819/25000000 : ℝ)|^17 ≤ (11419016406059/20000000000000 : ℝ)^13
        have hw : |(16285819/25000000 : ℝ)|=(16285819/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4438598491/10000000000 : ℝ)|^17 ≤ (4321317129543/12500000000000 : ℝ)^13
        have hw : |(4438598491/10000000000 : ℝ)|=(4438598491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307083_s1_s1_22 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (8530771749/10000000000 : ℝ)*x 0 + (2207333/5000000000 : ℝ)*x 1 + (2781103573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8530771749/10000000000 : ℝ)^17 ≤ (8123701545467/10000000000000 : ℝ)^13 := by
    have hnat : (8530771749 : ℕ)^17*10000000000000^13 ≤ 8123701545467^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8530771749 10000000000 8123701545467 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2207333/5000000000 : ℝ)^17 ≤ (4097875213/100000000000000 : ℝ)^13 := by
    have hnat : (2207333 : ℕ)^17*100000000000000^13 ≤ 4097875213^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2207333 5000000000 4097875213 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2781103573/10000000000 : ℝ)^17 ≤ (937944332813/5000000000000 : ℝ)^13 := by
    have hnat : (2781103573 : ℕ)^17*5000000000000^13 ≤ 937944332813^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2781103573 10000000000 937944332813 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8530771749/10000000000 : ℝ), (2207333/5000000000 : ℝ), (2781103573/10000000000 : ℝ)] ![(8123701545467/10000000000000 : ℝ), (4097875213/100000000000000 : ℝ), (937944332813/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8530771749/10000000000 : ℝ)|^17 ≤ (8123701545467/10000000000000 : ℝ)^13
        have hw : |(8530771749/10000000000 : ℝ)|=(8530771749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2207333/5000000000 : ℝ)|^17 ≤ (4097875213/100000000000000 : ℝ)^13
        have hw : |(2207333/5000000000 : ℝ)|=(2207333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2781103573/10000000000 : ℝ)|^17 ≤ (937944332813/5000000000000 : ℝ)^13
        have hw : |(2781103573/10000000000 : ℝ)|=(2781103573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307083_s1_s1_23 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (34205219/156250000 : ℝ)*x 0 + (3928020547/5000000000 : ℝ)*x 1 + (-535833337/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34205219/156250000 : ℝ)^17 ≤ (13717634466991/100000000000000 : ℝ)^13 := by
    have hnat : (34205219 : ℕ)^17*100000000000000^13 ≤ 13717634466991^13*156250000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34205219 156250000 13717634466991 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3928020547/5000000000 : ℝ)^17 ≤ (36469411042481/50000000000000 : ℝ)^13 := by
    have hnat : (3928020547 : ℕ)^17*50000000000000^13 ≤ 36469411042481^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3928020547 5000000000 36469411042481 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (535833337/2500000000 : ℝ)^17 ≤ (13343543440949/100000000000000 : ℝ)^13 := by
    have hnat : (535833337 : ℕ)^17*100000000000000^13 ≤ 13343543440949^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535833337 2500000000 13343543440949 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34205219/156250000 : ℝ), (3928020547/5000000000 : ℝ), (-535833337/2500000000 : ℝ)] ![(13717634466991/100000000000000 : ℝ), (36469411042481/50000000000000 : ℝ), (13343543440949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34205219/156250000 : ℝ)|^17 ≤ (13717634466991/100000000000000 : ℝ)^13
        have hw : |(34205219/156250000 : ℝ)|=(34205219/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3928020547/5000000000 : ℝ)|^17 ≤ (36469411042481/50000000000000 : ℝ)^13
        have hw : |(3928020547/5000000000 : ℝ)|=(3928020547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-535833337/2500000000 : ℝ)|^17 ≤ (13343543440949/100000000000000 : ℝ)^13
        have hw : |(-535833337/2500000000 : ℝ)|=(535833337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307083_s1_s1_27 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (381269879/625000000 : ℝ)*x 0 + (112946811/312500000 : ℝ)*x 1 + (3051289487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (381269879/625000000 : ℝ)^17 ≤ (52397080371493/100000000000000 : ℝ)^13 := by
    have hnat : (381269879 : ℕ)^17*100000000000000^13 ≤ 52397080371493^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      381269879 625000000 52397080371493 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (112946811/312500000 : ℝ)^17 ≤ (13212996675683/50000000000000 : ℝ)^13 := by
    have hnat : (112946811 : ℕ)^17*50000000000000^13 ≤ 13212996675683^13*312500000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112946811 312500000 13212996675683 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3051289487/10000000000 : ℝ)^17 ≤ (5294231564273/25000000000000 : ℝ)^13 := by
    have hnat : (3051289487 : ℕ)^17*25000000000000^13 ≤ 5294231564273^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3051289487 10000000000 5294231564273 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(381269879/625000000 : ℝ), (112946811/312500000 : ℝ), (3051289487/10000000000 : ℝ)] ![(52397080371493/100000000000000 : ℝ), (13212996675683/50000000000000 : ℝ), (5294231564273/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(381269879/625000000 : ℝ)|^17 ≤ (52397080371493/100000000000000 : ℝ)^13
        have hw : |(381269879/625000000 : ℝ)|=(381269879/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(112946811/312500000 : ℝ)|^17 ≤ (13212996675683/50000000000000 : ℝ)^13
        have hw : |(112946811/312500000 : ℝ)|=(112946811/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3051289487/10000000000 : ℝ)|^17 ≤ (5294231564273/25000000000000 : ℝ)^13
        have hw : |(3051289487/10000000000 : ℝ)|=(3051289487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c307083_s1 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((8111/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8111/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((17197/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(17197/20000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(90367/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(90367/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((31497/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(31497/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((7899/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(7899/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(71517/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(71517/100000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4817/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4817/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (92559/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (8111/10000 : ℝ) ^ (135/32 : ℝ) ≤ (8268707447634510061/20000000000000000000 : ℝ) := by
    have hpowers : (8111/10000 : ℝ)^135 ≤ (8268707447634510061/20000000000000000000 : ℝ)^32 := by
      have hnat : (8111 : ℕ)^135*20000000000000000000^32 ≤ 8268707447634510061^32*10000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8111 10000 8268707447634510061 20000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8111/10000 : ℝ)) (X := (8268707447634510061/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (28268707447634510061/20000000000000000000 : ℝ) ≤ (10854778537561531/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (28268707447634510061/20000000000000000000 : ℝ)^32 ≤ (10854778537561531/10000000000000000 : ℝ)^135 := by
      have hnat : (28268707447634510061 : ℕ)^32*10000000000000000^135 ≤ 10854778537561531^135*20000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28268707447634510061 20000000000000000000 10854778537561531 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10854778537561531/10000000000000000 : ℝ)) (X := (28268707447634510061/20000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (18268707447634510061/10000000000000000000 : ℝ) ≤ (2883861871785207/2500000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (18268707447634510061/10000000000000000000 : ℝ)^32 ≤ (2883861871785207/2500000000000000 : ℝ)^135 := by
      have hnat : (18268707447634510061 : ℕ)^32*2500000000000000^135 ≤ 2883861871785207^135*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18268707447634510061 10000000000000000000 2883861871785207 2500000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2883861871785207/2500000000000000 : ℝ)) (X := (18268707447634510061/10000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(854778537561531/8111000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(680668949579297/8111000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (8111/10000 : ℝ)) (alpha := (854778537561531/8111000000000000 : ℝ)) (beta := (680668949579297/8111000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (8111/10000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(854778537561531/8111000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(680668949579297/8111000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (17197/20000 : ℝ) ^ (135/32 : ℝ) ≤ (52886612090174641107/100000000000000000000 : ℝ) := by
    have hpowers : (17197/20000 : ℝ)^135 ≤ (52886612090174641107/100000000000000000000 : ℝ)^32 := by
      have hnat : (17197 : ℕ)^135*100000000000000000000^32 ≤ 52886612090174641107^32*20000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17197 20000 52886612090174641107 100000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17197/20000 : ℝ)) (X := (52886612090174641107/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (152886612090174641107/100000000000000000000 : ℝ) ≤ (2764664261398157/2500000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (152886612090174641107/100000000000000000000 : ℝ)^32 ≤ (2764664261398157/2500000000000000 : ℝ)^135 := by
      have hnat : (152886612090174641107 : ℕ)^32*2500000000000000^135 ≤ 2764664261398157^135*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        152886612090174641107 100000000000000000000 2764664261398157 2500000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2764664261398157/2500000000000000 : ℝ)) (X := (152886612090174641107/100000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (102886612090174641107/50000000000000000000 : ℝ) ≤ (5932732565278081/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (102886612090174641107/50000000000000000000 : ℝ)^32 ≤ (5932732565278081/5000000000000000 : ℝ)^135 := by
      have hnat : (102886612090174641107 : ℕ)^32*5000000000000000^135 ≤ 5932732565278081^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102886612090174641107 50000000000000000000 5932732565278081 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5932732565278081/5000000000000000 : ℝ)) (X := (102886612090174641107/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(264664261398157/2149625000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(403404042481767/4299250000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (17197/20000 : ℝ)) (alpha := (264664261398157/2149625000000000 : ℝ)) (beta := (403404042481767/4299250000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (17197/20000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(264664261398157/2149625000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(403404042481767/4299250000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (90367/100000 : ℝ) ^ (135/32 : ℝ) ≤ (3261268994669466549/5000000000000000000 : ℝ) := by
    have hpowers : (90367/100000 : ℝ)^135 ≤ (3261268994669466549/5000000000000000000 : ℝ)^32 := by
      have hnat : (90367 : ℕ)^135*5000000000000000000^32 ≤ 3261268994669466549^32*100000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        90367 100000 3261268994669466549 5000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (90367/100000 : ℝ)) (X := (3261268994669466549/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (8261268994669466549/5000000000000000000 : ℝ) ≤ (351999697699261/312500000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (8261268994669466549/5000000000000000000 : ℝ)^32 ≤ (351999697699261/312500000000000 : ℝ)^135 := by
      have hnat : (8261268994669466549 : ℕ)^32*312500000000000^135 ≤ 351999697699261^135*5000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8261268994669466549 5000000000000000000 351999697699261 312500000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (351999697699261/312500000000000 : ℝ)) (X := (8261268994669466549/5000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (5761268994669466549/2500000000000000000 : ℝ) ≤ (6094168434488931/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (5761268994669466549/2500000000000000000 : ℝ)^32 ≤ (6094168434488931/5000000000000000 : ℝ)^135 := by
      have hnat : (5761268994669466549 : ℕ)^32*5000000000000000^135 ≤ 6094168434488931^135*2500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5761268994669466549 2500000000000000000 6094168434488931 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6094168434488931/5000000000000000 : ℝ)) (X := (5761268994669466549/2500000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(39499697699261/282396875000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(92434654260151/903670000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (90367/100000 : ℝ)) (alpha := (39499697699261/282396875000000 : ℝ)) (beta := (92434654260151/903670000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (90367/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(39499697699261/282396875000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(92434654260151/903670000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-949029949/5000000000 : ℝ)*X 0 0+(5037027431/10000000000 : ℝ)*X 0 1+(5689274801/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307083_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((3549999101/10000000000 : ℝ)*X 2 0+(3461534639/5000000000 : ℝ)*X 2 1+(-2021779997/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307083_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3157562891/10000000000 : ℝ)*X 0 0+(932053713/2000000000 : ℝ)*X 0 1+(5057762023/10000000000 : ℝ)*X 0 2+(3157562891/10000000000 : ℝ)*X 1 0+(932053713/2000000000 : ℝ)*X 1 1+(5057762023/10000000000 : ℝ)*X 1 2+(3157562891/10000000000 : ℝ)*X 2 0+(932053713/2000000000 : ℝ)*X 2 1+(5057762023/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307083_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-2105999/8000000 : ℝ)*X 0 0+(1840458711/5000000000 : ℝ)*X 0 1+(6372605427/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307083_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((179111537/312500000 : ℝ)*X 1 0+(45073217/10000000000 : ℝ)*X 1 1+(1206205229/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307083_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((726797093/5000000000 : ℝ)*X 2 0+(8655583633/10000000000 : ℝ)*X 2 1+(-402378703/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307083_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((2768414407/10000000000 : ℝ)*X 0 0+(3000614293/5000000000 : ℝ)*X 0 1+(1994583151/5000000000 : ℝ)*X 0 2+(2768414407/10000000000 : ℝ)*X 1 0+(3000614293/5000000000 : ℝ)*X 1 1+(1994583151/5000000000 : ℝ)*X 1 2+(2768414407/10000000000 : ℝ)*X 2 0+(3000614293/5000000000 : ℝ)*X 2 1+(1994583151/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307083_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-247774877/5000000000 : ℝ)*X 0 0+(2728959351/10000000000 : ℝ)*X 0 1+(262805987/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307083_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((8862849263/10000000000 : ℝ)*X 1 0+(27281/500000000 : ℝ)*X 1 1+(2296361397/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307083_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((4761369187/10000000000 : ℝ)*X 2 0+(649891181/1000000000 : ℝ)*X 2 1+(-1040668359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307083_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((1452251279/5000000000 : ℝ)*X 0 0+(1626332501/5000000000 : ℝ)*X 0 1+(6516716107/10000000000 : ℝ)*X 0 2+(1452251279/5000000000 : ℝ)*X 1 0+(1626332501/5000000000 : ℝ)*X 1 1+(6516716107/10000000000 : ℝ)*X 1 2+(1452251279/5000000000 : ℝ)*X 2 0+(1626332501/5000000000 : ℝ)*X 2 1+(6516716107/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307083_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-37387421/250000000 : ℝ)*X 0 0+(16285819/25000000 : ℝ)*X 0 1+(4438598491/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307083_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((8530771749/10000000000 : ℝ)*X 1 0+(2207333/5000000000 : ℝ)*X 1 1+(2781103573/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307083_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((34205219/156250000 : ℝ)*X 2 0+(3928020547/5000000000 : ℝ)*X 2 1+(-535833337/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307083_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((381269879/625000000 : ℝ)*X 0 0+(112946811/312500000 : ℝ)*X 0 1+(3051289487/10000000000 : ℝ)*X 0 2+(381269879/625000000 : ℝ)*X 1 0+(112946811/312500000 : ℝ)*X 1 1+(3051289487/10000000000 : ℝ)*X 1 2+(381269879/625000000 : ℝ)*X 2 0+(112946811/312500000 : ℝ)*X 2 1+(3051289487/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307083_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((31497/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(31497/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (32573118764398716599968422331107/3151207244047250000000000000000000000 : ℝ) := by norm_num
    linear_combination (709665061707/1000000000000 : ℝ)*(base7) + (1838103/200000000000 : ℝ)*(base23) + (349389041093/1000000000000 : ℝ)*(base49) + (37913694187/200000000000 : ℝ)*(base60) + (1047473766461/500000000000 : ℝ)*(major_s1_0) + (1047473766461/500000000000 : ℝ)*(major_s1_1) + (1047473766461/500000000000 : ℝ)*(major_s1_2) + (43810199/1000000000000 : ℝ)*(sp_s1_0) + (5856653/250000000000 : ℝ)*(sp_s1_6) + (601060924091/250000000000 : ℝ)*(sp_s1_7) + (2404301884749/1000000000000 : ℝ)*(sp_s1_8) + (1202146347117/500000000000 : ℝ)*(sp_s1_9) + (1028662723819/500000000000 : ℝ)*(sp_s1_13) + (14378187/1000000000000 : ℝ)*(sp_s1_14) + (1347683812543/1000000000000 : ℝ)*(f.failure) + (2404301884749/1000000000000 : ℝ)*(f.sum) + (14870915967455024939/48563790593750000000000000000000 : ℝ)*base63 + (12987363085433/225917500000000000000000000 : ℝ)*base64 + (388513496276467/4299250000000000000000000000 : ℝ)*base66 + (1631755404579991/2259175000000000000000000000 : ℝ)*base69 + (13004791296885679547/366483368500000000000000000000000 : ℝ)*base71 + (2412674961626567/4055500000000000000000000000 : ℝ)*base73 + (138178561620997/537406250000000000000000000 : ℝ)*base75 + (2691388047688291/4055500000000000000000000000 : ℝ)*base77 + (590666542176134601/2789697340000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1967/12500000000000000 : ℝ)*base86 + (1967/12500000000000000 : ℝ)*base88 + (1967/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((7899/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(7899/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (78522753534408860171500676745861/6302414488094500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1496656917/3906250000 : ℝ)*(base7) + (4837717/200000000000 : ℝ)*(base33) + (285766453379/500000000000 : ℝ)*(base40) + (160565160931/1000000000000 : ℝ)*(base49) + (221672925747/500000000000 : ℝ)*(base60) + (2171660125049/1000000000000 : ℝ)*(major_s1_0) + (1085842156817/500000000000 : ℝ)*(major_s1_1) + (1085842156817/500000000000 : ℝ)*(major_s1_2) + (11908071/500000000000 : ℝ)*(sp_s1_2) + (2709892799747/1000000000000 : ℝ)*(sp_s1_14) + (2709651404319/1000000000000 : ℝ)*(sp_s1_15) + (135492239751/50000000000 : ℝ)*(sp_s1_16) + (445048225803/250000000000 : ℝ)*(sp_s1_20) + (108603421/500000000000 : ℝ)*(sp_s1_22) + (69852436623/50000000000 : ℝ)*(f.failure) + (2709892799747/1000000000000 : ℝ)*(f.sum) + (5497828425110474521/24281895296875000000000000000000 : ℝ)*base62 + (560388060209173/903670000000000000000000000 : ℝ)*base64 + (93816302132657/134351562500000000000000000 : ℝ)*base66 + (1058882400564999/4518350000000000000000000000 : ℝ)*base69 + (149829524656698136827/732966737000000000000000000000000 : ℝ)*base70 + (812677522191747/8111000000000000000000000000 : ℝ)*base72 + (458989143818491/537406250000000000000000000 : ℝ)*base74 + (6535657093019981/8111000000000000000000000000 : ℝ)*base76 + (6356402476115898937/27896973400000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (263/625000000000000 : ℝ)*base87 + (263/625000000000000 : ℝ)*base89 + (263/625000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(71517/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(71517/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3663854700914999429413587/278969734000000000000000000000 : ℝ) := by norm_num
    linear_combination (98483961583/125000000000 : ℝ)*(base7) + (8037113/1000000000000 : ℝ)*(base11) + (342503069033/1000000000000 : ℝ)*(base40) + (7479526467/62500000000 : ℝ)*(base49) + (18519/125000000000 : ℝ)*(base50) + (227871323057/100000000000 : ℝ)*(major_s1_0) + (227871323057/100000000000 : ℝ)*(major_s1_1) + (227871323057/100000000000 : ℝ)*(major_s1_2) + (97286779/1000000000000 : ℝ)*(sp_s1_2) + (19745651/200000000000 : ℝ)*(sp_s1_9) + (2605349297127/1000000000000 : ℝ)*(sp_s1_21) + (16283483339/6250000000 : ℝ)*(sp_s1_22) + (1302580659603/500000000000 : ℝ)*(sp_s1_23) + (1126886167523/500000000000 : ℝ)*(sp_s1_27) + (732950321191/500000000000 : ℝ)*(f.failure) + (16283483339/6250000000 : ℝ)*(f.sum) + (22663476686358626693/38851032475000000000000000000000 : ℝ)*base62 + (92087867281003/451835000000000000000000000 : ℝ)*base65 + (207619801198819/859850000000000000000000000 : ℝ)*base66 + (5201497318053/28239687500000000000000000 : ℝ)*base69 + (21317621391830302151/73296673700000000000000000000000 : ℝ)*base70 + (232422874167509/811100000000000000000000000 : ℝ)*base73 + (273535298017203/859850000000000000000000000 : ℝ)*base74 + (15373019597363/811100000000000000000000000 : ℝ)*base76 + (943667419068341449/2789697340000000000000000000000 : ℝ)*base78 + (179/6250000000000000 : ℝ)*base86 + (179/6250000000000000 : ℝ)*base88 + (179/6250000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((8111/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8111/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((17197/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(17197/20000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(90367/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(90367/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((31497/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(31497/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((7899/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(7899/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(71517/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(71517/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c307083_s1 p hpa hpb X hX hprev0

#print axioms solution
