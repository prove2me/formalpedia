-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304055_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:45:27.059996+00:00
-- url     : https://prove2.me/submissions/ffaf4cb3-e0cc-4d13-873a-031148016384

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
theorem collision_support_c304055_s2_s2_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (618396517/1250000000 : ℝ)*x 0 + (3178656127/5000000000 : ℝ)*x 1 + (-216206159/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (618396517/1250000000 : ℝ)^133 ≤ (9895999194659/25000000000000 : ℝ)^101 := by
    have hnat : (618396517 : ℕ)^133*25000000000000^101 ≤ 9895999194659^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      618396517 1250000000 9895999194659 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3178656127/5000000000 : ℝ)^133 ≤ (55073714506723/100000000000000 : ℝ)^101 := by
    have hnat : (3178656127 : ℕ)^133*100000000000000^101 ≤ 55073714506723^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3178656127 5000000000 55073714506723 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216206159/2000000000 : ℝ)^133 ≤ (667786087637/12500000000000 : ℝ)^101 := by
    have hnat : (216206159 : ℕ)^133*12500000000000^101 ≤ 667786087637^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216206159 2000000000 667786087637 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(618396517/1250000000 : ℝ), (3178656127/5000000000 : ℝ), (-216206159/2000000000 : ℝ)] ![(9895999194659/25000000000000 : ℝ), (55073714506723/100000000000000 : ℝ), (667786087637/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(618396517/1250000000 : ℝ)|^133 ≤ (9895999194659/25000000000000 : ℝ)^101
        have hw : |(618396517/1250000000 : ℝ)|=(618396517/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3178656127/5000000000 : ℝ)|^133 ≤ (55073714506723/100000000000000 : ℝ)^101
        have hw : |(3178656127/5000000000 : ℝ)|=(3178656127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-216206159/2000000000 : ℝ)|^133 ≤ (667786087637/12500000000000 : ℝ)^101
        have hw : |(-216206159/2000000000 : ℝ)|=(216206159/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s2_s2_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6663704737/10000000000 : ℝ)*x 0 + (474201419/1250000000 : ℝ)*x 1 + (1092786941/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6663704737/10000000000 : ℝ)^133 ≤ (58595371028929/100000000000000 : ℝ)^101 := by
    have hnat : (6663704737 : ℕ)^133*100000000000000^101 ≤ 58595371028929^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6663704737 10000000000 58595371028929 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (474201419/1250000000 : ℝ)^133 ≤ (1395254532909/5000000000000 : ℝ)^101 := by
    have hnat : (474201419 : ℕ)^133*5000000000000^101 ≤ 1395254532909^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      474201419 1250000000 1395254532909 5000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1092786941/5000000000 : ℝ)^133 ≤ (3374884575129/25000000000000 : ℝ)^101 := by
    have hnat : (1092786941 : ℕ)^133*25000000000000^101 ≤ 3374884575129^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092786941 5000000000 3374884575129 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6663704737/10000000000 : ℝ), (474201419/1250000000 : ℝ), (1092786941/5000000000 : ℝ)] ![(58595371028929/100000000000000 : ℝ), (1395254532909/5000000000000 : ℝ), (3374884575129/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6663704737/10000000000 : ℝ)|^133 ≤ (58595371028929/100000000000000 : ℝ)^101
        have hw : |(6663704737/10000000000 : ℝ)|=(6663704737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(474201419/1250000000 : ℝ)|^133 ≤ (1395254532909/5000000000000 : ℝ)^101
        have hw : |(474201419/1250000000 : ℝ)|=(474201419/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1092786941/5000000000 : ℝ)|^133 ≤ (3374884575129/25000000000000 : ℝ)^101
        have hw : |(1092786941/5000000000 : ℝ)|=(1092786941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s2_s2_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-3803661071/10000000000 : ℝ)*x 0 + (2306974117/5000000000 : ℝ)*x 1 + (2296069127/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3803661071/10000000000 : ℝ)^133 ≤ (28002476740733/100000000000000 : ℝ)^101 := by
    have hnat : (3803661071 : ℕ)^133*100000000000000^101 ≤ 28002476740733^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3803661071 10000000000 28002476740733 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2306974117/5000000000 : ℝ)^133 ≤ (451388327467/1250000000000 : ℝ)^101 := by
    have hnat : (2306974117 : ℕ)^133*1250000000000^101 ≤ 451388327467^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2306974117 5000000000 451388327467 1250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2296069127/5000000000 : ℝ)^133 ≤ (4485807130929/12500000000000 : ℝ)^101 := by
    have hnat : (2296069127 : ℕ)^133*12500000000000^101 ≤ 4485807130929^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2296069127 5000000000 4485807130929 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3803661071/10000000000 : ℝ), (2306974117/5000000000 : ℝ), (2296069127/5000000000 : ℝ)] ![(28002476740733/100000000000000 : ℝ), (451388327467/1250000000000 : ℝ), (4485807130929/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3803661071/10000000000 : ℝ)|^133 ≤ (28002476740733/100000000000000 : ℝ)^101
        have hw : |(-3803661071/10000000000 : ℝ)|=(3803661071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2306974117/5000000000 : ℝ)|^133 ≤ (451388327467/1250000000000 : ℝ)^101
        have hw : |(2306974117/5000000000 : ℝ)|=(2306974117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2296069127/5000000000 : ℝ)|^133 ≤ (4485807130929/12500000000000 : ℝ)^101
        have hw : |(2296069127/5000000000 : ℝ)|=(2296069127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s2_s2_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (475343559/2000000000 : ℝ)*x 0 + (2028179/5000000000 : ℝ)*x 1 + (4416366093/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (475343559/2000000000 : ℝ)^133 ≤ (7537677644291/50000000000000 : ℝ)^101 := by
    have hnat : (475343559 : ℕ)^133*50000000000000^101 ≤ 7537677644291^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      475343559 2000000000 7537677644291 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2028179/5000000000 : ℝ)^133 ≤ (3415752423/100000000000000 : ℝ)^101 := by
    have hnat : (2028179 : ℕ)^133*100000000000000^101 ≤ 3415752423^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2028179 5000000000 3415752423 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4416366093/5000000000 : ℝ)^133 ≤ (8492122894939/10000000000000 : ℝ)^101 := by
    have hnat : (4416366093 : ℕ)^133*10000000000000^101 ≤ 8492122894939^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4416366093 5000000000 8492122894939 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(475343559/2000000000 : ℝ), (2028179/5000000000 : ℝ), (4416366093/5000000000 : ℝ)] ![(7537677644291/50000000000000 : ℝ), (3415752423/100000000000000 : ℝ), (8492122894939/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(475343559/2000000000 : ℝ)|^133 ≤ (7537677644291/50000000000000 : ℝ)^101
        have hw : |(475343559/2000000000 : ℝ)|=(475343559/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2028179/5000000000 : ℝ)|^133 ≤ (3415752423/100000000000000 : ℝ)^101
        have hw : |(2028179/5000000000 : ℝ)|=(2028179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4416366093/5000000000 : ℝ)|^133 ≤ (8492122894939/10000000000000 : ℝ)^101
        have hw : |(4416366093/5000000000 : ℝ)|=(4416366093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s2_s2_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (974051959/5000000000 : ℝ)*x 0 + (4408097447/5000000000 : ℝ)*x 1 + (-407762579/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (974051959/5000000000 : ℝ)^133 ≤ (11602156839157/100000000000000 : ℝ)^101 := by
    have hnat : (974051959 : ℕ)^133*100000000000000^101 ≤ 11602156839157^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      974051959 5000000000 11602156839157 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4408097447/5000000000 : ℝ)^133 ≤ (84711920391691/100000000000000 : ℝ)^101 := by
    have hnat : (4408097447 : ℕ)^133*100000000000000^101 ≤ 84711920391691^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4408097447 5000000000 84711920391691 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (407762579/5000000000 : ℝ)^133 ≤ (1842961381713/50000000000000 : ℝ)^101 := by
    have hnat : (407762579 : ℕ)^133*50000000000000^101 ≤ 1842961381713^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407762579 5000000000 1842961381713 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(974051959/5000000000 : ℝ), (4408097447/5000000000 : ℝ), (-407762579/5000000000 : ℝ)] ![(11602156839157/100000000000000 : ℝ), (84711920391691/100000000000000 : ℝ), (1842961381713/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(974051959/5000000000 : ℝ)|^133 ≤ (11602156839157/100000000000000 : ℝ)^101
        have hw : |(974051959/5000000000 : ℝ)|=(974051959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4408097447/5000000000 : ℝ)|^133 ≤ (84711920391691/100000000000000 : ℝ)^101
        have hw : |(4408097447/5000000000 : ℝ)|=(4408097447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-407762579/5000000000 : ℝ)|^133 ≤ (1842961381713/50000000000000 : ℝ)^101
        have hw : |(-407762579/5000000000 : ℝ)|=(407762579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s2_s2_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3766431477/10000000000 : ℝ)*x 0 + (3757559353/5000000000 : ℝ)*x 1 + (819534743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3766431477/10000000000 : ℝ)^133 ≤ (13821057874113/50000000000000 : ℝ)^101 := by
    have hnat : (3766431477 : ℕ)^133*50000000000000^101 ≤ 13821057874113^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3766431477 10000000000 13821057874113 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3757559353/5000000000 : ℝ)^133 ≤ (4290504948463/6250000000000 : ℝ)^101 := by
    have hnat : (3757559353 : ℕ)^133*6250000000000^101 ≤ 4290504948463^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3757559353 5000000000 4290504948463 6250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (819534743/10000000000 : ℝ)^133 ≤ (370980507201/10000000000000 : ℝ)^101 := by
    have hnat : (819534743 : ℕ)^133*10000000000000^101 ≤ 370980507201^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      819534743 10000000000 370980507201 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3766431477/10000000000 : ℝ), (3757559353/5000000000 : ℝ), (819534743/10000000000 : ℝ)] ![(13821057874113/50000000000000 : ℝ), (4290504948463/6250000000000 : ℝ), (370980507201/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3766431477/10000000000 : ℝ)|^133 ≤ (13821057874113/50000000000000 : ℝ)^101
        have hw : |(3766431477/10000000000 : ℝ)|=(3766431477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3757559353/5000000000 : ℝ)|^133 ≤ (4290504948463/6250000000000 : ℝ)^101
        have hw : |(3757559353/5000000000 : ℝ)|=(3757559353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(819534743/10000000000 : ℝ)|^133 ≤ (370980507201/10000000000000 : ℝ)^101
        have hw : |(819534743/10000000000 : ℝ)|=(819534743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s2_s2_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2010141721/10000000000 : ℝ)*x 0 + (5400770983/10000000000 : ℝ)*x 1 + (5312500781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2010141721/10000000000 : ℝ)^133 ≤ (6045563920233/50000000000000 : ℝ)^101 := by
    have hnat : (2010141721 : ℕ)^133*50000000000000^101 ≤ 6045563920233^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010141721 10000000000 6045563920233 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5400770983/10000000000 : ℝ)^133 ≤ (1777253022937/4000000000000 : ℝ)^101 := by
    have hnat : (5400770983 : ℕ)^133*4000000000000^101 ≤ 1777253022937^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400770983 10000000000 1777253022937 4000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5312500781/10000000000 : ℝ)^133 ≤ (43477546564681/100000000000000 : ℝ)^101 := by
    have hnat : (5312500781 : ℕ)^133*100000000000000^101 ≤ 43477546564681^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312500781 10000000000 43477546564681 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2010141721/10000000000 : ℝ), (5400770983/10000000000 : ℝ), (5312500781/10000000000 : ℝ)] ![(6045563920233/50000000000000 : ℝ), (1777253022937/4000000000000 : ℝ), (43477546564681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2010141721/10000000000 : ℝ)|^133 ≤ (6045563920233/50000000000000 : ℝ)^101
        have hw : |(-2010141721/10000000000 : ℝ)|=(2010141721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5400770983/10000000000 : ℝ)|^133 ≤ (1777253022937/4000000000000 : ℝ)^101
        have hw : |(5400770983/10000000000 : ℝ)|=(5400770983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5312500781/10000000000 : ℝ)|^133 ≤ (43477546564681/100000000000000 : ℝ)^101
        have hw : |(5312500781/10000000000 : ℝ)|=(5312500781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s2_s2_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (44484477/312500000 : ℝ)*x 0 + (-5292903/2000000000 : ℝ)*x 1 + (4704212653/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (44484477/312500000 : ℝ)^133 ≤ (7675657815609/100000000000000 : ℝ)^101 := by
    have hnat : (44484477 : ℕ)^133*100000000000000^101 ≤ 7675657815609^101*312500000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44484477 312500000 7675657815609 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5292903/2000000000 : ℝ)^133 ≤ (40372181511/100000000000000 : ℝ)^101 := by
    have hnat : (5292903 : ℕ)^133*100000000000000^101 ≤ 40372181511^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5292903 2000000000 40372181511 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4704212653/5000000000 : ℝ)^133 ≤ (46141984999673/50000000000000 : ℝ)^101 := by
    have hnat : (4704212653 : ℕ)^133*50000000000000^101 ≤ 46141984999673^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4704212653 5000000000 46141984999673 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(44484477/312500000 : ℝ), (-5292903/2000000000 : ℝ), (4704212653/5000000000 : ℝ)] ![(7675657815609/100000000000000 : ℝ), (40372181511/100000000000000 : ℝ), (46141984999673/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(44484477/312500000 : ℝ)|^133 ≤ (7675657815609/100000000000000 : ℝ)^101
        have hw : |(44484477/312500000 : ℝ)|=(44484477/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5292903/2000000000 : ℝ)|^133 ≤ (40372181511/100000000000000 : ℝ)^101
        have hw : |(-5292903/2000000000 : ℝ)|=(5292903/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4704212653/5000000000 : ℝ)|^133 ≤ (46141984999673/50000000000000 : ℝ)^101
        have hw : |(4704212653/5000000000 : ℝ)|=(4704212653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s2_s2_16 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (482995541/625000000 : ℝ)*x 0 + (27340477/78125000 : ℝ)*x 1 + (-815881851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (482995541/625000000 : ℝ)^133 ≤ (14243868137357/20000000000000 : ℝ)^101 := by
    have hnat : (482995541 : ℕ)^133*20000000000000^101 ≤ 14243868137357^101*625000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482995541 625000000 14243868137357 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27340477/78125000 : ℝ)^133 ≤ (25092613471603/100000000000000 : ℝ)^101 := by
    have hnat : (27340477 : ℕ)^133*100000000000000^101 ≤ 25092613471603^101*78125000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27340477 78125000 25092613471603 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (815881851/10000000000 : ℝ)^133 ≤ (922011457739/25000000000000 : ℝ)^101 := by
    have hnat : (815881851 : ℕ)^133*25000000000000^101 ≤ 922011457739^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      815881851 10000000000 922011457739 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(482995541/625000000 : ℝ), (27340477/78125000 : ℝ), (-815881851/10000000000 : ℝ)] ![(14243868137357/20000000000000 : ℝ), (25092613471603/100000000000000 : ℝ), (922011457739/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(482995541/625000000 : ℝ)|^133 ≤ (14243868137357/20000000000000 : ℝ)^101
        have hw : |(482995541/625000000 : ℝ)|=(482995541/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(27340477/78125000 : ℝ)|^133 ≤ (25092613471603/100000000000000 : ℝ)^101
        have hw : |(27340477/78125000 : ℝ)|=(27340477/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-815881851/10000000000 : ℝ)|^133 ≤ (922011457739/25000000000000 : ℝ)^101
        have hw : |(-815881851/10000000000 : ℝ)|=(815881851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s2_s2_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2227171533/2500000000 : ℝ)*x 0 + (1837529661/10000000000 : ℝ)*x 1 + (381193247/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2227171533/2500000000 : ℝ)^133 ≤ (17176830529427/20000000000000 : ℝ)^101 := by
    have hnat : (2227171533 : ℕ)^133*20000000000000^101 ≤ 17176830529427^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2227171533 2500000000 17176830529427 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1837529661/10000000000 : ℝ)^133 ≤ (671429639391/6250000000000 : ℝ)^101 := by
    have hnat : (1837529661 : ℕ)^133*6250000000000^101 ≤ 671429639391^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1837529661 10000000000 671429639391 6250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (381193247/5000000000 : ℝ)^133 ≤ (3372973112243/100000000000000 : ℝ)^101 := by
    have hnat : (381193247 : ℕ)^133*100000000000000^101 ≤ 3372973112243^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      381193247 5000000000 3372973112243 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2227171533/2500000000 : ℝ), (1837529661/10000000000 : ℝ), (381193247/5000000000 : ℝ)] ![(17176830529427/20000000000000 : ℝ), (671429639391/6250000000000 : ℝ), (3372973112243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2227171533/2500000000 : ℝ)|^133 ≤ (17176830529427/20000000000000 : ℝ)^101
        have hw : |(2227171533/2500000000 : ℝ)|=(2227171533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1837529661/10000000000 : ℝ)|^133 ≤ (671429639391/6250000000000 : ℝ)^101
        have hw : |(1837529661/10000000000 : ℝ)|=(1837529661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(381193247/5000000000 : ℝ)|^133 ≤ (3372973112243/100000000000000 : ℝ)^101
        have hw : |(381193247/5000000000 : ℝ)|=(381193247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s2_s2_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1331841483/10000000000 : ℝ)*x 0 + (8197627607/10000000000 : ℝ)*x 1 + (2486012951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1331841483/10000000000 : ℝ)^133 ≤ (281262189327/4000000000000 : ℝ)^101 := by
    have hnat : (1331841483 : ℕ)^133*4000000000000^101 ≤ 281262189327^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1331841483 10000000000 281262189327 4000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8197627607/10000000000 : ℝ)^133 ≤ (38486806177643/50000000000000 : ℝ)^101 := by
    have hnat : (8197627607 : ℕ)^133*50000000000000^101 ≤ 38486806177643^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8197627607 10000000000 38486806177643 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2486012951/10000000000 : ℝ)^133 ≤ (499838528171/3125000000000 : ℝ)^101 := by
    have hnat : (2486012951 : ℕ)^133*3125000000000^101 ≤ 499838528171^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2486012951 10000000000 499838528171 3125000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1331841483/10000000000 : ℝ), (8197627607/10000000000 : ℝ), (2486012951/10000000000 : ℝ)] ![(281262189327/4000000000000 : ℝ), (38486806177643/50000000000000 : ℝ), (499838528171/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1331841483/10000000000 : ℝ)|^133 ≤ (281262189327/4000000000000 : ℝ)^101
        have hw : |(-1331841483/10000000000 : ℝ)|=(1331841483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8197627607/10000000000 : ℝ)|^133 ≤ (38486806177643/50000000000000 : ℝ)^101
        have hw : |(8197627607/10000000000 : ℝ)|=(8197627607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2486012951/10000000000 : ℝ)|^133 ≤ (499838528171/3125000000000 : ℝ)^101
        have hw : |(2486012951/10000000000 : ℝ)|=(2486012951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s2_s2_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1566297137/2000000000 : ℝ)*x 0 + (-465087/2000000000 : ℝ)*x 1 + (1876874831/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1566297137/2000000000 : ℝ)^133 ≤ (7247873827857/10000000000000 : ℝ)^101 := by
    have hnat : (1566297137 : ℕ)^133*10000000000000^101 ≤ 7247873827857^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1566297137 2000000000 7247873827857 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (465087/2000000000 : ℝ)^133 ≤ (1641714433/100000000000000 : ℝ)^101 := by
    have hnat : (465087 : ℕ)^133*100000000000000^101 ≤ 1641714433^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      465087 2000000000 1641714433 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1876874831/5000000000 : ℝ)^133 ≤ (13759810002033/50000000000000 : ℝ)^101 := by
    have hnat : (1876874831 : ℕ)^133*50000000000000^101 ≤ 13759810002033^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1876874831 5000000000 13759810002033 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1566297137/2000000000 : ℝ), (-465087/2000000000 : ℝ), (1876874831/5000000000 : ℝ)] ![(7247873827857/10000000000000 : ℝ), (1641714433/100000000000000 : ℝ), (13759810002033/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1566297137/2000000000 : ℝ)|^133 ≤ (7247873827857/10000000000000 : ℝ)^101
        have hw : |(1566297137/2000000000 : ℝ)|=(1566297137/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-465087/2000000000 : ℝ)|^133 ≤ (1641714433/100000000000000 : ℝ)^101
        have hw : |(-465087/2000000000 : ℝ)|=(465087/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1876874831/5000000000 : ℝ)|^133 ≤ (13759810002033/50000000000000 : ℝ)^101
        have hw : |(1876874831/5000000000 : ℝ)|=(1876874831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s2_s2_23 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1206148429/10000000000 : ℝ)*x 0 + (8791950417/10000000000 : ℝ)*x 1 + (-1663503763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1206148429/10000000000 : ℝ)^133 ≤ (6171054909091/100000000000000 : ℝ)^101 := by
    have hnat : (1206148429 : ℕ)^133*100000000000000^101 ≤ 6171054909091^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1206148429 10000000000 6171054909091 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8791950417/10000000000 : ℝ)^133 ≤ (42202644337291/50000000000000 : ℝ)^101 := by
    have hnat : (8791950417 : ℕ)^133*50000000000000^101 ≤ 42202644337291^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8791950417 10000000000 42202644337291 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1663503763/10000000000 : ℝ)^133 ≤ (4711828204023/50000000000000 : ℝ)^101 := by
    have hnat : (1663503763 : ℕ)^133*50000000000000^101 ≤ 4711828204023^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1663503763 10000000000 4711828204023 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1206148429/10000000000 : ℝ), (8791950417/10000000000 : ℝ), (-1663503763/10000000000 : ℝ)] ![(6171054909091/100000000000000 : ℝ), (42202644337291/50000000000000 : ℝ), (4711828204023/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1206148429/10000000000 : ℝ)|^133 ≤ (6171054909091/100000000000000 : ℝ)^101
        have hw : |(1206148429/10000000000 : ℝ)|=(1206148429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8791950417/10000000000 : ℝ)|^133 ≤ (42202644337291/50000000000000 : ℝ)^101
        have hw : |(8791950417/10000000000 : ℝ)|=(8791950417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1663503763/10000000000 : ℝ)|^133 ≤ (4711828204023/50000000000000 : ℝ)^101
        have hw : |(-1663503763/10000000000 : ℝ)|=(1663503763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304055_s2_s2_27 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (8441944133/10000000000 : ℝ)*x 0 + (1064865017/5000000000 : ℝ)*x 1 + (1319249433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8441944133/10000000000 : ℝ)^133 ≤ (80008682491327/100000000000000 : ℝ)^101 := by
    have hnat : (8441944133 : ℕ)^133*100000000000000^101 ≤ 80008682491327^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8441944133 10000000000 80008682491327 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1064865017/5000000000 : ℝ)^133 ≤ (13047175188619/100000000000000 : ℝ)^101 := by
    have hnat : (1064865017 : ℕ)^133*100000000000000^101 ≤ 13047175188619^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064865017 5000000000 13047175188619 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1319249433/10000000000 : ℝ)^133 ≤ (6944142308823/100000000000000 : ℝ)^101 := by
    have hnat : (1319249433 : ℕ)^133*100000000000000^101 ≤ 6944142308823^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319249433 10000000000 6944142308823 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8441944133/10000000000 : ℝ), (1064865017/5000000000 : ℝ), (1319249433/10000000000 : ℝ)] ![(80008682491327/100000000000000 : ℝ), (13047175188619/100000000000000 : ℝ), (6944142308823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8441944133/10000000000 : ℝ)|^133 ≤ (80008682491327/100000000000000 : ℝ)^101
        have hw : |(8441944133/10000000000 : ℝ)|=(8441944133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1064865017/5000000000 : ℝ)|^133 ≤ (13047175188619/100000000000000 : ℝ)^101
        have hw : |(1064865017/5000000000 : ℝ)|=(1064865017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1319249433/10000000000 : ℝ)|^133 ≤ (6944142308823/100000000000000 : ℝ)^101
        have hw : |(1319249433/10000000000 : ℝ)|=(1319249433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304055_s2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((2317/2500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2317/2500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9289/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9289/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11517/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(11517/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((22179/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22179/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17651/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(17651/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10991/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(10991/12500 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76617/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76617/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (187821/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  have s2_pow0 : (2317/2500 : ℝ) ^ (33/8 : ℝ) ≤ (73083166111933732343/100000000000000000000 : ℝ) := by
    have hpowers : (2317/2500 : ℝ)^33 ≤ (73083166111933732343/100000000000000000000 : ℝ)^8 := by
      have hnat : (2317 : ℕ)^33*100000000000000000000^8 ≤ 73083166111933732343^8*2500^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2317 2500 73083166111933732343 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2317/2500 : ℝ)) (X := (73083166111933732343/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner0a : (173083166111933732343/100000000000000000000 : ℝ) ≤ (11422436355224657/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (173083166111933732343/100000000000000000000 : ℝ)^8 ≤ (11422436355224657/10000000000000000 : ℝ)^33 := by
      have hnat : (173083166111933732343 : ℕ)^8*10000000000000000^33 ≤ 11422436355224657^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        173083166111933732343 100000000000000000000 11422436355224657 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11422436355224657/10000000000000000 : ℝ)) (X := (173083166111933732343/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner0b : (123083166111933732343/50000000000000000000 : ℝ) ≤ (777541051604791/625000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (123083166111933732343/50000000000000000000 : ℝ)^8 ≤ (777541051604791/625000000000000 : ℝ)^33 := by
      have hnat : (123083166111933732343 : ℕ)^8*625000000000000^33 ≤ 777541051604791^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        123083166111933732343 50000000000000000000 777541051604791 625000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (777541051604791/625000000000000 : ℝ)) (X := (123083166111933732343/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1422436355224657/9268000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1018220470451999/9268000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (2317/2500 : ℝ)) (alpha := (1422436355224657/9268000000000000 : ℝ)) (beta := (1018220470451999/9268000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (2317/2500 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1422436355224657/9268000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1018220470451999/9268000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (9289/10000 : ℝ) ^ (33/8 : ℝ) ≤ (18442168280753914933/25000000000000000000 : ℝ) := by
    have hpowers : (9289/10000 : ℝ)^33 ≤ (18442168280753914933/25000000000000000000 : ℝ)^8 := by
      have hnat : (9289 : ℕ)^33*25000000000000000000^8 ≤ 18442168280753914933^8*10000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9289 10000 18442168280753914933 25000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9289/10000 : ℝ)) (X := (18442168280753914933/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner1a : (43442168280753914933/25000000000000000000 : ℝ) ≤ (457335481673201/400000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (43442168280753914933/25000000000000000000 : ℝ)^8 ≤ (457335481673201/400000000000000 : ℝ)^33 := by
      have hnat : (43442168280753914933 : ℕ)^8*400000000000000^33 ≤ 457335481673201^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        43442168280753914933 25000000000000000000 457335481673201 400000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (457335481673201/400000000000000 : ℝ)) (X := (43442168280753914933/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner1b : (30942168280753914933/12500000000000000000 : ℝ) ≤ (12457418538999977/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (30942168280753914933/12500000000000000000 : ℝ)^8 ≤ (12457418538999977/10000000000000000 : ℝ)^33 := by
      have hnat : (30942168280753914933 : ℕ)^8*10000000000000000^33 ≤ 12457418538999977^33*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30942168280753914933 12500000000000000000 12457418538999977 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12457418538999977/10000000000000000 : ℝ)) (X := (30942168280753914933/12500000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(57335481673201/371560000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(32000984286561/290281250000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (9289/10000 : ℝ)) (alpha := (57335481673201/371560000000000 : ℝ)) (beta := (32000984286561/290281250000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (9289/10000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(57335481673201/371560000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(32000984286561/290281250000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (11517/12500 : ℝ) ^ (33/8 : ℝ) ≤ (14265962569767396093/20000000000000000000 : ℝ) := by
    have hpowers : (11517/12500 : ℝ)^33 ≤ (14265962569767396093/20000000000000000000 : ℝ)^8 := by
      have hnat : (11517 : ℕ)^33*20000000000000000000^8 ≤ 14265962569767396093^8*12500^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11517 12500 14265962569767396093 20000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11517/12500 : ℝ)) (X := (14265962569767396093/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner2a : (34265962569767396093/20000000000000000000 : ℝ) ≤ (1424284626009461/1250000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (34265962569767396093/20000000000000000000 : ℝ)^8 ≤ (1424284626009461/1250000000000000 : ℝ)^33 := by
      have hnat : (34265962569767396093 : ℕ)^8*1250000000000000^33 ≤ 1424284626009461^33*20000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        34265962569767396093 20000000000000000000 1424284626009461 1250000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1424284626009461/1250000000000000 : ℝ)) (X := (34265962569767396093/20000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner2b : (24265962569767396093/10000000000000000000 : ℝ) ≤ (6198730245615467/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (24265962569767396093/10000000000000000000 : ℝ)^8 ≤ (6198730245615467/5000000000000000 : ℝ)^33 := by
      have hnat : (24265962569767396093 : ℕ)^8*5000000000000000^33 ≤ 6198730245615467^33*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24265962569767396093 10000000000000000000 6198730245615467 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6198730245615467/5000000000000000 : ℝ)) (X := (24265962569767396093/10000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(5281352303317/34900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(167197247192541/1535600000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (11517/12500 : ℝ)) (alpha := (5281352303317/34900000000000 : ℝ)) (beta := (167197247192541/1535600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (11517/12500 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(5281352303317/34900000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(167197247192541/1535600000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_2 : ((618396517/1250000000 : ℝ)*X 2 0+(3178656127/5000000000 : ℝ)*X 2 1+(-216206159/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((6663704737/10000000000 : ℝ)*X 0 0+(474201419/1250000000 : ℝ)*X 0 1+(1092786941/5000000000 : ℝ)*X 0 2+(6663704737/10000000000 : ℝ)*X 1 0+(474201419/1250000000 : ℝ)*X 1 1+(1092786941/5000000000 : ℝ)*X 1 2+(6663704737/10000000000 : ℝ)*X 2 0+(474201419/1250000000 : ℝ)*X 2 1+(1092786941/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-3803661071/10000000000 : ℝ)*X 0 0+(2306974117/5000000000 : ℝ)*X 0 1+(2296069127/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((475343559/2000000000 : ℝ)*X 1 0+(2028179/5000000000 : ℝ)*X 1 1+(4416366093/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((974051959/5000000000 : ℝ)*X 2 0+(4408097447/5000000000 : ℝ)*X 2 1+(-407762579/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((3766431477/10000000000 : ℝ)*X 0 0+(3757559353/5000000000 : ℝ)*X 0 1+(819534743/10000000000 : ℝ)*X 0 2+(3766431477/10000000000 : ℝ)*X 1 0+(3757559353/5000000000 : ℝ)*X 1 1+(819534743/10000000000 : ℝ)*X 1 2+(3766431477/10000000000 : ℝ)*X 2 0+(3757559353/5000000000 : ℝ)*X 2 1+(819534743/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-2010141721/10000000000 : ℝ)*X 0 0+(5400770983/10000000000 : ℝ)*X 0 1+(5312500781/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((44484477/312500000 : ℝ)*X 1 0+(-5292903/2000000000 : ℝ)*X 1 1+(4704212653/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((482995541/625000000 : ℝ)*X 2 0+(27340477/78125000 : ℝ)*X 2 1+(-815881851/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((2227171533/2500000000 : ℝ)*X 0 0+(1837529661/10000000000 : ℝ)*X 0 1+(381193247/5000000000 : ℝ)*X 0 2+(2227171533/2500000000 : ℝ)*X 1 0+(1837529661/10000000000 : ℝ)*X 1 1+(381193247/5000000000 : ℝ)*X 1 2+(2227171533/2500000000 : ℝ)*X 2 0+(1837529661/10000000000 : ℝ)*X 2 1+(381193247/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-1331841483/10000000000 : ℝ)*X 0 0+(8197627607/10000000000 : ℝ)*X 0 1+(2486012951/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((1566297137/2000000000 : ℝ)*X 1 0+(-465087/2000000000 : ℝ)*X 1 1+(1876874831/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((1206148429/10000000000 : ℝ)*X 2 0+(8791950417/10000000000 : ℝ)*X 2 1+(-1663503763/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((8441944133/10000000000 : ℝ)*X 0 0+(1064865017/5000000000 : ℝ)*X 0 1+(1319249433/10000000000 : ℝ)*X 0 2+(8441944133/10000000000 : ℝ)*X 1 0+(1064865017/5000000000 : ℝ)*X 1 1+(1319249433/10000000000 : ℝ)*X 1 2+(8441944133/10000000000 : ℝ)*X 2 0+(1064865017/5000000000 : ℝ)*X 2 1+(1319249433/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304055_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((22179/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22179/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (12090825809863725561894249231/843115421500000000000000000000000 : ℝ) := by norm_num
    linear_combination (341419862173/500000000000 : ℝ)*(base7) + (139717/1000000000000 : ℝ)*(base23) + (8781602801/500000000000 : ℝ)*(base43) + (793273/1000000000000 : ℝ)*(base49) + (59202189381/62500000000 : ℝ)*(base53) + (328891370017/200000000000 : ℝ)*(major_s2_0) + (1626893644483/1000000000000 : ℝ)*(major_s2_1) + (697221819989/1000000000000 : ℝ)*(major_s2_2) + (812346798739/1000000000000 : ℝ)*(sp_s2_7) + (51871830389/62500000000 : ℝ)*(sp_s2_8) + (879810485501/500000000000 : ℝ)*(sp_s2_9) + (220882357719/125000000000 : ℝ)*(sp_s2_13) + (10210833/1000000000000 : ℝ)*(sp_s2_14) + (581421/20000000000 : ℝ)*(sp_s2_21) + (216843827481/200000000000 : ℝ)*(f.failure) + (11107401977/6250000000 : ℝ)*(f.sum) + (263478670724042891/648372200000000000000000000000 : ℝ)*base62 + (656966314404071/1535600000000000000000000000 : ℝ)*base64 + (975389025249171/2322250000000000000000000000 : ℝ)*base67 + (7704198402647/34900000000000000000000000 : ℝ)*base68 + (325146082002585329/1016567200000000000000000000000 : ℝ)*base70 + (47836205338569/264800000000000000000000000 : ℝ)*base73 + (120389819932157/371560000000000000000000000 : ℝ)*base74 + (286366110771833/264800000000000000000000000 : ℝ)*base76 + (2044534285555508821/12298636000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (221/2500000000000000 : ℝ)*base86 + (221/2500000000000000 : ℝ)*base88 + (221/2500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17651/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(17651/20000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (169721346137615470033727697/38323428250000000000000000000000 : ℝ) := by norm_num
    linear_combination (695797396401/1000000000000 : ℝ)*(base7) + (6144953411/250000000000 : ℝ)*(base34) + (130467/1000000000000 : ℝ)*(base40) + (82564179123/100000000000 : ℝ)*(base53) + (374402629781/250000000000 : ℝ)*(major_s2_0) + (47568447899/31250000000 : ℝ)*(major_s2_1) + (348274270769/500000000000 : ℝ)*(major_s2_2) + (3204389/50000000000 : ℝ)*(sp_s2_8) + (75491590411/100000000000 : ℝ)*(sp_s2_14) + (12178886693/15625000000 : ℝ)*(sp_s2_15) + (1605154627361/1000000000000 : ℝ)*(sp_s2_16) + (209351773333/125000000000 : ℝ)*(sp_s2_20) + (17118377/1000000000000 : ℝ)*(sp_s2_21) + (10082079/1000000000000 : ℝ)*(sp_s2_27) + (501803342993/500000000000 : ℝ)*(f.failure) + (1605154627361/1000000000000 : ℝ)*(f.sum) + (11121065680303219/23156150000000000000000000000 : ℝ)*base62 + (61549396285991/767800000000000000000000000 : ℝ)*base64 + (11973025687847/82937500000000000000000000 : ℝ)*base67 + (4755668734281/8725000000000000000000000 : ℝ)*base68 + (2209787980979297/8686487304687500000000000000 : ℝ)*base71 + (2299505012093281/2317000000000000000000000000 : ℝ)*base72 + (1374085152861/13270000000000000000000000 : ℝ)*base74 + (698412791159917/2317000000000000000000000000 : ℝ)*base77 + (1231132508402528203/3074659000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (4287/6250000000000000 : ℝ)*base87 + (4287/6250000000000000 : ℝ)*base89 + (4287/6250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10991/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(10991/12500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1472406243448859705687642469/268263997750000000000000000000000 : ℝ) := by norm_num
    linear_combination (1394401287/1600000000 : ℝ)*(base7) + (351173892167/1000000000000 : ℝ)*(base43) + (19332614027/1000000000000 : ℝ)*(base50) + (75962244171/50000000000 : ℝ)*(major_s2_0) + (292017747813/250000000000 : ℝ)*(major_s2_1) + (75962244171/50000000000 : ℝ)*(major_s2_2) + (160697/1000000000000 : ℝ)*(sp_s2_2) + (878313/62500000000 : ℝ)*(sp_s2_6) + (28879363/1000000000000 : ℝ)*(sp_s2_9) + (14772457/250000000000 : ℝ)*(sp_s2_20) + (228005767353/200000000000 : ℝ)*(sp_s2_21) + (372800682233/250000000000 : ℝ)*(sp_s2_22) + (227999959341/200000000000 : ℝ)*(sp_s2_23) + (1873092361299/1000000000000 : ℝ)*(sp_s2_27) + (12520808747/12500000000 : ℝ)*(f.failure) + (372800682233/250000000000 : ℝ)*(f.sum) + (6719117580122721/32418610000000000000000000000 : ℝ)*base62 + (3929246336709/6980000000000000000000000 : ℝ)*base64 + (949549093552137/1161125000000000000000000000 : ℝ)*base67 + (209782340857/3490000000000000000000000 : ℝ)*base68 + (10298386638978927/161726600000000000000000000000 : ℝ)*base70 + (218816720510569/463400000000000000000000000 : ℝ)*base73 + (3281255067143/92890000000000000000000000 : ℝ)*base75 + (215173321089553/463400000000000000000000000 : ℝ)*base76 + (1228104281500048291/3074659000000000000000000000000 : ℝ)*base79 + (1/78125000000000 : ℝ)*base86 + (617/625000000000000 : ℝ)*base89 + (1/78125000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((2317/2500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2317/2500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9289/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9289/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11517/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(11517/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((22179/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22179/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17651/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(17651/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10991/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(10991/12500 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304055_s2 p hpa hpb X hX hprev1

#print axioms solution
