-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c318057_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:23:57.288337+00:00
-- url     : https://prove2.me/submissions/957a1795-65e7-413b-898d-9dcf8b454b21

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
theorem collision_support_c318057_s1_s1_1 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (805692139/2500000000 : ℝ)*x 0 + (-3217195301/10000000000 : ℝ)*x 1 + (236383651/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (805692139/2500000000 : ℝ)^79 ≤ (24173243419067/100000000000000 : ℝ)^63 := by
    have hnat : (805692139 : ℕ)^79*100000000000000^63 ≤ 24173243419067^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      805692139 2500000000 24173243419067 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3217195301/10000000000 : ℝ)^79 ≤ (24120834422837/100000000000000 : ℝ)^63 := by
    have hnat : (3217195301 : ℕ)^79*100000000000000^63 ≤ 24120834422837^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3217195301 10000000000 24120834422837 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (236383651/400000000 : ℝ)^79 ≤ (5170592214751/10000000000000 : ℝ)^63 := by
    have hnat : (236383651 : ℕ)^79*10000000000000^63 ≤ 5170592214751^63*400000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      236383651 400000000 5170592214751 10000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(805692139/2500000000 : ℝ), (-3217195301/10000000000 : ℝ), (236383651/400000000 : ℝ)] ![(24173243419067/100000000000000 : ℝ), (24120834422837/100000000000000 : ℝ), (5170592214751/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(805692139/2500000000 : ℝ)|^79 ≤ (24173243419067/100000000000000 : ℝ)^63
        have hw : |(805692139/2500000000 : ℝ)|=(805692139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3217195301/10000000000 : ℝ)|^79 ≤ (24120834422837/100000000000000 : ℝ)^63
        have hw : |(-3217195301/10000000000 : ℝ)|=(3217195301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(236383651/400000000 : ℝ)|^79 ≤ (5170592214751/10000000000000 : ℝ)^63
        have hw : |(236383651/400000000 : ℝ)|=(236383651/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318057_s1_s1_2 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2806738701/5000000000 : ℝ)*x 0 + (562206013/1000000000 : ℝ)*x 1 + (-602349889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2806738701/5000000000 : ℝ)^79 ≤ (48478018728303/100000000000000 : ℝ)^63 := by
    have hnat : (2806738701 : ℕ)^79*100000000000000^63 ≤ 48478018728303^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2806738701 5000000000 48478018728303 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (562206013/1000000000 : ℝ)^79 ≤ (48570981497839/100000000000000 : ℝ)^63 := by
    have hnat : (562206013 : ℕ)^79*100000000000000^63 ≤ 48570981497839^63*1000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562206013 1000000000 48570981497839 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (602349889/10000000000 : ℝ)^79 ≤ (590199951219/20000000000000 : ℝ)^63 := by
    have hnat : (602349889 : ℕ)^79*20000000000000^63 ≤ 590199951219^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      602349889 10000000000 590199951219 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2806738701/5000000000 : ℝ), (562206013/1000000000 : ℝ), (-602349889/10000000000 : ℝ)] ![(48478018728303/100000000000000 : ℝ), (48570981497839/100000000000000 : ℝ), (590199951219/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2806738701/5000000000 : ℝ)|^79 ≤ (48478018728303/100000000000000 : ℝ)^63
        have hw : |(2806738701/5000000000 : ℝ)|=(2806738701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(562206013/1000000000 : ℝ)|^79 ≤ (48570981497839/100000000000000 : ℝ)^63
        have hw : |(562206013/1000000000 : ℝ)|=(562206013/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-602349889/10000000000 : ℝ)|^79 ≤ (590199951219/20000000000000 : ℝ)^63
        have hw : |(-602349889/10000000000 : ℝ)|=(602349889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318057_s1_s1_6 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2232834399/5000000000 : ℝ)*x 0 + (559062073/1250000000 : ℝ)*x 1 + (353574147/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2232834399/5000000000 : ℝ)^79 ≤ (9097222290823/25000000000000 : ℝ)^63 := by
    have hnat : (2232834399 : ℕ)^79*25000000000000^63 ≤ 9097222290823^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2232834399 5000000000 9097222290823 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (559062073/1250000000 : ℝ)^79 ≤ (36458669491847/100000000000000 : ℝ)^63 := by
    have hnat : (559062073 : ℕ)^79*100000000000000^63 ≤ 36458669491847^63*1250000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559062073 1250000000 36458669491847 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (353574147/1000000000 : ℝ)^79 ≤ (1086097652917/4000000000000 : ℝ)^63 := by
    have hnat : (353574147 : ℕ)^79*4000000000000^63 ≤ 1086097652917^63*1000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      353574147 1000000000 1086097652917 4000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2232834399/5000000000 : ℝ), (559062073/1250000000 : ℝ), (353574147/1000000000 : ℝ)] ![(9097222290823/25000000000000 : ℝ), (36458669491847/100000000000000 : ℝ), (1086097652917/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2232834399/5000000000 : ℝ)|^79 ≤ (9097222290823/25000000000000 : ℝ)^63
        have hw : |(2232834399/5000000000 : ℝ)|=(2232834399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(559062073/1250000000 : ℝ)|^79 ≤ (36458669491847/100000000000000 : ℝ)^63
        have hw : |(559062073/1250000000 : ℝ)|=(559062073/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(353574147/1000000000 : ℝ)|^79 ≤ (1086097652917/4000000000000 : ℝ)^63
        have hw : |(353574147/1000000000 : ℝ)|=(353574147/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318057_s1_s1_7 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-97708637/312500000 : ℝ)*x 0 + (2885845031/10000000000 : ℝ)*x 1 + (6269041763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (97708637/312500000 : ℝ)^79 ≤ (4654574900277/20000000000000 : ℝ)^63 := by
    have hnat : (97708637 : ℕ)^79*20000000000000^63 ≤ 4654574900277^63*312500000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97708637 312500000 4654574900277 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2885845031/10000000000 : ℝ)^79 ≤ (21047449859561/100000000000000 : ℝ)^63 := by
    have hnat : (2885845031 : ℕ)^79*100000000000000^63 ≤ 21047449859561^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2885845031 10000000000 21047449859561 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6269041763/10000000000 : ℝ)^79 ≤ (6959959452571/12500000000000 : ℝ)^63 := by
    have hnat : (6269041763 : ℕ)^79*12500000000000^63 ≤ 6959959452571^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6269041763 10000000000 6959959452571 12500000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-97708637/312500000 : ℝ), (2885845031/10000000000 : ℝ), (6269041763/10000000000 : ℝ)] ![(4654574900277/20000000000000 : ℝ), (21047449859561/100000000000000 : ℝ), (6959959452571/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-97708637/312500000 : ℝ)|^79 ≤ (4654574900277/20000000000000 : ℝ)^63
        have hw : |(-97708637/312500000 : ℝ)|=(97708637/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2885845031/10000000000 : ℝ)|^79 ≤ (21047449859561/100000000000000 : ℝ)^63
        have hw : |(2885845031/10000000000 : ℝ)|=(2885845031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6269041763/10000000000 : ℝ)|^79 ≤ (6959959452571/12500000000000 : ℝ)^63
        have hw : |(6269041763/10000000000 : ℝ)|=(6269041763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318057_s1_s1_8 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3121810279/10000000000 : ℝ)*x 0 + (-360169217/1250000000 : ℝ)*x 1 + (156920129/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3121810279/10000000000 : ℝ)^79 ≤ (4645492947547/20000000000000 : ℝ)^63 := by
    have hnat : (3121810279 : ℕ)^79*20000000000000^63 ≤ 4645492947547^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3121810279 10000000000 4645492947547 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (360169217/1250000000 : ℝ)^79 ≤ (21006382315597/100000000000000 : ℝ)^63 := by
    have hnat : (360169217 : ℕ)^79*100000000000000^63 ≤ 21006382315597^63*1250000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      360169217 1250000000 21006382315597 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (156920129/250000000 : ℝ)^79 ≤ (27883076461981/50000000000000 : ℝ)^63 := by
    have hnat : (156920129 : ℕ)^79*50000000000000^63 ≤ 27883076461981^63*250000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156920129 250000000 27883076461981 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3121810279/10000000000 : ℝ), (-360169217/1250000000 : ℝ), (156920129/250000000 : ℝ)] ![(4645492947547/20000000000000 : ℝ), (21006382315597/100000000000000 : ℝ), (27883076461981/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3121810279/10000000000 : ℝ)|^79 ≤ (4645492947547/20000000000000 : ℝ)^63
        have hw : |(3121810279/10000000000 : ℝ)|=(3121810279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-360169217/1250000000 : ℝ)|^79 ≤ (21006382315597/100000000000000 : ℝ)^63
        have hw : |(-360169217/1250000000 : ℝ)|=(360169217/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(156920129/250000000 : ℝ)|^79 ≤ (27883076461981/50000000000000 : ℝ)^63
        have hw : |(156920129/250000000 : ℝ)|=(156920129/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318057_s1_s1_9 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5361843291/10000000000 : ℝ)*x 0 + (605059723/1000000000 : ℝ)*x 1 + (-124391647/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5361843291/10000000000 : ℝ)^79 ≤ (1830747657197/4000000000000 : ℝ)^63 := by
    have hnat : (5361843291 : ℕ)^79*4000000000000^63 ≤ 1830747657197^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361843291 10000000000 1830747657197 4000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (605059723/1000000000 : ℝ)^79 ≤ (53257640933007/100000000000000 : ℝ)^63 := by
    have hnat : (605059723 : ℕ)^79*100000000000000^63 ≤ 53257640933007^63*1000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      605059723 1000000000 53257640933007 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (124391647/5000000000 : ℝ)^79 ≤ (973667622021/100000000000000 : ℝ)^63 := by
    have hnat : (124391647 : ℕ)^79*100000000000000^63 ≤ 973667622021^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124391647 5000000000 973667622021 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5361843291/10000000000 : ℝ), (605059723/1000000000 : ℝ), (-124391647/5000000000 : ℝ)] ![(1830747657197/4000000000000 : ℝ), (53257640933007/100000000000000 : ℝ), (973667622021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5361843291/10000000000 : ℝ)|^79 ≤ (1830747657197/4000000000000 : ℝ)^63
        have hw : |(5361843291/10000000000 : ℝ)|=(5361843291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(605059723/1000000000 : ℝ)|^79 ≤ (53257640933007/100000000000000 : ℝ)^63
        have hw : |(605059723/1000000000 : ℝ)|=(605059723/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-124391647/5000000000 : ℝ)|^79 ≤ (973667622021/100000000000000 : ℝ)^63
        have hw : |(-124391647/5000000000 : ℝ)|=(124391647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318057_s1_s1_12 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (918733841/2000000000 : ℝ)*x 0 + (2591873789/5000000000 : ℝ)*x 1 + (2595623873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (918733841/2000000000 : ℝ)^79 ≤ (37701533157383/100000000000000 : ℝ)^63 := by
    have hnat : (918733841 : ℕ)^79*100000000000000^63 ≤ 37701533157383^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      918733841 2000000000 37701533157383 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591873789/5000000000 : ℝ)^79 ≤ (43870485551023/100000000000000 : ℝ)^63 := by
    have hnat : (2591873789 : ℕ)^79*100000000000000^63 ≤ 43870485551023^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591873789 5000000000 43870485551023 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2595623873/10000000000 : ℝ)^79 ≤ (575874414991/3125000000000 : ℝ)^63 := by
    have hnat : (2595623873 : ℕ)^79*3125000000000^63 ≤ 575874414991^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2595623873 10000000000 575874414991 3125000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(918733841/2000000000 : ℝ), (2591873789/5000000000 : ℝ), (2595623873/10000000000 : ℝ)] ![(37701533157383/100000000000000 : ℝ), (43870485551023/100000000000000 : ℝ), (575874414991/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(918733841/2000000000 : ℝ)|^79 ≤ (37701533157383/100000000000000 : ℝ)^63
        have hw : |(918733841/2000000000 : ℝ)|=(918733841/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591873789/5000000000 : ℝ)|^79 ≤ (43870485551023/100000000000000 : ℝ)^63
        have hw : |(2591873789/5000000000 : ℝ)|=(2591873789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2595623873/10000000000 : ℝ)|^79 ≤ (575874414991/3125000000000 : ℝ)^63
        have hw : |(2595623873/10000000000 : ℝ)|=(2595623873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318057_s1_s1_13 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-578281099/2000000000 : ℝ)*x 0 + (3121224327/10000000000 : ℝ)*x 1 + (1253808537/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (578281099/2000000000 : ℝ)^79 ≤ (21098316171411/100000000000000 : ℝ)^63 := by
    have hnat : (578281099 : ℕ)^79*100000000000000^63 ≤ 21098316171411^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      578281099 2000000000 21098316171411 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3121224327/10000000000 : ℝ)^79 ≤ (23221997933349/100000000000000 : ℝ)^63 := by
    have hnat : (3121224327 : ℕ)^79*100000000000000^63 ≤ 23221997933349^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3121224327 10000000000 23221997933349 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1253808537/2000000000 : ℝ)^79 ≤ (5567968588921/10000000000000 : ℝ)^63 := by
    have hnat : (1253808537 : ℕ)^79*10000000000000^63 ≤ 5567968588921^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1253808537 2000000000 5567968588921 10000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-578281099/2000000000 : ℝ), (3121224327/10000000000 : ℝ), (1253808537/2000000000 : ℝ)] ![(21098316171411/100000000000000 : ℝ), (23221997933349/100000000000000 : ℝ), (5567968588921/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-578281099/2000000000 : ℝ)|^79 ≤ (21098316171411/100000000000000 : ℝ)^63
        have hw : |(-578281099/2000000000 : ℝ)|=(578281099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3121224327/10000000000 : ℝ)|^79 ≤ (23221997933349/100000000000000 : ℝ)^63
        have hw : |(3121224327/10000000000 : ℝ)|=(3121224327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1253808537/2000000000 : ℝ)|^79 ≤ (5567968588921/10000000000000 : ℝ)^63
        have hw : |(1253808537/2000000000 : ℝ)|=(1253808537/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318057_s1_s1_14 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (360863039/1250000000 : ℝ)*x 0 + (-1558182687/5000000000 : ℝ)*x 1 + (392300513/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (360863039/1250000000 : ℝ)^79 ≤ (21057138089609/100000000000000 : ℝ)^63 := by
    have hnat : (360863039 : ℕ)^79*100000000000000^63 ≤ 21057138089609^63*1250000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      360863039 1250000000 21057138089609 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1558182687/5000000000 : ℝ)^79 ≤ (5794168751699/25000000000000 : ℝ)^63 := by
    have hnat : (1558182687 : ℕ)^79*25000000000000^63 ≤ 5794168751699^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1558182687 5000000000 5794168751699 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (392300513/625000000 : ℝ)^79 ≤ (11153237376259/20000000000000 : ℝ)^63 := by
    have hnat : (392300513 : ℕ)^79*20000000000000^63 ≤ 11153237376259^63*625000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      392300513 625000000 11153237376259 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(360863039/1250000000 : ℝ), (-1558182687/5000000000 : ℝ), (392300513/625000000 : ℝ)] ![(21057138089609/100000000000000 : ℝ), (5794168751699/25000000000000 : ℝ), (11153237376259/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(360863039/1250000000 : ℝ)|^79 ≤ (21057138089609/100000000000000 : ℝ)^63
        have hw : |(360863039/1250000000 : ℝ)|=(360863039/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1558182687/5000000000 : ℝ)|^79 ≤ (5794168751699/25000000000000 : ℝ)^63
        have hw : |(-1558182687/5000000000 : ℝ)|=(1558182687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(392300513/625000000 : ℝ)|^79 ≤ (11153237376259/20000000000000 : ℝ)^63
        have hw : |(392300513/625000000 : ℝ)|=(392300513/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318057_s1_s1_15 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3021100637/5000000000 : ℝ)*x 0 + (1074099619/2000000000 : ℝ)*x 1 + (-248782281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3021100637/5000000000 : ℝ)^79 ≤ (13291246752179/25000000000000 : ℝ)^63 := by
    have hnat : (3021100637 : ℕ)^79*25000000000000^63 ≤ 13291246752179^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3021100637 5000000000 13291246752179 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1074099619/2000000000 : ℝ)^79 ≤ (4586135032793/10000000000000 : ℝ)^63 := by
    have hnat : (1074099619 : ℕ)^79*10000000000000^63 ≤ 4586135032793^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074099619 2000000000 4586135032793 10000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (248782281/10000000000 : ℝ)^79 ≤ (194732530109/20000000000000 : ℝ)^63 := by
    have hnat : (248782281 : ℕ)^79*20000000000000^63 ≤ 194732530109^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      248782281 10000000000 194732530109 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3021100637/5000000000 : ℝ), (1074099619/2000000000 : ℝ), (-248782281/10000000000 : ℝ)] ![(13291246752179/25000000000000 : ℝ), (4586135032793/10000000000000 : ℝ), (194732530109/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3021100637/5000000000 : ℝ)|^79 ≤ (13291246752179/25000000000000 : ℝ)^63
        have hw : |(3021100637/5000000000 : ℝ)|=(3021100637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1074099619/2000000000 : ℝ)|^79 ≤ (4586135032793/10000000000000 : ℝ)^63
        have hw : |(1074099619/2000000000 : ℝ)|=(1074099619/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-248782281/10000000000 : ℝ)|^79 ≤ (194732530109/20000000000000 : ℝ)^63
        have hw : |(-248782281/10000000000 : ℝ)|=(248782281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318057_s1_s1_18 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2588278147/5000000000 : ℝ)*x 0 + (575135709/1250000000 : ℝ)*x 1 + (1297809697/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2588278147/5000000000 : ℝ)^79 ≤ (21897090974621/50000000000000 : ℝ)^63 := by
    have hnat : (2588278147 : ℕ)^79*50000000000000^63 ≤ 21897090974621^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588278147 5000000000 21897090974621 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (575135709/1250000000 : ℝ)^79 ≤ (9444469156863/25000000000000 : ℝ)^63 := by
    have hnat : (575135709 : ℕ)^79*25000000000000^63 ≤ 9444469156863^63*1250000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      575135709 1250000000 9444469156863 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1297809697/5000000000 : ℝ)^79 ≤ (9213970702227/50000000000000 : ℝ)^63 := by
    have hnat : (1297809697 : ℕ)^79*50000000000000^63 ≤ 9213970702227^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1297809697 5000000000 9213970702227 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2588278147/5000000000 : ℝ), (575135709/1250000000 : ℝ), (1297809697/5000000000 : ℝ)] ![(21897090974621/50000000000000 : ℝ), (9444469156863/25000000000000 : ℝ), (9213970702227/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2588278147/5000000000 : ℝ)|^79 ≤ (21897090974621/50000000000000 : ℝ)^63
        have hw : |(2588278147/5000000000 : ℝ)|=(2588278147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(575135709/1250000000 : ℝ)|^79 ≤ (9444469156863/25000000000000 : ℝ)^63
        have hw : |(575135709/1250000000 : ℝ)|=(575135709/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1297809697/5000000000 : ℝ)|^79 ≤ (9213970702227/50000000000000 : ℝ)^63
        have hw : |(1297809697/5000000000 : ℝ)|=(1297809697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318057_s1_s1_19 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3378879637/10000000000 : ℝ)*x 0 + (1541785109/5000000000 : ℝ)*x 1 + (5888831081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3378879637/10000000000 : ℝ)^79 ≤ (513010138519/2000000000000 : ℝ)^63 := by
    have hnat : (3378879637 : ℕ)^79*2000000000000^63 ≤ 513010138519^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3378879637 10000000000 513010138519 2000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1541785109/5000000000 : ℝ)^79 ≤ (11435620731579/50000000000000 : ℝ)^63 := by
    have hnat : (1541785109 : ℕ)^79*50000000000000^63 ≤ 11435620731579^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1541785109 5000000000 11435620731579 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5888831081/10000000000 : ℝ)^79 ≤ (6434781450461/12500000000000 : ℝ)^63 := by
    have hnat : (5888831081 : ℕ)^79*12500000000000^63 ≤ 6434781450461^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5888831081 10000000000 6434781450461 12500000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3378879637/10000000000 : ℝ), (1541785109/5000000000 : ℝ), (5888831081/10000000000 : ℝ)] ![(513010138519/2000000000000 : ℝ), (11435620731579/50000000000000 : ℝ), (6434781450461/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3378879637/10000000000 : ℝ)|^79 ≤ (513010138519/2000000000000 : ℝ)^63
        have hw : |(-3378879637/10000000000 : ℝ)|=(3378879637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1541785109/5000000000 : ℝ)|^79 ≤ (11435620731579/50000000000000 : ℝ)^63
        have hw : |(1541785109/5000000000 : ℝ)|=(1541785109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5888831081/10000000000 : ℝ)|^79 ≤ (6434781450461/12500000000000 : ℝ)^63
        have hw : |(5888831081/10000000000 : ℝ)|=(5888831081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318057_s1_s1_20 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (771174371/2500000000 : ℝ)*x 0 + (-842207733/2500000000 : ℝ)*x 1 + (5896596447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (771174371/2500000000 : ℝ)^79 ≤ (5720431619231/25000000000000 : ℝ)^63 := by
    have hnat : (771174371 : ℕ)^79*25000000000000^63 ≤ 5720431619231^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      771174371 2500000000 5720431619231 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (842207733/2500000000 : ℝ)^79 ≤ (5110977078381/20000000000000 : ℝ)^63 := by
    have hnat : (842207733 : ℕ)^79*20000000000000^63 ≤ 5110977078381^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      842207733 2500000000 5110977078381 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5896596447/10000000000 : ℝ)^79 ≤ (12890847029011/25000000000000 : ℝ)^63 := by
    have hnat : (5896596447 : ℕ)^79*25000000000000^63 ≤ 12890847029011^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5896596447 10000000000 12890847029011 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(771174371/2500000000 : ℝ), (-842207733/2500000000 : ℝ), (5896596447/10000000000 : ℝ)] ![(5720431619231/25000000000000 : ℝ), (5110977078381/20000000000000 : ℝ), (12890847029011/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(771174371/2500000000 : ℝ)|^79 ≤ (5720431619231/25000000000000 : ℝ)^63
        have hw : |(771174371/2500000000 : ℝ)|=(771174371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-842207733/2500000000 : ℝ)|^79 ≤ (5110977078381/20000000000000 : ℝ)^63
        have hw : |(-842207733/2500000000 : ℝ)|=(842207733/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5896596447/10000000000 : ℝ)|^79 ≤ (12890847029011/25000000000000 : ℝ)^63
        have hw : |(5896596447/10000000000 : ℝ)|=(5896596447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318057_s1_s1_21 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2846615913/5000000000 : ℝ)*x 0 + (555089139/1000000000 : ℝ)*x 1 + (-586757381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2846615913/5000000000 : ℝ)^79 ≤ (4934325414381/10000000000000 : ℝ)^63 := by
    have hnat : (2846615913 : ℕ)^79*10000000000000^63 ≤ 4934325414381^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2846615913 5000000000 4934325414381 10000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (555089139/1000000000 : ℝ)^79 ≤ (11950304939537/25000000000000 : ℝ)^63 := by
    have hnat : (555089139 : ℕ)^79*25000000000000^63 ≤ 11950304939537^63*1000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      555089139 1000000000 11950304939537 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (586757381/10000000000 : ℝ)^79 ≤ (356940761299/12500000000000 : ℝ)^63 := by
    have hnat : (586757381 : ℕ)^79*12500000000000^63 ≤ 356940761299^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      586757381 10000000000 356940761299 12500000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2846615913/5000000000 : ℝ), (555089139/1000000000 : ℝ), (-586757381/10000000000 : ℝ)] ![(4934325414381/10000000000000 : ℝ), (11950304939537/25000000000000 : ℝ), (356940761299/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2846615913/5000000000 : ℝ)|^79 ≤ (4934325414381/10000000000000 : ℝ)^63
        have hw : |(2846615913/5000000000 : ℝ)|=(2846615913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(555089139/1000000000 : ℝ)|^79 ≤ (11950304939537/25000000000000 : ℝ)^63
        have hw : |(555089139/1000000000 : ℝ)|=(555089139/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-586757381/10000000000 : ℝ)|^79 ≤ (356940761299/12500000000000 : ℝ)^63
        have hw : |(-586757381/10000000000 : ℝ)|=(586757381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318057_s1_s1_25 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (428553419/1000000000 : ℝ)*x 0 + (4692276353/10000000000 : ℝ)*x 1 + (3491084443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (428553419/1000000000 : ℝ)^79 ≤ (2159861608249/6250000000000 : ℝ)^63 := by
    have hnat : (428553419 : ℕ)^79*6250000000000^63 ≤ 2159861608249^63*1000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428553419 1000000000 2159861608249 6250000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4692276353/10000000000 : ℝ)^79 ≤ (38719116970859/100000000000000 : ℝ)^63 := by
    have hnat : (4692276353 : ℕ)^79*100000000000000^63 ≤ 38719116970859^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4692276353 10000000000 38719116970859 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3491084443/10000000000 : ℝ)^79 ≤ (5344619457763/20000000000000 : ℝ)^63 := by
    have hnat : (3491084443 : ℕ)^79*20000000000000^63 ≤ 5344619457763^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3491084443 10000000000 5344619457763 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(428553419/1000000000 : ℝ), (4692276353/10000000000 : ℝ), (3491084443/10000000000 : ℝ)] ![(2159861608249/6250000000000 : ℝ), (38719116970859/100000000000000 : ℝ), (5344619457763/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(428553419/1000000000 : ℝ)|^79 ≤ (2159861608249/6250000000000 : ℝ)^63
        have hw : |(428553419/1000000000 : ℝ)|=(428553419/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4692276353/10000000000 : ℝ)|^79 ≤ (38719116970859/100000000000000 : ℝ)^63
        have hw : |(4692276353/10000000000 : ℝ)|=(4692276353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3491084443/10000000000 : ℝ)|^79 ≤ (5344619457763/20000000000000 : ℝ)^63
        have hw : |(3491084443/10000000000 : ℝ)|=(3491084443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c318057_s1 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((15111/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15111/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7499/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(7499/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(35999/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(35999/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((981/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(981/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7837/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(7837/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(979/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(979/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (39911/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (39911/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (39911/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (39911/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (39911/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (39911/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (15111/20000 : ℝ) ^ (39/8 : ℝ) ≤ (12749793553380286521/50000000000000000000 : ℝ) := by
    have hpowers : (15111/20000 : ℝ)^39 ≤ (12749793553380286521/50000000000000000000 : ℝ)^8 := by
      have hnat : (15111 : ℕ)^39*50000000000000000000^8 ≤ 12749793553380286521^8*20000^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15111 20000 12749793553380286521 50000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15111/20000 : ℝ)) (X := (12749793553380286521/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (62749793553380286521/50000000000000000000 : ℝ) ≤ (5238468318056731/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (62749793553380286521/50000000000000000000 : ℝ)^8 ≤ (5238468318056731/5000000000000000 : ℝ)^39 := by
      have hnat : (62749793553380286521 : ℕ)^8*5000000000000000^39 ≤ 5238468318056731^39*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62749793553380286521 50000000000000000000 5238468318056731 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5238468318056731/5000000000000000 : ℝ)) (X := (62749793553380286521/50000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (37749793553380286521/25000000000000000000 : ℝ) ≤ (1360262563483977/1250000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (37749793553380286521/25000000000000000000 : ℝ)^8 ≤ (1360262563483977/1250000000000000 : ℝ)^39 := by
      have hnat : (37749793553380286521 : ℕ)^8*1250000000000000^39 ≤ 1360262563483977^39*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37749793553380286521 25000000000000000000 1360262563483977 1250000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1360262563483977/1250000000000000 : ℝ)) (X := (37749793553380286521/25000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(10368187741597/164250000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(202581935879177/3777750000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (15111/20000 : ℝ)) (alpha := (10368187741597/164250000000000 : ℝ)) (beta := (202581935879177/3777750000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (15111/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(10368187741597/164250000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(202581935879177/3777750000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (7499/10000 : ℝ) ^ (39/8 : ℝ) ≤ (6145841525099480369/25000000000000000000 : ℝ) := by
    have hpowers : (7499/10000 : ℝ)^39 ≤ (6145841525099480369/25000000000000000000 : ℝ)^8 := by
      have hnat : (7499 : ℕ)^39*25000000000000000000^8 ≤ 6145841525099480369^8*10000^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7499 10000 6145841525099480369 25000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7499/10000 : ℝ)) (X := (6145841525099480369/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (31145841525099480369/25000000000000000000 : ℝ) ≤ (10461201103435099/10000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (31145841525099480369/25000000000000000000 : ℝ)^8 ≤ (10461201103435099/10000000000000000 : ℝ)^39 := by
      have hnat : (31145841525099480369 : ℕ)^8*10000000000000000^39 ≤ 10461201103435099^39*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31145841525099480369 25000000000000000000 10461201103435099 10000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10461201103435099/10000000000000000 : ℝ)) (X := (31145841525099480369/25000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (18645841525099480369/12500000000000000000 : ℝ) ≤ (10854879848628401/10000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (18645841525099480369/12500000000000000000 : ℝ)^8 ≤ (10854879848628401/10000000000000000 : ℝ)^39 := by
      have hnat : (18645841525099480369 : ℕ)^8*10000000000000000^39 ≤ 10854879848628401^39*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18645841525099480369 12500000000000000000 10854879848628401 10000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10854879848628401/10000000000000000 : ℝ)) (X := (18645841525099480369/12500000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(461201103435099/7499000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(196839372596651/3749500000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (7499/10000 : ℝ)) (alpha := (461201103435099/7499000000000000 : ℝ)) (beta := (196839372596651/3749500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (7499/10000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(461201103435099/7499000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(196839372596651/3749500000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (35999/100000 : ℝ) ^ (39/8 : ℝ) ≤ (6869353717851999/1000000000000000000 : ℝ) := by
    have hpowers : (35999/100000 : ℝ)^39 ≤ (6869353717851999/1000000000000000000 : ℝ)^8 := by
      have hnat : (35999 : ℕ)^39*1000000000000000000^8 ≤ 6869353717851999^8*100000^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35999 100000 6869353717851999 1000000000000000000 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (35999/100000 : ℝ)) (X := (6869353717851999/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (1006869353717851999/1000000000000000000 : ℝ) ≤ (625878291822297/625000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (1006869353717851999/1000000000000000000 : ℝ)^8 ≤ (625878291822297/625000000000000 : ℝ)^39 := by
      have hnat : (1006869353717851999 : ℕ)^8*625000000000000^39 ≤ 625878291822297^39*1000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1006869353717851999 1000000000000000000 625878291822297 625000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625878291822297/625000000000000 : ℝ)) (X := (1006869353717851999/1000000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (506869353717851999/500000000000000000 : ℝ) ≤ (2005605867217813/2000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (506869353717851999/500000000000000000 : ℝ)^8 ≤ (2005605867217813/2000000000000000 : ℝ)^39 := by
      have hnat : (506869353717851999 : ℕ)^8*2000000000000000^39 ≤ 2005605867217813^39*500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        506869353717851999 500000000000000000 2005605867217813 2000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2005605867217813/2000000000000000 : ℝ)) (X := (506869353717851999/500000000000000000 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(878291822297/224993750000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(13976666932313/3599900000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (35999/100000 : ℝ)) (alpha := (878291822297/224993750000000 : ℝ)) (beta := (13976666932313/3599900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (35999/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(878291822297/224993750000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(13976666932313/3599900000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_1 : ((805692139/2500000000 : ℝ)*X 1 0+(-3217195301/10000000000 : ℝ)*X 1 1+(236383651/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318057_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2806738701/5000000000 : ℝ)*X 2 0+(562206013/1000000000 : ℝ)*X 2 1+(-602349889/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318057_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((2232834399/5000000000 : ℝ)*X 0 0+(559062073/1250000000 : ℝ)*X 0 1+(353574147/1000000000 : ℝ)*X 0 2+(2232834399/5000000000 : ℝ)*X 1 0+(559062073/1250000000 : ℝ)*X 1 1+(353574147/1000000000 : ℝ)*X 1 2+(2232834399/5000000000 : ℝ)*X 2 0+(559062073/1250000000 : ℝ)*X 2 1+(353574147/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318057_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-97708637/312500000 : ℝ)*X 0 0+(2885845031/10000000000 : ℝ)*X 0 1+(6269041763/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318057_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((3121810279/10000000000 : ℝ)*X 1 0+(-360169217/1250000000 : ℝ)*X 1 1+(156920129/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318057_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((5361843291/10000000000 : ℝ)*X 2 0+(605059723/1000000000 : ℝ)*X 2 1+(-124391647/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318057_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_12 : ((918733841/2000000000 : ℝ)*X 0 0+(2591873789/5000000000 : ℝ)*X 0 1+(2595623873/10000000000 : ℝ)*X 0 2+(918733841/2000000000 : ℝ)*X 1 0+(2591873789/5000000000 : ℝ)*X 1 1+(2595623873/10000000000 : ℝ)*X 1 2+(918733841/2000000000 : ℝ)*X 2 0+(2591873789/5000000000 : ℝ)*X 2 1+(2595623873/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318057_s1_s1_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((-578281099/2000000000 : ℝ)*X 0 0+(3121224327/10000000000 : ℝ)*X 0 1+(1253808537/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318057_s1_s1_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((360863039/1250000000 : ℝ)*X 1 0+(-1558182687/5000000000 : ℝ)*X 1 1+(392300513/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318057_s1_s1_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((3021100637/5000000000 : ℝ)*X 2 0+(1074099619/2000000000 : ℝ)*X 2 1+(-248782281/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318057_s1_s1_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_18 : ((2588278147/5000000000 : ℝ)*X 0 0+(575135709/1250000000 : ℝ)*X 0 1+(1297809697/5000000000 : ℝ)*X 0 2+(2588278147/5000000000 : ℝ)*X 1 0+(575135709/1250000000 : ℝ)*X 1 1+(1297809697/5000000000 : ℝ)*X 1 2+(2588278147/5000000000 : ℝ)*X 2 0+(575135709/1250000000 : ℝ)*X 2 1+(1297809697/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318057_s1_s1_18 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_19 : ((-3378879637/10000000000 : ℝ)*X 0 0+(1541785109/5000000000 : ℝ)*X 0 1+(5888831081/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318057_s1_s1_19 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((771174371/2500000000 : ℝ)*X 1 0+(-842207733/2500000000 : ℝ)*X 1 1+(5896596447/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318057_s1_s1_20 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((2846615913/5000000000 : ℝ)*X 2 0+(555089139/1000000000 : ℝ)*X 2 1+(-586757381/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318057_s1_s1_21 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_25 : ((428553419/1000000000 : ℝ)*X 0 0+(4692276353/10000000000 : ℝ)*X 0 1+(3491084443/10000000000 : ℝ)*X 0 2+(428553419/1000000000 : ℝ)*X 1 0+(4692276353/10000000000 : ℝ)*X 1 1+(3491084443/10000000000 : ℝ)*X 1 2+(428553419/1000000000 : ℝ)*X 2 0+(4692276353/10000000000 : ℝ)*X 2 1+(3491084443/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318057_s1_s1_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((981/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(981/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7931776748779184579906077/492736312500000000000000000000 : ℝ) := by norm_num
    linear_combination (1247247/62500000000 : ℝ)*(base23) + (37223/12500000000 : ℝ)*(base49) + (5556982631119/1000000000000 : ℝ)*(base59) + (32646975579/12500000000 : ℝ)*(base60) + (10051302306973/1000000000000 : ℝ)*(major_s1_0) + (10051302306973/1000000000000 : ℝ)*(major_s1_1) + (10051302306973/1000000000000 : ℝ)*(major_s1_2) + (111072243/1000000000000 : ℝ)*(sp_s1_2) + (14594281776171/1000000000000 : ℝ)*(sp_s1_7) + (14593976062499/1000000000000 : ℝ)*(sp_s1_8) + (14594150747977/1000000000000 : ℝ)*(sp_s1_9) + (1377064601097/250000000000 : ℝ)*(sp_s1_12) + (38214209/125000000000 : ℝ)*(sp_s1_14) + (2953379/50000000000 : ℝ)*(sp_s1_25) + (172134920999/31250000000 : ℝ)*(f.failure) + (14594281776171/1000000000000 : ℝ)*(f.sum) + (42108004659862236033/269956501000000000000000000000000 : ℝ)*base63 + (2564340518075499/3599900000000000000000000000 : ℝ)*base64 + (63611005520727/3749500000000000000000000000 : ℝ)*base66 + (244675956747277/1799950000000000000000000000 : ℝ)*base69 + (8239154191213379027/11825671500000000000000000000000 : ℝ)*base70 + (359152775600779/3777750000000000000000000000 : ℝ)*base72 + (3659680643431373/7499000000000000000000000000 : ℝ)*base74 + (146305520512319/164250000000000000000000000 : ℝ)*base76 + (783740091905260961/56658694500000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (19/31250000000000 : ℝ)*base87 + (19/31250000000000 : ℝ)*base89 + (19/31250000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7837/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(7837/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (462157238489013214078283221831/33994272388425000000000000000000000 : ℝ) := by norm_num
    linear_combination (6775997/500000000000 : ℝ)*(base21) + (2778013807277/500000000000 : ℝ)*(base59) + (2947137576277/1000000000000 : ℝ)*(base60) + (5025167477711/500000000000 : ℝ)*(major_s1_0) + (5025167477711/500000000000 : ℝ)*(major_s1_1) + (5025167477711/500000000000 : ℝ)*(major_s1_2) + (3414261/1000000000000 : ℝ)*(sp_s1_1) + (1547731/50000000000 : ℝ)*(sp_s1_6) + (226606843/1000000000000 : ℝ)*(sp_s1_8) + (14592878035421/1000000000000 : ℝ)*(sp_s1_13) + (14592648014317/1000000000000 : ℝ)*(sp_s1_14) + (14592765157157/1000000000000 : ℝ)*(sp_s1_15) + (5507756389083/1000000000000 : ℝ)*(sp_s1_18) + (99326269/1000000000000 : ℝ)*(sp_s1_21) + (5507787343703/1000000000000 : ℝ)*(f.failure) + (14592878035421/1000000000000 : ℝ)*(f.sum) + (53935192339051458981/134978250500000000000000000000000 : ℝ)*base63 + (69417769399741/224993750000000000000000000 : ℝ)*base64 + (8591606648577/58585937500000000000000000 : ℝ)*base66 + (473787083807223/1799950000000000000000000000 : ℝ)*base69 + (59717330572851679/369552234375000000000000000000 : ℝ)*base70 + (503104156075381/3777750000000000000000000000 : ℝ)*base72 + (2198665414347089/3749500000000000000000000000 : ℝ)*base75 + (34493428103509/164250000000000000000000000 : ℝ)*base77 + (392834006225510723/28329347250000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (197/4000000000000000 : ℝ)*base87 + (197/4000000000000000 : ℝ)*base89 + (197/4000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(979/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(979/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1595004069209078113970631021/134978250500000000000000000000000 : ℝ) := by norm_num
    linear_combination (2614069/1000000000000 : ℝ)*(base40) + (2583867/1000000000000 : ℝ)*(base50) + (929452049093/1000000000000 : ℝ)*(base59) + (3191339989249/1000000000000 : ℝ)*(major_s1_0) + (3191339989249/1000000000000 : ℝ)*(major_s1_1) + (3191339989249/1000000000000 : ℝ)*(major_s1_2) + (3583153/1000000000000 : ℝ)*(sp_s1_1) + (12940779/500000000000 : ℝ)*(sp_s1_9) + (98941293/1000000000000 : ℝ)*(sp_s1_12) + (15108857/200000000000 : ℝ)*(sp_s1_15) + (4633757015463/1000000000000 : ℝ)*(sp_s1_19) + (463375343231/100000000000 : ℝ)*(sp_s1_20) + (4633655589621/1000000000000 : ℝ)*(sp_s1_21) + (1748820082819/1000000000000 : ℝ)*(sp_s1_25) + (1748919024113/1000000000000 : ℝ)*(f.failure) + (4633757015463/1000000000000 : ℝ)*(f.sum) + (65302526389779096571/269956501000000000000000000000000 : ℝ)*base62 + (177210552081013/3599900000000000000000000000 : ℝ)*base65 + (1177457301435549/3749500000000000000000000000 : ℝ)*base67 + (54300098275709/1799950000000000000000000000 : ℝ)*base68 + (6071516983908917449/11825671500000000000000000000000 : ℝ)*base71 + (333608342432113/944437500000000000000000000 : ℝ)*base72 + (6195738548690449/7499000000000000000000000000 : ℝ)*base74 + (19298413843397/164250000000000000000000000 : ℝ)*base76 + (6607393818922577243/56658694500000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (4787/4000000000000000 : ℝ)*base87 + (4787/4000000000000000 : ℝ)*base89 + (4787/4000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((15111/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15111/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7499/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(7499/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(35999/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(35999/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((981/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(981/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7837/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(7837/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(979/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(979/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c318057_s1 p hpa hpb X hX hprev0

#print axioms solution
