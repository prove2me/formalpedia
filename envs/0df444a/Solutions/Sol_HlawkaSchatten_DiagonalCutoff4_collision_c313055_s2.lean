-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c313055_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:33:30.260254+00:00
-- url     : https://prove2.me/submissions/e5f4ac1a-f2b8-4609-899d-b65e8006b692

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
theorem collision_support_c313055_s2_s2_0 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-119741503/625000000 : ℝ)*x 0 + (568299941/1000000000 : ℝ)*x 1 + (2401264939/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (119741503/625000000 : ℝ)^37 ≤ (6072483314047/50000000000000 : ℝ)^29 := by
    have hnat : (119741503 : ℕ)^37*50000000000000^29 ≤ 6072483314047^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119741503 625000000 6072483314047 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (568299941/1000000000 : ℝ)^37 ≤ (24313354776319/50000000000000 : ℝ)^29 := by
    have hnat : (568299941 : ℕ)^37*50000000000000^29 ≤ 24313354776319^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      568299941 1000000000 24313354776319 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2401264939/5000000000 : ℝ)^37 ≤ (39228323798611/100000000000000 : ℝ)^29 := by
    have hnat : (2401264939 : ℕ)^37*100000000000000^29 ≤ 39228323798611^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2401264939 5000000000 39228323798611 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-119741503/625000000 : ℝ), (568299941/1000000000 : ℝ), (2401264939/5000000000 : ℝ)] ![(6072483314047/50000000000000 : ℝ), (24313354776319/50000000000000 : ℝ), (39228323798611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-119741503/625000000 : ℝ)|^37 ≤ (6072483314047/50000000000000 : ℝ)^29
        have hw : |(-119741503/625000000 : ℝ)|=(119741503/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(568299941/1000000000 : ℝ)|^37 ≤ (24313354776319/50000000000000 : ℝ)^29
        have hw : |(568299941/1000000000 : ℝ)|=(568299941/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2401264939/5000000000 : ℝ)|^37 ≤ (39228323798611/100000000000000 : ℝ)^29
        have hw : |(2401264939/5000000000 : ℝ)|=(2401264939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313055_s2_s2_6 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6148610423/10000000000 : ℝ)*x 0 + (3908511199/10000000000 : ℝ)*x 1 + (1193148323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6148610423/10000000000 : ℝ)^37 ≤ (26883051320647/50000000000000 : ℝ)^29 := by
    have hnat : (6148610423 : ℕ)^37*50000000000000^29 ≤ 26883051320647^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6148610423 10000000000 26883051320647 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3908511199/10000000000 : ℝ)^37 ≤ (30162182995973/100000000000000 : ℝ)^29 := by
    have hnat : (3908511199 : ℕ)^37*100000000000000^29 ≤ 30162182995973^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3908511199 10000000000 30162182995973 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1193148323/5000000000 : ℝ)^37 ≤ (16071714348589/100000000000000 : ℝ)^29 := by
    have hnat : (1193148323 : ℕ)^37*100000000000000^29 ≤ 16071714348589^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1193148323 5000000000 16071714348589 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6148610423/10000000000 : ℝ), (3908511199/10000000000 : ℝ), (1193148323/5000000000 : ℝ)] ![(26883051320647/50000000000000 : ℝ), (30162182995973/100000000000000 : ℝ), (16071714348589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6148610423/10000000000 : ℝ)|^37 ≤ (26883051320647/50000000000000 : ℝ)^29
        have hw : |(6148610423/10000000000 : ℝ)|=(6148610423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3908511199/10000000000 : ℝ)|^37 ≤ (30162182995973/100000000000000 : ℝ)^29
        have hw : |(3908511199/10000000000 : ℝ)|=(3908511199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1193148323/5000000000 : ℝ)|^37 ≤ (16071714348589/100000000000000 : ℝ)^29
        have hw : |(1193148323/5000000000 : ℝ)|=(1193148323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313055_s2_s2_7 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-94663103/625000000 : ℝ)*x 0 + (2455101593/5000000000 : ℝ)*x 1 + (5867283869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (94663103/625000000 : ℝ)^37 ≤ (1799727592113/20000000000000 : ℝ)^29 := by
    have hnat : (94663103 : ℕ)^37*20000000000000^29 ≤ 1799727592113^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94663103 625000000 1799727592113 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2455101593/5000000000 : ℝ)^37 ≤ (2522118803887/6250000000000 : ℝ)^29 := by
    have hnat : (2455101593 : ℕ)^37*6250000000000^29 ≤ 2522118803887^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2455101593 5000000000 2522118803887 6250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5867283869/10000000000 : ℝ)^37 ≤ (25323730581953/50000000000000 : ℝ)^29 := by
    have hnat : (5867283869 : ℕ)^37*50000000000000^29 ≤ 25323730581953^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5867283869 10000000000 25323730581953 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-94663103/625000000 : ℝ), (2455101593/5000000000 : ℝ), (5867283869/10000000000 : ℝ)] ![(1799727592113/20000000000000 : ℝ), (2522118803887/6250000000000 : ℝ), (25323730581953/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-94663103/625000000 : ℝ)|^37 ≤ (1799727592113/20000000000000 : ℝ)^29
        have hw : |(-94663103/625000000 : ℝ)|=(94663103/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2455101593/5000000000 : ℝ)|^37 ≤ (2522118803887/6250000000000 : ℝ)^29
        have hw : |(2455101593/5000000000 : ℝ)|=(2455101593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5867283869/10000000000 : ℝ)|^37 ≤ (25323730581953/50000000000000 : ℝ)^29
        have hw : |(5867283869/10000000000 : ℝ)|=(5867283869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313055_s2_s2_8 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (910804789/2000000000 : ℝ)*x 0 + (-205572097/10000000000 : ℝ)*x 1 + (1386114279/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (910804789/2000000000 : ℝ)^37 ≤ (7331444121909/20000000000000 : ℝ)^29 := by
    have hnat : (910804789 : ℕ)^37*20000000000000^29 ≤ 7331444121909^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      910804789 2000000000 7331444121909 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (205572097/10000000000 : ℝ)^37 ≤ (88000468343/12500000000000 : ℝ)^29 := by
    have hnat : (205572097 : ℕ)^37*12500000000000^29 ≤ 88000468343^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205572097 10000000000 88000468343 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1386114279/2000000000 : ℝ)^37 ≤ (62638775626507/100000000000000 : ℝ)^29 := by
    have hnat : (1386114279 : ℕ)^37*100000000000000^29 ≤ 62638775626507^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1386114279 2000000000 62638775626507 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(910804789/2000000000 : ℝ), (-205572097/10000000000 : ℝ), (1386114279/2000000000 : ℝ)] ![(7331444121909/20000000000000 : ℝ), (88000468343/12500000000000 : ℝ), (62638775626507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(910804789/2000000000 : ℝ)|^37 ≤ (7331444121909/20000000000000 : ℝ)^29
        have hw : |(910804789/2000000000 : ℝ)|=(910804789/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-205572097/10000000000 : ℝ)|^37 ≤ (88000468343/12500000000000 : ℝ)^29
        have hw : |(-205572097/10000000000 : ℝ)|=(205572097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1386114279/2000000000 : ℝ)|^37 ≤ (62638775626507/100000000000000 : ℝ)^29
        have hw : |(1386114279/2000000000 : ℝ)|=(1386114279/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313055_s2_s2_9 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2267748997/5000000000 : ℝ)*x 0 + (1318273871/2000000000 : ℝ)*x 1 + (-461154659/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2267748997/5000000000 : ℝ)^37 ≤ (569797922613/1562500000000 : ℝ)^29 := by
    have hnat : (2267748997 : ℕ)^37*1562500000000^29 ≤ 569797922613^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2267748997 5000000000 569797922613 1562500000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1318273871/2000000000 : ℝ)^37 ≤ (7344257735973/12500000000000 : ℝ)^29 := by
    have hnat : (1318273871 : ℕ)^37*12500000000000^29 ≤ 7344257735973^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318273871 2000000000 7344257735973 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (461154659/5000000000 : ℝ)^37 ≤ (4778871056151/100000000000000 : ℝ)^29 := by
    have hnat : (461154659 : ℕ)^37*100000000000000^29 ≤ 4778871056151^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      461154659 5000000000 4778871056151 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2267748997/5000000000 : ℝ), (1318273871/2000000000 : ℝ), (-461154659/5000000000 : ℝ)] ![(569797922613/1562500000000 : ℝ), (7344257735973/12500000000000 : ℝ), (4778871056151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2267748997/5000000000 : ℝ)|^37 ≤ (569797922613/1562500000000 : ℝ)^29
        have hw : |(2267748997/5000000000 : ℝ)|=(2267748997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1318273871/2000000000 : ℝ)|^37 ≤ (7344257735973/12500000000000 : ℝ)^29
        have hw : |(1318273871/2000000000 : ℝ)|=(1318273871/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-461154659/5000000000 : ℝ)|^37 ≤ (4778871056151/100000000000000 : ℝ)^29
        have hw : |(-461154659/5000000000 : ℝ)|=(461154659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313055_s2_s2_13 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5134065871/10000000000 : ℝ)*x 0 + (5920369867/10000000000 : ℝ)*x 1 + (44390957/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5134065871/10000000000 : ℝ)^37 ≤ (21357909089719/50000000000000 : ℝ)^29 := by
    have hnat : (5134065871 : ℕ)^37*50000000000000^29 ≤ 21357909089719^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5134065871 10000000000 21357909089719 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5920369867/10000000000 : ℝ)^37 ≤ (12808212610567/25000000000000 : ℝ)^29 := by
    have hnat : (5920369867 : ℕ)^37*25000000000000^29 ≤ 12808212610567^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5920369867 10000000000 12808212610567 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (44390957/400000000 : ℝ)^37 ≤ (3025665680651/50000000000000 : ℝ)^29 := by
    have hnat : (44390957 : ℕ)^37*50000000000000^29 ≤ 3025665680651^29*400000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44390957 400000000 3025665680651 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5134065871/10000000000 : ℝ), (5920369867/10000000000 : ℝ), (44390957/400000000 : ℝ)] ![(21357909089719/50000000000000 : ℝ), (12808212610567/25000000000000 : ℝ), (3025665680651/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5134065871/10000000000 : ℝ)|^37 ≤ (21357909089719/50000000000000 : ℝ)^29
        have hw : |(5134065871/10000000000 : ℝ)|=(5134065871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5920369867/10000000000 : ℝ)|^37 ≤ (12808212610567/25000000000000 : ℝ)^29
        have hw : |(5920369867/10000000000 : ℝ)|=(5920369867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(44390957/400000000 : ℝ)|^37 ≤ (3025665680651/50000000000000 : ℝ)^29
        have hw : |(44390957/400000000 : ℝ)|=(44390957/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313055_s2_s2_14 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-396508133/5000000000 : ℝ)*x 0 + (5243026821/10000000000 : ℝ)*x 1 + (3003123393/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (396508133/5000000000 : ℝ)^37 ≤ (3941266273599/100000000000000 : ℝ)^29 := by
    have hnat : (396508133 : ℕ)^37*100000000000000^29 ≤ 3941266273599^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396508133 5000000000 3941266273599 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243026821/10000000000 : ℝ)^37 ≤ (21937918359679/50000000000000 : ℝ)^29 := by
    have hnat : (5243026821 : ℕ)^37*50000000000000^29 ≤ 21937918359679^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243026821 10000000000 21937918359679 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3003123393/5000000000 : ℝ)^37 ≤ (26091448494507/50000000000000 : ℝ)^29 := by
    have hnat : (3003123393 : ℕ)^37*50000000000000^29 ≤ 26091448494507^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3003123393 5000000000 26091448494507 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-396508133/5000000000 : ℝ), (5243026821/10000000000 : ℝ), (3003123393/5000000000 : ℝ)] ![(3941266273599/100000000000000 : ℝ), (21937918359679/50000000000000 : ℝ), (26091448494507/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-396508133/5000000000 : ℝ)|^37 ≤ (3941266273599/100000000000000 : ℝ)^29
        have hw : |(-396508133/5000000000 : ℝ)|=(396508133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243026821/10000000000 : ℝ)|^37 ≤ (21937918359679/50000000000000 : ℝ)^29
        have hw : |(5243026821/10000000000 : ℝ)|=(5243026821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3003123393/5000000000 : ℝ)|^37 ≤ (26091448494507/50000000000000 : ℝ)^29
        have hw : |(3003123393/5000000000 : ℝ)|=(3003123393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313055_s2_s2_15 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4248188859/10000000000 : ℝ)*x 0 + (-369895763/5000000000 : ℝ)*x 1 + (694863633/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4248188859/10000000000 : ℝ)^37 ≤ (33545892506649/100000000000000 : ℝ)^29 := by
    have hnat : (4248188859 : ℕ)^37*100000000000000^29 ≤ 33545892506649^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4248188859 10000000000 33545892506649 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (369895763/5000000000 : ℝ)^37 ≤ (1803472493451/50000000000000 : ℝ)^29 := by
    have hnat : (369895763 : ℕ)^37*50000000000000^29 ≤ 1803472493451^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      369895763 5000000000 1803472493451 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (694863633/1000000000 : ℝ)^37 ≤ (12569432500257/20000000000000 : ℝ)^29 := by
    have hnat : (694863633 : ℕ)^37*20000000000000^29 ≤ 12569432500257^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      694863633 1000000000 12569432500257 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4248188859/10000000000 : ℝ), (-369895763/5000000000 : ℝ), (694863633/1000000000 : ℝ)] ![(33545892506649/100000000000000 : ℝ), (1803472493451/50000000000000 : ℝ), (12569432500257/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4248188859/10000000000 : ℝ)|^37 ≤ (33545892506649/100000000000000 : ℝ)^29
        have hw : |(4248188859/10000000000 : ℝ)|=(4248188859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-369895763/5000000000 : ℝ)|^37 ≤ (1803472493451/50000000000000 : ℝ)^29
        have hw : |(-369895763/5000000000 : ℝ)|=(369895763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(694863633/1000000000 : ℝ)|^37 ≤ (12569432500257/20000000000000 : ℝ)^29
        have hw : |(694863633/1000000000 : ℝ)|=(694863633/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313055_s2_s2_16 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (597311373/1000000000 : ℝ)*x 0 + (5283090377/10000000000 : ℝ)*x 1 + (-48959159/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (597311373/1000000000 : ℝ)^37 ≤ (51815902774801/100000000000000 : ℝ)^29 := by
    have hnat : (597311373 : ℕ)^37*100000000000000^29 ≤ 51815902774801^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      597311373 1000000000 51815902774801 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5283090377/10000000000 : ℝ)^37 ≤ (11076010792539/25000000000000 : ℝ)^29 := by
    have hnat : (5283090377 : ℕ)^37*25000000000000^29 ≤ 11076010792539^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5283090377 10000000000 11076010792539 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (48959159/625000000 : ℝ)^37 ≤ (6208086473/160000000000 : ℝ)^29 := by
    have hnat : (48959159 : ℕ)^37*160000000000^29 ≤ 6208086473^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48959159 625000000 6208086473 160000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(597311373/1000000000 : ℝ), (5283090377/10000000000 : ℝ), (-48959159/625000000 : ℝ)] ![(51815902774801/100000000000000 : ℝ), (11076010792539/25000000000000 : ℝ), (6208086473/160000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(597311373/1000000000 : ℝ)|^37 ≤ (51815902774801/100000000000000 : ℝ)^29
        have hw : |(597311373/1000000000 : ℝ)|=(597311373/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5283090377/10000000000 : ℝ)|^37 ≤ (11076010792539/25000000000000 : ℝ)^29
        have hw : |(5283090377/10000000000 : ℝ)|=(5283090377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-48959159/625000000 : ℝ)|^37 ≤ (6208086473/160000000000 : ℝ)^29
        have hw : |(-48959159/625000000 : ℝ)|=(48959159/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313055_s2_s2_20 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1515208147/2000000000 : ℝ)*x 0 + (102350223/312500000 : ℝ)*x 1 + (533301391/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1515208147/2000000000 : ℝ)^37 ≤ (35087708732799/50000000000000 : ℝ)^29 := by
    have hnat : (1515208147 : ℕ)^37*50000000000000^29 ≤ 35087708732799^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1515208147 2000000000 35087708732799 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (102350223/312500000 : ℝ)^37 ≤ (24071964603427/100000000000000 : ℝ)^29 := by
    have hnat : (102350223 : ℕ)^37*100000000000000^29 ≤ 24071964603427^29*312500000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102350223 312500000 24071964603427 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (533301391/5000000000 : ℝ)^37 ≤ (115052358249/2000000000000 : ℝ)^29 := by
    have hnat : (533301391 : ℕ)^37*2000000000000^29 ≤ 115052358249^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533301391 5000000000 115052358249 2000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1515208147/2000000000 : ℝ), (102350223/312500000 : ℝ), (533301391/5000000000 : ℝ)] ![(35087708732799/50000000000000 : ℝ), (24071964603427/100000000000000 : ℝ), (115052358249/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1515208147/2000000000 : ℝ)|^37 ≤ (35087708732799/50000000000000 : ℝ)^29
        have hw : |(1515208147/2000000000 : ℝ)|=(1515208147/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(102350223/312500000 : ℝ)|^37 ≤ (24071964603427/100000000000000 : ℝ)^29
        have hw : |(102350223/312500000 : ℝ)|=(102350223/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(533301391/5000000000 : ℝ)|^37 ≤ (115052358249/2000000000000 : ℝ)^29
        have hw : |(533301391/5000000000 : ℝ)|=(533301391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313055_s2_s2_21 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-159654627/2000000000 : ℝ)*x 0 + (399028841/625000000 : ℝ)*x 1 + (96790261/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (159654627/2000000000 : ℝ)^37 ≤ (3974630483141/100000000000000 : ℝ)^29 := by
    have hnat : (159654627 : ℕ)^37*100000000000000^29 ≤ 3974630483141^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      159654627 2000000000 3974630483141 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (399028841/625000000 : ℝ)^37 ≤ (28205607071083/50000000000000 : ℝ)^29 := by
    have hnat : (399028841 : ℕ)^37*50000000000000^29 ≤ 28205607071083^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399028841 625000000 28205607071083 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (96790261/200000000 : ℝ)^37 ≤ (7922831073279/20000000000000 : ℝ)^29 := by
    have hnat : (96790261 : ℕ)^37*20000000000000^29 ≤ 7922831073279^29*200000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96790261 200000000 7922831073279 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-159654627/2000000000 : ℝ), (399028841/625000000 : ℝ), (96790261/200000000 : ℝ)] ![(3974630483141/100000000000000 : ℝ), (28205607071083/50000000000000 : ℝ), (7922831073279/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-159654627/2000000000 : ℝ)|^37 ≤ (3974630483141/100000000000000 : ℝ)^29
        have hw : |(-159654627/2000000000 : ℝ)|=(159654627/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(399028841/625000000 : ℝ)|^37 ≤ (28205607071083/50000000000000 : ℝ)^29
        have hw : |(399028841/625000000 : ℝ)|=(399028841/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(96790261/200000000 : ℝ)|^37 ≤ (7922831073279/20000000000000 : ℝ)^29
        have hw : |(96790261/200000000 : ℝ)|=(96790261/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313055_s2_s2_22 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1496595731/2500000000 : ℝ)*x 0 + (-187538691/10000000000 : ℝ)*x 1 + (1392833987/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1496595731/2500000000 : ℝ)^37 ≤ (25981405064377/50000000000000 : ℝ)^29 := by
    have hnat : (1496595731 : ℕ)^37*50000000000000^29 ≤ 25981405064377^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1496595731 2500000000 25981405064377 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (187538691/10000000000 : ℝ)^37 ≤ (626184275661/100000000000000 : ℝ)^29 := by
    have hnat : (187538691 : ℕ)^37*100000000000000^29 ≤ 626184275661^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187538691 10000000000 626184275661 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1392833987/2500000000 : ℝ)^37 ≤ (23705502792013/50000000000000 : ℝ)^29 := by
    have hnat : (1392833987 : ℕ)^37*50000000000000^29 ≤ 23705502792013^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1392833987 2500000000 23705502792013 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1496595731/2500000000 : ℝ), (-187538691/10000000000 : ℝ), (1392833987/2500000000 : ℝ)] ![(25981405064377/50000000000000 : ℝ), (626184275661/100000000000000 : ℝ), (23705502792013/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1496595731/2500000000 : ℝ)|^37 ≤ (25981405064377/50000000000000 : ℝ)^29
        have hw : |(1496595731/2500000000 : ℝ)|=(1496595731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-187538691/10000000000 : ℝ)|^37 ≤ (626184275661/100000000000000 : ℝ)^29
        have hw : |(-187538691/10000000000 : ℝ)|=(187538691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1392833987/2500000000 : ℝ)|^37 ≤ (23705502792013/50000000000000 : ℝ)^29
        have hw : |(1392833987/2500000000 : ℝ)|=(1392833987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313055_s2_s2_23 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4216339931/10000000000 : ℝ)*x 0 + (6609402849/10000000000 : ℝ)*x 1 + (-1356169373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4216339931/10000000000 : ℝ)^37 ≤ (33225351247959/100000000000000 : ℝ)^29 := by
    have hnat : (4216339931 : ℕ)^37*100000000000000^29 ≤ 33225351247959^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4216339931 10000000000 33225351247959 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6609402849/10000000000 : ℝ)^37 ≤ (58959229877907/100000000000000 : ℝ)^29 := by
    have hnat : (6609402849 : ℕ)^37*100000000000000^29 ≤ 58959229877907^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6609402849 10000000000 58959229877907 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356169373/10000000000 : ℝ)^37 ≤ (7815418857167/100000000000000 : ℝ)^29 := by
    have hnat : (1356169373 : ℕ)^37*100000000000000^29 ≤ 7815418857167^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356169373 10000000000 7815418857167 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4216339931/10000000000 : ℝ), (6609402849/10000000000 : ℝ), (-1356169373/10000000000 : ℝ)] ![(33225351247959/100000000000000 : ℝ), (58959229877907/100000000000000 : ℝ), (7815418857167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4216339931/10000000000 : ℝ)|^37 ≤ (33225351247959/100000000000000 : ℝ)^29
        have hw : |(4216339931/10000000000 : ℝ)|=(4216339931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6609402849/10000000000 : ℝ)|^37 ≤ (58959229877907/100000000000000 : ℝ)^29
        have hw : |(6609402849/10000000000 : ℝ)|=(6609402849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1356169373/10000000000 : ℝ)|^37 ≤ (7815418857167/100000000000000 : ℝ)^29
        have hw : |(-1356169373/10000000000 : ℝ)|=(1356169373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313055_s2_s2_27 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7607878173/10000000000 : ℝ)*x 0 + (47945473/200000000 : ℝ)*x 1 + (82203129/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7607878173/10000000000 : ℝ)^37 ≤ (35275946148999/50000000000000 : ℝ)^29 := by
    have hnat : (7607878173 : ℕ)^37*50000000000000^29 ≤ 35275946148999^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7607878173 10000000000 35275946148999 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (47945473/200000000 : ℝ)^37 ≤ (3233219761197/20000000000000 : ℝ)^29 := by
    have hnat : (47945473 : ℕ)^37*20000000000000^29 ≤ 3233219761197^29*200000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47945473 200000000 3233219761197 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82203129/400000000 : ℝ)^37 ≤ (1328200889087/10000000000000 : ℝ)^29 := by
    have hnat : (82203129 : ℕ)^37*10000000000000^29 ≤ 1328200889087^29*400000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82203129 400000000 1328200889087 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7607878173/10000000000 : ℝ), (47945473/200000000 : ℝ), (82203129/400000000 : ℝ)] ![(35275946148999/50000000000000 : ℝ), (3233219761197/20000000000000 : ℝ), (1328200889087/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7607878173/10000000000 : ℝ)|^37 ≤ (35275946148999/50000000000000 : ℝ)^29
        have hw : |(7607878173/10000000000 : ℝ)|=(7607878173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(47945473/200000000 : ℝ)|^37 ≤ (3233219761197/20000000000000 : ℝ)^29
        have hw : |(47945473/200000000 : ℝ)|=(47945473/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(82203129/400000000 : ℝ)|^37 ≤ (1328200889087/10000000000000 : ℝ)^29
        have hw : |(82203129/400000000 : ℝ)|=(82203129/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c313055_s2 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((33021/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(33021/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2011/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2011/3125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(65489/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(65489/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((43631/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(43631/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(44399/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(44399/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2779/6250 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(2779/6250 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (78599/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (78599/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (78599/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (78599/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78599/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78599/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (33021/50000 : ℝ) ^ (73/16 : ℝ) ≤ (188295418194927021/1250000000000000000 : ℝ) := by
    have hpowers : (33021/50000 : ℝ)^73 ≤ (188295418194927021/1250000000000000000 : ℝ)^16 := by
      have hnat : (33021 : ℕ)^73*1250000000000000000^16 ≤ 188295418194927021^16*50000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33021 50000 188295418194927021 1250000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (33021/50000 : ℝ)) (X := (188295418194927021/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (1438295418194927021/1250000000000000000 : ℝ) ≤ (2062463578751181/2000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (1438295418194927021/1250000000000000000 : ℝ)^16 ≤ (2062463578751181/2000000000000000 : ℝ)^73 := by
      have hnat : (1438295418194927021 : ℕ)^16*2000000000000000^73 ≤ 2062463578751181^73*1250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1438295418194927021 1250000000000000000 2062463578751181 2000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2062463578751181/2000000000000000 : ℝ)) (X := (1438295418194927021/1250000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (813295418194927021/625000000000000000 : ℝ) ≤ (2118834433676393/2000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (813295418194927021/625000000000000000 : ℝ)^16 ≤ (2118834433676393/2000000000000000 : ℝ)^73 := by
      have hnat : (813295418194927021 : ℕ)^16*2000000000000000^73 ≤ 2118834433676393^73*625000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        813295418194927021 625000000000000000 2118834433676393 2000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2118834433676393/2000000000000000 : ℝ)) (X := (813295418194927021/625000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(62463578751181/1320840000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(14092713731303/330210000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (33021/50000 : ℝ)) (alpha := (62463578751181/1320840000000000 : ℝ)) (beta := (14092713731303/330210000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (33021/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(62463578751181/1320840000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(14092713731303/330210000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (2011/3125 : ℝ) ^ (73/16 : ℝ) ≤ (836458435965305421/6250000000000000000 : ℝ) := by
    have hpowers : (2011/3125 : ℝ)^73 ≤ (836458435965305421/6250000000000000000 : ℝ)^16 := by
      have hnat : (2011 : ℕ)^73*6250000000000000000^16 ≤ 836458435965305421^16*3125^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2011 3125 836458435965305421 6250000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2011/3125 : ℝ)) (X := (836458435965305421/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (7086458435965305421/6250000000000000000 : ℝ) ≤ (10279121392214927/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (7086458435965305421/6250000000000000000 : ℝ)^16 ≤ (10279121392214927/10000000000000000 : ℝ)^73 := by
      have hnat : (7086458435965305421 : ℕ)^16*10000000000000000^73 ≤ 10279121392214927^73*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7086458435965305421 6250000000000000000 10279121392214927 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10279121392214927/10000000000000000 : ℝ)) (X := (7086458435965305421/6250000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (3961458435965305421/3125000000000000000 : ℝ) ≤ (1053359111702691/1000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (3961458435965305421/3125000000000000000 : ℝ)^16 ≤ (1053359111702691/1000000000000000 : ℝ)^73 := by
      have hnat : (3961458435965305421 : ℕ)^16*1000000000000000^73 ≤ 1053359111702691^73*3125000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3961458435965305421 3125000000000000000 1053359111702691 1000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1053359111702691/1000000000000000 : ℝ)) (X := (3961458435965305421/3125000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(279121392214927/6435200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(254469724811983/6435200000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (2011/3125 : ℝ)) (alpha := (279121392214927/6435200000000000 : ℝ)) (beta := (254469724811983/6435200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (2011/3125 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(279121392214927/6435200000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(254469724811983/6435200000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (65489/100000 : ℝ) ^ (73/16 : ℝ) ≤ (7078450269945029/48828125000000000 : ℝ) := by
    have hpowers : (65489/100000 : ℝ)^73 ≤ (7078450269945029/48828125000000000 : ℝ)^16 := by
      have hnat : (65489 : ℕ)^73*48828125000000000^16 ≤ 7078450269945029^16*100000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        65489 100000 7078450269945029 48828125000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (65489/100000 : ℝ)) (X := (7078450269945029/48828125000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (55906575269945029/48828125000000000 : ℝ) ≤ (10301159274723877/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (55906575269945029/48828125000000000 : ℝ)^16 ≤ (10301159274723877/10000000000000000 : ℝ)^73 := by
      have hnat : (55906575269945029 : ℕ)^16*10000000000000000^73 ≤ 10301159274723877^73*48828125000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55906575269945029 48828125000000000 10301159274723877 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10301159274723877/10000000000000000 : ℝ)) (X := (55906575269945029/48828125000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (31492512769945029/24414062500000000 : ℝ) ≤ (2643467218628967/2500000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (31492512769945029/24414062500000000 : ℝ)^16 ≤ (2643467218628967/2500000000000000 : ℝ)^73 := by
      have hnat : (31492512769945029 : ℕ)^16*2500000000000000^73 ≤ 2643467218628967^73*24414062500000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31492512769945029 24414062500000000 2643467218628967 2500000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2643467218628967/2500000000000000 : ℝ)) (X := (31492512769945029/24414062500000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(301159274723877/6548900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(272709599791991/6548900000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (65489/100000 : ℝ)) (alpha := (301159274723877/6548900000000000 : ℝ)) (beta := (272709599791991/6548900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (65489/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(301159274723877/6548900000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(272709599791991/6548900000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-119741503/625000000 : ℝ)*X 0 0+(568299941/1000000000 : ℝ)*X 0 1+(2401264939/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313055_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((6148610423/10000000000 : ℝ)*X 0 0+(3908511199/10000000000 : ℝ)*X 0 1+(1193148323/5000000000 : ℝ)*X 0 2+(6148610423/10000000000 : ℝ)*X 1 0+(3908511199/10000000000 : ℝ)*X 1 1+(1193148323/5000000000 : ℝ)*X 1 2+(6148610423/10000000000 : ℝ)*X 2 0+(3908511199/10000000000 : ℝ)*X 2 1+(1193148323/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313055_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-94663103/625000000 : ℝ)*X 0 0+(2455101593/5000000000 : ℝ)*X 0 1+(5867283869/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313055_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((910804789/2000000000 : ℝ)*X 1 0+(-205572097/10000000000 : ℝ)*X 1 1+(1386114279/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313055_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((2267748997/5000000000 : ℝ)*X 2 0+(1318273871/2000000000 : ℝ)*X 2 1+(-461154659/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313055_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((5134065871/10000000000 : ℝ)*X 0 0+(5920369867/10000000000 : ℝ)*X 0 1+(44390957/400000000 : ℝ)*X 0 2+(5134065871/10000000000 : ℝ)*X 1 0+(5920369867/10000000000 : ℝ)*X 1 1+(44390957/400000000 : ℝ)*X 1 2+(5134065871/10000000000 : ℝ)*X 2 0+(5920369867/10000000000 : ℝ)*X 2 1+(44390957/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313055_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-396508133/5000000000 : ℝ)*X 0 0+(5243026821/10000000000 : ℝ)*X 0 1+(3003123393/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313055_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((4248188859/10000000000 : ℝ)*X 1 0+(-369895763/5000000000 : ℝ)*X 1 1+(694863633/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313055_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((597311373/1000000000 : ℝ)*X 2 0+(5283090377/10000000000 : ℝ)*X 2 1+(-48959159/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313055_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((1515208147/2000000000 : ℝ)*X 0 0+(102350223/312500000 : ℝ)*X 0 1+(533301391/5000000000 : ℝ)*X 0 2+(1515208147/2000000000 : ℝ)*X 1 0+(102350223/312500000 : ℝ)*X 1 1+(533301391/5000000000 : ℝ)*X 1 2+(1515208147/2000000000 : ℝ)*X 2 0+(102350223/312500000 : ℝ)*X 2 1+(533301391/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313055_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-159654627/2000000000 : ℝ)*X 0 0+(399028841/625000000 : ℝ)*X 0 1+(96790261/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313055_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((1496595731/2500000000 : ℝ)*X 1 0+(-187538691/10000000000 : ℝ)*X 1 1+(1392833987/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313055_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((4216339931/10000000000 : ℝ)*X 2 0+(6609402849/10000000000 : ℝ)*X 2 1+(-1356169373/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313055_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((7607878173/10000000000 : ℝ)*X 0 0+(47945473/200000000 : ℝ)*X 0 1+(82203129/400000000 : ℝ)*X 0 2+(7607878173/10000000000 : ℝ)*X 1 0+(47945473/200000000 : ℝ)*X 1 1+(82203129/400000000 : ℝ)*X 1 2+(7607878173/10000000000 : ℝ)*X 2 0+(47945473/200000000 : ℝ)*X 2 1+(82203129/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313055_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((43631/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(43631/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (17560796172251136161609581673/2416006762755000000000000000000000 : ℝ) := by norm_num
    linear_combination (4518591/1000000000000 : ℝ)*(base19) + (29258100123/100000000000 : ℝ)*(base49) + (2160829168807/500000000000 : ℝ)*(major_s2_0) + (2160829168807/500000000000 : ℝ)*(major_s2_1) + (2160829168807/500000000000 : ℝ)*(major_s2_2) + (1479243/100000000000 : ℝ)*(sp_s2_0) + (1145063/1000000000000 : ℝ)*(sp_s2_6) + (3046725775573/500000000000 : ℝ)*(sp_s2_7) + (6093440152529/1000000000000 : ℝ)*(sp_s2_8) + (1523346996629/250000000000 : ℝ)*(sp_s2_9) + (2549845355031/1000000000000 : ℝ)*(sp_s2_13) + (2308117/100000000000 : ℝ)*(sp_s2_15) + (1408713/1000000000000 : ℝ)*(sp_s2_21) + (39882887/500000000000 : ℝ)*(sp_s2_23) + (1274923250047/500000000000 : ℝ)*(f.failure) + (609346775229/100000000000 : ℝ)*(f.sum) + (46197469167000083431/210717406400000000000000000000000 : ℝ)*base62 + (1030232178504627/3274450000000000000000000000 : ℝ)*base65 + (436317677943401/3217600000000000000000000000 : ℝ)*base66 + (451198666700293/1637225000000000000000000000 : ℝ)*base68 + (6145794792593617121/216251226900000000000000000000000 : ℝ)*base70 + (55989449360473/165105000000000000000000000 : ℝ)*base72 + (950271459278391/3217600000000000000000000000 : ℝ)*base74 + (197460529095173/660420000000000000000000000 : ℝ)*base76 + (42838803235226686661/106248369600000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (15889/50000000000000000 : ℝ)*base87 + (15889/50000000000000000 : ℝ)*base89 + (15889/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(44399/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(44399/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (537924478888626593192232351/42143481280000000000000000000000 : ℝ) := by norm_num
    linear_combination (1015971/1000000000000 : ℝ)*(base21) + (3345727/1000000000000 : ℝ)*(base39) + (206055038801/1000000000000 : ℝ)*(base49) + (184969/200000000000 : ℝ)*(base60) + (4067962107113/1000000000000 : ℝ)*(major_s2_0) + (4067962107113/1000000000000 : ℝ)*(major_s2_1) + (4067962107113/1000000000000 : ℝ)*(major_s2_2) + (13281407/500000000000 : ℝ)*(sp_s2_7) + (77589503/1000000000000 : ℝ)*(sp_s2_8) + (5735731669187/1000000000000 : ℝ)*(sp_s2_14) + (5735680642497/1000000000000 : ℝ)*(sp_s2_15) + (5735757216029/1000000000000 : ℝ)*(sp_s2_16) + (240009598007/100000000000 : ℝ)*(sp_s2_20) + (13149489/200000000000 : ℝ)*(sp_s2_27) + (480032345503/200000000000 : ℝ)*(f.failure) + (716969779/125000000 : ℝ)*(f.sum) + (55711585783703502089/421434812800000000000000000000000 : ℝ)*base62 + (1386511150315907/6548900000000000000000000000 : ℝ)*base64 + (4035528991404839/6435200000000000000000000000 : ℝ)*base66 + (1261195731288331/6548900000000000000000000000 : ℝ)*base69 + (57560380956229372789/432502453800000000000000000000000 : ℝ)*base70 + (71000402504479/330210000000000000000000000 : ℝ)*base73 + (1478598904706151/6435200000000000000000000000 : ℝ)*base75 + (423986115291401/1320840000000000000000000000 : ℝ)*base77 + (151366902750084381259/212496739200000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (6961/20000000000000000 : ℝ)*base87 + (6961/20000000000000000 : ℝ)*base89 + (6961/20000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2779/6250 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(2779/6250 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (8775385465022308622800285991383/2319366492244800000000000000000000000 : ℝ) := by norm_num
    linear_combination (1836213/1000000000000 : ℝ)*(base15) + (21110839301/200000000000 : ℝ)*(base40) + (3808854311/20000000000 : ℝ)*(base49) + (22103/40000000000 : ℝ)*(base59) + (4049220728227/1000000000000 : ℝ)*(major_s2_0) + (4049220728227/1000000000000 : ℝ)*(major_s2_1) + (4049220728227/1000000000000 : ℝ)*(major_s2_2) + (1938019/1000000000000 : ℝ)*(sp_s2_0) + (1770639/62500000000 : ℝ)*(sp_s2_9) + (11211209/500000000000 : ℝ)*(sp_s2_20) + (5709334238523/1000000000000 : ℝ)*(sp_s2_21) + (5709334340329/1000000000000 : ℝ)*(sp_s2_22) + (5709307846317/1000000000000 : ℝ)*(sp_s2_23) + (2389081596313/1000000000000 : ℝ)*(sp_s2_27) + (2389104018731/1000000000000 : ℝ)*(f.failure) + (2854668088271/500000000000 : ℝ)*(f.sum) + (123917245589580823229/421434812800000000000000000000000 : ℝ)*base63 + (1995652568836683/6548900000000000000000000000 : ℝ)*base64 + (2451731597692301/6435200000000000000000000000 : ℝ)*base66 + (1811085301157671/6548900000000000000000000000 : ℝ)*base68 + (122453592025487401511/432502453800000000000000000000000 : ℝ)*base70 + (12397753607341/41276250000000000000000000 : ℝ)*base73 + (2536212164834189/6435200000000000000000000000 : ℝ)*base75 + (141270593678203/1320840000000000000000000000 : ℝ)*base77 + (17583251729104303399/212496739200000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (39003/100000000000000000 : ℝ)*base86 + (39003/100000000000000000 : ℝ)*base88 + (39003/100000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((33021/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(33021/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2011/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2011/3125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(65489/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(65489/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((43631/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(43631/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(44399/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(44399/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2779/6250 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(2779/6250 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c313055_s2 p hpa hpb X hX hprev1

#print axioms solution
