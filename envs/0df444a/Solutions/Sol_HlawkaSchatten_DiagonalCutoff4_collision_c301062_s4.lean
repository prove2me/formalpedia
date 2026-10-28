-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301062_s4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:39:02.90027+00:00
-- url     : https://prove2.me/submissions/261cf5fd-24fe-4b88-aafe-52dba5b673c8

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
theorem collision_support_c301062_s4_s4_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-353581633/2000000000 : ℝ)*x 0 + (4934548653/10000000000 : ℝ)*x 1 + (-5999662133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (353581633/2000000000 : ℝ)^65 ≤ (200799326991/2000000000000 : ℝ)^49 := by
    have hnat : (353581633 : ℕ)^65*2000000000000^49 ≤ 200799326991^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      353581633 2000000000 200799326991 2000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4934548653/10000000000 : ℝ)^65 ≤ (19590852594493/50000000000000 : ℝ)^49 := by
    have hnat : (4934548653 : ℕ)^65*50000000000000^49 ≤ 19590852594493^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4934548653 10000000000 19590852594493 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5999662133/10000000000 : ℝ)^65 ≤ (50778328435083/100000000000000 : ℝ)^49 := by
    have hnat : (5999662133 : ℕ)^65*100000000000000^49 ≤ 50778328435083^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5999662133 10000000000 50778328435083 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-353581633/2000000000 : ℝ), (4934548653/10000000000 : ℝ), (-5999662133/10000000000 : ℝ)] ![(200799326991/2000000000000 : ℝ), (19590852594493/50000000000000 : ℝ), (50778328435083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-353581633/2000000000 : ℝ)|^65 ≤ (200799326991/2000000000000 : ℝ)^49
        have hw : |(-353581633/2000000000 : ℝ)|=(353581633/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4934548653/10000000000 : ℝ)|^65 ≤ (19590852594493/50000000000000 : ℝ)^49
        have hw : |(4934548653/10000000000 : ℝ)|=(4934548653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5999662133/10000000000 : ℝ)|^65 ≤ (50778328435083/100000000000000 : ℝ)^49
        have hw : |(-5999662133/10000000000 : ℝ)|=(5999662133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s4_s4_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4946078653/10000000000 : ℝ)*x 0 + (-889905179/5000000000 : ℝ)*x 1 + (-5980836081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4946078653/10000000000 : ℝ)^65 ≤ (39303197288993/100000000000000 : ℝ)^49 := by
    have hnat : (4946078653 : ℕ)^65*100000000000000^49 ≤ 39303197288993^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4946078653 10000000000 39303197288993 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (889905179/5000000000 : ℝ)^65 ≤ (10129728489797/100000000000000 : ℝ)^49 := by
    have hnat : (889905179 : ℕ)^65*100000000000000^49 ≤ 10129728489797^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      889905179 5000000000 10129728489797 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5980836081/10000000000 : ℝ)^65 ≤ (6320884274483/12500000000000 : ℝ)^49 := by
    have hnat : (5980836081 : ℕ)^65*12500000000000^49 ≤ 6320884274483^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5980836081 10000000000 6320884274483 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4946078653/10000000000 : ℝ), (-889905179/5000000000 : ℝ), (-5980836081/10000000000 : ℝ)] ![(39303197288993/100000000000000 : ℝ), (10129728489797/100000000000000 : ℝ), (6320884274483/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4946078653/10000000000 : ℝ)|^65 ≤ (39303197288993/100000000000000 : ℝ)^49
        have hw : |(4946078653/10000000000 : ℝ)|=(4946078653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-889905179/5000000000 : ℝ)|^65 ≤ (10129728489797/100000000000000 : ℝ)^49
        have hw : |(-889905179/5000000000 : ℝ)|=(889905179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5980836081/10000000000 : ℝ)|^65 ≤ (6320884274483/12500000000000 : ℝ)^49
        have hw : |(-5980836081/10000000000 : ℝ)|=(5980836081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s4_s4_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2655557471/5000000000 : ℝ)*x 0 + (5325241967/10000000000 : ℝ)*x 1 + (1102202983/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655557471/5000000000 : ℝ)^65 ≤ (43196684947141/100000000000000 : ℝ)^49 := by
    have hnat : (2655557471 : ℕ)^65*100000000000000^49 ≤ 43196684947141^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655557471 5000000000 43196684947141 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5325241967/10000000000 : ℝ)^65 ≤ (1354661495367/3125000000000 : ℝ)^49 := by
    have hnat : (5325241967 : ℕ)^65*3125000000000^49 ≤ 1354661495367^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5325241967 10000000000 1354661495367 3125000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1102202983/5000000000 : ℝ)^65 ≤ (13454147187867/100000000000000 : ℝ)^49 := by
    have hnat : (1102202983 : ℕ)^65*100000000000000^49 ≤ 13454147187867^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102202983 5000000000 13454147187867 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655557471/5000000000 : ℝ), (5325241967/10000000000 : ℝ), (1102202983/5000000000 : ℝ)] ![(43196684947141/100000000000000 : ℝ), (1354661495367/3125000000000 : ℝ), (13454147187867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655557471/5000000000 : ℝ)|^65 ≤ (43196684947141/100000000000000 : ℝ)^49
        have hw : |(2655557471/5000000000 : ℝ)|=(2655557471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5325241967/10000000000 : ℝ)|^65 ≤ (1354661495367/3125000000000 : ℝ)^49
        have hw : |(5325241967/10000000000 : ℝ)|=(5325241967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1102202983/5000000000 : ℝ)|^65 ≤ (13454147187867/100000000000000 : ℝ)^49
        have hw : |(1102202983/5000000000 : ℝ)|=(1102202983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s4_s4_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1126735471/2000000000 : ℝ)*x 0 + (5604800313/10000000000 : ℝ)*x 1 + (-332968103/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1126735471/2000000000 : ℝ)^65 ≤ (11677716545551/25000000000000 : ℝ)^49 := by
    have hnat : (1126735471 : ℕ)^65*25000000000000^49 ≤ 11677716545551^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126735471 2000000000 11677716545551 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5604800313/10000000000 : ℝ)^65 ≤ (46393520996657/100000000000000 : ℝ)^49 := by
    have hnat : (5604800313 : ℕ)^65*100000000000000^49 ≤ 46393520996657^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5604800313 10000000000 46393520996657 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (332968103/2500000000 : ℝ)^65 ≤ (1379122561007/20000000000000 : ℝ)^49 := by
    have hnat : (332968103 : ℕ)^65*20000000000000^49 ≤ 1379122561007^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332968103 2500000000 1379122561007 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1126735471/2000000000 : ℝ), (5604800313/10000000000 : ℝ), (-332968103/2500000000 : ℝ)] ![(11677716545551/25000000000000 : ℝ), (46393520996657/100000000000000 : ℝ), (1379122561007/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1126735471/2000000000 : ℝ)|^65 ≤ (11677716545551/25000000000000 : ℝ)^49
        have hw : |(1126735471/2000000000 : ℝ)|=(1126735471/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5604800313/10000000000 : ℝ)|^65 ≤ (46393520996657/100000000000000 : ℝ)^49
        have hw : |(5604800313/10000000000 : ℝ)|=(5604800313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-332968103/2500000000 : ℝ)|^65 ≤ (1379122561007/20000000000000 : ℝ)^49
        have hw : |(-332968103/2500000000 : ℝ)|=(332968103/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s4_s4_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-662001513/5000000000 : ℝ)*x 0 + (1065494031/2500000000 : ℝ)*x 1 + (-3440286077/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (662001513/5000000000 : ℝ)^65 ≤ (1368323682363/20000000000000 : ℝ)^49 := by
    have hnat : (662001513 : ℕ)^65*20000000000000^49 ≤ 1368323682363^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662001513 5000000000 1368323682363 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1065494031/2500000000 : ℝ)^65 ≤ (504066337683/1562500000000 : ℝ)^49 := by
    have hnat : (1065494031 : ℕ)^65*1562500000000^49 ≤ 504066337683^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065494031 2500000000 504066337683 1562500000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3440286077/5000000000 : ℝ)^65 ≤ (60898135971653/100000000000000 : ℝ)^49 := by
    have hnat : (3440286077 : ℕ)^65*100000000000000^49 ≤ 60898135971653^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3440286077 5000000000 60898135971653 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-662001513/5000000000 : ℝ), (1065494031/2500000000 : ℝ), (-3440286077/5000000000 : ℝ)] ![(1368323682363/20000000000000 : ℝ), (504066337683/1562500000000 : ℝ), (60898135971653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-662001513/5000000000 : ℝ)|^65 ≤ (1368323682363/20000000000000 : ℝ)^49
        have hw : |(-662001513/5000000000 : ℝ)|=(662001513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1065494031/2500000000 : ℝ)|^65 ≤ (504066337683/1562500000000 : ℝ)^49
        have hw : |(1065494031/2500000000 : ℝ)|=(1065494031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3440286077/5000000000 : ℝ)|^65 ≤ (60898135971653/100000000000000 : ℝ)^49
        have hw : |(-3440286077/5000000000 : ℝ)|=(3440286077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s4_s4_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4531612041/10000000000 : ℝ)*x 0 + (-900653383/10000000000 : ℝ)*x 1 + (-53756347/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4531612041/10000000000 : ℝ)^65 ≤ (2187201173959/6250000000000 : ℝ)^49 := by
    have hnat : (4531612041 : ℕ)^65*6250000000000^49 ≤ 2187201173959^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4531612041 10000000000 2187201173959 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (900653383/10000000000 : ℝ)^65 ≤ (256489022647/6250000000000 : ℝ)^49 := by
    have hnat : (900653383 : ℕ)^65*6250000000000^49 ≤ 256489022647^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900653383 10000000000 256489022647 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53756347/78125000 : ℝ)^65 ≤ (3045047842477/5000000000000 : ℝ)^49 := by
    have hnat : (53756347 : ℕ)^65*5000000000000^49 ≤ 3045047842477^49*78125000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53756347 78125000 3045047842477 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4531612041/10000000000 : ℝ), (-900653383/10000000000 : ℝ), (-53756347/78125000 : ℝ)] ![(2187201173959/6250000000000 : ℝ), (256489022647/6250000000000 : ℝ), (3045047842477/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4531612041/10000000000 : ℝ)|^65 ≤ (2187201173959/6250000000000 : ℝ)^49
        have hw : |(4531612041/10000000000 : ℝ)|=(4531612041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-900653383/10000000000 : ℝ)|^65 ≤ (256489022647/6250000000000 : ℝ)^49
        have hw : |(-900653383/10000000000 : ℝ)|=(900653383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-53756347/78125000 : ℝ)|^65 ≤ (3045047842477/5000000000000 : ℝ)^49
        have hw : |(-53756347/78125000 : ℝ)|=(53756347/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s4_s4_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4714740061/10000000000 : ℝ)*x 0 + (3256620609/5000000000 : ℝ)*x 1 + (1272832969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4714740061/10000000000 : ℝ)^65 ≤ (36883465012699/100000000000000 : ℝ)^49 := by
    have hnat : (4714740061 : ℕ)^65*100000000000000^49 ≤ 36883465012699^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4714740061 10000000000 36883465012699 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3256620609/5000000000 : ℝ)^65 ≤ (28311719079687/50000000000000 : ℝ)^49 := by
    have hnat : (3256620609 : ℕ)^65*50000000000000^49 ≤ 28311719079687^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3256620609 5000000000 28311719079687 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1272832969/10000000000 : ℝ)^65 ≤ (1623274202991/25000000000000 : ℝ)^49 := by
    have hnat : (1272832969 : ℕ)^65*25000000000000^49 ≤ 1623274202991^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1272832969 10000000000 1623274202991 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4714740061/10000000000 : ℝ), (3256620609/5000000000 : ℝ), (1272832969/10000000000 : ℝ)] ![(36883465012699/100000000000000 : ℝ), (28311719079687/50000000000000 : ℝ), (1623274202991/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4714740061/10000000000 : ℝ)|^65 ≤ (36883465012699/100000000000000 : ℝ)^49
        have hw : |(4714740061/10000000000 : ℝ)|=(4714740061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3256620609/5000000000 : ℝ)|^65 ≤ (28311719079687/50000000000000 : ℝ)^49
        have hw : |(3256620609/5000000000 : ℝ)|=(3256620609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1272832969/10000000000 : ℝ)|^65 ≤ (1623274202991/25000000000000 : ℝ)^49
        have hw : |(1272832969/10000000000 : ℝ)|=(1272832969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s4_s4_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2536930427/5000000000 : ℝ)*x 0 + (6717837577/10000000000 : ℝ)*x 1 + (-35144919/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2536930427/5000000000 : ℝ)^65 ≤ (40655805516937/100000000000000 : ℝ)^49 := by
    have hnat : (2536930427 : ℕ)^65*100000000000000^49 ≤ 40655805516937^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2536930427 5000000000 40655805516937 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6717837577/10000000000 : ℝ)^65 ≤ (58994923451751/100000000000000 : ℝ)^49 := by
    have hnat : (6717837577 : ℕ)^65*100000000000000^49 ≤ 58994923451751^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6717837577 10000000000 58994923451751 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35144919/2500000000 : ℝ)^65 ≤ (349271018369/100000000000000 : ℝ)^49 := by
    have hnat : (35144919 : ℕ)^65*100000000000000^49 ≤ 349271018369^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35144919 2500000000 349271018369 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2536930427/5000000000 : ℝ), (6717837577/10000000000 : ℝ), (-35144919/2500000000 : ℝ)] ![(40655805516937/100000000000000 : ℝ), (58994923451751/100000000000000 : ℝ), (349271018369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2536930427/5000000000 : ℝ)|^65 ≤ (40655805516937/100000000000000 : ℝ)^49
        have hw : |(2536930427/5000000000 : ℝ)|=(2536930427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6717837577/10000000000 : ℝ)|^65 ≤ (58994923451751/100000000000000 : ℝ)^49
        have hw : |(6717837577/10000000000 : ℝ)|=(6717837577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-35144919/2500000000 : ℝ)|^65 ≤ (349271018369/100000000000000 : ℝ)^49
        have hw : |(-35144919/2500000000 : ℝ)|=(35144919/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s4_s4_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-223269023/2500000000 : ℝ)*x 0 + (2270777819/5000000000 : ℝ)*x 1 + (-6876028349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (223269023/2500000000 : ℝ)^65 ≤ (2536304827/62500000000 : ℝ)^49 := by
    have hnat : (223269023 : ℕ)^65*62500000000^49 ≤ 2536304827^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223269023 2500000000 2536304827 62500000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2270777819/5000000000 : ℝ)^65 ≤ (35097118332661/100000000000000 : ℝ)^49 := by
    have hnat : (2270777819 : ℕ)^65*100000000000000^49 ≤ 35097118332661^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2270777819 5000000000 35097118332661 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6876028349/10000000000 : ℝ)^65 ≤ (3042239696871/5000000000000 : ℝ)^49 := by
    have hnat : (6876028349 : ℕ)^65*5000000000000^49 ≤ 3042239696871^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6876028349 10000000000 3042239696871 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-223269023/2500000000 : ℝ), (2270777819/5000000000 : ℝ), (-6876028349/10000000000 : ℝ)] ![(2536304827/62500000000 : ℝ), (35097118332661/100000000000000 : ℝ), (3042239696871/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-223269023/2500000000 : ℝ)|^65 ≤ (2536304827/62500000000 : ℝ)^49
        have hw : |(-223269023/2500000000 : ℝ)|=(223269023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2270777819/5000000000 : ℝ)|^65 ≤ (35097118332661/100000000000000 : ℝ)^49
        have hw : |(2270777819/5000000000 : ℝ)|=(2270777819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6876028349/10000000000 : ℝ)|^65 ≤ (3042239696871/5000000000000 : ℝ)^49
        have hw : |(-6876028349/10000000000 : ℝ)|=(6876028349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s4_s4_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4275402363/10000000000 : ℝ)*x 0 + (-32791741/250000000 : ℝ)*x 1 + (-1375254627/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4275402363/10000000000 : ℝ)^65 ≤ (32395126824023/100000000000000 : ℝ)^49 := by
    have hnat : (4275402363 : ℕ)^65*100000000000000^49 ≤ 32395126824023^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4275402363 10000000000 32395126824023 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32791741/250000000 : ℝ)^65 ≤ (6757205849919/100000000000000 : ℝ)^49 := by
    have hnat : (32791741 : ℕ)^65*100000000000000^49 ≤ 6757205849919^49*250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32791741 250000000 6757205849919 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1375254627/2000000000 : ℝ)^65 ≤ (60847667311319/100000000000000 : ℝ)^49 := by
    have hnat : (1375254627 : ℕ)^65*100000000000000^49 ≤ 60847667311319^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1375254627 2000000000 60847667311319 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4275402363/10000000000 : ℝ), (-32791741/250000000 : ℝ), (-1375254627/2000000000 : ℝ)] ![(32395126824023/100000000000000 : ℝ), (6757205849919/100000000000000 : ℝ), (60847667311319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4275402363/10000000000 : ℝ)|^65 ≤ (32395126824023/100000000000000 : ℝ)^49
        have hw : |(4275402363/10000000000 : ℝ)|=(4275402363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-32791741/250000000 : ℝ)|^65 ≤ (6757205849919/100000000000000 : ℝ)^49
        have hw : |(-32791741/250000000 : ℝ)|=(32791741/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1375254627/2000000000 : ℝ)|^65 ≤ (60847667311319/100000000000000 : ℝ)^49
        have hw : |(-1375254627/2000000000 : ℝ)|=(1375254627/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s4_s4_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1261248277/2000000000 : ℝ)*x 0 + (4938887269/10000000000 : ℝ)*x 1 + (1277376603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1261248277/2000000000 : ℝ)^65 ≤ (6781090985163/12500000000000 : ℝ)^49 := by
    have hnat : (1261248277 : ℕ)^65*12500000000000^49 ≤ 6781090985163^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1261248277 2000000000 6781090985163 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4938887269/10000000000 : ℝ)^65 ≤ (19613705252327/50000000000000 : ℝ)^49 := by
    have hnat : (4938887269 : ℕ)^65*50000000000000^49 ≤ 19613705252327^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4938887269 10000000000 19613705252327 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1277376603/10000000000 : ℝ)^65 ≤ (815482699883/12500000000000 : ℝ)^49 := by
    have hnat : (1277376603 : ℕ)^65*12500000000000^49 ≤ 815482699883^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1277376603 10000000000 815482699883 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1261248277/2000000000 : ℝ), (4938887269/10000000000 : ℝ), (1277376603/10000000000 : ℝ)] ![(6781090985163/12500000000000 : ℝ), (19613705252327/50000000000000 : ℝ), (815482699883/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1261248277/2000000000 : ℝ)|^65 ≤ (6781090985163/12500000000000 : ℝ)^49
        have hw : |(1261248277/2000000000 : ℝ)|=(1261248277/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4938887269/10000000000 : ℝ)|^65 ≤ (19613705252327/50000000000000 : ℝ)^49
        have hw : |(4938887269/10000000000 : ℝ)|=(4938887269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1277376603/10000000000 : ℝ)|^65 ≤ (815482699883/12500000000000 : ℝ)^49
        have hw : |(1277376603/10000000000 : ℝ)|=(1277376603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s4_s4_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3555894857/5000000000 : ℝ)*x 0 + (4628724349/10000000000 : ℝ)*x 1 + (-149478389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3555894857/5000000000 : ℝ)^65 ≤ (63627592122641/100000000000000 : ℝ)^49 := by
    have hnat : (3555894857 : ℕ)^65*100000000000000^49 ≤ 63627592122641^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3555894857 5000000000 63627592122641 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4628724349/10000000000 : ℝ)^65 ≤ (7198701962303/20000000000000 : ℝ)^49 := by
    have hnat : (4628724349 : ℕ)^65*20000000000000^49 ≤ 7198701962303^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4628724349 10000000000 7198701962303 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (149478389/10000000000 : ℝ)^65 ≤ (94724514371/25000000000000 : ℝ)^49 := by
    have hnat : (149478389 : ℕ)^65*25000000000000^49 ≤ 94724514371^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149478389 10000000000 94724514371 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3555894857/5000000000 : ℝ), (4628724349/10000000000 : ℝ), (-149478389/10000000000 : ℝ)] ![(63627592122641/100000000000000 : ℝ), (7198701962303/20000000000000 : ℝ), (94724514371/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3555894857/5000000000 : ℝ)|^65 ≤ (63627592122641/100000000000000 : ℝ)^49
        have hw : |(3555894857/5000000000 : ℝ)|=(3555894857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4628724349/10000000000 : ℝ)|^65 ≤ (7198701962303/20000000000000 : ℝ)^49
        have hw : |(4628724349/10000000000 : ℝ)|=(4628724349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-149478389/10000000000 : ℝ)|^65 ≤ (94724514371/25000000000000 : ℝ)^49
        have hw : |(-149478389/10000000000 : ℝ)|=(149478389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s4_s4_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-33184793/625000000 : ℝ)*x 0 + (58511713/100000000 : ℝ)*x 1 + (-1456685923/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33184793/625000000 : ℝ)^65 ≤ (407175705163/20000000000000 : ℝ)^49 := by
    have hnat : (33184793 : ℕ)^65*20000000000000^49 ≤ 407175705163^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33184793 625000000 407175705163 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (58511713/100000000 : ℝ)^65 ≤ (1227949409529/2500000000000 : ℝ)^49 := by
    have hnat : (58511713 : ℕ)^65*2500000000000^49 ≤ 1227949409529^49*100000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58511713 100000000 1227949409529 2500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1456685923/2500000000 : ℝ)^65 ≤ (24423072536221/50000000000000 : ℝ)^49 := by
    have hnat : (1456685923 : ℕ)^65*50000000000000^49 ≤ 24423072536221^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1456685923 2500000000 24423072536221 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-33184793/625000000 : ℝ), (58511713/100000000 : ℝ), (-1456685923/2500000000 : ℝ)] ![(407175705163/20000000000000 : ℝ), (1227949409529/2500000000000 : ℝ), (24423072536221/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-33184793/625000000 : ℝ)|^65 ≤ (407175705163/20000000000000 : ℝ)^49
        have hw : |(-33184793/625000000 : ℝ)|=(33184793/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(58511713/100000000 : ℝ)|^65 ≤ (1227949409529/2500000000000 : ℝ)^49
        have hw : |(58511713/100000000 : ℝ)|=(58511713/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1456685923/2500000000 : ℝ)|^65 ≤ (24423072536221/50000000000000 : ℝ)^49
        have hw : |(-1456685923/2500000000 : ℝ)|=(1456685923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s4_s4_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1574280487/2500000000 : ℝ)*x 0 + (-977285697/10000000000 : ℝ)*x 1 + (-2566330343/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1574280487/2500000000 : ℝ)^65 ≤ (54144687558487/100000000000000 : ℝ)^49 := by
    have hnat : (1574280487 : ℕ)^65*100000000000000^49 ≤ 54144687558487^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1574280487 2500000000 54144687558487 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (977285697/10000000000 : ℝ)^65 ≤ (2286665624521/50000000000000 : ℝ)^49 := by
    have hnat : (977285697 : ℕ)^65*50000000000000^49 ≤ 2286665624521^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977285697 10000000000 2286665624521 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2566330343/5000000000 : ℝ)^65 ≤ (41281981179553/100000000000000 : ℝ)^49 := by
    have hnat : (2566330343 : ℕ)^65*100000000000000^49 ≤ 41281981179553^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2566330343 5000000000 41281981179553 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1574280487/2500000000 : ℝ), (-977285697/10000000000 : ℝ), (-2566330343/5000000000 : ℝ)] ![(54144687558487/100000000000000 : ℝ), (2286665624521/50000000000000 : ℝ), (41281981179553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1574280487/2500000000 : ℝ)|^65 ≤ (54144687558487/100000000000000 : ℝ)^49
        have hw : |(1574280487/2500000000 : ℝ)|=(1574280487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-977285697/10000000000 : ℝ)|^65 ≤ (2286665624521/50000000000000 : ℝ)^49
        have hw : |(-977285697/10000000000 : ℝ)|=(977285697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2566330343/5000000000 : ℝ)|^65 ≤ (41281981179553/100000000000000 : ℝ)^49
        have hw : |(-2566330343/5000000000 : ℝ)|=(2566330343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s4_s4_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (441088517/1000000000 : ℝ)*x 0 + (6248502667/10000000000 : ℝ)*x 1 + (2103739071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (441088517/1000000000 : ℝ)^65 ≤ (33763893979719/100000000000000 : ℝ)^49 := by
    have hnat : (441088517 : ℕ)^65*100000000000000^49 ≤ 33763893979719^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441088517 1000000000 33763893979719 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6248502667/10000000000 : ℝ)^65 ≤ (53590839282587/100000000000000 : ℝ)^49 := by
    have hnat : (6248502667 : ℕ)^65*100000000000000^49 ≤ 53590839282587^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6248502667 10000000000 53590839282587 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2103739071/10000000000 : ℝ)^65 ≤ (1580658341551/12500000000000 : ℝ)^49 := by
    have hnat : (2103739071 : ℕ)^65*12500000000000^49 ≤ 1580658341551^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103739071 10000000000 1580658341551 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(441088517/1000000000 : ℝ), (6248502667/10000000000 : ℝ), (2103739071/10000000000 : ℝ)] ![(33763893979719/100000000000000 : ℝ), (53590839282587/100000000000000 : ℝ), (1580658341551/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(441088517/1000000000 : ℝ)|^65 ≤ (33763893979719/100000000000000 : ℝ)^49
        have hw : |(441088517/1000000000 : ℝ)|=(441088517/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6248502667/10000000000 : ℝ)|^65 ≤ (53590839282587/100000000000000 : ℝ)^49
        have hw : |(6248502667/10000000000 : ℝ)|=(6248502667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2103739071/10000000000 : ℝ)|^65 ≤ (1580658341551/12500000000000 : ℝ)^49
        have hw : |(2103739071/10000000000 : ℝ)|=(2103739071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s4_s4_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (757351061/1000000000 : ℝ)*x 0 + (3973843203/10000000000 : ℝ)*x 1 + (-408069853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (757351061/1000000000 : ℝ)^65 ≤ (69164635327349/100000000000000 : ℝ)^49 := by
    have hnat : (757351061 : ℕ)^65*100000000000000^49 ≤ 69164635327349^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      757351061 1000000000 69164635327349 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3973843203/10000000000 : ℝ)^65 ≤ (29399555236839/100000000000000 : ℝ)^49 := by
    have hnat : (3973843203 : ℕ)^65*100000000000000^49 ≤ 29399555236839^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3973843203 10000000000 29399555236839 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (408069853/10000000000 : ℝ)^65 ≤ (717904714531/50000000000000 : ℝ)^49 := by
    have hnat : (408069853 : ℕ)^65*50000000000000^49 ≤ 717904714531^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408069853 10000000000 717904714531 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(757351061/1000000000 : ℝ), (3973843203/10000000000 : ℝ), (-408069853/10000000000 : ℝ)] ![(69164635327349/100000000000000 : ℝ), (29399555236839/100000000000000 : ℝ), (717904714531/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(757351061/1000000000 : ℝ)|^65 ≤ (69164635327349/100000000000000 : ℝ)^49
        have hw : |(757351061/1000000000 : ℝ)|=(757351061/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3973843203/10000000000 : ℝ)|^65 ≤ (29399555236839/100000000000000 : ℝ)^49
        have hw : |(3973843203/10000000000 : ℝ)|=(3973843203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-408069853/10000000000 : ℝ)|^65 ≤ (717904714531/50000000000000 : ℝ)^49
        have hw : |(-408069853/10000000000 : ℝ)|=(408069853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301062_s4 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev3 : (0 : ℝ) ≤ ((37891/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(37891/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(75797/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(75797/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-7311/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-7311/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((29189/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(29189/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14691/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14691/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-5079/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-5079/12500 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
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
  rcases hprev3 with ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩
  have s4_pow0 : (37891/50000 : ℝ) ^ (129/32 : ℝ) ≤ (32696456671546701121/100000000000000000000 : ℝ) := by
    have hpowers : (37891/50000 : ℝ)^129 ≤ (32696456671546701121/100000000000000000000 : ℝ)^32 := by
      have hnat : (37891 : ℕ)^129*100000000000000000000^32 ≤ 32696456671546701121^32*50000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37891 50000 32696456671546701121 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (37891/50000 : ℝ)) (X := (32696456671546701121/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s4_corner0a : (132696456671546701121/100000000000000000000 : ℝ) ≤ (41902194342799/39062500000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (132696456671546701121/100000000000000000000 : ℝ)^32 ≤ (41902194342799/39062500000000 : ℝ)^129 := by
      have hnat : (132696456671546701121 : ℕ)^32*39062500000000^129 ≤ 41902194342799^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        132696456671546701121 100000000000000000000 41902194342799 39062500000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (41902194342799/39062500000000 : ℝ)) (X := (132696456671546701121/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s4_corner0b : (82696456671546701121/50000000000000000000 : ℝ) ≤ (11329369517955473/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (82696456671546701121/50000000000000000000 : ℝ)^32 ≤ (11329369517955473/10000000000000000 : ℝ)^129 := by
      have hnat : (82696456671546701121 : ℕ)^32*10000000000000000^129 ≤ 11329369517955473^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        82696456671546701121 50000000000000000000 11329369517955473 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11329369517955473/10000000000000000 : ℝ)) (X := (82696456671546701121/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s4_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(2839694342799/29602343750000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(602407766198929/7578200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (37891/50000 : ℝ)) (alpha := (2839694342799/29602343750000 : ℝ)) (beta := (602407766198929/7578200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow0,s4_corner0a]) (by linarith only [s4_pow0,s4_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (37891/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(2839694342799/29602343750000 : ℝ)*((1 : ℝ)*pair X 0 1)+(602407766198929/7578200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow1 : (75797/100000 : ℝ) ^ (129/32 : ℝ) ≤ (16361276995561568417/50000000000000000000 : ℝ) := by
    have hpowers : (75797/100000 : ℝ)^129 ≤ (16361276995561568417/50000000000000000000 : ℝ)^32 := by
      have hnat : (75797 : ℕ)^129*50000000000000000000^32 ≤ 16361276995561568417^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        75797 100000 16361276995561568417 50000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (75797/100000 : ℝ)) (X := (16361276995561568417/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s4_corner1a : (66361276995561568417/50000000000000000000 : ℝ) ≤ (335233907518451/312500000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (66361276995561568417/50000000000000000000 : ℝ)^32 ≤ (335233907518451/312500000000000 : ℝ)^129 := by
      have hnat : (66361276995561568417 : ℕ)^32*312500000000000^129 ≤ 335233907518451^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        66361276995561568417 50000000000000000000 335233907518451 312500000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (335233907518451/312500000000000 : ℝ)) (X := (66361276995561568417/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s4_corner1b : (41361276995561568417/25000000000000000000 : ℝ) ≤ (2266051262695071/2000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (41361276995561568417/25000000000000000000 : ℝ)^32 ≤ (2266051262695071/2000000000000000 : ℝ)^129 := by
      have hnat : (41361276995561568417 : ℕ)^32*2000000000000000^129 ≤ 2266051262695071^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        41361276995561568417 25000000000000000000 2266051262695071 2000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2266051262695071/2000000000000000 : ℝ)) (X := (41361276995561568417/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s4_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(22733907518451/236865625000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(602771272884923/7579700000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (75797/100000 : ℝ)) (alpha := (22733907518451/236865625000000 : ℝ)) (beta := (602771272884923/7579700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow1,s4_corner1a]) (by linarith only [s4_pow1,s4_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (75797/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(22733907518451/236865625000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(602771272884923/7579700000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow2 : (7311/12500 : ℝ) ^ (129/32 : ℝ) ≤ (1438460475100508701/12500000000000000000 : ℝ) := by
    have hpowers : (7311/12500 : ℝ)^129 ≤ (1438460475100508701/12500000000000000000 : ℝ)^32 := by
      have hnat : (7311 : ℕ)^129*12500000000000000000^32 ≤ 1438460475100508701^32*12500^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7311 12500 1438460475100508701 12500000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7311/12500 : ℝ)) (X := (1438460475100508701/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s4_corner2a : (13938460475100508701/12500000000000000000 : ℝ) ≤ (10273880803176829/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (13938460475100508701/12500000000000000000 : ℝ)^32 ≤ (10273880803176829/10000000000000000 : ℝ)^129 := by
      have hnat : (13938460475100508701 : ℕ)^32*10000000000000000^129 ≤ 10273880803176829^129*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13938460475100508701 12500000000000000000 10273880803176829 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10273880803176829/10000000000000000 : ℝ)) (X := (13938460475100508701/12500000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s4_corner2b : (7688460475100508701/6250000000000000000 : ℝ) ≤ (5263631856091841/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (7688460475100508701/6250000000000000000 : ℝ)^32 ≤ (5263631856091841/5000000000000000 : ℝ)^129 := by
      have hnat : (7688460475100508701 : ℕ)^32*5000000000000000^129 ≤ 5263631856091841^129*6250000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7688460475100508701 6250000000000000000 5263631856091841 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5263631856091841/5000000000000000 : ℝ)) (X := (7688460475100508701/6250000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s4_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(91293601058943/1949600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(84460969668951/1949600000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (7311/12500 : ℝ)) (alpha := (91293601058943/1949600000000000 : ℝ)) (beta := (84460969668951/1949600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow2,s4_corner2a]) (by linarith only [s4_pow2,s4_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (7311/12500 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(91293601058943/1949600000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(84460969668951/1949600000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s4_0 : ((-353581633/2000000000 : ℝ)*X 0 0+(4934548653/10000000000 : ℝ)*X 0 1+(-5999662133/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s4_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_1 : ((4946078653/10000000000 : ℝ)*X 1 0+(-889905179/5000000000 : ℝ)*X 1 1+(-5980836081/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s4_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_2 : ((2655557471/5000000000 : ℝ)*X 2 0+(5325241967/10000000000 : ℝ)*X 2 1+(1102202983/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s4_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_6 : ((1126735471/2000000000 : ℝ)*X 0 0+(5604800313/10000000000 : ℝ)*X 0 1+(-332968103/2500000000 : ℝ)*X 0 2+(1126735471/2000000000 : ℝ)*X 1 0+(5604800313/10000000000 : ℝ)*X 1 1+(-332968103/2500000000 : ℝ)*X 1 2+(1126735471/2000000000 : ℝ)*X 2 0+(5604800313/10000000000 : ℝ)*X 2 1+(-332968103/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s4_s4_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_7 : ((-662001513/5000000000 : ℝ)*X 0 0+(1065494031/2500000000 : ℝ)*X 0 1+(-3440286077/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s4_s4_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_8 : ((4531612041/10000000000 : ℝ)*X 1 0+(-900653383/10000000000 : ℝ)*X 1 1+(-53756347/78125000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s4_s4_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_9 : ((4714740061/10000000000 : ℝ)*X 2 0+(3256620609/5000000000 : ℝ)*X 2 1+(1272832969/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s4_s4_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_13 : ((2536930427/5000000000 : ℝ)*X 0 0+(6717837577/10000000000 : ℝ)*X 0 1+(-35144919/2500000000 : ℝ)*X 0 2+(2536930427/5000000000 : ℝ)*X 1 0+(6717837577/10000000000 : ℝ)*X 1 1+(-35144919/2500000000 : ℝ)*X 1 2+(2536930427/5000000000 : ℝ)*X 2 0+(6717837577/10000000000 : ℝ)*X 2 1+(-35144919/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s4_s4_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_14 : ((-223269023/2500000000 : ℝ)*X 0 0+(2270777819/5000000000 : ℝ)*X 0 1+(-6876028349/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s4_s4_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_15 : ((4275402363/10000000000 : ℝ)*X 1 0+(-32791741/250000000 : ℝ)*X 1 1+(-1375254627/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s4_s4_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_16 : ((1261248277/2000000000 : ℝ)*X 2 0+(4938887269/10000000000 : ℝ)*X 2 1+(1277376603/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s4_s4_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_20 : ((3555894857/5000000000 : ℝ)*X 0 0+(4628724349/10000000000 : ℝ)*X 0 1+(-149478389/10000000000 : ℝ)*X 0 2+(3555894857/5000000000 : ℝ)*X 1 0+(4628724349/10000000000 : ℝ)*X 1 1+(-149478389/10000000000 : ℝ)*X 1 2+(3555894857/5000000000 : ℝ)*X 2 0+(4628724349/10000000000 : ℝ)*X 2 1+(-149478389/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s4_s4_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_21 : ((-33184793/625000000 : ℝ)*X 0 0+(58511713/100000000 : ℝ)*X 0 1+(-1456685923/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s4_s4_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_22 : ((1574280487/2500000000 : ℝ)*X 1 0+(-977285697/10000000000 : ℝ)*X 1 1+(-2566330343/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s4_s4_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_23 : ((441088517/1000000000 : ℝ)*X 2 0+(6248502667/10000000000 : ℝ)*X 2 1+(2103739071/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s4_s4_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_27 : ((757351061/1000000000 : ℝ)*X 0 0+(3973843203/10000000000 : ℝ)*X 0 1+(-408069853/10000000000 : ℝ)*X 0 2+(757351061/1000000000 : ℝ)*X 1 0+(3973843203/10000000000 : ℝ)*X 1 1+(-408069853/10000000000 : ℝ)*X 1 2+(757351061/1000000000 : ℝ)*X 2 0+(3973843203/10000000000 : ℝ)*X 2 1+(-408069853/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s4_s4_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s4_0 : (0 : ℝ) ≤ ((29189/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(29189/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7853007042216067531157918460387/1399824559499800000000000000000000000 : ℝ) := by norm_num
    linear_combination (2281531/1000000000000 : ℝ)*(base39) + (23013/62500000000 : ℝ)*(base49) + (11292306813/100000000000 : ℝ)*(base60) + (4534105641183/1000000000000 : ℝ)*(major_s4_0) + (4534105641183/1000000000000 : ℝ)*(major_s4_1) + (4534105641183/1000000000000 : ℝ)*(major_s4_2) + (4310977/500000000000 : ℝ)*(sp_s4_6) + (3001503326769/500000000000 : ℝ)*(sp_s4_7) + (1200590417823/200000000000 : ℝ)*(sp_s4_8) + (6003006288197/1000000000000 : ℝ)*(sp_s4_9) + (3065150271249/1000000000000 : ℝ)*(sp_s4_13) + (2193281/50000000000 : ℝ)*(sp_s4_14) + (98430043/1000000000000 : ℝ)*(sp_s4_15) + (44230961/1000000000000 : ℝ)*(sp_s4_23) + (766289723301/250000000000 : ℝ)*(f.failure) + (3001525259579/500000000000 : ℝ)*(f.sum) + (47392390572243990709/147773831200000000000000000000000 : ℝ)*base63 + (1831290001845913/1949600000000000000000000000 : ℝ)*base65 + (3611227518902211/7579700000000000000000000000 : ℝ)*base66 + (1244599775995169/1949600000000000000000000000 : ℝ)*base69 + (43138927052364112699/73872293600000000000000000000000 : ℝ)*base71 + (498434028924053/7578200000000000000000000000 : ℝ)*base72 + (2955280310244073/3789850000000000000000000000 : ℝ)*base75 + (103054283835703/118409375000000000000000000 : ℝ)*base77 + (184236717285343673337/574404825400000000000000000000000 : ℝ)*base79 + (531/6250000000000000 : ℝ)*base87 + (531/6250000000000000 : ℝ)*base89 + (531/6250000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s4_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14691/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14691/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6303862754325743868745370911539/399949874142800000000000000000000000 : ℝ) := by norm_num
    linear_combination (1161957/500000000000 : ℝ)*(base12) + (4306911/1000000000000 : ℝ)*(base60) + (4551107449441/1000000000000 : ℝ)*(major_s4_0) + (4551107449441/1000000000000 : ℝ)*(major_s4_1) + (4551107449441/1000000000000 : ℝ)*(major_s4_2) + (68501/62500000000 : ℝ)*(sp_s4_1) + (37486927/1000000000000 : ℝ)*(sp_s4_2) + (37488471/500000000000 : ℝ)*(sp_s4_7) + (12322883/200000000000 : ℝ)*(sp_s4_8) + (1506369960133/250000000000 : ℝ)*(sp_s4_14) + (3012747215479/500000000000 : ℝ)*(sp_s4_15) + (6025519654461/1000000000000 : ℝ)*(sp_s4_16) + (1538267957333/500000000000 : ℝ)*(sp_s4_20) + (7286809/62500000000 : ℝ)*(sp_s4_27) + (3076652503611/1000000000000 : ℝ)*(f.failure) + (1506389285347/250000000000 : ℝ)*(f.sum) + (134102456045866907403/147773831200000000000000000000000 : ℝ)*base63 + (686203314452009/1949600000000000000000000000 : ℝ)*base64 + (601883495677217/7579700000000000000000000000 : ℝ)*base66 + (612377916609103/1949600000000000000000000000 : ℝ)*base69 + (808181300168460899/10553184800000000000000000000000 : ℝ)*base71 + (748319847020247/1082600000000000000000000000 : ℝ)*base73 + (1783302175813501/3789850000000000000000000000 : ℝ)*base75 + (12274933509527/67662500000000000000000000 : ℝ)*base77 + (3440068433539878443/82057832200000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (13391/25000000000000000 : ℝ)*base87 + (13391/25000000000000000 : ℝ)*base89 + (13391/25000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s4_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-5079/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-5079/12500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6615489489861434617375107924633/1399824559499800000000000000000000000 : ℝ) := by norm_num
    linear_combination (1835053/500000000000 : ℝ)*(base11) + (19222861899/62500000000 : ℝ)*(base39) + (3345784723977/1000000000000 : ℝ)*(major_s4_0) + (3345784723977/1000000000000 : ℝ)*(major_s4_1) + (3345784723977/1000000000000 : ℝ)*(major_s4_2) + (20854021/1000000000000 : ℝ)*(sp_s4_0) + (304171/25000000000 : ℝ)*(sp_s4_1) + (10327093/1000000000000 : ℝ)*(sp_s4_2) + (7479/62500000000 : ℝ)*(sp_s4_8) + (30448729/1000000000000 : ℝ)*(sp_s4_9) + (4429716515821/1000000000000 : ℝ)*(sp_s4_21) + (1107432188361/250000000000 : ℝ)*(sp_s4_22) + (2214850132063/500000000000 : ℝ)*(sp_s4_23) + (1130913416341/500000000000 : ℝ)*(sp_s4_27) + (1130913416341/500000000000 : ℝ)*(f.failure) + (4429741039949/1000000000000 : ℝ)*(f.sum) + (28788261515705314771/147773831200000000000000000000000 : ℝ)*base63 + (1404003728891487/1949600000000000000000000000 : ℝ)*base65 + (1546645830693359/7579700000000000000000000000 : ℝ)*base66 + (1288230914983351/1949600000000000000000000000 : ℝ)*base69 + (3210586957849772621/73872293600000000000000000000000 : ℝ)*base71 + (3314863361034287/7578200000000000000000000000 : ℝ)*base72 + (2337680512261757/3789850000000000000000000000 : ℝ)*base75 + (1130088642619717/1894550000000000000000000000 : ℝ)*base77 + (102993731302281188363/574404825400000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (5979/12500000000000000 : ℝ)*base86 + (5979/12500000000000000 : ℝ)*base88 + (5979/12500000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev3 : (0 : ℝ) ≤ ((37891/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(37891/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(75797/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(75797/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-7311/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-7311/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((29189/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(29189/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14691/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14691/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-5079/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-5079/12500 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301062_s4 p hpa hpb X hX hprev3

#print axioms solution
