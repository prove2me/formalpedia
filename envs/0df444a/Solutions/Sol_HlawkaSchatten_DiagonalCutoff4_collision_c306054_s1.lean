-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c306054_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:56:01.141179+00:00
-- url     : https://prove2.me/submissions/3097d919-9c01-4c57-8a23-079140287f3f

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
theorem collision_support_c306054_s1_s1_1 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1482972963/2500000000 : ℝ)*x 0 + (-1331040037/10000000000 : ℝ)*x 1 + (-5181973583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1482972963/2500000000 : ℝ)^17 ≤ (12628347761753/25000000000000 : ℝ)^13 := by
    have hnat : (1482972963 : ℕ)^17*25000000000000^13 ≤ 12628347761753^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1482972963 2500000000 12628347761753 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1331040037/10000000000 : ℝ)^17 ≤ (715667776723/10000000000000 : ℝ)^13 := by
    have hnat : (1331040037 : ℕ)^17*10000000000000^13 ≤ 715667776723^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1331040037 10000000000 715667776723 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5181973583/10000000000 : ℝ)^17 ≤ (42329931167959/100000000000000 : ℝ)^13 := by
    have hnat : (5181973583 : ℕ)^17*100000000000000^13 ≤ 42329931167959^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181973583 10000000000 42329931167959 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1482972963/2500000000 : ℝ), (-1331040037/10000000000 : ℝ), (-5181973583/10000000000 : ℝ)] ![(12628347761753/25000000000000 : ℝ), (715667776723/10000000000000 : ℝ), (42329931167959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1482972963/2500000000 : ℝ)|^17 ≤ (12628347761753/25000000000000 : ℝ)^13
        have hw : |(1482972963/2500000000 : ℝ)|=(1482972963/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1331040037/10000000000 : ℝ)|^17 ≤ (715667776723/10000000000000 : ℝ)^13
        have hw : |(-1331040037/10000000000 : ℝ)|=(1331040037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5181973583/10000000000 : ℝ)|^17 ≤ (42329931167959/100000000000000 : ℝ)^13
        have hw : |(-5181973583/10000000000 : ℝ)|=(5181973583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306054_s1_s1_2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2828779401/5000000000 : ℝ)*x 0 + (1405344509/2500000000 : ℝ)*x 1 + (269640897/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2828779401/5000000000 : ℝ)^17 ≤ (5935057887601/12500000000000 : ℝ)^13 := by
    have hnat : (2828779401 : ℕ)^17*12500000000000^13 ≤ 5935057887601^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2828779401 5000000000 5935057887601 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1405344509/2500000000 : ℝ)^17 ≤ (23541891202739/50000000000000 : ℝ)^13 := by
    have hnat : (1405344509 : ℕ)^17*50000000000000^13 ≤ 23541891202739^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1405344509 2500000000 23541891202739 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269640897/2500000000 : ℝ)^17 ≤ (1358938621249/25000000000000 : ℝ)^13 := by
    have hnat : (269640897 : ℕ)^17*25000000000000^13 ≤ 1358938621249^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269640897 2500000000 1358938621249 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2828779401/5000000000 : ℝ), (1405344509/2500000000 : ℝ), (269640897/2500000000 : ℝ)] ![(5935057887601/12500000000000 : ℝ), (23541891202739/50000000000000 : ℝ), (1358938621249/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2828779401/5000000000 : ℝ)|^17 ≤ (5935057887601/12500000000000 : ℝ)^13
        have hw : |(2828779401/5000000000 : ℝ)|=(2828779401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1405344509/2500000000 : ℝ)|^17 ≤ (23541891202739/50000000000000 : ℝ)^13
        have hw : |(1405344509/2500000000 : ℝ)|=(1405344509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269640897/2500000000 : ℝ)|^17 ≤ (1358938621249/25000000000000 : ℝ)^13
        have hw : |(269640897/2500000000 : ℝ)|=(269640897/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306054_s1_s1_6 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5451856717/10000000000 : ℝ)*x 0 + (678693957/1250000000 : ℝ)*x 1 + (-1688819209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5451856717/10000000000 : ℝ)^17 ≤ (1413615191901/3125000000000 : ℝ)^13 := by
    have hnat : (5451856717 : ℕ)^17*3125000000000^13 ≤ 1413615191901^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451856717 10000000000 1413615191901 3125000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (678693957/1250000000 : ℝ)^17 ≤ (11248455423763/25000000000000 : ℝ)^13 := by
    have hnat : (678693957 : ℕ)^17*25000000000000^13 ≤ 11248455423763^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678693957 1250000000 11248455423763 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1688819209/10000000000 : ℝ)^17 ≤ (4885246074713/50000000000000 : ℝ)^13 := by
    have hnat : (1688819209 : ℕ)^17*50000000000000^13 ≤ 4885246074713^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1688819209 10000000000 4885246074713 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5451856717/10000000000 : ℝ), (678693957/1250000000 : ℝ), (-1688819209/10000000000 : ℝ)] ![(1413615191901/3125000000000 : ℝ), (11248455423763/25000000000000 : ℝ), (4885246074713/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5451856717/10000000000 : ℝ)|^17 ≤ (1413615191901/3125000000000 : ℝ)^13
        have hw : |(5451856717/10000000000 : ℝ)|=(5451856717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(678693957/1250000000 : ℝ)|^17 ≤ (11248455423763/25000000000000 : ℝ)^13
        have hw : |(678693957/1250000000 : ℝ)|=(678693957/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1688819209/10000000000 : ℝ)|^17 ≤ (4885246074713/50000000000000 : ℝ)^13
        have hw : |(-1688819209/10000000000 : ℝ)|=(1688819209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306054_s1_s1_7 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1407/5000000000 : ℝ)*x 0 + (1554636089/10000000000 : ℝ)*x 1 + (-4661164533/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1407/5000000000 : ℝ)^17 ≤ (271477/100000000000000 : ℝ)^13 := by
    have hnat : (1407 : ℕ)^17*100000000000000^13 ≤ 271477^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1407 5000000000 271477 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1554636089/10000000000 : ℝ)^17 ≤ (2191992868621/25000000000000 : ℝ)^13 := by
    have hnat : (1554636089 : ℕ)^17*25000000000000^13 ≤ 2191992868621^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1554636089 10000000000 2191992868621 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4661164533/5000000000 : ℝ)^17 ≤ (91232028246321/100000000000000 : ℝ)^13 := by
    have hnat : (4661164533 : ℕ)^17*100000000000000^13 ≤ 91232028246321^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4661164533 5000000000 91232028246321 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1407/5000000000 : ℝ), (1554636089/10000000000 : ℝ), (-4661164533/5000000000 : ℝ)] ![(271477/100000000000000 : ℝ), (2191992868621/25000000000000 : ℝ), (91232028246321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1407/5000000000 : ℝ)|^17 ≤ (271477/100000000000000 : ℝ)^13
        have hw : |(-1407/5000000000 : ℝ)|=(1407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1554636089/10000000000 : ℝ)|^17 ≤ (2191992868621/25000000000000 : ℝ)^13
        have hw : |(1554636089/10000000000 : ℝ)|=(1554636089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4661164533/5000000000 : ℝ)|^17 ≤ (91232028246321/100000000000000 : ℝ)^13
        have hw : |(-4661164533/5000000000 : ℝ)|=(4661164533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306054_s1_s1_8 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3937186953/10000000000 : ℝ)*x 0 + (-350701797/2500000000 : ℝ)*x 1 + (-7004734239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3937186953/10000000000 : ℝ)^17 ≤ (461793611891/1562500000000 : ℝ)^13 := by
    have hnat : (3937186953 : ℕ)^17*1562500000000^13 ≤ 461793611891^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3937186953 10000000000 461793611891 1562500000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (350701797/2500000000 : ℝ)^17 ≤ (3832708833597/50000000000000 : ℝ)^13 := by
    have hnat : (350701797 : ℕ)^17*50000000000000^13 ≤ 3832708833597^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      350701797 2500000000 3832708833597 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7004734239/10000000000 : ℝ)^17 ≤ (62779791154749/100000000000000 : ℝ)^13 := by
    have hnat : (7004734239 : ℕ)^17*100000000000000^13 ≤ 62779791154749^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7004734239 10000000000 62779791154749 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3937186953/10000000000 : ℝ), (-350701797/2500000000 : ℝ), (-7004734239/10000000000 : ℝ)] ![(461793611891/1562500000000 : ℝ), (3832708833597/50000000000000 : ℝ), (62779791154749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3937186953/10000000000 : ℝ)|^17 ≤ (461793611891/1562500000000 : ℝ)^13
        have hw : |(3937186953/10000000000 : ℝ)|=(3937186953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-350701797/2500000000 : ℝ)|^17 ≤ (3832708833597/50000000000000 : ℝ)^13
        have hw : |(-350701797/2500000000 : ℝ)|=(350701797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7004734239/10000000000 : ℝ)|^17 ≤ (62779791154749/100000000000000 : ℝ)^13
        have hw : |(-7004734239/10000000000 : ℝ)|=(7004734239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306054_s1_s1_9 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1450746503/5000000000 : ℝ)*x 0 + (8209077329/10000000000 : ℝ)*x 1 + (335109703/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1450746503/5000000000 : ℝ)^17 ≤ (9913894893663/50000000000000 : ℝ)^13 := by
    have hnat : (1450746503 : ℕ)^17*50000000000000^13 ≤ 9913894893663^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1450746503 5000000000 9913894893663 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8209077329/10000000000 : ℝ)^17 ≤ (15450885427743/20000000000000 : ℝ)^13 := by
    have hnat : (8209077329 : ℕ)^17*20000000000000^13 ≤ 15450885427743^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8209077329 10000000000 15450885427743 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (335109703/5000000000 : ℝ)^17 ≤ (2917783057027/100000000000000 : ℝ)^13 := by
    have hnat : (335109703 : ℕ)^17*100000000000000^13 ≤ 2917783057027^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335109703 5000000000 2917783057027 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1450746503/5000000000 : ℝ), (8209077329/10000000000 : ℝ), (335109703/5000000000 : ℝ)] ![(9913894893663/50000000000000 : ℝ), (15450885427743/20000000000000 : ℝ), (2917783057027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1450746503/5000000000 : ℝ)|^17 ≤ (9913894893663/50000000000000 : ℝ)^13
        have hw : |(1450746503/5000000000 : ℝ)|=(1450746503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8209077329/10000000000 : ℝ)|^17 ≤ (15450885427743/20000000000000 : ℝ)^13
        have hw : |(8209077329/10000000000 : ℝ)|=(8209077329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(335109703/5000000000 : ℝ)|^17 ≤ (2917783057027/100000000000000 : ℝ)^13
        have hw : |(335109703/5000000000 : ℝ)|=(335109703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306054_s1_s1_13 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (138830343/400000000 : ℝ)*x 0 + (7754770259/10000000000 : ℝ)*x 1 + (-361876831/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (138830343/400000000 : ℝ)^17 ≤ (6265511604729/25000000000000 : ℝ)^13 := by
    have hnat : (138830343 : ℕ)^17*25000000000000^13 ≤ 6265511604729^13*400000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138830343 400000000 6265511604729 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7754770259/10000000000 : ℝ)^17 ≤ (4481982582309/6250000000000 : ℝ)^13 := by
    have hnat : (7754770259 : ℕ)^17*6250000000000^13 ≤ 4481982582309^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7754770259 10000000000 4481982582309 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (361876831/5000000000 : ℝ)^17 ≤ (1613116123413/50000000000000 : ℝ)^13 := by
    have hnat : (361876831 : ℕ)^17*50000000000000^13 ≤ 1613116123413^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      361876831 5000000000 1613116123413 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(138830343/400000000 : ℝ), (7754770259/10000000000 : ℝ), (-361876831/5000000000 : ℝ)] ![(6265511604729/25000000000000 : ℝ), (4481982582309/6250000000000 : ℝ), (1613116123413/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(138830343/400000000 : ℝ)|^17 ≤ (6265511604729/25000000000000 : ℝ)^13
        have hw : |(138830343/400000000 : ℝ)|=(138830343/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7754770259/10000000000 : ℝ)|^17 ≤ (4481982582309/6250000000000 : ℝ)^13
        have hw : |(7754770259/10000000000 : ℝ)|=(7754770259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-361876831/5000000000 : ℝ)|^17 ≤ (1613116123413/50000000000000 : ℝ)^13
        have hw : |(-361876831/5000000000 : ℝ)|=(361876831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306054_s1_s1_14 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1238679/1250000000 : ℝ)*x 0 + (29589563/156250000 : ℝ)*x 1 + (-9119046491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1238679/1250000000 : ℝ)^17 ≤ (5898289401/50000000000000 : ℝ)^13 := by
    have hnat : (1238679 : ℕ)^17*50000000000000^13 ≤ 5898289401^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1238679 1250000000 5898289401 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (29589563/156250000 : ℝ)^17 ≤ (88663531389/781250000000 : ℝ)^13 := by
    have hnat : (29589563 : ℕ)^17*781250000000^13 ≤ 88663531389^13*156250000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29589563 156250000 88663531389 781250000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9119046491/10000000000 : ℝ)^17 ≤ (88639271384059/100000000000000 : ℝ)^13 := by
    have hnat : (9119046491 : ℕ)^17*100000000000000^13 ≤ 88639271384059^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9119046491 10000000000 88639271384059 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1238679/1250000000 : ℝ), (29589563/156250000 : ℝ), (-9119046491/10000000000 : ℝ)] ![(5898289401/50000000000000 : ℝ), (88663531389/781250000000 : ℝ), (88639271384059/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1238679/1250000000 : ℝ)|^17 ≤ (5898289401/50000000000000 : ℝ)^13
        have hw : |(1238679/1250000000 : ℝ)|=(1238679/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(29589563/156250000 : ℝ)|^17 ≤ (88663531389/781250000000 : ℝ)^13
        have hw : |(29589563/156250000 : ℝ)|=(29589563/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-9119046491/10000000000 : ℝ)|^17 ≤ (88639271384059/100000000000000 : ℝ)^13
        have hw : |(-9119046491/10000000000 : ℝ)|=(9119046491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306054_s1_s1_15 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1867108943/5000000000 : ℝ)*x 0 + (-756860031/2500000000 : ℝ)*x 1 + (-752098909/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1867108943/5000000000 : ℝ)^17 ≤ (27578381773187/100000000000000 : ℝ)^13 := by
    have hnat : (1867108943 : ℕ)^17*100000000000000^13 ≤ 27578381773187^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1867108943 5000000000 27578381773187 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (756860031/2500000000 : ℝ)^17 ≤ (5240183719613/25000000000000 : ℝ)^13 := by
    have hnat : (756860031 : ℕ)^17*25000000000000^13 ≤ 5240183719613^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      756860031 2500000000 5240183719613 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (752098909/1250000000 : ℝ)^17 ≤ (51460883332567/100000000000000 : ℝ)^13 := by
    have hnat : (752098909 : ℕ)^17*100000000000000^13 ≤ 51460883332567^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      752098909 1250000000 51460883332567 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1867108943/5000000000 : ℝ), (-756860031/2500000000 : ℝ), (-752098909/1250000000 : ℝ)] ![(27578381773187/100000000000000 : ℝ), (5240183719613/25000000000000 : ℝ), (51460883332567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1867108943/5000000000 : ℝ)|^17 ≤ (27578381773187/100000000000000 : ℝ)^13
        have hw : |(1867108943/5000000000 : ℝ)|=(1867108943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-756860031/2500000000 : ℝ)|^17 ≤ (5240183719613/25000000000000 : ℝ)^13
        have hw : |(-756860031/2500000000 : ℝ)|=(756860031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-752098909/1250000000 : ℝ)|^17 ≤ (51460883332567/100000000000000 : ℝ)^13
        have hw : |(-752098909/1250000000 : ℝ)|=(752098909/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306054_s1_s1_16 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (8290263327/10000000000 : ℝ)*x 0 + (2546605819/10000000000 : ℝ)*x 1 + (507993903/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8290263327/10000000000 : ℝ)^17 ≤ (78255059426117/100000000000000 : ℝ)^13 := by
    have hnat : (8290263327 : ℕ)^17*100000000000000^13 ≤ 78255059426117^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8290263327 10000000000 78255059426117 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2546605819/10000000000 : ℝ)^17 ≤ (16717861387909/100000000000000 : ℝ)^13 := by
    have hnat : (2546605819 : ℕ)^17*100000000000000^13 ≤ 16717861387909^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2546605819 10000000000 16717861387909 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (507993903/5000000000 : ℝ)^17 ≤ (5027079170723/100000000000000 : ℝ)^13 := by
    have hnat : (507993903 : ℕ)^17*100000000000000^13 ≤ 5027079170723^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507993903 5000000000 5027079170723 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8290263327/10000000000 : ℝ), (2546605819/10000000000 : ℝ), (507993903/5000000000 : ℝ)] ![(78255059426117/100000000000000 : ℝ), (16717861387909/100000000000000 : ℝ), (5027079170723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8290263327/10000000000 : ℝ)|^17 ≤ (78255059426117/100000000000000 : ℝ)^13
        have hw : |(8290263327/10000000000 : ℝ)|=(8290263327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2546605819/10000000000 : ℝ)|^17 ≤ (16717861387909/100000000000000 : ℝ)^13
        have hw : |(2546605819/10000000000 : ℝ)|=(2546605819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(507993903/5000000000 : ℝ)|^17 ≤ (5027079170723/100000000000000 : ℝ)^13
        have hw : |(507993903/5000000000 : ℝ)|=(507993903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306054_s1_s1_20 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (7686183267/10000000000 : ℝ)*x 0 + (845720327/2500000000 : ℝ)*x 1 + (-4966713/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7686183267/10000000000 : ℝ)^17 ≤ (17720860898231/25000000000000 : ℝ)^13 := by
    have hnat : (7686183267 : ℕ)^17*25000000000000^13 ≤ 17720860898231^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7686183267 10000000000 17720860898231 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (845720327/2500000000 : ℝ)^17 ≤ (12117748140961/50000000000000 : ℝ)^13 := by
    have hnat : (845720327 : ℕ)^17*50000000000000^13 ≤ 12117748140961^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845720327 2500000000 12117748140961 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4966713/50000000 : ℝ)^17 ≤ (1220265028737/25000000000000 : ℝ)^13 := by
    have hnat : (4966713 : ℕ)^17*25000000000000^13 ≤ 1220265028737^13*50000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4966713 50000000 1220265028737 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7686183267/10000000000 : ℝ), (845720327/2500000000 : ℝ), (-4966713/50000000 : ℝ)] ![(17720860898231/25000000000000 : ℝ), (12117748140961/50000000000000 : ℝ), (1220265028737/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7686183267/10000000000 : ℝ)|^17 ≤ (17720860898231/25000000000000 : ℝ)^13
        have hw : |(7686183267/10000000000 : ℝ)|=(7686183267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(845720327/2500000000 : ℝ)|^17 ≤ (12117748140961/50000000000000 : ℝ)^13
        have hw : |(845720327/2500000000 : ℝ)|=(845720327/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4966713/50000000 : ℝ)|^17 ≤ (1220265028737/25000000000000 : ℝ)^13
        have hw : |(-4966713/50000000 : ℝ)|=(4966713/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306054_s1_s1_21 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1592133/250000000 : ℝ)*x 0 + (6653556673/10000000000 : ℝ)*x 1 + (-2536495967/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1592133/250000000 : ℝ)^17 ≤ (134387579211/100000000000000 : ℝ)^13 := by
    have hnat : (1592133 : ℕ)^17*100000000000000^13 ≤ 134387579211^13*250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1592133 250000000 134387579211 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6653556673/10000000000 : ℝ)^17 ≤ (58696052483911/100000000000000 : ℝ)^13 := by
    have hnat : (6653556673 : ℕ)^17*100000000000000^13 ≤ 58696052483911^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6653556673 10000000000 58696052483911 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2536495967/5000000000 : ℝ)^17 ≤ (41169559920177/100000000000000 : ℝ)^13 := by
    have hnat : (2536495967 : ℕ)^17*100000000000000^13 ≤ 41169559920177^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2536495967 5000000000 41169559920177 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1592133/250000000 : ℝ), (6653556673/10000000000 : ℝ), (-2536495967/5000000000 : ℝ)] ![(134387579211/100000000000000 : ℝ), (58696052483911/100000000000000 : ℝ), (41169559920177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1592133/250000000 : ℝ)|^17 ≤ (134387579211/100000000000000 : ℝ)^13
        have hw : |(1592133/250000000 : ℝ)|=(1592133/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6653556673/10000000000 : ℝ)|^17 ≤ (58696052483911/100000000000000 : ℝ)^13
        have hw : |(6653556673/10000000000 : ℝ)|=(6653556673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2536495967/5000000000 : ℝ)|^17 ≤ (41169559920177/100000000000000 : ℝ)^13
        have hw : |(-2536495967/5000000000 : ℝ)|=(2536495967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306054_s1_s1_22 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4145995221/5000000000 : ℝ)*x 0 + (-1639053199/10000000000 : ℝ)*x 1 + (-1008713831/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4145995221/5000000000 : ℝ)^17 ≤ (15655275862087/20000000000000 : ℝ)^13 := by
    have hnat : (4145995221 : ℕ)^17*20000000000000^13 ≤ 15655275862087^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4145995221 5000000000 15655275862087 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1639053199/10000000000 : ℝ)^17 ≤ (9395705002821/100000000000000 : ℝ)^13 := by
    have hnat : (1639053199 : ℕ)^17*100000000000000^13 ≤ 9395705002821^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1639053199 10000000000 9395705002821 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1008713831/5000000000 : ℝ)^17 ≤ (12327915669193/100000000000000 : ℝ)^13 := by
    have hnat : (1008713831 : ℕ)^17*100000000000000^13 ≤ 12327915669193^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008713831 5000000000 12327915669193 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4145995221/5000000000 : ℝ), (-1639053199/10000000000 : ℝ), (-1008713831/5000000000 : ℝ)] ![(15655275862087/20000000000000 : ℝ), (9395705002821/100000000000000 : ℝ), (12327915669193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4145995221/5000000000 : ℝ)|^17 ≤ (15655275862087/20000000000000 : ℝ)^13
        have hw : |(4145995221/5000000000 : ℝ)|=(4145995221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1639053199/10000000000 : ℝ)|^17 ≤ (9395705002821/100000000000000 : ℝ)^13
        have hw : |(-1639053199/10000000000 : ℝ)|=(1639053199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1008713831/5000000000 : ℝ)|^17 ≤ (12327915669193/100000000000000 : ℝ)^13
        have hw : |(-1008713831/5000000000 : ℝ)|=(1008713831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306054_s1_s1_23 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2782810033/10000000000 : ℝ)*x 0 + (3617625101/5000000000 : ℝ)*x 1 + (1215416161/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2782810033/10000000000 : ℝ)^17 ≤ (18773939985733/100000000000000 : ℝ)^13 := by
    have hnat : (2782810033 : ℕ)^17*100000000000000^13 ≤ 18773939985733^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2782810033 10000000000 18773939985733 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3617625101/5000000000 : ℝ)^17 ≤ (32747526185529/50000000000000 : ℝ)^13 := by
    have hnat : (3617625101 : ℕ)^17*50000000000000^13 ≤ 32747526185529^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3617625101 5000000000 32747526185529 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1215416161/5000000000 : ℝ)^17 ≤ (1966375953213/12500000000000 : ℝ)^13 := by
    have hnat : (1215416161 : ℕ)^17*12500000000000^13 ≤ 1966375953213^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1215416161 5000000000 1966375953213 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2782810033/10000000000 : ℝ), (3617625101/5000000000 : ℝ), (1215416161/5000000000 : ℝ)] ![(18773939985733/100000000000000 : ℝ), (32747526185529/50000000000000 : ℝ), (1966375953213/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2782810033/10000000000 : ℝ)|^17 ≤ (18773939985733/100000000000000 : ℝ)^13
        have hw : |(2782810033/10000000000 : ℝ)|=(2782810033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3617625101/5000000000 : ℝ)|^17 ≤ (32747526185529/50000000000000 : ℝ)^13
        have hw : |(3617625101/5000000000 : ℝ)|=(3617625101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1215416161/5000000000 : ℝ)|^17 ≤ (1966375953213/12500000000000 : ℝ)^13
        have hw : |(1215416161/5000000000 : ℝ)|=(1215416161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306054_s1_s1_27 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3707311299/5000000000 : ℝ)*x 0 + (870568031/2500000000 : ℝ)*x 1 + (-1337587749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3707311299/5000000000 : ℝ)^17 ≤ (8453303535839/12500000000000 : ℝ)^13 := by
    have hnat : (3707311299 : ℕ)^17*12500000000000^13 ≤ 8453303535839^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3707311299 5000000000 8453303535839 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (870568031/2500000000 : ℝ)^17 ≤ (5034164245383/20000000000000 : ℝ)^13 := by
    have hnat : (870568031 : ℕ)^17*20000000000000^13 ≤ 5034164245383^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870568031 2500000000 5034164245383 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1337587749/10000000000 : ℝ)^17 ≤ (7202750467113/100000000000000 : ℝ)^13 := by
    have hnat : (1337587749 : ℕ)^17*100000000000000^13 ≤ 7202750467113^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337587749 10000000000 7202750467113 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3707311299/5000000000 : ℝ), (870568031/2500000000 : ℝ), (-1337587749/10000000000 : ℝ)] ![(8453303535839/12500000000000 : ℝ), (5034164245383/20000000000000 : ℝ), (7202750467113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3707311299/5000000000 : ℝ)|^17 ≤ (8453303535839/12500000000000 : ℝ)^13
        have hw : |(3707311299/5000000000 : ℝ)|=(3707311299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(870568031/2500000000 : ℝ)|^17 ≤ (5034164245383/20000000000000 : ℝ)^13
        have hw : |(870568031/2500000000 : ℝ)|=(870568031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1337587749/10000000000 : ℝ)|^17 ≤ (7202750467113/100000000000000 : ℝ)^13
        have hw : |(-1337587749/10000000000 : ℝ)|=(1337587749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c306054_s1 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((92739/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(92739/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11799/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(11799/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-42039/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-42039/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((41333/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(41333/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(86621/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(86621/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-35907/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-35907/50000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (38461/50000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (38461/50000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (92997/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  have s1_pow0 : (92739/100000 : ℝ) ^ (67/16 : ℝ) ≤ (72930860211944747353/100000000000000000000 : ℝ) := by
    have hpowers : (92739/100000 : ℝ)^67 ≤ (72930860211944747353/100000000000000000000 : ℝ)^16 := by
      have hnat : (92739 : ℕ)^67*100000000000000000000^16 ≤ 72930860211944747353^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        92739 100000 72930860211944747353 100000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (92739/100000 : ℝ)) (X := (72930860211944747353/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (172930860211944747353/100000000000000000000 : ℝ) ≤ (2279477812043949/2000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (172930860211944747353/100000000000000000000 : ℝ)^16 ≤ (2279477812043949/2000000000000000 : ℝ)^67 := by
      have hnat : (172930860211944747353 : ℕ)^16*2000000000000000^67 ≤ 2279477812043949^67*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        172930860211944747353 100000000000000000000 2279477812043949 2000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2279477812043949/2000000000000000 : ℝ)) (X := (172930860211944747353/100000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (122930860211944747353/50000000000000000000 : ℝ) ≤ (1239650680924281/1000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (122930860211944747353/50000000000000000000 : ℝ)^16 ≤ (1239650680924281/1000000000000000 : ℝ)^67 := by
      have hnat : (122930860211944747353 : ℕ)^16*1000000000000000^67 ≤ 1239650680924281^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        122930860211944747353 50000000000000000000 1239650680924281 1000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1239650680924281/1000000000000000 : ℝ)) (X := (122930860211944747353/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(279477812043949/1854780000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(66607849934871/618260000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (92739/100000 : ℝ)) (alpha := (279477812043949/1854780000000000 : ℝ)) (beta := (66607849934871/618260000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (92739/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(279477812043949/1854780000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(66607849934871/618260000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (11799/12500 : ℝ) ^ (67/16 : ℝ) ≤ (15706199006940456429/20000000000000000000 : ℝ) := by
    have hpowers : (11799/12500 : ℝ)^67 ≤ (15706199006940456429/20000000000000000000 : ℝ)^16 := by
      have hnat : (11799 : ℕ)^67*20000000000000000000^16 ≤ 15706199006940456429^16*12500^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11799 12500 15706199006940456429 20000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11799/12500 : ℝ)) (X := (15706199006940456429/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (35706199006940456429/20000000000000000000 : ℝ) ≤ (2871115906246413/2500000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (35706199006940456429/20000000000000000000 : ℝ)^16 ≤ (2871115906246413/2500000000000000 : ℝ)^67 := by
      have hnat : (35706199006940456429 : ℕ)^16*2500000000000000^67 ≤ 2871115906246413^67*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35706199006940456429 20000000000000000000 2871115906246413 2500000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2871115906246413/2500000000000000 : ℝ)) (X := (35706199006940456429/20000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (25706199006940456429/10000000000000000000 : ℝ) ≤ (6264544442112789/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (25706199006940456429/10000000000000000000 : ℝ)^16 ≤ (6264544442112789/5000000000000000 : ℝ)^67 := by
      have hnat : (25706199006940456429 : ℕ)^16*5000000000000000^67 ≤ 6264544442112789^67*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25706199006940456429 10000000000000000000 6264544442112789 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6264544442112789/5000000000000000 : ℝ)) (X := (25706199006940456429/10000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(371115906246413/2359800000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(174104209873321/1573200000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (11799/12500 : ℝ)) (alpha := (371115906246413/2359800000000000 : ℝ)) (beta := (174104209873321/1573200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (11799/12500 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(371115906246413/2359800000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(174104209873321/1573200000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (42039/50000 : ℝ) ^ (67/16 : ℝ) ≤ (48373491430672444401/100000000000000000000 : ℝ) := by
    have hpowers : (42039/50000 : ℝ)^67 ≤ (48373491430672444401/100000000000000000000 : ℝ)^16 := by
      have hnat : (42039 : ℕ)^67*100000000000000000000^16 ≤ 48373491430672444401^16*50000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        42039 50000 48373491430672444401 100000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (42039/50000 : ℝ)) (X := (48373491430672444401/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (148373491430672444401/100000000000000000000 : ℝ) ≤ (686753574725913/625000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (148373491430672444401/100000000000000000000 : ℝ)^16 ≤ (686753574725913/625000000000000 : ℝ)^67 := by
      have hnat : (148373491430672444401 : ℕ)^16*625000000000000^67 ≤ 686753574725913^67*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        148373491430672444401 100000000000000000000 686753574725913 625000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (686753574725913/625000000000000 : ℝ)) (X := (148373491430672444401/100000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (98373491430672444401/50000000000000000000 : ℝ) ≤ (2938508918262231/2500000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (98373491430672444401/50000000000000000000 : ℝ)^16 ≤ (2938508918262231/2500000000000000 : ℝ)^67 := by
      have hnat : (98373491430672444401 : ℕ)^16*2500000000000000^67 ≤ 2938508918262231^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        98373491430672444401 50000000000000000000 2938508918262231 2500000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2938508918262231/2500000000000000 : ℝ)) (X := (98373491430672444401/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(61753574725913/525487500000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(7092393309577/77850000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (42039/50000 : ℝ)) (alpha := (61753574725913/525487500000000 : ℝ)) (beta := (7092393309577/77850000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (42039/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(61753574725913/525487500000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(7092393309577/77850000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_1 : ((1482972963/2500000000 : ℝ)*X 1 0+(-1331040037/10000000000 : ℝ)*X 1 1+(-5181973583/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2828779401/5000000000 : ℝ)*X 2 0+(1405344509/2500000000 : ℝ)*X 2 1+(269640897/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((5451856717/10000000000 : ℝ)*X 0 0+(678693957/1250000000 : ℝ)*X 0 1+(-1688819209/10000000000 : ℝ)*X 0 2+(5451856717/10000000000 : ℝ)*X 1 0+(678693957/1250000000 : ℝ)*X 1 1+(-1688819209/10000000000 : ℝ)*X 1 2+(5451856717/10000000000 : ℝ)*X 2 0+(678693957/1250000000 : ℝ)*X 2 1+(-1688819209/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-1407/5000000000 : ℝ)*X 0 0+(1554636089/10000000000 : ℝ)*X 0 1+(-4661164533/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((3937186953/10000000000 : ℝ)*X 1 0+(-350701797/2500000000 : ℝ)*X 1 1+(-7004734239/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((1450746503/5000000000 : ℝ)*X 2 0+(8209077329/10000000000 : ℝ)*X 2 1+(335109703/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((138830343/400000000 : ℝ)*X 0 0+(7754770259/10000000000 : ℝ)*X 0 1+(-361876831/5000000000 : ℝ)*X 0 2+(138830343/400000000 : ℝ)*X 1 0+(7754770259/10000000000 : ℝ)*X 1 1+(-361876831/5000000000 : ℝ)*X 1 2+(138830343/400000000 : ℝ)*X 2 0+(7754770259/10000000000 : ℝ)*X 2 1+(-361876831/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((1238679/1250000000 : ℝ)*X 0 0+(29589563/156250000 : ℝ)*X 0 1+(-9119046491/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((1867108943/5000000000 : ℝ)*X 1 0+(-756860031/2500000000 : ℝ)*X 1 1+(-752098909/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((8290263327/10000000000 : ℝ)*X 2 0+(2546605819/10000000000 : ℝ)*X 2 1+(507993903/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((7686183267/10000000000 : ℝ)*X 0 0+(845720327/2500000000 : ℝ)*X 0 1+(-4966713/50000000 : ℝ)*X 0 2+(7686183267/10000000000 : ℝ)*X 1 0+(845720327/2500000000 : ℝ)*X 1 1+(-4966713/50000000 : ℝ)*X 1 2+(7686183267/10000000000 : ℝ)*X 2 0+(845720327/2500000000 : ℝ)*X 2 1+(-4966713/50000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((1592133/250000000 : ℝ)*X 0 0+(6653556673/10000000000 : ℝ)*X 0 1+(-2536495967/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((4145995221/5000000000 : ℝ)*X 1 0+(-1639053199/10000000000 : ℝ)*X 1 1+(-1008713831/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((2782810033/10000000000 : ℝ)*X 2 0+(3617625101/5000000000 : ℝ)*X 2 1+(1215416161/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((3707311299/5000000000 : ℝ)*X 0 0+(870568031/2500000000 : ℝ)*X 0 1+(-1337587749/10000000000 : ℝ)*X 0 2+(3707311299/5000000000 : ℝ)*X 1 0+(870568031/2500000000 : ℝ)*X 1 1+(-1337587749/10000000000 : ℝ)*X 1 2+(3707311299/5000000000 : ℝ)*X 2 0+(870568031/2500000000 : ℝ)*X 2 1+(-1337587749/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((41333/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(41333/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2051006045884341633945333/307507067500000000000000000000 : ℝ) := by norm_num
    linear_combination (716349574797/1000000000000 : ℝ)*(base7) + (444663/500000000000 : ℝ)*(base39) + (681952339/2500000000 : ℝ)*(base53) + (48404805821/250000000000 : ℝ)*(base60) + (87624412689/50000000000 : ℝ)*(major_s1_0) + (87624412689/50000000000 : ℝ)*(major_s1_1) + (73985365909/50000000000 : ℝ)*(major_s1_2) + (1955911/40000000000 : ℝ)*(sp_s1_1) + (825618239827/500000000000 : ℝ)*(sp_s1_7) + (825691865159/500000000000 : ℝ)*(sp_s1_8) + (1924245273933/1000000000000 : ℝ)*(sp_s1_9) + (463239043943/250000000000 : ℝ)*(sp_s1_13) + (227858679/1000000000000 : ℝ)*(sp_s1_14) + (31710241/1000000000000 : ℝ)*(sp_s1_15) + (45464264039/40000000000 : ℝ)*(f.failure) + (1924245273933/1000000000000 : ℝ)*(f.sum) + (49202567483881417/183710430000000000000000000000 : ℝ)*base63 + (3087301148849/7785000000000000000000000 : ℝ)*base65 + (1806083448949/26220000000000000000000000 : ℝ)*base66 + (11238060301687/105097500000000000000000000 : ℝ)*base68 + (248229425578635721/481315410000000000000000000000 : ℝ)*base71 + (273173659652649/309130000000000000000000000 : ℝ)*base73 + (2071889954377/7866000000000000000000000 : ℝ)*base75 + (25820306681921/61826000000000000000000000 : ℝ)*base77 + (706783808856437/2245260000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (1373/2000000000000000 : ℝ)*base86 + (1373/2000000000000000 : ℝ)*base88 + (1373/2000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(86621/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(86621/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (280410551269264246941153433/22140508860000000000000000000000 : ℝ) := by norm_num
    linear_combination (804513465789/1000000000000 : ℝ)*(base7) + (106903/200000000000 : ℝ)*(base40) + (616414891017/1000000000000 : ℝ)*(base53) + (7736985781/100000000000 : ℝ)*(base60) + (1722552581469/1000000000000 : ℝ)*(major_s1_0) + (1722552581469/1000000000000 : ℝ)*(major_s1_1) + (276534422613/250000000000 : ℝ)*(major_s1_2) + (6671093/1000000000000 : ℝ)*(sp_s1_1) + (45122889/1000000000000 : ℝ)*(sp_s1_8) + (1212712489347/1000000000000 : ℝ)*(sp_s1_14) + (242532139073/200000000000 : ℝ)*(sp_s1_15) + (457281845091/250000000000 : ℝ)*(sp_s1_16) + (240208381893/125000000000 : ℝ)*(sp_s1_20) + (9428253/250000000000 : ℝ)*(sp_s1_27) + (34912228199/31250000000 : ℝ)*(f.failure) + (457281845091/250000000000 : ℝ)*(f.sum) + (71599507296035749/408245400000000000000000000000 : ℝ)*base63 + (1436130198049/2162500000000000000000000 : ℝ)*base65 + (76243832379583/524400000000000000000000000 : ℝ)*base66 + (75775618641071/233550000000000000000000000 : ℝ)*base69 + (81802454773830381/534794900000000000000000000000 : ℝ)*base71 + (266793549125207/618260000000000000000000000 : ℝ)*base73 + (531640180760579/786600000000000000000000000 : ℝ)*base75 + (139930115016629/618260000000000000000000000 : ℝ)*base76 + (17716551968222021/44905200000000000000000000000 : ℝ)*base79 + (389/3125000000000000 : ℝ)*base87 + (389/3125000000000000 : ℝ)*base89 + (389/3125000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-35907/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-35907/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (30238149349756112110640787809/1992645797400000000000000000000000 : ℝ) := by norm_num
    linear_combination (436947456891/500000000000 : ℝ)*(base7) + (78266469811/500000000000 : ℝ)*(base39) + (73467/500000000000 : ℝ)*(base43) + (1655655713183/1000000000000 : ℝ)*(major_s1_0) + (1655655566249/1000000000000 : ℝ)*(major_s1_1) + (1655655713183/1000000000000 : ℝ)*(major_s1_2) + (8478813/500000000000 : ℝ)*(sp_s1_2) + (12369349/500000000000 : ℝ)*(sp_s1_6) + (28504077/1000000000000 : ℝ)*(sp_s1_9) + (207458747/1000000000000 : ℝ)*(sp_s1_20) + (1695704672357/1000000000000 : ℝ)*(sp_s1_21) + (1695704819291/1000000000000 : ℝ)*(sp_s1_22) + (847829605327/500000000000 : ℝ)*(sp_s1_23) + (243433362059/125000000000 : ℝ)*(sp_s1_27) + (214760836027/200000000000 : ℝ)*(f.failure) + (1695704819291/1000000000000 : ℝ)*(f.sum) + (600194313943052117/3674208600000000000000000000000 : ℝ)*base63 + (6493473388243/38925000000000000000000000 : ℝ)*base65 + (8677691751569/1573200000000000000000000000 : ℝ)*base66 + (513734005414681/2101950000000000000000000000 : ℝ)*base69 + (183364018685120999/4813154100000000000000000000000 : ℝ)*base70 + (56659137713891/123652000000000000000000000 : ℝ)*base72 + (344751921028177/2359800000000000000000000000 : ℝ)*base75 + (61071515384497/370956000000000000000000000 : ℝ)*base77 + (1013086460932320383/2559596400000000000000000000000 : ℝ)*base78 + (489/10000000000000000 : ℝ)*base86 + (489/10000000000000000 : ℝ)*base88 + (489/10000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((92739/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(92739/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11799/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(11799/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-42039/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-42039/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((41333/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(41333/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(86621/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(86621/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-35907/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-35907/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c306054_s1 p hpa hpb X hX hprev0

#print axioms solution
