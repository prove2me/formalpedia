-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c313060_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:34:14.24624+00:00
-- url     : https://prove2.me/submissions/472172a3-c0e6-4ef2-89a0-6e15043937b9

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
theorem collision_support_c313060_s1_s1_0 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-27860563/156250000 : ℝ)*x 0 + (4321589013/10000000000 : ℝ)*x 1 + (-6226036763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (27860563/156250000 : ℝ)^37 ≤ (11081435709829/100000000000000 : ℝ)^29 := by
    have hnat : (27860563 : ℕ)^37*100000000000000^29 ≤ 11081435709829^29*156250000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27860563 156250000 11081435709829 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4321589013/10000000000 : ℝ)^37 ≤ (6857428848937/20000000000000 : ℝ)^29 := by
    have hnat : (4321589013 : ℕ)^37*20000000000000^29 ≤ 6857428848937^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4321589013 10000000000 6857428848937 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6226036763/10000000000 : ℝ)^37 ≤ (27315710013707/50000000000000 : ℝ)^29 := by
    have hnat : (6226036763 : ℕ)^37*50000000000000^29 ≤ 27315710013707^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6226036763 10000000000 27315710013707 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-27860563/156250000 : ℝ), (4321589013/10000000000 : ℝ), (-6226036763/10000000000 : ℝ)] ![(11081435709829/100000000000000 : ℝ), (6857428848937/20000000000000 : ℝ), (27315710013707/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-27860563/156250000 : ℝ)|^37 ≤ (11081435709829/100000000000000 : ℝ)^29
        have hw : |(-27860563/156250000 : ℝ)|=(27860563/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4321589013/10000000000 : ℝ)|^37 ≤ (6857428848937/20000000000000 : ℝ)^29
        have hw : |(4321589013/10000000000 : ℝ)|=(4321589013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6226036763/10000000000 : ℝ)|^37 ≤ (27315710013707/50000000000000 : ℝ)^29
        have hw : |(-6226036763/10000000000 : ℝ)|=(6226036763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313060_s1_s1_2 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2346719629/5000000000 : ℝ)*x 0 + (23536891/39062500 : ℝ)*x 1 + (1581560693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2346719629/5000000000 : ℝ)^37 ≤ (38095009381133/100000000000000 : ℝ)^29 := by
    have hnat : (2346719629 : ℕ)^37*100000000000000^29 ≤ 38095009381133^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2346719629 5000000000 38095009381133 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (23536891/39062500 : ℝ)^37 ≤ (26197894751399/50000000000000 : ℝ)^29 := by
    have hnat : (23536891 : ℕ)^37*50000000000000^29 ≤ 26197894751399^29*39062500^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23536891 39062500 26197894751399 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1581560693/10000000000 : ℝ)^37 ≤ (9509201097949/100000000000000 : ℝ)^29 := by
    have hnat : (1581560693 : ℕ)^37*100000000000000^29 ≤ 9509201097949^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1581560693 10000000000 9509201097949 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2346719629/5000000000 : ℝ), (23536891/39062500 : ℝ), (1581560693/10000000000 : ℝ)] ![(38095009381133/100000000000000 : ℝ), (26197894751399/50000000000000 : ℝ), (9509201097949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2346719629/5000000000 : ℝ)|^37 ≤ (38095009381133/100000000000000 : ℝ)^29
        have hw : |(2346719629/5000000000 : ℝ)|=(2346719629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(23536891/39062500 : ℝ)|^37 ≤ (26197894751399/50000000000000 : ℝ)^29
        have hw : |(23536891/39062500 : ℝ)|=(23536891/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1581560693/10000000000 : ℝ)|^37 ≤ (9509201097949/100000000000000 : ℝ)^29
        have hw : |(1581560693/10000000000 : ℝ)|=(1581560693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313060_s1_s1_7 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-959939779/5000000000 : ℝ)*x 0 + (195012373/625000000 : ℝ)*x 1 + (-7151247383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (959939779/5000000000 : ℝ)^37 ≤ (3044363256249/25000000000000 : ℝ)^29 := by
    have hnat : (959939779 : ℕ)^37*25000000000000^29 ≤ 3044363256249^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      959939779 5000000000 3044363256249 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (195012373/625000000 : ℝ)^37 ≤ (11314000544741/50000000000000 : ℝ)^29 := by
    have hnat : (195012373 : ℕ)^37*50000000000000^29 ≤ 11314000544741^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195012373 625000000 11314000544741 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7151247383/10000000000 : ℝ)^37 ≤ (8149318232651/12500000000000 : ℝ)^29 := by
    have hnat : (7151247383 : ℕ)^37*12500000000000^29 ≤ 8149318232651^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7151247383 10000000000 8149318232651 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-959939779/5000000000 : ℝ), (195012373/625000000 : ℝ), (-7151247383/10000000000 : ℝ)] ![(3044363256249/25000000000000 : ℝ), (11314000544741/50000000000000 : ℝ), (8149318232651/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-959939779/5000000000 : ℝ)|^37 ≤ (3044363256249/25000000000000 : ℝ)^29
        have hw : |(-959939779/5000000000 : ℝ)|=(959939779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(195012373/625000000 : ℝ)|^37 ≤ (11314000544741/50000000000000 : ℝ)^29
        have hw : |(195012373/625000000 : ℝ)|=(195012373/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7151247383/10000000000 : ℝ)|^37 ≤ (8149318232651/12500000000000 : ℝ)^29
        have hw : |(-7151247383/10000000000 : ℝ)|=(7151247383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313060_s1_s1_8 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3547161219/10000000000 : ℝ)*x 0 + (-141018099/1000000000 : ℝ)*x 1 + (-1786521113/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3547161219/10000000000 : ℝ)^37 ≤ (26650793798691/100000000000000 : ℝ)^29 := by
    have hnat : (3547161219 : ℕ)^37*100000000000000^29 ≤ 26650793798691^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3547161219 10000000000 26650793798691 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (141018099/1000000000 : ℝ)^37 ≤ (2053676654129/25000000000000 : ℝ)^29 := by
    have hnat : (141018099 : ℕ)^37*25000000000000^29 ≤ 2053676654129^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141018099 1000000000 2053676654129 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1786521113/2500000000 : ℝ)^37 ≤ (65134499561097/100000000000000 : ℝ)^29 := by
    have hnat : (1786521113 : ℕ)^37*100000000000000^29 ≤ 65134499561097^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1786521113 2500000000 65134499561097 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3547161219/10000000000 : ℝ), (-141018099/1000000000 : ℝ), (-1786521113/2500000000 : ℝ)] ![(26650793798691/100000000000000 : ℝ), (2053676654129/25000000000000 : ℝ), (65134499561097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3547161219/10000000000 : ℝ)|^37 ≤ (26650793798691/100000000000000 : ℝ)^29
        have hw : |(3547161219/10000000000 : ℝ)|=(3547161219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-141018099/1000000000 : ℝ)|^37 ≤ (2053676654129/25000000000000 : ℝ)^29
        have hw : |(-141018099/1000000000 : ℝ)|=(141018099/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1786521113/2500000000 : ℝ)|^37 ≤ (65134499561097/100000000000000 : ℝ)^29
        have hw : |(-1786521113/2500000000 : ℝ)|=(1786521113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313060_s1_s1_9 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (117694561/312500000 : ℝ)*x 0 + (1769894819/2500000000 : ℝ)*x 1 + (1225753391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (117694561/312500000 : ℝ)^37 ≤ (28768354777091/100000000000000 : ℝ)^29 := by
    have hnat : (117694561 : ℕ)^37*100000000000000^29 ≤ 28768354777091^29*312500000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117694561 312500000 28768354777091 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1769894819/2500000000 : ℝ)^37 ≤ (64362098241623/100000000000000 : ℝ)^29 := by
    have hnat : (1769894819 : ℕ)^37*100000000000000^29 ≤ 64362098241623^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1769894819 2500000000 64362098241623 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1225753391/10000000000 : ℝ)^37 ≤ (85869337141/1250000000000 : ℝ)^29 := by
    have hnat : (1225753391 : ℕ)^37*1250000000000^29 ≤ 85869337141^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1225753391 10000000000 85869337141 1250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(117694561/312500000 : ℝ), (1769894819/2500000000 : ℝ), (1225753391/10000000000 : ℝ)] ![(28768354777091/100000000000000 : ℝ), (64362098241623/100000000000000 : ℝ), (85869337141/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(117694561/312500000 : ℝ)|^37 ≤ (28768354777091/100000000000000 : ℝ)^29
        have hw : |(117694561/312500000 : ℝ)|=(117694561/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1769894819/2500000000 : ℝ)|^37 ≤ (64362098241623/100000000000000 : ℝ)^29
        have hw : |(1769894819/2500000000 : ℝ)|=(1769894819/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1225753391/10000000000 : ℝ)|^37 ≤ (85869337141/1250000000000 : ℝ)^29
        have hw : |(1225753391/10000000000 : ℝ)|=(1225753391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313060_s1_s1_13 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1317455831/2500000000 : ℝ)*x 0 + (6333094951/10000000000 : ℝ)*x 1 + (-859147/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1317455831/2500000000 : ℝ)^37 ≤ (44162142984097/100000000000000 : ℝ)^29 := by
    have hnat : (1317455831 : ℕ)^37*100000000000000^29 ≤ 44162142984097^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317455831 2500000000 44162142984097 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6333094951/10000000000 : ℝ)^37 ≤ (2233311847623/4000000000000 : ℝ)^29 := by
    have hnat : (6333094951 : ℕ)^37*4000000000000^29 ≤ 2233311847623^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6333094951 10000000000 2233311847623 4000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (859147/2000000000 : ℝ)^37 ≤ (5060812369/100000000000000 : ℝ)^29 := by
    have hnat : (859147 : ℕ)^37*100000000000000^29 ≤ 5060812369^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859147 2000000000 5060812369 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1317455831/2500000000 : ℝ), (6333094951/10000000000 : ℝ), (-859147/2000000000 : ℝ)] ![(44162142984097/100000000000000 : ℝ), (2233311847623/4000000000000 : ℝ), (5060812369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1317455831/2500000000 : ℝ)|^37 ≤ (44162142984097/100000000000000 : ℝ)^29
        have hw : |(1317455831/2500000000 : ℝ)|=(1317455831/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6333094951/10000000000 : ℝ)|^37 ≤ (2233311847623/4000000000000 : ℝ)^29
        have hw : |(6333094951/10000000000 : ℝ)|=(6333094951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-859147/2000000000 : ℝ)|^37 ≤ (5060812369/100000000000000 : ℝ)^29
        have hw : |(-859147/2000000000 : ℝ)|=(859147/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313060_s1_s1_14 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-153198019/1250000000 : ℝ)*x 0 + (1688043593/5000000000 : ℝ)*x 1 + (-925085883/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (153198019/1250000000 : ℝ)^37 ≤ (3434168436143/50000000000000 : ℝ)^29 := by
    have hnat : (153198019 : ℕ)^37*50000000000000^29 ≤ 3434168436143^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153198019 1250000000 3434168436143 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1688043593/5000000000 : ℝ)^37 ≤ (500438673223/2000000000000 : ℝ)^29 := by
    have hnat : (1688043593 : ℕ)^37*2000000000000^29 ≤ 500438673223^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1688043593 5000000000 500438673223 2000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (925085883/1250000000 : ℝ)^37 ≤ (68109729460189/100000000000000 : ℝ)^29 := by
    have hnat : (925085883 : ℕ)^37*100000000000000^29 ≤ 68109729460189^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      925085883 1250000000 68109729460189 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-153198019/1250000000 : ℝ), (1688043593/5000000000 : ℝ), (-925085883/1250000000 : ℝ)] ![(3434168436143/50000000000000 : ℝ), (500438673223/2000000000000 : ℝ), (68109729460189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-153198019/1250000000 : ℝ)|^37 ≤ (3434168436143/50000000000000 : ℝ)^29
        have hw : |(-153198019/1250000000 : ℝ)|=(153198019/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1688043593/5000000000 : ℝ)|^37 ≤ (500438673223/2000000000000 : ℝ)^29
        have hw : |(1688043593/5000000000 : ℝ)|=(1688043593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-925085883/1250000000 : ℝ)|^37 ≤ (68109729460189/100000000000000 : ℝ)^29
        have hw : |(-925085883/1250000000 : ℝ)|=(925085883/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313060_s1_s1_15 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (287194981/1000000000 : ℝ)*x 0 + (-1847690051/10000000000 : ℝ)*x 1 + (-3697669543/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (287194981/1000000000 : ℝ)^37 ≤ (5089186873239/25000000000000 : ℝ)^29 := by
    have hnat : (287194981 : ℕ)^37*25000000000000^29 ≤ 5089186873239^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287194981 1000000000 5089186873239 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1847690051/10000000000 : ℝ)^37 ≤ (11596312549181/100000000000000 : ℝ)^29 := by
    have hnat : (1847690051 : ℕ)^37*100000000000000^29 ≤ 11596312549181^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1847690051 10000000000 11596312549181 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3697669543/5000000000 : ℝ)^37 ≤ (17011734985321/25000000000000 : ℝ)^29 := by
    have hnat : (3697669543 : ℕ)^37*25000000000000^29 ≤ 17011734985321^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3697669543 5000000000 17011734985321 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(287194981/1000000000 : ℝ), (-1847690051/10000000000 : ℝ), (-3697669543/5000000000 : ℝ)] ![(5089186873239/25000000000000 : ℝ), (11596312549181/100000000000000 : ℝ), (17011734985321/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(287194981/1000000000 : ℝ)|^37 ≤ (5089186873239/25000000000000 : ℝ)^29
        have hw : |(287194981/1000000000 : ℝ)|=(287194981/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1847690051/10000000000 : ℝ)|^37 ≤ (11596312549181/100000000000000 : ℝ)^29
        have hw : |(-1847690051/10000000000 : ℝ)|=(1847690051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3697669543/5000000000 : ℝ)|^37 ≤ (17011734985321/25000000000000 : ℝ)^29
        have hw : |(-3697669543/5000000000 : ℝ)|=(3697669543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313060_s1_s1_16 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6238079309/10000000000 : ℝ)*x 0 + (146320633/312500000 : ℝ)*x 1 + (51170537/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6238079309/10000000000 : ℝ)^37 ≤ (54766275521407/100000000000000 : ℝ)^29 := by
    have hnat : (6238079309 : ℕ)^37*100000000000000^29 ≤ 54766275521407^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6238079309 10000000000 54766275521407 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (146320633/312500000 : ℝ)^37 ≤ (37979280738523/100000000000000 : ℝ)^29 := by
    have hnat : (146320633 : ℕ)^37*100000000000000^29 ≤ 37979280738523^29*312500000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      146320633 312500000 37979280738523 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51170537/400000000 : ℝ)^37 ≤ (7254443733701/100000000000000 : ℝ)^29 := by
    have hnat : (51170537 : ℕ)^37*100000000000000^29 ≤ 7254443733701^29*400000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51170537 400000000 7254443733701 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6238079309/10000000000 : ℝ), (146320633/312500000 : ℝ), (51170537/400000000 : ℝ)] ![(54766275521407/100000000000000 : ℝ), (37979280738523/100000000000000 : ℝ), (7254443733701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6238079309/10000000000 : ℝ)|^37 ≤ (54766275521407/100000000000000 : ℝ)^29
        have hw : |(6238079309/10000000000 : ℝ)|=(6238079309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(146320633/312500000 : ℝ)|^37 ≤ (37979280738523/100000000000000 : ℝ)^29
        have hw : |(146320633/312500000 : ℝ)|=(146320633/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(51170537/400000000 : ℝ)|^37 ≤ (7254443733701/100000000000000 : ℝ)^29
        have hw : |(51170537/400000000 : ℝ)|=(51170537/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313060_s1_s1_20 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2048380031/2500000000 : ℝ)*x 0 + (774354043/2500000000 : ℝ)*x 1 + (-8500149/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2048380031/2500000000 : ℝ)^37 ≤ (77553307546779/100000000000000 : ℝ)^29 := by
    have hnat : (2048380031 : ℕ)^37*100000000000000^29 ≤ 77553307546779^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2048380031 2500000000 77553307546779 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (774354043/2500000000 : ℝ)^37 ≤ (22417420974479/100000000000000 : ℝ)^29 := by
    have hnat : (774354043 : ℕ)^37*100000000000000^29 ≤ 22417420974479^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      774354043 2500000000 22417420974479 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8500149/5000000000 : ℝ)^37 ≤ (29271470717/100000000000000 : ℝ)^29 := by
    have hnat : (8500149 : ℕ)^37*100000000000000^29 ≤ 29271470717^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8500149 5000000000 29271470717 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2048380031/2500000000 : ℝ), (774354043/2500000000 : ℝ), (-8500149/5000000000 : ℝ)] ![(77553307546779/100000000000000 : ℝ), (22417420974479/100000000000000 : ℝ), (29271470717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2048380031/2500000000 : ℝ)|^37 ≤ (77553307546779/100000000000000 : ℝ)^29
        have hw : |(2048380031/2500000000 : ℝ)|=(2048380031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(774354043/2500000000 : ℝ)|^37 ≤ (22417420974479/100000000000000 : ℝ)^29
        have hw : |(774354043/2500000000 : ℝ)|=(774354043/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8500149/5000000000 : ℝ)|^37 ≤ (29271470717/100000000000000 : ℝ)^29
        have hw : |(-8500149/5000000000 : ℝ)|=(8500149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313060_s1_s1_21 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-353126533/5000000000 : ℝ)*x 0 + (1157238821/2000000000 : ℝ)*x 1 + (-5519070401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (353126533/5000000000 : ℝ)^37 ≤ (3399634014393/100000000000000 : ℝ)^29 := by
    have hnat : (353126533 : ℕ)^37*100000000000000^29 ≤ 3399634014393^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      353126533 5000000000 3399634014393 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1157238821/2000000000 : ℝ)^37 ≤ (12439022349741/25000000000000 : ℝ)^29 := by
    have hnat : (1157238821 : ℕ)^37*25000000000000^29 ≤ 12439022349741^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1157238821 2000000000 12439022349741 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5519070401/10000000000 : ℝ)^37 ≤ (11711069142689/25000000000000 : ℝ)^29 := by
    have hnat : (5519070401 : ℕ)^37*25000000000000^29 ≤ 11711069142689^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5519070401 10000000000 11711069142689 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-353126533/5000000000 : ℝ), (1157238821/2000000000 : ℝ), (-5519070401/10000000000 : ℝ)] ![(3399634014393/100000000000000 : ℝ), (12439022349741/25000000000000 : ℝ), (11711069142689/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-353126533/5000000000 : ℝ)|^37 ≤ (3399634014393/100000000000000 : ℝ)^29
        have hw : |(-353126533/5000000000 : ℝ)|=(353126533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1157238821/2000000000 : ℝ)|^37 ≤ (12439022349741/25000000000000 : ℝ)^29
        have hw : |(1157238821/2000000000 : ℝ)|=(1157238821/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5519070401/10000000000 : ℝ)|^37 ≤ (11711069142689/25000000000000 : ℝ)^29
        have hw : |(-5519070401/10000000000 : ℝ)|=(5519070401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313060_s1_s1_22 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3046500921/5000000000 : ℝ)*x 0 + (-25104473/250000000 : ℝ)*x 1 + (-2510864349/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3046500921/5000000000 : ℝ)^37 ≤ (53146470657531/100000000000000 : ℝ)^29 := by
    have hnat : (3046500921 : ℕ)^37*100000000000000^29 ≤ 53146470657531^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3046500921 5000000000 53146470657531 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (25104473/250000000 : ℝ)^37 ≤ (5326582344237/100000000000000 : ℝ)^29 := by
    have hnat : (25104473 : ℕ)^37*100000000000000^29 ≤ 5326582344237^29*250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25104473 250000000 5326582344237 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2510864349/5000000000 : ℝ)^37 ≤ (41526946990667/100000000000000 : ℝ)^29 := by
    have hnat : (2510864349 : ℕ)^37*100000000000000^29 ≤ 41526946990667^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2510864349 5000000000 41526946990667 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3046500921/5000000000 : ℝ), (-25104473/250000000 : ℝ), (-2510864349/5000000000 : ℝ)] ![(53146470657531/100000000000000 : ℝ), (5326582344237/100000000000000 : ℝ), (41526946990667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3046500921/5000000000 : ℝ)|^37 ≤ (53146470657531/100000000000000 : ℝ)^29
        have hw : |(3046500921/5000000000 : ℝ)|=(3046500921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-25104473/250000000 : ℝ)|^37 ≤ (5326582344237/100000000000000 : ℝ)^29
        have hw : |(-25104473/250000000 : ℝ)|=(25104473/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2510864349/5000000000 : ℝ)|^37 ≤ (41526946990667/100000000000000 : ℝ)^29
        have hw : |(-2510864349/5000000000 : ℝ)|=(2510864349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313060_s1_s1_23 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (863953969/2500000000 : ℝ)*x 0 + (7013416889/10000000000 : ℝ)*x 1 + (862692061/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (863953969/2500000000 : ℝ)^37 ≤ (1611143506697/6250000000000 : ℝ)^29 := by
    have hnat : (863953969 : ℕ)^37*6250000000000^29 ≤ 1611143506697^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863953969 2500000000 1611143506697 6250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7013416889/10000000000 : ℝ)^37 ≤ (15898915433517/25000000000000 : ℝ)^29 := by
    have hnat : (7013416889 : ℕ)^37*25000000000000^29 ≤ 15898915433517^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7013416889 10000000000 15898915433517 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (862692061/5000000000 : ℝ)^37 ≤ (5313021074197/50000000000000 : ℝ)^29 := by
    have hnat : (862692061 : ℕ)^37*50000000000000^29 ≤ 5313021074197^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862692061 5000000000 5313021074197 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(863953969/2500000000 : ℝ), (7013416889/10000000000 : ℝ), (862692061/5000000000 : ℝ)] ![(1611143506697/6250000000000 : ℝ), (15898915433517/25000000000000 : ℝ), (5313021074197/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(863953969/2500000000 : ℝ)|^37 ≤ (1611143506697/6250000000000 : ℝ)^29
        have hw : |(863953969/2500000000 : ℝ)|=(863953969/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7013416889/10000000000 : ℝ)|^37 ≤ (15898915433517/25000000000000 : ℝ)^29
        have hw : |(7013416889/10000000000 : ℝ)|=(7013416889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(862692061/5000000000 : ℝ)|^37 ≤ (5313021074197/50000000000000 : ℝ)^29
        have hw : |(862692061/5000000000 : ℝ)|=(862692061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313060_s1_s1_27 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4361853991/5000000000 : ℝ)*x 0 + (2353437583/10000000000 : ℝ)*x 1 + (-2375221/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4361853991/5000000000 : ℝ)^37 ≤ (10501535884017/12500000000000 : ℝ)^29 := by
    have hnat : (4361853991 : ℕ)^37*12500000000000^29 ≤ 10501535884017^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361853991 5000000000 10501535884017 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2353437583/10000000000 : ℝ)^37 ≤ (1578989664369/10000000000000 : ℝ)^29 := by
    have hnat : (2353437583 : ℕ)^37*10000000000000^29 ≤ 1578989664369^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2353437583 10000000000 1578989664369 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2375221/312500000 : ℝ)^37 ≤ (197816267621/100000000000000 : ℝ)^29 := by
    have hnat : (2375221 : ℕ)^37*100000000000000^29 ≤ 197816267621^29*312500000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2375221 312500000 197816267621 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4361853991/5000000000 : ℝ), (2353437583/10000000000 : ℝ), (-2375221/312500000 : ℝ)] ![(10501535884017/12500000000000 : ℝ), (1578989664369/10000000000000 : ℝ), (197816267621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4361853991/5000000000 : ℝ)|^37 ≤ (10501535884017/12500000000000 : ℝ)^29
        have hw : |(4361853991/5000000000 : ℝ)|=(4361853991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2353437583/10000000000 : ℝ)|^37 ≤ (1578989664369/10000000000000 : ℝ)^29
        have hw : |(2353437583/10000000000 : ℝ)|=(2353437583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2375221/312500000 : ℝ)|^37 ≤ (197816267621/100000000000000 : ℝ)^29
        have hw : |(-2375221/312500000 : ℝ)|=(2375221/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c313060_s1 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((42031/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(42031/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(83733/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(83733/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-37599/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-37599/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((31029/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(31029/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31911/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(31911/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-24613/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-24613/50000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78599/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78599/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (176973/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base18 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).1]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (42031/50000 : ℝ) ^ (73/16 : ℝ) ≤ (45288320538315405761/100000000000000000000 : ℝ) := by
    have hpowers : (42031/50000 : ℝ)^73 ≤ (45288320538315405761/100000000000000000000 : ℝ)^16 := by
      have hnat : (42031 : ℕ)^73*100000000000000000000^16 ≤ 45288320538315405761^16*50000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        42031 50000 45288320538315405761 100000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (42031/50000 : ℝ)) (X := (45288320538315405761/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (145288320538315405761/100000000000000000000 : ℝ) ≤ (10853190211961187/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (145288320538315405761/100000000000000000000 : ℝ)^16 ≤ (10853190211961187/10000000000000000 : ℝ)^73 := by
      have hnat : (145288320538315405761 : ℕ)^16*10000000000000000^73 ≤ 10853190211961187^73*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        145288320538315405761 100000000000000000000 10853190211961187 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10853190211961187/10000000000000000 : ℝ)) (X := (145288320538315405761/100000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (95288320538315405761/50000000000000000000 : ℝ) ≤ (5759106862309153/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (95288320538315405761/50000000000000000000 : ℝ)^16 ≤ (5759106862309153/5000000000000000 : ℝ)^73 := by
      have hnat : (95288320538315405761 : ℕ)^16*5000000000000000^73 ≤ 5759106862309153^73*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        95288320538315405761 50000000000000000000 5759106862309153 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5759106862309153/5000000000000000 : ℝ)) (X := (95288320538315405761/50000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(853190211961187/8406200000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(60456682968829/764200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (42031/50000 : ℝ)) (alpha := (853190211961187/8406200000000000 : ℝ)) (beta := (60456682968829/764200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (42031/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(853190211961187/8406200000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(60456682968829/764200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (83733/100000 : ℝ) ^ (73/16 : ℝ) ≤ (44485243518369129407/100000000000000000000 : ℝ) := by
    have hpowers : (83733/100000 : ℝ)^73 ≤ (44485243518369129407/100000000000000000000 : ℝ)^16 := by
      have hnat : (83733 : ℕ)^73*100000000000000000000^16 ≤ 44485243518369129407^16*100000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        83733 100000 44485243518369129407 100000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (83733/100000 : ℝ)) (X := (44485243518369129407/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (144485243518369129407/100000000000000000000 : ℝ) ≤ (5420006548970549/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (144485243518369129407/100000000000000000000 : ℝ)^16 ≤ (5420006548970549/5000000000000000 : ℝ)^73 := by
      have hnat : (144485243518369129407 : ℕ)^16*5000000000000000^73 ≤ 5420006548970549^73*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        144485243518369129407 100000000000000000000 5420006548970549 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5420006548970549/5000000000000000 : ℝ)) (X := (144485243518369129407/100000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (94485243518369129407/50000000000000000000 : ℝ) ≤ (1437108360696429/1250000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (94485243518369129407/50000000000000000000 : ℝ)^16 ≤ (1437108360696429/1250000000000000 : ℝ)^73 := by
      have hnat : (94485243518369129407 : ℕ)^16*1250000000000000^73 ≤ 1437108360696429^73*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        94485243518369129407 50000000000000000000 1437108360696429 1250000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1437108360696429/1250000000000000 : ℝ)) (X := (94485243518369129407/50000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(140002182990183/1395550000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(328426893815167/4186650000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (83733/100000 : ℝ)) (alpha := (140002182990183/1395550000000000 : ℝ)) (beta := (328426893815167/4186650000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (83733/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(140002182990183/1395550000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(328426893815167/4186650000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (37599/50000 : ℝ) ^ (73/16 : ℝ) ≤ (1089560097043375089/4000000000000000000 : ℝ) := by
    have hpowers : (37599/50000 : ℝ)^73 ≤ (1089560097043375089/4000000000000000000 : ℝ)^16 := by
      have hnat : (37599 : ℕ)^73*4000000000000000000^16 ≤ 1089560097043375089^16*50000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37599 50000 1089560097043375089 4000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (37599/50000 : ℝ)) (X := (1089560097043375089/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (5089560097043375089/4000000000000000000 : ℝ) ≤ (5271090482560467/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (5089560097043375089/4000000000000000000 : ℝ)^16 ≤ (5271090482560467/5000000000000000 : ℝ)^73 := by
      have hnat : (5089560097043375089 : ℕ)^16*5000000000000000^73 ≤ 5271090482560467^73*4000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5089560097043375089 4000000000000000000 5271090482560467 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5271090482560467/5000000000000000 : ℝ)) (X := (5089560097043375089/4000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (3089560097043375089/2000000000000000000 : ℝ) ≤ (5500034767874939/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (3089560097043375089/2000000000000000000 : ℝ)^16 ≤ (5500034767874939/5000000000000000 : ℝ)^73 := by
      have hnat : (3089560097043375089 : ℕ)^16*5000000000000000^73 ≤ 5500034767874939^73*2000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3089560097043375089 2000000000000000000 5500034767874939 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5500034767874939/5000000000000000 : ℝ)) (X := (3089560097043375089/2000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(271090482560467/3759900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(28618035664309/469987500000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (37599/50000 : ℝ)) (alpha := (271090482560467/3759900000000000 : ℝ)) (beta := (28618035664309/469987500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (37599/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(271090482560467/3759900000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(28618035664309/469987500000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-27860563/156250000 : ℝ)*X 0 0+(4321589013/10000000000 : ℝ)*X 0 1+(-6226036763/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313060_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2346719629/5000000000 : ℝ)*X 2 0+(23536891/39062500 : ℝ)*X 2 1+(1581560693/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313060_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-959939779/5000000000 : ℝ)*X 0 0+(195012373/625000000 : ℝ)*X 0 1+(-7151247383/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313060_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((3547161219/10000000000 : ℝ)*X 1 0+(-141018099/1000000000 : ℝ)*X 1 1+(-1786521113/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313060_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((117694561/312500000 : ℝ)*X 2 0+(1769894819/2500000000 : ℝ)*X 2 1+(1225753391/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313060_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((1317455831/2500000000 : ℝ)*X 0 0+(6333094951/10000000000 : ℝ)*X 0 1+(-859147/2000000000 : ℝ)*X 0 2+(1317455831/2500000000 : ℝ)*X 1 0+(6333094951/10000000000 : ℝ)*X 1 1+(-859147/2000000000 : ℝ)*X 1 2+(1317455831/2500000000 : ℝ)*X 2 0+(6333094951/10000000000 : ℝ)*X 2 1+(-859147/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313060_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-153198019/1250000000 : ℝ)*X 0 0+(1688043593/5000000000 : ℝ)*X 0 1+(-925085883/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313060_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((287194981/1000000000 : ℝ)*X 1 0+(-1847690051/10000000000 : ℝ)*X 1 1+(-3697669543/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313060_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((6238079309/10000000000 : ℝ)*X 2 0+(146320633/312500000 : ℝ)*X 2 1+(51170537/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313060_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((2048380031/2500000000 : ℝ)*X 0 0+(774354043/2500000000 : ℝ)*X 0 1+(-8500149/5000000000 : ℝ)*X 0 2+(2048380031/2500000000 : ℝ)*X 1 0+(774354043/2500000000 : ℝ)*X 1 1+(-8500149/5000000000 : ℝ)*X 1 2+(2048380031/2500000000 : ℝ)*X 2 0+(774354043/2500000000 : ℝ)*X 2 1+(-8500149/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313060_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-353126533/5000000000 : ℝ)*X 0 0+(1157238821/2000000000 : ℝ)*X 0 1+(-5519070401/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313060_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((3046500921/5000000000 : ℝ)*X 1 0+(-25104473/250000000 : ℝ)*X 1 1+(-2510864349/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313060_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((863953969/2500000000 : ℝ)*X 2 0+(7013416889/10000000000 : ℝ)*X 2 1+(862692061/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313060_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((4361853991/5000000000 : ℝ)*X 0 0+(2353437583/10000000000 : ℝ)*X 0 1+(-2375221/312500000 : ℝ)*X 0 2+(4361853991/5000000000 : ℝ)*X 1 0+(2353437583/10000000000 : ℝ)*X 1 1+(-2375221/312500000 : ℝ)*X 1 2+(4361853991/5000000000 : ℝ)*X 2 0+(2353437583/10000000000 : ℝ)*X 2 1+(-2375221/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313060_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((31029/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(31029/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2875907321239749203282349/823085192187500000000000000000 : ℝ) := by norm_num
    linear_combination (3278312217/5000000000 : ℝ)*(base7) + (1814347/1000000000000 : ℝ)*(base18) + (2497/31250000000 : ℝ)*(base39) + (20796884417/200000000000 : ℝ)*(base59) + (793881893679/250000000000 : ℝ)*(major_s1_0) + (793881893679/250000000000 : ℝ)*(major_s1_1) + (793881893679/250000000000 : ℝ)*(major_s1_2) + (3580307/500000000000 : ℝ)*(sp_s1_0) + (818124345921/200000000000 : ℝ)*(sp_s1_7) + (1022662008517/250000000000 : ℝ)*(sp_s1_8) + (4090660858253/1000000000000 : ℝ)*(sp_s1_9) + (158079608619/62500000000 : ℝ)*(sp_s1_13) + (15984017/500000000000 : ℝ)*(sp_s1_14) + (5504919/500000000000 : ℝ)*(sp_s1_15) + (234201411813/125000000000 : ℝ)*(f.failure) + (4090660858253/1000000000000 : ℝ)*(f.sum) + (54172797893851493/2186303518750000000000000000000 : ℝ)*base62 + (166331660218879/313325000000000000000000000 : ℝ)*base65 + (563090689634261/1395550000000000000000000000 : ℝ)*base66 + (126789462659171/313325000000000000000000000 : ℝ)*base69 + (3212192898333049567/26338726150000000000000000000000 : ℝ)*base71 + (50396016016489/191050000000000000000000000 : ℝ)*base72 + (155855991524417/348887500000000000000000000 : ℝ)*base75 + (897993653349513/2101550000000000000000000000 : ℝ)*base77 + (76499935272627027/266619827500000000000000000000 : ℝ)*base79 + (69/12500000000000000 : ℝ)*base86 + (69/12500000000000000 : ℝ)*base88 + (69/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31911/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(31911/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (8844144886639685122921299/1066479310000000000000000000000 : ℝ) := by norm_num
    linear_combination (724350656909/1000000000000 : ℝ)*(base7) + (541643/1000000000000 : ℝ)*(base39) + (128118964893/50000000000 : ℝ)*(major_s1_0) + (128118964893/50000000000 : ℝ)*(major_s1_1) + (128118964893/50000000000 : ℝ)*(major_s1_2) + (6848219/1000000000000 : ℝ)*(sp_s1_0) + (10677507/1000000000000 : ℝ)*(sp_s1_2) + (83228231/1000000000000 : ℝ)*(sp_s1_8) + (1592799459791/500000000000 : ℝ)*(sp_s1_14) + (318552675521/100000000000 : ℝ)*(sp_s1_15) + (1592799652967/500000000000 : ℝ)*(sp_s1_16) + (1118093032331/500000000000 : ℝ)*(sp_s1_20) + (105391/25000000000 : ℝ)*(sp_s1_21) + (8744223/1000000000000 : ℝ)*(sp_s1_27) + (188980518997/125000000000 : ℝ)*(f.failure) + (3185609983441/1000000000000 : ℝ)*(f.sum) + (64019609644858249/874521407500000000000000000000 : ℝ)*base63 + (1570314493117/6266500000000000000000000 : ℝ)*base64 + (23075775377059/55822000000000000000000000 : ℝ)*base67 + (1443280863853/5013200000000000000000000 : ℝ)*base68 + (245779140555391/8230851921875000000000000000 : ℝ)*base71 + (28799422628381/38210000000000000000000000 : ℝ)*base73 + (9694072326807/27911000000000000000000000 : ℝ)*base74 + (4437029482629/13134687500000000000000000 : ℝ)*base76 + (42561982863022937/133309913750000000000000000000 : ℝ)*base79 + (5461/12500000000000000 : ℝ)*base86 + (5461/12500000000000000 : ℝ)*base88 + (5461/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-24613/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-24613/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (149516492965183405269993789419/33415462980575000000000000000000000 : ℝ) := by norm_num
    linear_combination (195014455047/500000000000 : ℝ)*(base7) + (422683/125000000000 : ℝ)*(base11) + (133257/1000000000000 : ℝ)*(base34) + (10794530261/62500000000 : ℝ)*(base39) + (1175057/500000000000 : ℝ)*(base43) + (662825908177/250000000000 : ℝ)*(major_s1_0) + (2651301415851/1000000000000 : ℝ)*(major_s1_1) + (530260753193/200000000000 : ℝ)*(major_s1_2) + (7650763/1000000000000 : ℝ)*(sp_s1_0) + (43905151/1000000000000 : ℝ)*(sp_s1_9) + (175409979073/50000000000 : ℝ)*(sp_s1_21) + (3508213097059/1000000000000 : ℝ)*(sp_s1_22) + (1754083420897/500000000000 : ℝ)*(sp_s1_23) + (97716988293/50000000000 : ℝ)*(sp_s1_27) + (1564310989023/1000000000000 : ℝ)*(f.failure) + (3508213097059/1000000000000 : ℝ)*(f.sum) + (18912183679680499321/104942568900000000000000000000000 : ℝ)*base62 + (9242726200349/375990000000000000000000000 : ℝ)*base64 + (282828521552367/697775000000000000000000000 : ℝ)*base67 + (355380369714073/751980000000000000000000000 : ℝ)*base68 + (386058570294176861/79016178450000000000000000000000 : ℝ)*base71 + (141420373568443/191050000000000000000000000 : ℝ)*base73 + (664681464456147/1395550000000000000000000000 : ℝ)*base74 + (1305588048711811/2101550000000000000000000000 : ℝ)*base76 + (256020494504731987/5332396550000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (41201/100000000000000000 : ℝ)*base87 + (41201/100000000000000000 : ℝ)*base89 + (41201/100000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((42031/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(42031/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(83733/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(83733/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-37599/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-37599/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((31029/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(31029/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31911/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(31911/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-24613/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-24613/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c313060_s1 p hpa hpb X hX hprev0

#print axioms solution
