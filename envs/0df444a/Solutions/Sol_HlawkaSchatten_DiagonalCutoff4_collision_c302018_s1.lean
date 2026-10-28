-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c302018_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:15:48.231064+00:00
-- url     : https://prove2.me/submissions/da48b5f7-2111-4279-90c1-de35b33564d5

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
theorem collision_support_c302018_s1_s1_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-5054561857/10000000000 : ℝ)*x 0 + (1718520357/5000000000 : ℝ)*x 1 + (-2229480627/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5054561857/10000000000 : ℝ)^67 ≤ (40805760990887/100000000000000 : ℝ)^51 := by
    have hnat : (5054561857 : ℕ)^67*100000000000000^51 ≤ 40805760990887^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5054561857 10000000000 40805760990887 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1718520357/5000000000 : ℝ)^67 ≤ (384143963509/1562500000000 : ℝ)^51 := by
    have hnat : (1718520357 : ℕ)^67*1562500000000^51 ≤ 384143963509^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1718520357 5000000000 384143963509 1562500000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2229480627/5000000000 : ℝ)^67 ≤ (34609025329083/100000000000000 : ℝ)^51 := by
    have hnat : (2229480627 : ℕ)^67*100000000000000^51 ≤ 34609025329083^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2229480627 5000000000 34609025329083 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5054561857/10000000000 : ℝ), (1718520357/5000000000 : ℝ), (-2229480627/5000000000 : ℝ)] ![(40805760990887/100000000000000 : ℝ), (384143963509/1562500000000 : ℝ), (34609025329083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5054561857/10000000000 : ℝ)|^67 ≤ (40805760990887/100000000000000 : ℝ)^51
        have hw : |(-5054561857/10000000000 : ℝ)|=(5054561857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1718520357/5000000000 : ℝ)|^67 ≤ (384143963509/1562500000000 : ℝ)^51
        have hw : |(1718520357/5000000000 : ℝ)|=(1718520357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2229480627/5000000000 : ℝ)|^67 ≤ (34609025329083/100000000000000 : ℝ)^51
        have hw : |(-2229480627/5000000000 : ℝ)|=(2229480627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302018_s1_s1_1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4906306947/10000000000 : ℝ)*x 0 + (-2881398259/10000000000 : ℝ)*x 1 + (-2548566529/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4906306947/10000000000 : ℝ)^67 ≤ (39240685569269/100000000000000 : ℝ)^51 := by
    have hnat : (4906306947 : ℕ)^67*100000000000000^51 ≤ 39240685569269^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4906306947 10000000000 39240685569269 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2881398259/10000000000 : ℝ)^67 ≤ (9750728651743/50000000000000 : ℝ)^51 := by
    have hnat : (2881398259 : ℕ)^67*50000000000000^51 ≤ 9750728651743^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2881398259 10000000000 9750728651743 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2548566529/5000000000 : ℝ)^67 ≤ (41257857115497/100000000000000 : ℝ)^51 := by
    have hnat : (2548566529 : ℕ)^67*100000000000000^51 ≤ 41257857115497^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2548566529 5000000000 41257857115497 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4906306947/10000000000 : ℝ), (-2881398259/10000000000 : ℝ), (-2548566529/5000000000 : ℝ)] ![(39240685569269/100000000000000 : ℝ), (9750728651743/50000000000000 : ℝ), (41257857115497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4906306947/10000000000 : ℝ)|^67 ≤ (39240685569269/100000000000000 : ℝ)^51
        have hw : |(4906306947/10000000000 : ℝ)|=(4906306947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2881398259/10000000000 : ℝ)|^67 ≤ (9750728651743/50000000000000 : ℝ)^51
        have hw : |(-2881398259/10000000000 : ℝ)|=(2881398259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2548566529/5000000000 : ℝ)|^67 ≤ (41257857115497/100000000000000 : ℝ)^51
        have hw : |(-2548566529/5000000000 : ℝ)|=(2548566529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302018_s1_s1_7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2574194671/5000000000 : ℝ)*x 0 + (2953652603/10000000000 : ℝ)*x 1 + (-4792553823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2574194671/5000000000 : ℝ)^67 ≤ (20901879999861/50000000000000 : ℝ)^51 := by
    have hnat : (2574194671 : ℕ)^67*50000000000000^51 ≤ 20901879999861^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2574194671 5000000000 20901879999861 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2953652603/10000000000 : ℝ)^67 ≤ (20146409696191/100000000000000 : ℝ)^51 := by
    have hnat : (2953652603 : ℕ)^67*100000000000000^51 ≤ 20146409696191^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2953652603 10000000000 20146409696191 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4792553823/10000000000 : ℝ)^67 ≤ (38049830292741/100000000000000 : ℝ)^51 := by
    have hnat : (4792553823 : ℕ)^67*100000000000000^51 ≤ 38049830292741^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4792553823 10000000000 38049830292741 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2574194671/5000000000 : ℝ), (2953652603/10000000000 : ℝ), (-4792553823/10000000000 : ℝ)] ![(20901879999861/50000000000000 : ℝ), (20146409696191/100000000000000 : ℝ), (38049830292741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2574194671/5000000000 : ℝ)|^67 ≤ (20901879999861/50000000000000 : ℝ)^51
        have hw : |(-2574194671/5000000000 : ℝ)|=(2574194671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2953652603/10000000000 : ℝ)|^67 ≤ (20146409696191/100000000000000 : ℝ)^51
        have hw : |(2953652603/10000000000 : ℝ)|=(2953652603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4792553823/10000000000 : ℝ)|^67 ≤ (38049830292741/100000000000000 : ℝ)^51
        have hw : |(-4792553823/10000000000 : ℝ)|=(4792553823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302018_s1_s1_8 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4828113953/10000000000 : ℝ)*x 0 + (-2020066503/10000000000 : ℝ)*x 1 + (-1460365239/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4828113953/10000000000 : ℝ)^67 ≤ (9605289641793/25000000000000 : ℝ)^51 := by
    have hnat : (4828113953 : ℕ)^67*25000000000000^51 ≤ 9605289641793^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4828113953 10000000000 9605289641793 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2020066503/10000000000 : ℝ)^67 ≤ (12230414350087/100000000000000 : ℝ)^51 := by
    have hnat : (2020066503 : ℕ)^67*100000000000000^51 ≤ 12230414350087^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2020066503 10000000000 12230414350087 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1460365239/2500000000 : ℝ)^67 ≤ (394787416569/800000000000 : ℝ)^51 := by
    have hnat : (1460365239 : ℕ)^67*800000000000^51 ≤ 394787416569^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1460365239 2500000000 394787416569 800000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4828113953/10000000000 : ℝ), (-2020066503/10000000000 : ℝ), (-1460365239/2500000000 : ℝ)] ![(9605289641793/25000000000000 : ℝ), (12230414350087/100000000000000 : ℝ), (394787416569/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4828113953/10000000000 : ℝ)|^67 ≤ (9605289641793/25000000000000 : ℝ)^51
        have hw : |(4828113953/10000000000 : ℝ)|=(4828113953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2020066503/10000000000 : ℝ)|^67 ≤ (12230414350087/100000000000000 : ℝ)^51
        have hw : |(-2020066503/10000000000 : ℝ)|=(2020066503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1460365239/2500000000 : ℝ)|^67 ≤ (394787416569/800000000000 : ℝ)^51
        have hw : |(-1460365239/2500000000 : ℝ)|=(1460365239/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302018_s1_s1_9 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3858114889/10000000000 : ℝ)*x 0 + (5497644421/10000000000 : ℝ)*x 1 + (3567199447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3858114889/10000000000 : ℝ)^67 ≤ (5723220717661/20000000000000 : ℝ)^51 := by
    have hnat : (3858114889 : ℕ)^67*20000000000000^51 ≤ 5723220717661^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3858114889 10000000000 5723220717661 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5497644421/10000000000 : ℝ)^67 ≤ (2278418207069/5000000000000 : ℝ)^51 := by
    have hnat : (5497644421 : ℕ)^67*5000000000000^51 ≤ 2278418207069^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5497644421 10000000000 2278418207069 5000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3567199447/10000000000 : ℝ)^67 ≤ (25815532256873/100000000000000 : ℝ)^51 := by
    have hnat : (3567199447 : ℕ)^67*100000000000000^51 ≤ 25815532256873^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3567199447 10000000000 25815532256873 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3858114889/10000000000 : ℝ), (5497644421/10000000000 : ℝ), (3567199447/10000000000 : ℝ)] ![(5723220717661/20000000000000 : ℝ), (2278418207069/5000000000000 : ℝ), (25815532256873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3858114889/10000000000 : ℝ)|^67 ≤ (5723220717661/20000000000000 : ℝ)^51
        have hw : |(3858114889/10000000000 : ℝ)|=(3858114889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5497644421/10000000000 : ℝ)|^67 ≤ (2278418207069/5000000000000 : ℝ)^51
        have hw : |(5497644421/10000000000 : ℝ)|=(5497644421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3567199447/10000000000 : ℝ)|^67 ≤ (25815532256873/100000000000000 : ℝ)^51
        have hw : |(3567199447/10000000000 : ℝ)|=(3567199447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302018_s1_s1_13 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (310158787/5000000000 : ℝ)*x 0 + (2266273369/2500000000 : ℝ)*x 1 + (-833656991/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (310158787/5000000000 : ℝ)^67 ≤ (518628457193/20000000000000 : ℝ)^51 := by
    have hnat : (310158787 : ℕ)^67*20000000000000^51 ≤ 518628457193^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      310158787 5000000000 518628457193 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2266273369/2500000000 : ℝ)^67 ≤ (17580405261929/20000000000000 : ℝ)^51 := by
    have hnat : (2266273369 : ℕ)^67*20000000000000^51 ≤ 17580405261929^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2266273369 2500000000 17580405261929 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (833656991/5000000000 : ℝ)^67 ≤ (4752415694987/50000000000000 : ℝ)^51 := by
    have hnat : (833656991 : ℕ)^67*50000000000000^51 ≤ 4752415694987^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833656991 5000000000 4752415694987 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(310158787/5000000000 : ℝ), (2266273369/2500000000 : ℝ), (-833656991/5000000000 : ℝ)] ![(518628457193/20000000000000 : ℝ), (17580405261929/20000000000000 : ℝ), (4752415694987/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(310158787/5000000000 : ℝ)|^67 ≤ (518628457193/20000000000000 : ℝ)^51
        have hw : |(310158787/5000000000 : ℝ)|=(310158787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2266273369/2500000000 : ℝ)|^67 ≤ (17580405261929/20000000000000 : ℝ)^51
        have hw : |(2266273369/2500000000 : ℝ)|=(2266273369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-833656991/5000000000 : ℝ)|^67 ≤ (4752415694987/50000000000000 : ℝ)^51
        have hw : |(-833656991/5000000000 : ℝ)|=(833656991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302018_s1_s1_14 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-19932567/39062500 : ℝ)*x 0 + (3376520917/10000000000 : ℝ)*x 1 + (-558049593/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (19932567/39062500 : ℝ)^67 ≤ (41317459771019/100000000000000 : ℝ)^51 := by
    have hnat : (19932567 : ℕ)^67*100000000000000^51 ≤ 41317459771019^51*39062500^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19932567 39062500 41317459771019 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3376520917/10000000000 : ℝ)^67 ≤ (24018080150203/100000000000000 : ℝ)^51 := by
    have hnat : (3376520917 : ℕ)^67*100000000000000^51 ≤ 24018080150203^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3376520917 10000000000 24018080150203 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (558049593/1250000000 : ℝ)^67 ≤ (34664460068569/100000000000000 : ℝ)^51 := by
    have hnat : (558049593 : ℕ)^67*100000000000000^51 ≤ 34664460068569^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      558049593 1250000000 34664460068569 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-19932567/39062500 : ℝ), (3376520917/10000000000 : ℝ), (-558049593/1250000000 : ℝ)] ![(41317459771019/100000000000000 : ℝ), (24018080150203/100000000000000 : ℝ), (34664460068569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-19932567/39062500 : ℝ)|^67 ≤ (41317459771019/100000000000000 : ℝ)^51
        have hw : |(-19932567/39062500 : ℝ)|=(19932567/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3376520917/10000000000 : ℝ)|^67 ≤ (24018080150203/100000000000000 : ℝ)^51
        have hw : |(3376520917/10000000000 : ℝ)|=(3376520917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-558049593/1250000000 : ℝ)|^67 ≤ (34664460068569/100000000000000 : ℝ)^51
        have hw : |(-558049593/1250000000 : ℝ)|=(558049593/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302018_s1_s1_15 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1296673007/2500000000 : ℝ)*x 0 + (-2416664011/10000000000 : ℝ)*x 1 + (-2597850181/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1296673007/2500000000 : ℝ)^67 ≤ (21106408342683/50000000000000 : ℝ)^51 := by
    have hnat : (1296673007 : ℕ)^67*50000000000000^51 ≤ 21106408342683^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296673007 2500000000 21106408342683 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2416664011/10000000000 : ℝ)^67 ≤ (7739011684187/50000000000000 : ℝ)^51 := by
    have hnat : (2416664011 : ℕ)^67*50000000000000^51 ≤ 7739011684187^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2416664011 10000000000 7739011684187 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2597850181/5000000000 : ℝ)^67 ≤ (10577289980587/25000000000000 : ℝ)^51 := by
    have hnat : (2597850181 : ℕ)^67*25000000000000^51 ≤ 10577289980587^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597850181 5000000000 10577289980587 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1296673007/2500000000 : ℝ), (-2416664011/10000000000 : ℝ), (-2597850181/5000000000 : ℝ)] ![(21106408342683/50000000000000 : ℝ), (7739011684187/50000000000000 : ℝ), (10577289980587/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1296673007/2500000000 : ℝ)|^67 ≤ (21106408342683/50000000000000 : ℝ)^51
        have hw : |(1296673007/2500000000 : ℝ)|=(1296673007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2416664011/10000000000 : ℝ)|^67 ≤ (7739011684187/50000000000000 : ℝ)^51
        have hw : |(-2416664011/10000000000 : ℝ)|=(2416664011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2597850181/5000000000 : ℝ)|^67 ≤ (10577289980587/25000000000000 : ℝ)^51
        have hw : |(-2597850181/5000000000 : ℝ)|=(2597850181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302018_s1_s1_16 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4232423309/10000000000 : ℝ)*x 0 + (1049871503/2000000000 : ℝ)*x 1 + (3459681219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4232423309/10000000000 : ℝ)^67 ≤ (807942749117/2500000000000 : ℝ)^51 := by
    have hnat : (4232423309 : ℕ)^67*2500000000000^51 ≤ 807942749117^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232423309 10000000000 807942749117 2500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049871503/2000000000 : ℝ)^67 ≤ (8576820341739/20000000000000 : ℝ)^51 := by
    have hnat : (1049871503 : ℕ)^67*20000000000000^51 ≤ 8576820341739^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049871503 2000000000 8576820341739 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3459681219/10000000000 : ℝ)^67 ≤ (4959637660871/20000000000000 : ℝ)^51 := by
    have hnat : (3459681219 : ℕ)^67*20000000000000^51 ≤ 4959637660871^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3459681219 10000000000 4959637660871 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4232423309/10000000000 : ℝ), (1049871503/2000000000 : ℝ), (3459681219/10000000000 : ℝ)] ![(807942749117/2500000000000 : ℝ), (8576820341739/20000000000000 : ℝ), (4959637660871/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4232423309/10000000000 : ℝ)|^67 ≤ (807942749117/2500000000000 : ℝ)^51
        have hw : |(4232423309/10000000000 : ℝ)|=(4232423309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049871503/2000000000 : ℝ)|^67 ≤ (8576820341739/20000000000000 : ℝ)^51
        have hw : |(1049871503/2000000000 : ℝ)|=(1049871503/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3459681219/10000000000 : ℝ)|^67 ≤ (4959637660871/20000000000000 : ℝ)^51
        have hw : |(3459681219/10000000000 : ℝ)|=(3459681219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302018_s1_s1_20 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2708677/500000000 : ℝ)*x 0 + (7888999133/10000000000 : ℝ)*x 1 + (-146228107/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2708677/500000000 : ℝ)^67 ≤ (52697316887/50000000000000 : ℝ)^51 := by
    have hnat : (2708677 : ℕ)^67*50000000000000^51 ≤ 52697316887^51*500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708677 500000000 52697316887 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7888999133/10000000000 : ℝ)^67 ≤ (73234387901247/100000000000000 : ℝ)^51 := by
    have hnat : (7888999133 : ℕ)^67*100000000000000^51 ≤ 73234387901247^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7888999133 10000000000 73234387901247 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (146228107/400000000 : ℝ)^67 ≤ (5332043490681/20000000000000 : ℝ)^51 := by
    have hnat : (146228107 : ℕ)^67*20000000000000^51 ≤ 5332043490681^51*400000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      146228107 400000000 5332043490681 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2708677/500000000 : ℝ), (7888999133/10000000000 : ℝ), (-146228107/400000000 : ℝ)] ![(52697316887/50000000000000 : ℝ), (73234387901247/100000000000000 : ℝ), (5332043490681/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2708677/500000000 : ℝ)|^67 ≤ (52697316887/50000000000000 : ℝ)^51
        have hw : |(2708677/500000000 : ℝ)|=(2708677/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7888999133/10000000000 : ℝ)|^67 ≤ (73234387901247/100000000000000 : ℝ)^51
        have hw : |(7888999133/10000000000 : ℝ)|=(7888999133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-146228107/400000000 : ℝ)|^67 ≤ (5332043490681/20000000000000 : ℝ)^51
        have hw : |(-146228107/400000000 : ℝ)|=(146228107/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302018_s1_s1_21 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-633387281/1250000000 : ℝ)*x 0 + (3661043429/10000000000 : ℝ)*x 1 + (-1058906273/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (633387281/1250000000 : ℝ)^67 ≤ (20469385443813/50000000000000 : ℝ)^51 := by
    have hnat : (633387281 : ℕ)^67*50000000000000^51 ≤ 20469385443813^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      633387281 1250000000 20469385443813 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3661043429/10000000000 : ℝ)^67 ≤ (6677849340417/25000000000000 : ℝ)^51 := by
    have hnat : (3661043429 : ℕ)^67*25000000000000^51 ≤ 6677849340417^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3661043429 10000000000 6677849340417 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1058906273/2500000000 : ℝ)^67 ≤ (32349831738971/100000000000000 : ℝ)^51 := by
    have hnat : (1058906273 : ℕ)^67*100000000000000^51 ≤ 32349831738971^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058906273 2500000000 32349831738971 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-633387281/1250000000 : ℝ), (3661043429/10000000000 : ℝ), (-1058906273/2500000000 : ℝ)] ![(20469385443813/50000000000000 : ℝ), (6677849340417/25000000000000 : ℝ), (32349831738971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-633387281/1250000000 : ℝ)|^67 ≤ (20469385443813/50000000000000 : ℝ)^51
        have hw : |(-633387281/1250000000 : ℝ)|=(633387281/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3661043429/10000000000 : ℝ)|^67 ≤ (6677849340417/25000000000000 : ℝ)^51
        have hw : |(3661043429/10000000000 : ℝ)|=(3661043429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1058906273/2500000000 : ℝ)|^67 ≤ (32349831738971/100000000000000 : ℝ)^51
        have hw : |(-1058906273/2500000000 : ℝ)|=(1058906273/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302018_s1_s1_22 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5054637989/10000000000 : ℝ)*x 0 + (-655319331/2500000000 : ℝ)*x 1 + (-2582046291/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5054637989/10000000000 : ℝ)^67 ≤ (40806568431997/100000000000000 : ℝ)^51 := by
    have hnat : (5054637989 : ℕ)^67*100000000000000^51 ≤ 40806568431997^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5054637989 10000000000 40806568431997 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655319331/2500000000 : ℝ)^67 ≤ (17222082574001/100000000000000 : ℝ)^51 := by
    have hnat : (655319331 : ℕ)^67*100000000000000^51 ≤ 17222082574001^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655319331 2500000000 17222082574001 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2582046291/5000000000 : ℝ)^67 ≤ (10492837244413/25000000000000 : ℝ)^51 := by
    have hnat : (2582046291 : ℕ)^67*25000000000000^51 ≤ 10492837244413^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2582046291 5000000000 10492837244413 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5054637989/10000000000 : ℝ), (-655319331/2500000000 : ℝ), (-2582046291/5000000000 : ℝ)] ![(40806568431997/100000000000000 : ℝ), (17222082574001/100000000000000 : ℝ), (10492837244413/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5054637989/10000000000 : ℝ)|^67 ≤ (40806568431997/100000000000000 : ℝ)^51
        have hw : |(5054637989/10000000000 : ℝ)|=(5054637989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-655319331/2500000000 : ℝ)|^67 ≤ (17222082574001/100000000000000 : ℝ)^51
        have hw : |(-655319331/2500000000 : ℝ)|=(655319331/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2582046291/5000000000 : ℝ)|^67 ≤ (10492837244413/25000000000000 : ℝ)^51
        have hw : |(-2582046291/5000000000 : ℝ)|=(2582046291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302018_s1_s1_23 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4793683229/10000000000 : ℝ)*x 0 + (4452873027/10000000000 : ℝ)*x 1 + (746355393/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4793683229/10000000000 : ℝ)^67 ≤ (594712665573/1562500000000 : ℝ)^51 := by
    have hnat : (4793683229 : ℕ)^67*1562500000000^51 ≤ 594712665573^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4793683229 10000000000 594712665573 1562500000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4452873027/10000000000 : ℝ)^67 ≤ (34546958711611/100000000000000 : ℝ)^51 := by
    have hnat : (4452873027 : ℕ)^67*100000000000000^51 ≤ 34546958711611^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4452873027 10000000000 34546958711611 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (746355393/2000000000 : ℝ)^67 ≤ (6847857668549/25000000000000 : ℝ)^51 := by
    have hnat : (746355393 : ℕ)^67*25000000000000^51 ≤ 6847857668549^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      746355393 2000000000 6847857668549 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4793683229/10000000000 : ℝ), (4452873027/10000000000 : ℝ), (746355393/2000000000 : ℝ)] ![(594712665573/1562500000000 : ℝ), (34546958711611/100000000000000 : ℝ), (6847857668549/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4793683229/10000000000 : ℝ)|^67 ≤ (594712665573/1562500000000 : ℝ)^51
        have hw : |(4793683229/10000000000 : ℝ)|=(4793683229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4452873027/10000000000 : ℝ)|^67 ≤ (34546958711611/100000000000000 : ℝ)^51
        have hw : |(4452873027/10000000000 : ℝ)|=(4452873027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(746355393/2000000000 : ℝ)|^67 ≤ (6847857668549/25000000000000 : ℝ)^51
        have hw : |(746355393/2000000000 : ℝ)|=(746355393/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302018_s1_s1_27 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (56808061/10000000000 : ℝ)*x 0 + (4369180521/5000000000 : ℝ)*x 1 + (-2493093501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (56808061/10000000000 : ℝ)^67 ≤ (112178888293/100000000000000 : ℝ)^51 := by
    have hnat : (56808061 : ℕ)^67*100000000000000^51 ≤ 112178888293^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56808061 10000000000 112178888293 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4369180521/5000000000 : ℝ)^67 ≤ (16752710101173/20000000000000 : ℝ)^51 := by
    have hnat : (4369180521 : ℕ)^67*20000000000000^51 ≤ 16752710101173^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369180521 5000000000 16752710101173 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2493093501/10000000000 : ℝ)^67 ≤ (16124270590421/100000000000000 : ℝ)^51 := by
    have hnat : (2493093501 : ℕ)^67*100000000000000^51 ≤ 16124270590421^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2493093501 10000000000 16124270590421 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(56808061/10000000000 : ℝ), (4369180521/5000000000 : ℝ), (-2493093501/10000000000 : ℝ)] ![(112178888293/100000000000000 : ℝ), (16752710101173/20000000000000 : ℝ), (16124270590421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(56808061/10000000000 : ℝ)|^67 ≤ (112178888293/100000000000000 : ℝ)^51
        have hw : |(56808061/10000000000 : ℝ)|=(56808061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4369180521/5000000000 : ℝ)|^67 ≤ (16752710101173/20000000000000 : ℝ)^51
        have hw : |(4369180521/5000000000 : ℝ)|=(4369180521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2493093501/10000000000 : ℝ)|^67 ≤ (16124270590421/100000000000000 : ℝ)^51
        have hw : |(-2493093501/10000000000 : ℝ)|=(2493093501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c302018_s1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((92319/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(92319/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(34309/50000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(34309/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-5669/6250 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-5669/6250 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((4051/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4051/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(20689/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(20689/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-4077/12500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-4077/12500 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4769/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4769/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base60 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s1_pow0 : (92319/100000 : ℝ) ^ (65/16 : ℝ) ≤ (72276158139035340173/100000000000000000000 : ℝ) := by
    have hpowers : (92319/100000 : ℝ)^65 ≤ (72276158139035340173/100000000000000000000 : ℝ)^16 := by
      have hnat : (92319 : ℕ)^65*100000000000000000000^16 ≤ 72276158139035340173^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        92319 100000 72276158139035340173 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (92319/100000 : ℝ)) (X := (72276158139035340173/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (172276158139035340173/100000000000000000000 : ℝ) ≤ (5716335898335707/5000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (172276158139035340173/100000000000000000000 : ℝ)^16 ≤ (5716335898335707/5000000000000000 : ℝ)^65 := by
      have hnat : (172276158139035340173 : ℕ)^16*5000000000000000^65 ≤ 5716335898335707^65*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        172276158139035340173 100000000000000000000 5716335898335707 5000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5716335898335707/5000000000000000 : ℝ)) (X := (172276158139035340173/100000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (122276158139035340173/50000000000000000000 : ℝ) ≤ (12462328864518837/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (122276158139035340173/50000000000000000000 : ℝ)^16 ≤ (12462328864518837/10000000000000000 : ℝ)^65 := by
      have hnat : (122276158139035340173 : ℕ)^16*10000000000000000^65 ≤ 12462328864518837^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        122276158139035340173 50000000000000000000 12462328864518837 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12462328864518837/10000000000000000 : ℝ)) (X := (122276158139035340173/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(238778632778569/1538650000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1029657067847423/9231900000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (92319/100000 : ℝ)) (alpha := (238778632778569/1538650000000000 : ℝ)) (beta := (1029657067847423/9231900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (92319/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(238778632778569/1538650000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1029657067847423/9231900000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (34309/50000 : ℝ) ^ (65/16 : ℝ) ≤ (5413393653623073343/25000000000000000000 : ℝ) := by
    have hpowers : (34309/50000 : ℝ)^65 ≤ (5413393653623073343/25000000000000000000 : ℝ)^16 := by
      have hnat : (34309 : ℕ)^65*25000000000000000000^16 ≤ 5413393653623073343^16*50000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        34309 50000 5413393653623073343 25000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (34309/50000 : ℝ)) (X := (5413393653623073343/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (30413393653623073343/25000000000000000000 : ℝ) ≤ (10494308217837759/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (30413393653623073343/25000000000000000000 : ℝ)^16 ≤ (10494308217837759/10000000000000000 : ℝ)^65 := by
      have hnat : (30413393653623073343 : ℕ)^16*10000000000000000^65 ≤ 10494308217837759^65*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30413393653623073343 25000000000000000000 10494308217837759 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10494308217837759/10000000000000000 : ℝ)) (X := (30413393653623073343/25000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (17913393653623073343/12500000000000000000 : ℝ) ≤ (5463059597206011/5000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (17913393653623073343/12500000000000000000 : ℝ)^16 ≤ (5463059597206011/5000000000000000 : ℝ)^65 := by
      have hnat : (17913393653623073343 : ℕ)^16*5000000000000000^65 ≤ 5463059597206011^65*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17913393653623073343 12500000000000000000 5463059597206011 5000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5463059597206011/5000000000000000 : ℝ)) (X := (17913393653623073343/12500000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(494308217837759/6861800000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(39255543324933/623800000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (34309/50000 : ℝ)) (alpha := (494308217837759/6861800000000000 : ℝ)) (beta := (39255543324933/623800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (34309/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(494308217837759/6861800000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(39255543324933/623800000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (5669/6250 : ℝ) ^ (65/16 : ℝ) ≤ (13455114774669107137/20000000000000000000 : ℝ) := by
    have hpowers : (5669/6250 : ℝ)^65 ≤ (13455114774669107137/20000000000000000000 : ℝ)^16 := by
      have hnat : (5669 : ℕ)^65*20000000000000000000^16 ≤ 13455114774669107137^16*6250^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5669 6250 13455114774669107137 20000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5669/6250 : ℝ)) (X := (13455114774669107137/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (33455114774669107137/20000000000000000000 : ℝ) ≤ (11350076174404111/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (33455114774669107137/20000000000000000000 : ℝ)^16 ≤ (11350076174404111/10000000000000000 : ℝ)^65 := by
      have hnat : (33455114774669107137 : ℕ)^16*10000000000000000^65 ≤ 11350076174404111^65*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33455114774669107137 20000000000000000000 11350076174404111 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11350076174404111/10000000000000000 : ℝ)) (X := (33455114774669107137/20000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (23455114774669107137/10000000000000000000 : ℝ) ≤ (1541861672815931/1250000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (23455114774669107137/10000000000000000000 : ℝ)^16 ≤ (1541861672815931/1250000000000000 : ℝ)^65 := by
      have hnat : (23455114774669107137 : ℕ)^16*1250000000000000^65 ≤ 1541861672815931^65*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23455114774669107137 10000000000000000000 1541861672815931 1250000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1541861672815931/1250000000000000 : ℝ)) (X := (23455114774669107137/10000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1350076174404111/9070400000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(984817208123337/9070400000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (5669/6250 : ℝ)) (alpha := (1350076174404111/9070400000000000 : ℝ)) (beta := (984817208123337/9070400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (5669/6250 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1350076174404111/9070400000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(984817208123337/9070400000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-5054561857/10000000000 : ℝ)*X 0 0+(1718520357/5000000000 : ℝ)*X 0 1+(-2229480627/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302018_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4906306947/10000000000 : ℝ)*X 1 0+(-2881398259/10000000000 : ℝ)*X 1 1+(-2548566529/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302018_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-2574194671/5000000000 : ℝ)*X 0 0+(2953652603/10000000000 : ℝ)*X 0 1+(-4792553823/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302018_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((4828113953/10000000000 : ℝ)*X 1 0+(-2020066503/10000000000 : ℝ)*X 1 1+(-1460365239/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302018_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((3858114889/10000000000 : ℝ)*X 2 0+(5497644421/10000000000 : ℝ)*X 2 1+(3567199447/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302018_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((310158787/5000000000 : ℝ)*X 0 0+(2266273369/2500000000 : ℝ)*X 0 1+(-833656991/5000000000 : ℝ)*X 0 2+(310158787/5000000000 : ℝ)*X 1 0+(2266273369/2500000000 : ℝ)*X 1 1+(-833656991/5000000000 : ℝ)*X 1 2+(310158787/5000000000 : ℝ)*X 2 0+(2266273369/2500000000 : ℝ)*X 2 1+(-833656991/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302018_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-19932567/39062500 : ℝ)*X 0 0+(3376520917/10000000000 : ℝ)*X 0 1+(-558049593/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302018_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((1296673007/2500000000 : ℝ)*X 1 0+(-2416664011/10000000000 : ℝ)*X 1 1+(-2597850181/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302018_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((4232423309/10000000000 : ℝ)*X 2 0+(1049871503/2000000000 : ℝ)*X 2 1+(3459681219/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302018_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((2708677/500000000 : ℝ)*X 0 0+(7888999133/10000000000 : ℝ)*X 0 1+(-146228107/400000000 : ℝ)*X 0 2+(2708677/500000000 : ℝ)*X 1 0+(7888999133/10000000000 : ℝ)*X 1 1+(-146228107/400000000 : ℝ)*X 1 2+(2708677/500000000 : ℝ)*X 2 0+(7888999133/10000000000 : ℝ)*X 2 1+(-146228107/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302018_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-633387281/1250000000 : ℝ)*X 0 0+(3661043429/10000000000 : ℝ)*X 0 1+(-1058906273/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302018_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((5054637989/10000000000 : ℝ)*X 1 0+(-655319331/2500000000 : ℝ)*X 1 1+(-2582046291/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302018_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((4793683229/10000000000 : ℝ)*X 2 0+(4452873027/10000000000 : ℝ)*X 2 1+(746355393/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302018_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((56808061/10000000000 : ℝ)*X 0 0+(4369180521/5000000000 : ℝ)*X 0 1+(-2493093501/10000000000 : ℝ)*X 0 2+(56808061/10000000000 : ℝ)*X 1 0+(4369180521/5000000000 : ℝ)*X 1 1+(-2493093501/10000000000 : ℝ)*X 1 2+(56808061/10000000000 : ℝ)*X 2 0+(4369180521/5000000000 : ℝ)*X 2 1+(-2493093501/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302018_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((4051/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4051/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (111535498911952198738317429/14145288800000000000000000000000 : ℝ) := by norm_num
    linear_combination (206203/40000000000 : ℝ)*(base49) + (427707349799/250000000000 : ℝ)*(base50) + (2412059/500000000000 : ℝ)*(base53) + (589381460657/1000000000000 : ℝ)*(base60) + (5449758662429/1000000000000 : ℝ)*(major_s1_0) + (5449758662429/1000000000000 : ℝ)*(major_s1_1) + (5449753838311/1000000000000 : ℝ)*(major_s1_2) + (26845601/500000000000 : ℝ)*(sp_s1_0) + (72761497/1000000000000 : ℝ)*(sp_s1_1) + (724606832679/100000000000 : ℝ)*(sp_s1_7) + (452878078531/62500000000 : ℝ)*(sp_s1_8) + (724612684211/100000000000 : ℝ)*(sp_s1_9) + (913330043091/250000000000 : ℝ)*(sp_s1_13) + (1353641/20000000000 : ℝ)*(sp_s1_27) + (1826693927207/500000000000 : ℝ)*(f.failure) + (724612684211/100000000000 : ℝ)*(f.sum) + (17673843992511369819/311196353600000000000000000000000 : ℝ)*base63 + (1673641183191327/9070400000000000000000000000 : ℝ)*base65 + (203353974259377/623800000000000000000000000 : ℝ)*base66 + (597761917260841/9070400000000000000000000000 : ℝ)*base68 + (94199768712957193259/279123419200000000000000000000000 : ℝ)*base71 + (4379989775885467/9231900000000000000000000000 : ℝ)*base73 + (653937304232291/6861800000000000000000000000 : ℝ)*base74 + (109675986285909/1538650000000000000000000000 : ℝ)*base76 + (7190062740263586677/57588592200000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (1819/5000000000000000 : ℝ)*base87 + (1819/5000000000000000 : ℝ)*base89 + (1819/5000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(20689/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(20689/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2643413478989292127958446870089/478822269466640000000000000000000000 : ℝ) := by norm_num
    linear_combination (218429214337/250000000000 : ℝ)*(base1) + (2707057/1000000000000 : ℝ)*(base39) + (71971231511/50000000000 : ℝ)*(base50) + (106788526113/100000000000 : ℝ)*(base60) + (1346705373847/200000000000 : ℝ)*(major_s1_0) + (1346705373847/200000000000 : ℝ)*(major_s1_1) + (1346705373847/200000000000 : ℝ)*(major_s1_2) + (18871551/250000000000 : ℝ)*(sp_s1_7) + (2456674478903/250000000000 : ℝ)*(sp_s1_14) + (2238264136117/250000000000 : ℝ)*(sp_s1_15) + (8953032989277/1000000000000 : ℝ)*(sp_s1_16) + (455034218477/125000000000 : ℝ)*(sp_s1_20) + (23555191/1000000000000 : ℝ)*(sp_s1_23) + (4748617/1000000000000 : ℝ)*(sp_s1_27) + (4513995353781/1000000000000 : ℝ)*(f.failure) + (2238264136117/250000000000 : ℝ)*(f.sum) + (20509212486401766469/62239270720000000000000000000000 : ℝ)*base62 + (13433816077401/72563200000000000000000000 : ℝ)*base64 + (49168960277961/124760000000000000000000000 : ℝ)*base67 + (35063692705893/362816000000000000000000000 : ℝ)*base68 + (1112679785890413761/11164936768000000000000000000000 : ℝ)*base70 + (35307909987053/369276000000000000000000000 : ℝ)*base72 + (568895953069597/1372360000000000000000000000 : ℝ)*base74 + (55421137837399/307730000000000000000000000 : ℝ)*base76 + (51203740535241653/460708737600000000000000000000 : ℝ)*base79 + (1177/10000000000000000 : ℝ)*base87 + (1177/10000000000000000 : ℝ)*base89 + (1177/10000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-4077/12500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-4077/12500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1321792953828531109959351728199/149631959208325000000000000000000000 : ℝ) := by norm_num
    linear_combination (25694845757/125000000000 : ℝ)*(base1) + (864583/250000000000 : ℝ)*(base39) + (2272705662497/1000000000000 : ℝ)*(base50) + (77896588381/200000000000 : ℝ)*(base60) + (7920989060973/1000000000000 : ℝ)*(major_s1_0) + (7920989060973/1000000000000 : ℝ)*(major_s1_1) + (7920989060973/1000000000000 : ℝ)*(major_s1_2) + (68756941/1000000000000 : ℝ)*(sp_s1_13) + (17353269/500000000000 : ℝ)*(sp_s1_15) + (27952353/500000000000 : ℝ)*(sp_s1_16) + (5368746169631/500000000000 : ℝ)*(sp_s1_21) + (10531898866669/1000000000000 : ℝ)*(sp_s1_22) + (21063755337/2000000000 : ℝ)*(sp_s1_23) + (1020882816239/200000000000 : ℝ)*(sp_s1_27) + (165938800131/31250000000 : ℝ)*(f.failure) + (10531933573207/1000000000000 : ℝ)*(f.sum) + (57278188498535678471/311196353600000000000000000000000 : ℝ)*base62 + (1825129405838741/9070400000000000000000000000 : ℝ)*base65 + (217873630689371/623800000000000000000000000 : ℝ)*base67 + (4030384260067363/9070400000000000000000000000 : ℝ)*base68 + (139725275158610887929/279123419200000000000000000000000 : ℝ)*base71 + (52438333947023/3077300000000000000000000000 : ℝ)*base73 + (1294400746300447/6861800000000000000000000000 : ℝ)*base74 + (640942179025097/1538650000000000000000000000 : ℝ)*base77 + (1379961522371013603/19196197400000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (129/625000000000000 : ℝ)*base87 + (129/625000000000000 : ℝ)*base89 + (129/625000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((92319/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(92319/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(34309/50000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(34309/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-5669/6250 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-5669/6250 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((4051/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4051/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(20689/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(20689/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-4077/12500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-4077/12500 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c302018_s1 p hpa hpb X hX hprev0

#print axioms solution
