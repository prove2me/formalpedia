-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c302060_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:24:11.770205+00:00
-- url     : https://prove2.me/submissions/75eba4b6-d8c5-4691-8027-cdc0740f5208

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
theorem collision_support_c302060_s2_s2_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-829713289/5000000000 : ℝ)*x 0 + (224603319/500000000 : ℝ)*x 1 + (-258194423/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (829713289/5000000000 : ℝ)^131 ≤ (9285884279901/100000000000000 : ℝ)^99 := by
    have hnat : (829713289 : ℕ)^131*100000000000000^99 ≤ 9285884279901^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      829713289 5000000000 9285884279901 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (224603319/500000000 : ℝ)^131 ≤ (17341055818293/50000000000000 : ℝ)^99 := by
    have hnat : (224603319 : ℕ)^131*50000000000000^99 ≤ 17341055818293^99*500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224603319 500000000 17341055818293 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258194423/400000000 : ℝ)^131 ≤ (56032004069283/100000000000000 : ℝ)^99 := by
    have hnat : (258194423 : ℕ)^131*100000000000000^99 ≤ 56032004069283^99*400000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258194423 400000000 56032004069283 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-829713289/5000000000 : ℝ), (224603319/500000000 : ℝ), (-258194423/400000000 : ℝ)] ![(9285884279901/100000000000000 : ℝ), (17341055818293/50000000000000 : ℝ), (56032004069283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-829713289/5000000000 : ℝ)|^131 ≤ (9285884279901/100000000000000 : ℝ)^99
        have hw : |(-829713289/5000000000 : ℝ)|=(829713289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(224603319/500000000 : ℝ)|^131 ≤ (17341055818293/50000000000000 : ℝ)^99
        have hw : |(224603319/500000000 : ℝ)|=(224603319/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-258194423/400000000 : ℝ)|^131 ≤ (56032004069283/100000000000000 : ℝ)^99
        have hw : |(-258194423/400000000 : ℝ)|=(258194423/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302060_s2_s2_1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (560801207/1250000000 : ℝ)*x 0 + (-1661613389/10000000000 : ℝ)*x 1 + (-3229240231/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (560801207/1250000000 : ℝ)^131 ≤ (1384973294741/4000000000000 : ℝ)^99 := by
    have hnat : (560801207 : ℕ)^131*4000000000000^99 ≤ 1384973294741^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560801207 1250000000 1384973294741 4000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1661613389/10000000000 : ℝ)^131 ≤ (372083207119/4000000000000 : ℝ)^99 := by
    have hnat : (1661613389 : ℕ)^131*4000000000000^99 ≤ 372083207119^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1661613389 10000000000 372083207119 4000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3229240231/5000000000 : ℝ)^131 ≤ (28036793723347/50000000000000 : ℝ)^99 := by
    have hnat : (3229240231 : ℕ)^131*50000000000000^99 ≤ 28036793723347^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3229240231 5000000000 28036793723347 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(560801207/1250000000 : ℝ), (-1661613389/10000000000 : ℝ), (-3229240231/5000000000 : ℝ)] ![(1384973294741/4000000000000 : ℝ), (372083207119/4000000000000 : ℝ), (28036793723347/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(560801207/1250000000 : ℝ)|^131 ≤ (1384973294741/4000000000000 : ℝ)^99
        have hw : |(560801207/1250000000 : ℝ)|=(560801207/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1661613389/10000000000 : ℝ)|^131 ≤ (372083207119/4000000000000 : ℝ)^99
        have hw : |(-1661613389/10000000000 : ℝ)|=(1661613389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3229240231/5000000000 : ℝ)|^131 ≤ (28036793723347/50000000000000 : ℝ)^99
        have hw : |(-3229240231/5000000000 : ℝ)|=(3229240231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302060_s2_s2_7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-300106639/2500000000 : ℝ)*x 0 + (1156915953/5000000000 : ℝ)*x 1 + (-8410914201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (300106639/2500000000 : ℝ)^131 ≤ (1209976944963/20000000000000 : ℝ)^99 := by
    have hnat : (300106639 : ℕ)^131*20000000000000^99 ≤ 1209976944963^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300106639 2500000000 1209976944963 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1156915953/5000000000 : ℝ)^131 ≤ (2883322982547/20000000000000 : ℝ)^99 := by
    have hnat : (1156915953 : ℕ)^131*20000000000000^99 ≤ 2883322982547^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1156915953 5000000000 2883322982547 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8410914201/10000000000 : ℝ)^131 ≤ (15906700070657/20000000000000 : ℝ)^99 := by
    have hnat : (8410914201 : ℕ)^131*20000000000000^99 ≤ 15906700070657^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8410914201 10000000000 15906700070657 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-300106639/2500000000 : ℝ), (1156915953/5000000000 : ℝ), (-8410914201/10000000000 : ℝ)] ![(1209976944963/20000000000000 : ℝ), (2883322982547/20000000000000 : ℝ), (15906700070657/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-300106639/2500000000 : ℝ)|^131 ≤ (1209976944963/20000000000000 : ℝ)^99
        have hw : |(-300106639/2500000000 : ℝ)|=(300106639/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1156915953/5000000000 : ℝ)|^131 ≤ (2883322982547/20000000000000 : ℝ)^99
        have hw : |(1156915953/5000000000 : ℝ)|=(1156915953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8410914201/10000000000 : ℝ)|^131 ≤ (15906700070657/20000000000000 : ℝ)^99
        have hw : |(-8410914201/10000000000 : ℝ)|=(8410914201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302060_s2_s2_8 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2620562311/10000000000 : ℝ)*x 0 + (-778236241/10000000000 : ℝ)*x 1 + (-84156247/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2620562311/10000000000 : ℝ)^131 ≤ (16998116080359/100000000000000 : ℝ)^99 := by
    have hnat : (2620562311 : ℕ)^131*100000000000000^99 ≤ 16998116080359^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620562311 10000000000 16998116080359 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (778236241/10000000000 : ℝ)^131 ≤ (1704719126003/50000000000000 : ℝ)^99 := by
    have hnat : (778236241 : ℕ)^131*50000000000000^99 ≤ 1704719126003^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      778236241 10000000000 1704719126003 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84156247/100000000 : ℝ)^131 ≤ (9949055707183/12500000000000 : ℝ)^99 := by
    have hnat : (84156247 : ℕ)^131*12500000000000^99 ≤ 9949055707183^99*100000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84156247 100000000 9949055707183 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2620562311/10000000000 : ℝ), (-778236241/10000000000 : ℝ), (-84156247/100000000 : ℝ)] ![(16998116080359/100000000000000 : ℝ), (1704719126003/50000000000000 : ℝ), (9949055707183/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2620562311/10000000000 : ℝ)|^131 ≤ (16998116080359/100000000000000 : ℝ)^99
        have hw : |(2620562311/10000000000 : ℝ)|=(2620562311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-778236241/10000000000 : ℝ)|^131 ≤ (1704719126003/50000000000000 : ℝ)^99
        have hw : |(-778236241/10000000000 : ℝ)|=(778236241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-84156247/100000000 : ℝ)|^131 ≤ (9949055707183/12500000000000 : ℝ)^99
        have hw : |(-84156247/100000000 : ℝ)|=(84156247/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302060_s2_s2_9 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2391614669/10000000000 : ℝ)*x 0 + (2010297751/2500000000 : ℝ)*x 1 + (877368953/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2391614669/10000000000 : ℝ)^131 ≤ (15061357750581/100000000000000 : ℝ)^99 := by
    have hnat : (2391614669 : ℕ)^131*100000000000000^99 ≤ 15061357750581^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2391614669 10000000000 15061357750581 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2010297751/2500000000 : ℝ)^131 ≤ (37470273952279/50000000000000 : ℝ)^99 := by
    have hnat : (2010297751 : ℕ)^131*50000000000000^99 ≤ 37470273952279^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010297751 2500000000 37470273952279 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (877368953/5000000000 : ℝ)^131 ≤ (9998094333901/100000000000000 : ℝ)^99 := by
    have hnat : (877368953 : ℕ)^131*100000000000000^99 ≤ 9998094333901^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      877368953 5000000000 9998094333901 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2391614669/10000000000 : ℝ), (2010297751/2500000000 : ℝ), (877368953/5000000000 : ℝ)] ![(15061357750581/100000000000000 : ℝ), (37470273952279/50000000000000 : ℝ), (9998094333901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2391614669/10000000000 : ℝ)|^131 ≤ (15061357750581/100000000000000 : ℝ)^99
        have hw : |(2391614669/10000000000 : ℝ)|=(2391614669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2010297751/2500000000 : ℝ)|^131 ≤ (37470273952279/50000000000000 : ℝ)^99
        have hw : |(2010297751/2500000000 : ℝ)|=(2010297751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(877368953/5000000000 : ℝ)|^131 ≤ (9998094333901/100000000000000 : ℝ)^99
        have hw : |(877368953/5000000000 : ℝ)|=(877368953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302060_s2_s2_13 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4513840249/10000000000 : ℝ)*x 0 + (7229268401/10000000000 : ℝ)*x 1 + (-41017/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4513840249/10000000000 : ℝ)^131 ≤ (8726183756191/25000000000000 : ℝ)^99 := by
    have hnat : (4513840249 : ℕ)^131*25000000000000^99 ≤ 8726183756191^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4513840249 10000000000 8726183756191 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7229268401/10000000000 : ℝ)^131 ≤ (3254760918219/5000000000000 : ℝ)^99 := by
    have hnat : (7229268401 : ℕ)^131*5000000000000^99 ≤ 3254760918219^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7229268401 10000000000 3254760918219 5000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41017/2500000000 : ℝ)^131 ≤ (46597749/100000000000000 : ℝ)^99 := by
    have hnat : (41017 : ℕ)^131*100000000000000^99 ≤ 46597749^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41017 2500000000 46597749 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4513840249/10000000000 : ℝ), (7229268401/10000000000 : ℝ), (-41017/2500000000 : ℝ)] ![(8726183756191/25000000000000 : ℝ), (3254760918219/5000000000000 : ℝ), (46597749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4513840249/10000000000 : ℝ)|^131 ≤ (8726183756191/25000000000000 : ℝ)^99
        have hw : |(4513840249/10000000000 : ℝ)|=(4513840249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7229268401/10000000000 : ℝ)|^131 ≤ (3254760918219/5000000000000 : ℝ)^99
        have hw : |(7229268401/10000000000 : ℝ)|=(7229268401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-41017/2500000000 : ℝ)|^131 ≤ (46597749/100000000000000 : ℝ)^99
        have hw : |(-41017/2500000000 : ℝ)|=(41017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302060_s2_s2_14 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-34123601/250000000 : ℝ)*x 0 + (1855578431/10000000000 : ℝ)*x 1 + (-1722475993/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34123601/250000000 : ℝ)^131 ≤ (7170608457913/100000000000000 : ℝ)^99 := by
    have hnat : (34123601 : ℕ)^131*100000000000000^99 ≤ 7170608457913^99*250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34123601 250000000 7170608457913 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1855578431/10000000000 : ℝ)^131 ≤ (10765350777493/100000000000000 : ℝ)^99 := by
    have hnat : (1855578431 : ℕ)^131*100000000000000^99 ≤ 10765350777493^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1855578431 10000000000 10765350777493 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1722475993/2000000000 : ℝ)^131 ≤ (41032020374253/50000000000000 : ℝ)^99 := by
    have hnat : (1722475993 : ℕ)^131*50000000000000^99 ≤ 41032020374253^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1722475993 2000000000 41032020374253 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-34123601/250000000 : ℝ), (1855578431/10000000000 : ℝ), (-1722475993/2000000000 : ℝ)] ![(7170608457913/100000000000000 : ℝ), (10765350777493/100000000000000 : ℝ), (41032020374253/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-34123601/250000000 : ℝ)|^131 ≤ (7170608457913/100000000000000 : ℝ)^99
        have hw : |(-34123601/250000000 : ℝ)|=(34123601/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1855578431/10000000000 : ℝ)|^131 ≤ (10765350777493/100000000000000 : ℝ)^99
        have hw : |(1855578431/10000000000 : ℝ)|=(1855578431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1722475993/2000000000 : ℝ)|^131 ≤ (41032020374253/50000000000000 : ℝ)^99
        have hw : |(-1722475993/2000000000 : ℝ)|=(1722475993/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302060_s2_s2_15 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1467441053/10000000000 : ℝ)*x 0 + (-35055981/200000000 : ℝ)*x 1 + (-8617206471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1467441053/10000000000 : ℝ)^131 ≤ (1578323881093/20000000000000 : ℝ)^99 := by
    have hnat : (1467441053 : ℕ)^131*20000000000000^99 ≤ 1578323881093^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1467441053 10000000000 1578323881093 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35055981/200000000 : ℝ)^131 ≤ (9983478989681/100000000000000 : ℝ)^99 := by
    have hnat : (35055981 : ℕ)^131*100000000000000^99 ≤ 9983478989681^99*200000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35055981 200000000 9983478989681 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8617206471/10000000000 : ℝ)^131 ≤ (82124901595917/100000000000000 : ℝ)^99 := by
    have hnat : (8617206471 : ℕ)^131*100000000000000^99 ≤ 82124901595917^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8617206471 10000000000 82124901595917 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1467441053/10000000000 : ℝ), (-35055981/200000000 : ℝ), (-8617206471/10000000000 : ℝ)] ![(1578323881093/20000000000000 : ℝ), (9983478989681/100000000000000 : ℝ), (82124901595917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1467441053/10000000000 : ℝ)|^131 ≤ (1578323881093/20000000000000 : ℝ)^99
        have hw : |(1467441053/10000000000 : ℝ)|=(1467441053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-35055981/200000000 : ℝ)|^131 ≤ (9983478989681/100000000000000 : ℝ)^99
        have hw : |(-35055981/200000000 : ℝ)|=(35055981/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8617206471/10000000000 : ℝ)|^131 ≤ (82124901595917/100000000000000 : ℝ)^99
        have hw : |(-8617206471/10000000000 : ℝ)|=(8617206471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302060_s2_s2_16 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6657516383/10000000000 : ℝ)*x 0 + (969622201/2500000000 : ℝ)*x 1 + (429760749/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6657516383/10000000000 : ℝ)^131 ≤ (29185763185211/50000000000000 : ℝ)^99 := by
    have hnat : (6657516383 : ℕ)^131*50000000000000^99 ≤ 29185763185211^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6657516383 10000000000 29185763185211 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (969622201/2500000000 : ℝ)^131 ≤ (28556500163151/100000000000000 : ℝ)^99 := by
    have hnat : (969622201 : ℕ)^131*100000000000000^99 ≤ 28556500163151^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      969622201 2500000000 28556500163151 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (429760749/2000000000 : ℝ)^131 ≤ (408499170197/3125000000000 : ℝ)^99 := by
    have hnat : (429760749 : ℕ)^131*3125000000000^99 ≤ 408499170197^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429760749 2000000000 408499170197 3125000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6657516383/10000000000 : ℝ), (969622201/2500000000 : ℝ), (429760749/2000000000 : ℝ)] ![(29185763185211/50000000000000 : ℝ), (28556500163151/100000000000000 : ℝ), (408499170197/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6657516383/10000000000 : ℝ)|^131 ≤ (29185763185211/50000000000000 : ℝ)^99
        have hw : |(6657516383/10000000000 : ℝ)|=(6657516383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(969622201/2500000000 : ℝ)|^131 ≤ (28556500163151/100000000000000 : ℝ)^99
        have hw : |(969622201/2500000000 : ℝ)|=(969622201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(429760749/2000000000 : ℝ)|^131 ≤ (408499170197/3125000000000 : ℝ)^99
        have hw : |(429760749/2000000000 : ℝ)|=(429760749/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302060_s2_s2_20 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4413738193/5000000000 : ℝ)*x 0 + (2409791263/10000000000 : ℝ)*x 1 + (-4571/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4413738193/5000000000 : ℝ)^131 ≤ (10598373105927/12500000000000 : ℝ)^99 := by
    have hnat : (4413738193 : ℕ)^131*12500000000000^99 ≤ 10598373105927^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4413738193 5000000000 10598373105927 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2409791263/10000000000 : ℝ)^131 ≤ (1901626462799/12500000000000 : ℝ)^99 := by
    have hnat : (2409791263 : ℕ)^131*12500000000000^99 ≤ 1901626462799^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2409791263 10000000000 1901626462799 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4571/2000000000 : ℝ)^131 ≤ (858147/25000000000000 : ℝ)^99 := by
    have hnat : (4571 : ℕ)^131*25000000000000^99 ≤ 858147^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4571 2000000000 858147 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4413738193/5000000000 : ℝ), (2409791263/10000000000 : ℝ), (-4571/2000000000 : ℝ)] ![(10598373105927/12500000000000 : ℝ), (1901626462799/12500000000000 : ℝ), (858147/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4413738193/5000000000 : ℝ)|^131 ≤ (10598373105927/12500000000000 : ℝ)^99
        have hw : |(4413738193/5000000000 : ℝ)|=(4413738193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2409791263/10000000000 : ℝ)|^131 ≤ (1901626462799/12500000000000 : ℝ)^99
        have hw : |(2409791263/10000000000 : ℝ)|=(2409791263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4571/2000000000 : ℝ)|^131 ≤ (858147/25000000000000 : ℝ)^99
        have hw : |(-4571/2000000000 : ℝ)|=(4571/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302060_s2_s2_21 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-342400401/2000000000 : ℝ)*x 0 + (4050361233/10000000000 : ℝ)*x 1 + (-6804252601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (342400401/2000000000 : ℝ)^131 ≤ (37801419431/390625000000 : ℝ)^99 := by
    have hnat : (342400401 : ℕ)^131*390625000000^99 ≤ 37801419431^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342400401 2000000000 37801419431 390625000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4050361233/10000000000 : ℝ)^131 ≤ (30242873511661/100000000000000 : ℝ)^99 := by
    have hnat : (4050361233 : ℕ)^131*100000000000000^99 ≤ 30242873511661^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4050361233 10000000000 30242873511661 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6804252601/10000000000 : ℝ)^131 ≤ (3003998154793/5000000000000 : ℝ)^99 := by
    have hnat : (6804252601 : ℕ)^131*5000000000000^99 ≤ 3003998154793^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6804252601 10000000000 3003998154793 5000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-342400401/2000000000 : ℝ), (4050361233/10000000000 : ℝ), (-6804252601/10000000000 : ℝ)] ![(37801419431/390625000000 : ℝ), (30242873511661/100000000000000 : ℝ), (3003998154793/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-342400401/2000000000 : ℝ)|^131 ≤ (37801419431/390625000000 : ℝ)^99
        have hw : |(-342400401/2000000000 : ℝ)|=(342400401/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4050361233/10000000000 : ℝ)|^131 ≤ (30242873511661/100000000000000 : ℝ)^99
        have hw : |(4050361233/10000000000 : ℝ)|=(4050361233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6804252601/10000000000 : ℝ)|^131 ≤ (3003998154793/5000000000000 : ℝ)^99
        have hw : |(-6804252601/10000000000 : ℝ)|=(6804252601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302060_s2_s2_22 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1798598993/2500000000 : ℝ)*x 0 + (-1389271541/10000000000 : ℝ)*x 1 + (-954785901/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1798598993/2500000000 : ℝ)^131 ≤ (64680040719739/100000000000000 : ℝ)^99 := by
    have hnat : (1798598993 : ℕ)^131*100000000000000^99 ≤ 64680040719739^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1798598993 2500000000 64680040719739 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1389271541/10000000000 : ℝ)^131 ≤ (7340205772011/100000000000000 : ℝ)^99 := by
    have hnat : (1389271541 : ℕ)^131*100000000000000^99 ≤ 7340205772011^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1389271541 10000000000 7340205772011 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (954785901/2500000000 : ℝ)^131 ≤ (2797975349239/10000000000000 : ℝ)^99 := by
    have hnat : (954785901 : ℕ)^131*10000000000000^99 ≤ 2797975349239^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      954785901 2500000000 2797975349239 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1798598993/2500000000 : ℝ), (-1389271541/10000000000 : ℝ), (-954785901/2500000000 : ℝ)] ![(64680040719739/100000000000000 : ℝ), (7340205772011/100000000000000 : ℝ), (2797975349239/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1798598993/2500000000 : ℝ)|^131 ≤ (64680040719739/100000000000000 : ℝ)^99
        have hw : |(1798598993/2500000000 : ℝ)|=(1798598993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1389271541/10000000000 : ℝ)|^131 ≤ (7340205772011/100000000000000 : ℝ)^99
        have hw : |(-1389271541/10000000000 : ℝ)|=(1389271541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-954785901/2500000000 : ℝ)|^131 ≤ (2797975349239/10000000000000 : ℝ)^99
        have hw : |(-954785901/2500000000 : ℝ)|=(954785901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302060_s2_s2_23 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2072124673/10000000000 : ℝ)*x 0 + (3861913441/5000000000 : ℝ)*x 1 + (2561104931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2072124673/10000000000 : ℝ)^131 ≤ (12458317634123/100000000000000 : ℝ)^99 := by
    have hnat : (2072124673 : ℕ)^131*100000000000000^99 ≤ 12458317634123^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072124673 10000000000 12458317634123 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3861913441/5000000000 : ℝ)^131 ≤ (71052011858261/100000000000000 : ℝ)^99 := by
    have hnat : (3861913441 : ℕ)^131*100000000000000^99 ≤ 71052011858261^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3861913441 5000000000 71052011858261 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2561104931/10000000000 : ℝ)^131 ≤ (8244835248633/50000000000000 : ℝ)^99 := by
    have hnat : (2561104931 : ℕ)^131*50000000000000^99 ≤ 8244835248633^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2561104931 10000000000 8244835248633 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2072124673/10000000000 : ℝ), (3861913441/5000000000 : ℝ), (2561104931/10000000000 : ℝ)] ![(12458317634123/100000000000000 : ℝ), (71052011858261/100000000000000 : ℝ), (8244835248633/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2072124673/10000000000 : ℝ)|^131 ≤ (12458317634123/100000000000000 : ℝ)^99
        have hw : |(2072124673/10000000000 : ℝ)|=(2072124673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3861913441/5000000000 : ℝ)|^131 ≤ (71052011858261/100000000000000 : ℝ)^99
        have hw : |(3861913441/5000000000 : ℝ)|=(3861913441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2561104931/10000000000 : ℝ)|^131 ≤ (8244835248633/50000000000000 : ℝ)^99
        have hw : |(2561104931/10000000000 : ℝ)|=(2561104931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302060_s2_s2_27 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2273196301/2500000000 : ℝ)*x 0 + (497992899/2500000000 : ℝ)*x 1 + (-4653/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2273196301/2500000000 : ℝ)^131 ≤ (44087599184861/50000000000000 : ℝ)^99 := by
    have hnat : (2273196301 : ℕ)^131*50000000000000^99 ≤ 44087599184861^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2273196301 2500000000 44087599184861 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (497992899/2500000000 : ℝ)^131 ≤ (5912331921983/50000000000000 : ℝ)^99 := by
    have hnat : (497992899 : ℕ)^131*50000000000000^99 ≤ 5912331921983^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497992899 2500000000 5912331921983 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4653/125000000 : ℝ)^131 ≤ (137774829/100000000000000 : ℝ)^99 := by
    have hnat : (4653 : ℕ)^131*100000000000000^99 ≤ 137774829^99*125000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4653 125000000 137774829 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2273196301/2500000000 : ℝ), (497992899/2500000000 : ℝ), (-4653/125000000 : ℝ)] ![(44087599184861/50000000000000 : ℝ), (5912331921983/50000000000000 : ℝ), (137774829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2273196301/2500000000 : ℝ)|^131 ≤ (44087599184861/50000000000000 : ℝ)^99
        have hw : |(2273196301/2500000000 : ℝ)|=(2273196301/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(497992899/2500000000 : ℝ)|^131 ≤ (5912331921983/50000000000000 : ℝ)^99
        have hw : |(497992899/2500000000 : ℝ)|=(497992899/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4653/125000000 : ℝ)|^131 ≤ (137774829/100000000000000 : ℝ)^99
        have hw : |(-4653/125000000 : ℝ)|=(4653/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c302060_s2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev1 : (0 : ℝ) ≤ ((3673/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3673/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(92099/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(92099/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-85519/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-85519/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((84979/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(84979/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(85723/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(85723/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-3831/5000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-3831/5000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4769/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4769/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (36753/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base60 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s2_pow0 : (3673/4000 : ℝ) ^ (65/16 : ℝ) ≤ (35358905302696201919/50000000000000000000 : ℝ) := by
    have hpowers : (3673/4000 : ℝ)^65 ≤ (35358905302696201919/50000000000000000000 : ℝ)^16 := by
      have hnat : (3673 : ℕ)^65*50000000000000000000^16 ≤ 35358905302696201919^16*4000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3673 4000 35358905302696201919 50000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3673/4000 : ℝ)) (X := (35358905302696201919/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (85358905302696201919/50000000000000000000 : ℝ) ≤ (2281425669184759/2000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (85358905302696201919/50000000000000000000 : ℝ)^16 ≤ (2281425669184759/2000000000000000 : ℝ)^65 := by
      have hnat : (85358905302696201919 : ℕ)^16*2000000000000000^65 ≤ 2281425669184759^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        85358905302696201919 50000000000000000000 2281425669184759 2000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2281425669184759/2000000000000000 : ℝ)) (X := (85358905302696201919/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (60358905302696201919/25000000000000000000 : ℝ) ≤ (12423044005826759/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (60358905302696201919/25000000000000000000 : ℝ)^16 ≤ (12423044005826759/10000000000000000 : ℝ)^65 := by
      have hnat : (60358905302696201919 : ℕ)^16*10000000000000000^65 ≤ 12423044005826759^65*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60358905302696201919 25000000000000000000 12423044005826759 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12423044005826759/10000000000000000 : ℝ)) (X := (60358905302696201919/25000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(281425669184759/1836500000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(253978914975741/2295625000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (3673/4000 : ℝ)) (alpha := (281425669184759/1836500000000000 : ℝ)) (beta := (253978914975741/2295625000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (3673/4000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(281425669184759/1836500000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(253978914975741/2295625000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (92099/100000 : ℝ) ^ (65/16 : ℝ) ≤ (14315798821093372931/20000000000000000000 : ℝ) := by
    have hpowers : (92099/100000 : ℝ)^65 ≤ (14315798821093372931/20000000000000000000 : ℝ)^16 := by
      have hnat : (92099 : ℕ)^65*20000000000000000000^16 ≤ 14315798821093372931^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        92099 100000 14315798821093372931 20000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (92099/100000 : ℝ)) (X := (14315798821093372931/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (34315798821093372931/20000000000000000000 : ℝ) ≤ (5710632973243277/5000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (34315798821093372931/20000000000000000000 : ℝ)^16 ≤ (5710632973243277/5000000000000000 : ℝ)^65 := by
      have hnat : (34315798821093372931 : ℕ)^16*5000000000000000^65 ≤ 5710632973243277^65*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        34315798821093372931 20000000000000000000 5710632973243277 5000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5710632973243277/5000000000000000 : ℝ)) (X := (34315798821093372931/20000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (24315798821093372931/10000000000000000000 : ℝ) ≤ (1555600097509177/1250000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (24315798821093372931/10000000000000000000 : ℝ)^16 ≤ (1555600097509177/1250000000000000 : ℝ)^65 := by
      have hnat : (24315798821093372931 : ℕ)^16*1250000000000000^65 ≤ 1555600097509177^65*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24315798821093372931 10000000000000000000 1555600097509177 1250000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1555600097509177/1250000000000000 : ℝ)) (X := (24315798821093372931/10000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(101518996177611/657850000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(511767416793431/4604950000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (92099/100000 : ℝ)) (alpha := (101518996177611/657850000000000 : ℝ)) (beta := (511767416793431/4604950000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (92099/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(101518996177611/657850000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(511767416793431/4604950000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (85519/100000 : ℝ) ^ (65/16 : ℝ) ≤ (52966877224849180703/100000000000000000000 : ℝ) := by
    have hpowers : (85519/100000 : ℝ)^65 ≤ (52966877224849180703/100000000000000000000 : ℝ)^16 := by
      have hnat : (85519 : ℕ)^65*100000000000000000000^16 ≤ 52966877224849180703^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        85519 100000 52966877224849180703 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (85519/100000 : ℝ)) (X := (52966877224849180703/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (152966877224849180703/100000000000000000000 : ℝ) ≤ (5551487477690083/5000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (152966877224849180703/100000000000000000000 : ℝ)^16 ≤ (5551487477690083/5000000000000000 : ℝ)^65 := by
      have hnat : (152966877224849180703 : ℕ)^16*5000000000000000^65 ≤ 5551487477690083^65*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        152966877224849180703 100000000000000000000 5551487477690083 5000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5551487477690083/5000000000000000 : ℝ)) (X := (152966877224849180703/100000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (102966877224849180703/50000000000000000000 : ℝ) ≤ (2986518770272609/2500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (102966877224849180703/50000000000000000000 : ℝ)^16 ≤ (2986518770272609/2500000000000000 : ℝ)^65 := by
      have hnat : (102966877224849180703 : ℕ)^16*2500000000000000^65 ≤ 2986518770272609^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102966877224849180703 50000000000000000000 2986518770272609 2500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2986518770272609/2500000000000000 : ℝ)) (X := (102966877224849180703/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(551487477690083/4275950000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(84310012571027/855190000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (85519/100000 : ℝ)) (alpha := (551487477690083/4275950000000000 : ℝ)) (beta := (84310012571027/855190000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (85519/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(551487477690083/4275950000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(84310012571027/855190000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-829713289/5000000000 : ℝ)*X 0 0+(224603319/500000000 : ℝ)*X 0 1+(-258194423/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302060_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((560801207/1250000000 : ℝ)*X 1 0+(-1661613389/10000000000 : ℝ)*X 1 1+(-3229240231/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302060_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-300106639/2500000000 : ℝ)*X 0 0+(1156915953/5000000000 : ℝ)*X 0 1+(-8410914201/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302060_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((2620562311/10000000000 : ℝ)*X 1 0+(-778236241/10000000000 : ℝ)*X 1 1+(-84156247/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302060_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((2391614669/10000000000 : ℝ)*X 2 0+(2010297751/2500000000 : ℝ)*X 2 1+(877368953/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302060_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((4513840249/10000000000 : ℝ)*X 0 0+(7229268401/10000000000 : ℝ)*X 0 1+(-41017/2500000000 : ℝ)*X 0 2+(4513840249/10000000000 : ℝ)*X 1 0+(7229268401/10000000000 : ℝ)*X 1 1+(-41017/2500000000 : ℝ)*X 1 2+(4513840249/10000000000 : ℝ)*X 2 0+(7229268401/10000000000 : ℝ)*X 2 1+(-41017/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302060_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-34123601/250000000 : ℝ)*X 0 0+(1855578431/10000000000 : ℝ)*X 0 1+(-1722475993/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302060_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((1467441053/10000000000 : ℝ)*X 1 0+(-35055981/200000000 : ℝ)*X 1 1+(-8617206471/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302060_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((6657516383/10000000000 : ℝ)*X 2 0+(969622201/2500000000 : ℝ)*X 2 1+(429760749/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302060_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((4413738193/5000000000 : ℝ)*X 0 0+(2409791263/10000000000 : ℝ)*X 0 1+(-4571/2000000000 : ℝ)*X 0 2+(4413738193/5000000000 : ℝ)*X 1 0+(2409791263/10000000000 : ℝ)*X 1 1+(-4571/2000000000 : ℝ)*X 1 2+(4413738193/5000000000 : ℝ)*X 2 0+(2409791263/10000000000 : ℝ)*X 2 1+(-4571/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302060_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-342400401/2000000000 : ℝ)*X 0 0+(4050361233/10000000000 : ℝ)*X 0 1+(-6804252601/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302060_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((1798598993/2500000000 : ℝ)*X 1 0+(-1389271541/10000000000 : ℝ)*X 1 1+(-954785901/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302060_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((2072124673/10000000000 : ℝ)*X 2 0+(3861913441/5000000000 : ℝ)*X 2 1+(2561104931/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302060_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((2273196301/2500000000 : ℝ)*X 0 0+(497992899/2500000000 : ℝ)*X 0 1+(-4653/125000000 : ℝ)*X 0 2+(2273196301/2500000000 : ℝ)*X 1 0+(497992899/2500000000 : ℝ)*X 1 1+(-4653/125000000 : ℝ)*X 1 2+(2273196301/2500000000 : ℝ)*X 2 0+(497992899/2500000000 : ℝ)*X 2 1+(-4653/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302060_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((84979/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(84979/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2269566900471487697221774533291/737993250546250000000000000000000000 : ℝ) := by norm_num
    linear_combination (99586487433/250000000000 : ℝ)*(base5) + (428290517357/500000000000 : ℝ)*(base7) + (589579/1000000000000 : ℝ)*(base43) + (120193684853/62500000000 : ℝ)*(major_s2_0) + (1923098368069/1000000000000 : ℝ)*(major_s2_1) + (120193684853/62500000000 : ℝ)*(major_s2_2) + (194823/250000000000 : ℝ)*(sp_s2_0) + (1911203/1000000000000 : ℝ)*(sp_s2_1) + (2032297265929/1000000000000 : ℝ)*(sp_s2_7) + (508070420821/250000000000 : ℝ)*(sp_s2_8) + (2430638469071/1000000000000 : ℝ)*(sp_s2_9) + (34948692551/20000000000 : ℝ)*(sp_s2_13) + (7520157/500000000000 : ℝ)*(sp_s2_15) + (2762941/500000000000 : ℝ)*(sp_s2_23) + (1289199542567/1000000000000 : ℝ)*(f.failure) + (5080746587/2500000000 : ℝ)*(f.sum) + (5311146419757412141/56258674150000000000000000000000 : ℝ)*base62 + (7519402771187/53449375000000000000000000 : ℝ)*base64 + (106139921755453/2302475000000000000000000000 : ℝ)*base66 + (354313040283299/1068987500000000000000000000 : ℝ)*base68 + (3644045758192602121/78527821750000000000000000000000 : ℝ)*base70 + (435507653279917/573906250000000000000000000 : ℝ)*base73 + (3313319291079/164462500000000000000000000 : ℝ)*base74 + (28919852929967/459125000000000000000000000 : ℝ)*base76 + (27426989635175090439/422849533750000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (8061/10000000000000000 : ℝ)*base86 + (8061/10000000000000000 : ℝ)*base88 + (8061/10000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(85723/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(85723/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (19636364921088758505657093/1121826025000000000000000000000 : ℝ) := by norm_num
    linear_combination (175564791699/200000000000 : ℝ)*(base7) + (262421/250000000000 : ℝ)*(base34) + (271697/1000000000000 : ℝ)*(base39) + (1830019/1000000000000 : ℝ)*(base53) + (38895769773/500000000000 : ℝ)*(base60) + (180716282837/100000000000 : ℝ)*(major_s2_0) + (903581939027/500000000000 : ℝ)*(major_s2_1) + (361432409607/200000000000 : ℝ)*(major_s2_2) + (26277779/500000000000 : ℝ)*(sp_s2_8) + (932564268859/500000000000 : ℝ)*(sp_s2_14) + (466269257961/250000000000 : ℝ)*(sp_s2_15) + (932565708711/500000000000 : ℝ)*(sp_s2_16) + (2089219208381/1000000000000 : ℝ)*(sp_s2_20) + (83138691/1000000000000 : ℝ)*(sp_s2_27) + (1211479438261/1000000000000 : ℝ)*(f.failure) + (932565708711/500000000000 : ℝ)*(f.sum) + (19195884124340191679/56258674150000000000000000000000 : ℝ)*base62 + (69002366668611/106898750000000000000000000 : ℝ)*base64 + (1998744160631551/4604950000000000000000000000 : ℝ)*base66 + (139299443243319/855190000000000000000000000 : ℝ)*base68 + (7736985813921602083/15705564350000000000000000000000 : ℝ)*base70 + (117471270598957/918250000000000000000000000 : ℝ)*base72 + (34309679319517/328925000000000000000000000 : ℝ)*base75 + (756112469673/2869531250000000000000000 : ℝ)*base76 + (37274893540095229317/84569906750000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (663/10000000000000000 : ℝ)*base86 + (663/10000000000000000 : ℝ)*base88 + (663/10000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-3831/5000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-3831/5000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (48994330517620458823459671/11218260250000000000000000000000 : ℝ) := by norm_num
    linear_combination (608687849591/1000000000000 : ℝ)*(base7) + (453561/125000000000 : ℝ)*(base16) + (4025619/1000000000000 : ℝ)*(base34) + (42516089527/62500000000 : ℝ)*(base43) + (817511923853/500000000000 : ℝ)*(major_s2_0) + (954770440893/1000000000000 : ℝ)*(major_s2_1) + (65401114933/40000000000 : ℝ)*(major_s2_2) + (42826779/500000000000 : ℝ)*(sp_s2_0) + (1079349/125000000000 : ℝ)*(sp_s2_9) + (64941583/1000000000000 : ℝ)*(sp_s2_20) + (560385929483/500000000000 : ℝ)*(sp_s2_21) + (1801115342087/1000000000000 : ℝ)*(sp_s2_22) + (1120852903351/1000000000000 : ℝ)*(sp_s2_23) + (426175615101/250000000000 : ℝ)*(sp_s2_27) + (219216715603/200000000000 : ℝ)*(f.failure) + (72044758823/40000000000 : ℝ)*(f.sum) + (156347942945477073/1004619181250000000000000000000 : ℝ)*base62 + (10698655881/15271250000000000000000000 : ℝ)*base65 + (913609300799911/2302475000000000000000000000 : ℝ)*base66 + (42629926928979/122170000000000000000000000 : ℝ)*base69 + (287113220324835221/2804565062500000000000000000000 : ℝ)*base71 + (1197481500646083/4591250000000000000000000000 : ℝ)*base72 + (66879855834749/328925000000000000000000000 : ℝ)*base75 + (51974590990363/229562500000000000000000000 : ℝ)*base77 + (45940568397610534883/422849533750000000000000000000000 : ℝ)*base79 + (49/2000000000000000 : ℝ)*base86 + (49/2000000000000000 : ℝ)*base88 + (49/2000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev1 : (0 : ℝ) ≤ ((3673/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3673/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(92099/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(92099/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-85519/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-85519/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((84979/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(84979/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(85723/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(85723/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-3831/5000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-3831/5000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c302060_s2 p hpa hpb X hX hprev1

#print axioms solution
