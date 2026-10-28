-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c302060_s4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:24:13.786329+00:00
-- url     : https://prove2.me/submissions/730ec9c3-b9b7-4fb8-a3e8-9d69de1a7b7d

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
theorem collision_support_c302060_s4_s4_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2244740621/10000000000 : ℝ)*x 0 + (2104687359/5000000000 : ℝ)*x 1 + (-6305813443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2244740621/10000000000 : ℝ)^131 ≤ (13849755227373/100000000000000 : ℝ)^99 := by
    have hnat : (2244740621 : ℕ)^131*100000000000000^99 ≤ 13849755227373^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244740621 10000000000 13849755227373 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2104687359/5000000000 : ℝ)^131 ≤ (31823838831521/100000000000000 : ℝ)^99 := by
    have hnat : (2104687359 : ℕ)^131*100000000000000^99 ≤ 31823838831521^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2104687359 5000000000 31823838831521 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6305813443/10000000000 : ℝ)^131 ≤ (54326405928403/100000000000000 : ℝ)^99 := by
    have hnat : (6305813443 : ℕ)^131*100000000000000^99 ≤ 54326405928403^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6305813443 10000000000 54326405928403 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2244740621/10000000000 : ℝ), (2104687359/5000000000 : ℝ), (-6305813443/10000000000 : ℝ)] ![(13849755227373/100000000000000 : ℝ), (31823838831521/100000000000000 : ℝ), (54326405928403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2244740621/10000000000 : ℝ)|^131 ≤ (13849755227373/100000000000000 : ℝ)^99
        have hw : |(-2244740621/10000000000 : ℝ)|=(2244740621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2104687359/5000000000 : ℝ)|^131 ≤ (31823838831521/100000000000000 : ℝ)^99
        have hw : |(2104687359/5000000000 : ℝ)|=(2104687359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6305813443/10000000000 : ℝ)|^131 ≤ (54326405928403/100000000000000 : ℝ)^99
        have hw : |(-6305813443/10000000000 : ℝ)|=(6305813443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302060_s4_s4_1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1119315667/2500000000 : ℝ)*x 0 + (-2546353099/10000000000 : ℝ)*x 1 + (-1460546977/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1119315667/2500000000 : ℝ)^131 ≤ (863273811203/2500000000000 : ℝ)^99 := by
    have hnat : (1119315667 : ℕ)^131*2500000000000^99 ≤ 863273811203^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119315667 2500000000 863273811203 2500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2546353099/10000000000 : ℝ)^131 ≤ (8182053751503/50000000000000 : ℝ)^99 := by
    have hnat : (2546353099 : ℕ)^131*50000000000000^99 ≤ 8182053751503^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2546353099 10000000000 8182053751503 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1460546977/2500000000 : ℝ)^131 ≤ (49104940032679/100000000000000 : ℝ)^99 := by
    have hnat : (1460546977 : ℕ)^131*100000000000000^99 ≤ 49104940032679^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1460546977 2500000000 49104940032679 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1119315667/2500000000 : ℝ), (-2546353099/10000000000 : ℝ), (-1460546977/2500000000 : ℝ)] ![(863273811203/2500000000000 : ℝ), (8182053751503/50000000000000 : ℝ), (49104940032679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1119315667/2500000000 : ℝ)|^131 ≤ (863273811203/2500000000000 : ℝ)^99
        have hw : |(1119315667/2500000000 : ℝ)|=(1119315667/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2546353099/10000000000 : ℝ)|^131 ≤ (8182053751503/50000000000000 : ℝ)^99
        have hw : |(-2546353099/10000000000 : ℝ)|=(2546353099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1460546977/2500000000 : ℝ)|^131 ≤ (49104940032679/100000000000000 : ℝ)^99
        have hw : |(-1460546977/2500000000 : ℝ)|=(1460546977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302060_s4_s4_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2370759101/5000000000 : ℝ)*x 0 + (5875594451/10000000000 : ℝ)*x 1 + (543339053/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2370759101/5000000000 : ℝ)^131 ≤ (232832432189/625000000000 : ℝ)^99 := by
    have hnat : (2370759101 : ℕ)^131*625000000000^99 ≤ 232832432189^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2370759101 5000000000 232832432189 625000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5875594451/10000000000 : ℝ)^131 ≤ (773075515427/1562500000000 : ℝ)^99 := by
    have hnat : (5875594451 : ℕ)^131*1562500000000^99 ≤ 773075515427^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5875594451 10000000000 773075515427 1562500000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543339053/2500000000 : ℝ)^131 ≤ (13269977843931/100000000000000 : ℝ)^99 := by
    have hnat : (543339053 : ℕ)^131*100000000000000^99 ≤ 13269977843931^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543339053 2500000000 13269977843931 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2370759101/5000000000 : ℝ), (5875594451/10000000000 : ℝ), (543339053/2500000000 : ℝ)] ![(232832432189/625000000000 : ℝ), (773075515427/1562500000000 : ℝ), (13269977843931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2370759101/5000000000 : ℝ)|^131 ≤ (232832432189/625000000000 : ℝ)^99
        have hw : |(2370759101/5000000000 : ℝ)|=(2370759101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5875594451/10000000000 : ℝ)|^131 ≤ (773075515427/1562500000000 : ℝ)^99
        have hw : |(5875594451/10000000000 : ℝ)|=(5875594451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(543339053/2500000000 : ℝ)|^131 ≤ (13269977843931/100000000000000 : ℝ)^99
        have hw : |(543339053/2500000000 : ℝ)|=(543339053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302060_s4_s4_6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1704559631/2500000000 : ℝ)*x 0 + (2236800451/5000000000 : ℝ)*x 1 + (-135055721/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1704559631/2500000000 : ℝ)^131 ≤ (12048685307887/20000000000000 : ℝ)^99 := by
    have hnat : (1704559631 : ℕ)^131*20000000000000^99 ≤ 12048685307887^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1704559631 2500000000 12048685307887 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2236800451/5000000000 : ℝ)^131 ≤ (34493587425167/100000000000000 : ℝ)^99 := by
    have hnat : (2236800451 : ℕ)^131*100000000000000^99 ≤ 34493587425167^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2236800451 5000000000 34493587425167 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135055721/1250000000 : ℝ)^131 ≤ (1052597204133/20000000000000 : ℝ)^99 := by
    have hnat : (135055721 : ℕ)^131*20000000000000^99 ≤ 1052597204133^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135055721 1250000000 1052597204133 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1704559631/2500000000 : ℝ), (2236800451/5000000000 : ℝ), (-135055721/1250000000 : ℝ)] ![(12048685307887/20000000000000 : ℝ), (34493587425167/100000000000000 : ℝ), (1052597204133/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1704559631/2500000000 : ℝ)|^131 ≤ (12048685307887/20000000000000 : ℝ)^99
        have hw : |(1704559631/2500000000 : ℝ)|=(1704559631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2236800451/5000000000 : ℝ)|^131 ≤ (34493587425167/100000000000000 : ℝ)^99
        have hw : |(2236800451/5000000000 : ℝ)|=(2236800451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-135055721/1250000000 : ℝ)|^131 ≤ (1052597204133/20000000000000 : ℝ)^99
        have hw : |(-135055721/1250000000 : ℝ)|=(135055721/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302060_s4_s4_7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-493615789/2500000000 : ℝ)*x 0 + (759375899/2000000000 : ℝ)*x 1 + (-6844319623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (493615789/2500000000 : ℝ)^131 ≤ (182614565617/1562500000000 : ℝ)^99 := by
    have hnat : (493615789 : ℕ)^131*1562500000000^99 ≤ 182614565617^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      493615789 2500000000 182614565617 1562500000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (759375899/2000000000 : ℝ)^131 ≤ (5552824676053/20000000000000 : ℝ)^99 := by
    have hnat : (759375899 : ℕ)^131*20000000000000^99 ≤ 5552824676053^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      759375899 2000000000 5552824676053 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6844319623/10000000000 : ℝ)^131 ≤ (30274272202249/50000000000000 : ℝ)^99 := by
    have hnat : (6844319623 : ℕ)^131*50000000000000^99 ≤ 30274272202249^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6844319623 10000000000 30274272202249 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-493615789/2500000000 : ℝ), (759375899/2000000000 : ℝ), (-6844319623/10000000000 : ℝ)] ![(182614565617/1562500000000 : ℝ), (5552824676053/20000000000000 : ℝ), (30274272202249/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-493615789/2500000000 : ℝ)|^131 ≤ (182614565617/1562500000000 : ℝ)^99
        have hw : |(-493615789/2500000000 : ℝ)|=(493615789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(759375899/2000000000 : ℝ)|^131 ≤ (5552824676053/20000000000000 : ℝ)^99
        have hw : |(759375899/2000000000 : ℝ)|=(759375899/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6844319623/10000000000 : ℝ)|^131 ≤ (30274272202249/50000000000000 : ℝ)^99
        have hw : |(-6844319623/10000000000 : ℝ)|=(6844319623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302060_s4_s4_8 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4067140059/10000000000 : ℝ)*x 0 + (-795494281/5000000000 : ℝ)*x 1 + (-3433266001/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4067140059/10000000000 : ℝ)^131 ≤ (30408762424107/100000000000000 : ℝ)^99 := by
    have hnat : (4067140059 : ℕ)^131*100000000000000^99 ≤ 30408762424107^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4067140059 10000000000 30408762424107 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (795494281/5000000000 : ℝ)^131 ≤ (1097817270487/12500000000000 : ℝ)^99 := by
    have hnat : (795494281 : ℕ)^131*12500000000000^99 ≤ 1097817270487^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      795494281 5000000000 1097817270487 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3433266001/5000000000 : ℝ)^131 ≤ (30404349698357/50000000000000 : ℝ)^99 := by
    have hnat : (3433266001 : ℕ)^131*50000000000000^99 ≤ 30404349698357^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3433266001 5000000000 30404349698357 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4067140059/10000000000 : ℝ), (-795494281/5000000000 : ℝ), (-3433266001/5000000000 : ℝ)] ![(30408762424107/100000000000000 : ℝ), (1097817270487/12500000000000 : ℝ), (30404349698357/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4067140059/10000000000 : ℝ)|^131 ≤ (30408762424107/100000000000000 : ℝ)^99
        have hw : |(4067140059/10000000000 : ℝ)|=(4067140059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-795494281/5000000000 : ℝ)|^131 ≤ (1097817270487/12500000000000 : ℝ)^99
        have hw : |(-795494281/5000000000 : ℝ)|=(795494281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3433266001/5000000000 : ℝ)|^131 ≤ (30404349698357/50000000000000 : ℝ)^99
        have hw : |(-3433266001/5000000000 : ℝ)|=(3433266001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302060_s4_s4_9 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4334637717/10000000000 : ℝ)*x 0 + (6844624433/10000000000 : ℝ)*x 1 + (1247375303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4334637717/10000000000 : ℝ)^131 ≤ (6616589831673/20000000000000 : ℝ)^99 := by
    have hnat : (4334637717 : ℕ)^131*20000000000000^99 ≤ 6616589831673^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4334637717 10000000000 6616589831673 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6844624433/10000000000 : ℝ)^131 ≤ (3784507034019/6250000000000 : ℝ)^99 := by
    have hnat : (6844624433 : ℕ)^131*6250000000000^99 ≤ 3784507034019^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6844624433 10000000000 3784507034019 6250000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1247375303/10000000000 : ℝ)^131 ≤ (3182469140991/50000000000000 : ℝ)^99 := by
    have hnat : (1247375303 : ℕ)^131*50000000000000^99 ≤ 3182469140991^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1247375303 10000000000 3182469140991 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4334637717/10000000000 : ℝ), (6844624433/10000000000 : ℝ), (1247375303/10000000000 : ℝ)] ![(6616589831673/20000000000000 : ℝ), (3784507034019/6250000000000 : ℝ), (3182469140991/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4334637717/10000000000 : ℝ)|^131 ≤ (6616589831673/20000000000000 : ℝ)^99
        have hw : |(4334637717/10000000000 : ℝ)|=(4334637717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6844624433/10000000000 : ℝ)|^131 ≤ (3784507034019/6250000000000 : ℝ)^99
        have hw : |(6844624433/10000000000 : ℝ)|=(6844624433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1247375303/10000000000 : ℝ)|^131 ≤ (3182469140991/50000000000000 : ℝ)^99
        have hw : |(1247375303/10000000000 : ℝ)|=(1247375303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302060_s4_s4_13 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6227533747/10000000000 : ℝ)*x 0 + (5572069113/10000000000 : ℝ)*x 1 + (-165853839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6227533747/10000000000 : ℝ)^131 ≤ (10687162110487/20000000000000 : ℝ)^99 := by
    have hnat : (6227533747 : ℕ)^131*20000000000000^99 ≤ 10687162110487^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6227533747 10000000000 10687162110487 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5572069113/10000000000 : ℝ)^131 ≤ (11530836779461/25000000000000 : ℝ)^99 := by
    have hnat : (5572069113 : ℕ)^131*25000000000000^99 ≤ 11530836779461^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5572069113 10000000000 11530836779461 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (165853839/10000000000 : ℝ)^131 ≤ (13776322369/3125000000000 : ℝ)^99 := by
    have hnat : (165853839 : ℕ)^131*3125000000000^99 ≤ 13776322369^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165853839 10000000000 13776322369 3125000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6227533747/10000000000 : ℝ), (5572069113/10000000000 : ℝ), (-165853839/10000000000 : ℝ)] ![(10687162110487/20000000000000 : ℝ), (11530836779461/25000000000000 : ℝ), (13776322369/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6227533747/10000000000 : ℝ)|^131 ≤ (10687162110487/20000000000000 : ℝ)^99
        have hw : |(6227533747/10000000000 : ℝ)|=(6227533747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5572069113/10000000000 : ℝ)|^131 ≤ (11530836779461/25000000000000 : ℝ)^99
        have hw : |(5572069113/10000000000 : ℝ)|=(5572069113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-165853839/10000000000 : ℝ)|^131 ≤ (13776322369/3125000000000 : ℝ)^99
        have hw : |(-165853839/10000000000 : ℝ)|=(165853839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302060_s4_s4_14 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-253465463/2000000000 : ℝ)*x 0 + (4339834583/10000000000 : ℝ)*x 1 + (-6828596281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (253465463/2000000000 : ℝ)^131 ≤ (6500001495531/100000000000000 : ℝ)^99 := by
    have hnat : (253465463 : ℕ)^131*100000000000000^99 ≤ 6500001495531^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253465463 2000000000 6500001495531 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4339834583/10000000000 : ℝ)^131 ≤ (8283860894891/25000000000000 : ℝ)^99 := by
    have hnat : (4339834583 : ℕ)^131*25000000000000^99 ≤ 8283860894891^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4339834583 10000000000 8283860894891 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6828596281/10000000000 : ℝ)^131 ≤ (1509113872721/2500000000000 : ℝ)^99 := by
    have hnat : (6828596281 : ℕ)^131*2500000000000^99 ≤ 1509113872721^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6828596281 10000000000 1509113872721 2500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-253465463/2000000000 : ℝ), (4339834583/10000000000 : ℝ), (-6828596281/10000000000 : ℝ)] ![(6500001495531/100000000000000 : ℝ), (8283860894891/25000000000000 : ℝ), (1509113872721/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-253465463/2000000000 : ℝ)|^131 ≤ (6500001495531/100000000000000 : ℝ)^99
        have hw : |(-253465463/2000000000 : ℝ)|=(253465463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4339834583/10000000000 : ℝ)|^131 ≤ (8283860894891/25000000000000 : ℝ)^99
        have hw : |(4339834583/10000000000 : ℝ)|=(4339834583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6828596281/10000000000 : ℝ)|^131 ≤ (1509113872721/2500000000000 : ℝ)^99
        have hw : |(-6828596281/10000000000 : ℝ)|=(6828596281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302060_s4_s4_15 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (505006201/1250000000 : ℝ)*x 0 + (-413118391/2500000000 : ℝ)*x 1 + (-3425404909/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (505006201/1250000000 : ℝ)^131 ≤ (7535258654259/25000000000000 : ℝ)^99 := by
    have hnat : (505006201 : ℕ)^131*25000000000000^99 ≤ 7535258654259^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505006201 1250000000 7535258654259 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (413118391/2500000000 : ℝ)^131 ≤ (9234434921939/100000000000000 : ℝ)^99 := by
    have hnat : (413118391 : ℕ)^131*100000000000000^99 ≤ 9234434921939^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413118391 2500000000 9234434921939 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3425404909/5000000000 : ℝ)^131 ≤ (30312265222021/50000000000000 : ℝ)^99 := by
    have hnat : (3425404909 : ℕ)^131*50000000000000^99 ≤ 30312265222021^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3425404909 5000000000 30312265222021 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(505006201/1250000000 : ℝ), (-413118391/2500000000 : ℝ), (-3425404909/5000000000 : ℝ)] ![(7535258654259/25000000000000 : ℝ), (9234434921939/100000000000000 : ℝ), (30312265222021/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(505006201/1250000000 : ℝ)|^131 ≤ (7535258654259/25000000000000 : ℝ)^99
        have hw : |(505006201/1250000000 : ℝ)|=(505006201/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-413118391/2500000000 : ℝ)|^131 ≤ (9234434921939/100000000000000 : ℝ)^99
        have hw : |(-413118391/2500000000 : ℝ)|=(413118391/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3425404909/5000000000 : ℝ)|^131 ≤ (30312265222021/50000000000000 : ℝ)^99
        have hw : |(-3425404909/5000000000 : ℝ)|=(3425404909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302060_s4_s4_16 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2902331647/5000000000 : ℝ)*x 0 + (1090912109/2000000000 : ℝ)*x 1 + (78943643/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2902331647/5000000000 : ℝ)^131 ≤ (24344011191231/50000000000000 : ℝ)^99 := by
    have hnat : (2902331647 : ℕ)^131*50000000000000^99 ≤ 24344011191231^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2902331647 5000000000 24344011191231 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1090912109/2000000000 : ℝ)^131 ≤ (2802541368173/6250000000000 : ℝ)^99 := by
    have hnat : (1090912109 : ℕ)^131*6250000000000^99 ≤ 2802541368173^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090912109 2000000000 2802541368173 6250000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (78943643/625000000 : ℝ)^131 ≤ (808914463627/12500000000000 : ℝ)^99 := by
    have hnat : (78943643 : ℕ)^131*12500000000000^99 ≤ 808914463627^99*625000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78943643 625000000 808914463627 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2902331647/5000000000 : ℝ), (1090912109/2000000000 : ℝ), (78943643/625000000 : ℝ)] ![(24344011191231/50000000000000 : ℝ), (2802541368173/6250000000000 : ℝ), (808914463627/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2902331647/5000000000 : ℝ)|^131 ≤ (24344011191231/50000000000000 : ℝ)^99
        have hw : |(2902331647/5000000000 : ℝ)|=(2902331647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1090912109/2000000000 : ℝ)|^131 ≤ (2802541368173/6250000000000 : ℝ)^99
        have hw : |(1090912109/2000000000 : ℝ)|=(1090912109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(78943643/625000000 : ℝ)|^131 ≤ (808914463627/12500000000000 : ℝ)^99
        have hw : |(78943643/625000000 : ℝ)|=(78943643/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302060_s4_s4_20 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3897188947/5000000000 : ℝ)*x 0 + (3773094567/10000000000 : ℝ)*x 1 + (-197038327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3897188947/5000000000 : ℝ)^131 ≤ (71912059543129/100000000000000 : ℝ)^99 := by
    have hnat : (3897188947 : ℕ)^131*100000000000000^99 ≤ 71912059543129^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3897188947 5000000000 71912059543129 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3773094567/10000000000 : ℝ)^131 ≤ (27534215127881/100000000000000 : ℝ)^99 := by
    have hnat : (3773094567 : ℕ)^131*100000000000000^99 ≤ 27534215127881^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3773094567 10000000000 27534215127881 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (197038327/10000000000 : ℝ)^131 ≤ (553725310889/100000000000000 : ℝ)^99 := by
    have hnat : (197038327 : ℕ)^131*100000000000000^99 ≤ 553725310889^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197038327 10000000000 553725310889 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3897188947/5000000000 : ℝ), (3773094567/10000000000 : ℝ), (-197038327/10000000000 : ℝ)] ![(71912059543129/100000000000000 : ℝ), (27534215127881/100000000000000 : ℝ), (553725310889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3897188947/5000000000 : ℝ)|^131 ≤ (71912059543129/100000000000000 : ℝ)^99
        have hw : |(3897188947/5000000000 : ℝ)|=(3897188947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3773094567/10000000000 : ℝ)|^131 ≤ (27534215127881/100000000000000 : ℝ)^99
        have hw : |(3773094567/10000000000 : ℝ)|=(3773094567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-197038327/10000000000 : ℝ)|^131 ≤ (553725310889/100000000000000 : ℝ)^99
        have hw : |(-197038327/10000000000 : ℝ)|=(197038327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302060_s4_s4_21 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-121117099/1250000000 : ℝ)*x 0 + (5426128423/10000000000 : ℝ)*x 1 + (-1200785887/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (121117099/1250000000 : ℝ)^131 ≤ (1139130231989/25000000000000 : ℝ)^99 := by
    have hnat : (121117099 : ℕ)^131*25000000000000^99 ≤ 1139130231989^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121117099 1250000000 1139130231989 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5426128423/10000000000 : ℝ)^131 ≤ (44531638627693/100000000000000 : ℝ)^99 := by
    have hnat : (5426128423 : ℕ)^131*100000000000000^99 ≤ 44531638627693^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426128423 10000000000 44531638627693 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1200785887/2000000000 : ℝ)^131 ≤ (25455920217283/50000000000000 : ℝ)^99 := by
    have hnat : (1200785887 : ℕ)^131*50000000000000^99 ≤ 25455920217283^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1200785887 2000000000 25455920217283 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-121117099/1250000000 : ℝ), (5426128423/10000000000 : ℝ), (-1200785887/2000000000 : ℝ)] ![(1139130231989/25000000000000 : ℝ), (44531638627693/100000000000000 : ℝ), (25455920217283/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-121117099/1250000000 : ℝ)|^131 ≤ (1139130231989/25000000000000 : ℝ)^99
        have hw : |(-121117099/1250000000 : ℝ)|=(121117099/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5426128423/10000000000 : ℝ)|^131 ≤ (44531638627693/100000000000000 : ℝ)^99
        have hw : |(5426128423/10000000000 : ℝ)|=(5426128423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1200785887/2000000000 : ℝ)|^131 ≤ (25455920217283/50000000000000 : ℝ)^99
        have hw : |(-1200785887/2000000000 : ℝ)|=(1200785887/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302060_s4_s4_22 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5835555351/10000000000 : ℝ)*x 0 + (-1412500933/10000000000 : ℝ)*x 1 + (-5327688709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5835555351/10000000000 : ℝ)^131 ≤ (3064449111501/6250000000000 : ℝ)^99 := by
    have hnat : (5835555351 : ℕ)^131*6250000000000^99 ≤ 3064449111501^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5835555351 10000000000 3064449111501 6250000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1412500933/10000000000 : ℝ)^131 ≤ (3751523181817/50000000000000 : ℝ)^99 := by
    have hnat : (1412500933 : ℕ)^131*50000000000000^99 ≤ 3751523181817^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1412500933 10000000000 3751523181817 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5327688709/10000000000 : ℝ)^131 ≤ (21732883919133/50000000000000 : ℝ)^99 := by
    have hnat : (5327688709 : ℕ)^131*50000000000000^99 ≤ 21732883919133^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5327688709 10000000000 21732883919133 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5835555351/10000000000 : ℝ), (-1412500933/10000000000 : ℝ), (-5327688709/10000000000 : ℝ)] ![(3064449111501/6250000000000 : ℝ), (3751523181817/50000000000000 : ℝ), (21732883919133/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5835555351/10000000000 : ℝ)|^131 ≤ (3064449111501/6250000000000 : ℝ)^99
        have hw : |(5835555351/10000000000 : ℝ)|=(5835555351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1412500933/10000000000 : ℝ)|^131 ≤ (3751523181817/50000000000000 : ℝ)^99
        have hw : |(-1412500933/10000000000 : ℝ)|=(1412500933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5327688709/10000000000 : ℝ)|^131 ≤ (21732883919133/50000000000000 : ℝ)^99
        have hw : |(-5327688709/10000000000 : ℝ)|=(5327688709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302060_s4_s4_23 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (260056739/625000000 : ℝ)*x 0 + (6511693403/10000000000 : ℝ)*x 1 + (100550113/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (260056739/625000000 : ℝ)^131 ≤ (313398835397/1000000000000 : ℝ)^99 := by
    have hnat : (260056739 : ℕ)^131*1000000000000^99 ≤ 313398835397^99*625000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260056739 625000000 313398835397 1000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6511693403/10000000000 : ℝ)^131 ≤ (28342868970633/50000000000000 : ℝ)^99 := by
    have hnat : (6511693403 : ℕ)^131*50000000000000^99 ≤ 28342868970633^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6511693403 10000000000 28342868970633 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (100550113/500000000 : ℝ)^131 ≤ (11974378498867/100000000000000 : ℝ)^99 := by
    have hnat : (100550113 : ℕ)^131*100000000000000^99 ≤ 11974378498867^99*500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100550113 500000000 11974378498867 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(260056739/625000000 : ℝ), (6511693403/10000000000 : ℝ), (100550113/500000000 : ℝ)] ![(313398835397/1000000000000 : ℝ), (28342868970633/50000000000000 : ℝ), (11974378498867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(260056739/625000000 : ℝ)|^131 ≤ (313398835397/1000000000000 : ℝ)^99
        have hw : |(260056739/625000000 : ℝ)|=(260056739/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6511693403/10000000000 : ℝ)|^131 ≤ (28342868970633/50000000000000 : ℝ)^99
        have hw : |(6511693403/10000000000 : ℝ)|=(6511693403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(100550113/500000000 : ℝ)|^131 ≤ (11974378498867/100000000000000 : ℝ)^99
        have hw : |(100550113/500000000 : ℝ)|=(100550113/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302060_s4_s4_27 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4042614277/5000000000 : ℝ)*x 0 + (3354967513/10000000000 : ℝ)*x 1 + (-147559437/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4042614277/5000000000 : ℝ)^131 ≤ (75484097882709/100000000000000 : ℝ)^99 := by
    have hnat : (4042614277 : ℕ)^131*100000000000000^99 ≤ 75484097882709^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4042614277 5000000000 75484097882709 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3354967513/10000000000 : ℝ)^131 ≤ (2357086131549/10000000000000 : ℝ)^99 := by
    have hnat : (3354967513 : ℕ)^131*10000000000000^99 ≤ 2357086131549^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3354967513 10000000000 2357086131549 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (147559437/5000000000 : ℝ)^131 ≤ (236260198689/25000000000000 : ℝ)^99 := by
    have hnat : (147559437 : ℕ)^131*25000000000000^99 ≤ 236260198689^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147559437 5000000000 236260198689 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4042614277/5000000000 : ℝ), (3354967513/10000000000 : ℝ), (-147559437/5000000000 : ℝ)] ![(75484097882709/100000000000000 : ℝ), (2357086131549/10000000000000 : ℝ), (236260198689/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4042614277/5000000000 : ℝ)|^131 ≤ (75484097882709/100000000000000 : ℝ)^99
        have hw : |(4042614277/5000000000 : ℝ)|=(4042614277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3354967513/10000000000 : ℝ)|^131 ≤ (2357086131549/10000000000000 : ℝ)^99
        have hw : |(3354967513/10000000000 : ℝ)|=(3354967513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-147559437/5000000000 : ℝ)|^131 ≤ (236260198689/25000000000000 : ℝ)^99
        have hw : |(-147559437/5000000000 : ℝ)|=(147559437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c302060_s4 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev3 : (0 : ℝ) ≤ ((74657/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(74657/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(76033/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(76033/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-64177/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-64177/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((26293/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(26293/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(56531/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(56531/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-9979/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-9979/25000 : ℝ)*X 1 2) := by
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
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base18 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  rcases hprev3 with ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩
  have s4_pow0 : (74657/100000 : ℝ) ^ (65/16 : ℝ) ≤ (3050345590786192037/10000000000000000000 : ℝ) := by
    have hpowers : (74657/100000 : ℝ)^65 ≤ (3050345590786192037/10000000000000000000 : ℝ)^16 := by
      have hnat : (74657 : ℕ)^65*10000000000000000000^16 ≤ 3050345590786192037^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        74657 100000 3050345590786192037 10000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (74657/100000 : ℝ)) (X := (3050345590786192037/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s4_corner0a : (13050345590786192037/10000000000000000000 : ℝ) ≤ (10677284211804809/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (13050345590786192037/10000000000000000000 : ℝ)^16 ≤ (10677284211804809/10000000000000000 : ℝ)^65 := by
      have hnat : (13050345590786192037 : ℕ)^16*10000000000000000^65 ≤ 10677284211804809^65*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13050345590786192037 10000000000000000000 10677284211804809 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10677284211804809/10000000000000000 : ℝ)) (X := (13050345590786192037/10000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s4_corner0b : (8050345590786192037/5000000000000000000 : ℝ) ≤ (11243863746803627/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (8050345590786192037/5000000000000000000 : ℝ)^16 ≤ (11243863746803627/10000000000000000 : ℝ)^65 := by
      have hnat : (8050345590786192037 : ℕ)^16*10000000000000000^65 ≤ 11243863746803627^65*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8050345590786192037 5000000000000000000 11243863746803627 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11243863746803627/10000000000000000 : ℝ)) (X := (8050345590786192037/5000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s4_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(677284211804809/7465700000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(2341237747929/30850000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (74657/100000 : ℝ)) (alpha := (677284211804809/7465700000000000 : ℝ)) (beta := (2341237747929/30850000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow0,s4_corner0a]) (by linarith only [s4_pow0,s4_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (74657/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(677284211804809/7465700000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(2341237747929/30850000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow1 : (76033/100000 : ℝ) ^ (65/16 : ℝ) ≤ (1642635270041644033/5000000000000000000 : ℝ) := by
    have hpowers : (76033/100000 : ℝ)^65 ≤ (1642635270041644033/5000000000000000000 : ℝ)^16 := by
      have hnat : (76033 : ℕ)^65*5000000000000000000^16 ≤ 1642635270041644033^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        76033 100000 1642635270041644033 5000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (76033/100000 : ℝ)) (X := (1642635270041644033/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s4_corner1a : (6642635270041644033/5000000000000000000 : ℝ) ≤ (2144855776272941/2000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (6642635270041644033/5000000000000000000 : ℝ)^16 ≤ (2144855776272941/2000000000000000 : ℝ)^65 := by
      have hnat : (6642635270041644033 : ℕ)^16*2000000000000000^65 ≤ 2144855776272941^65*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6642635270041644033 5000000000000000000 2144855776272941 2000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2144855776272941/2000000000000000 : ℝ)) (X := (6642635270041644033/5000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s4_corner1b : (4142635270041644033/2500000000000000000 : ℝ) ≤ (5661878873453357/5000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (4142635270041644033/2500000000000000000 : ℝ)^16 ≤ (5661878873453357/5000000000000000 : ℝ)^65 := by
      have hnat : (4142635270041644033 : ℕ)^16*5000000000000000^65 ≤ 5661878873453357^65*2500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4142635270041644033 2500000000000000000 5661878873453357 5000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5661878873453357/5000000000000000 : ℝ)) (X := (4142635270041644033/2500000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s4_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(144855776272941/1520660000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(599478865542009/7603300000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (76033/100000 : ℝ)) (alpha := (144855776272941/1520660000000000 : ℝ)) (beta := (599478865542009/7603300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow1,s4_corner1a]) (by linarith only [s4_pow1,s4_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (76033/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(144855776272941/1520660000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(599478865542009/7603300000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow2 : (64177/100000 : ℝ) ^ (65/16 : ℝ) ≤ (2062475857377279139/12500000000000000000 : ℝ) := by
    have hpowers : (64177/100000 : ℝ)^65 ≤ (2062475857377279139/12500000000000000000 : ℝ)^16 := by
      have hnat : (64177 : ℕ)^65*12500000000000000000^16 ≤ 2062475857377279139^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64177 100000 2062475857377279139 12500000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (64177/100000 : ℝ)) (X := (2062475857377279139/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s4_corner2a : (14562475857377279139/12500000000000000000 : ℝ) ≤ (2595770025097959/2500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (14562475857377279139/12500000000000000000 : ℝ)^16 ≤ (2595770025097959/2500000000000000 : ℝ)^65 := by
      have hnat : (14562475857377279139 : ℕ)^16*2500000000000000^65 ≤ 2595770025097959^65*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14562475857377279139 12500000000000000000 2595770025097959 2500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2595770025097959/2500000000000000 : ℝ)) (X := (14562475857377279139/12500000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s4_corner2b : (8312475857377279139/6250000000000000000 : ℝ) ≤ (1072719677711379/1000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (8312475857377279139/6250000000000000000 : ℝ)^16 ≤ (1072719677711379/1000000000000000 : ℝ)^65 := by
      have hnat : (8312475857377279139 : ℕ)^16*1000000000000000^65 ≤ 1072719677711379^65*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8312475857377279139 6250000000000000000 1072719677711379 1000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1072719677711379/1000000000000000 : ℝ)) (X := (8312475857377279139/6250000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s4_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(95770025097959/1604425000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(172058338360977/3208850000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (64177/100000 : ℝ)) (alpha := (95770025097959/1604425000000000 : ℝ)) (beta := (172058338360977/3208850000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow2,s4_corner2a]) (by linarith only [s4_pow2,s4_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (64177/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(95770025097959/1604425000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(172058338360977/3208850000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s4_0 : ((-2244740621/10000000000 : ℝ)*X 0 0+(2104687359/5000000000 : ℝ)*X 0 1+(-6305813443/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302060_s4_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_1 : ((1119315667/2500000000 : ℝ)*X 1 0+(-2546353099/10000000000 : ℝ)*X 1 1+(-1460546977/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302060_s4_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_2 : ((2370759101/5000000000 : ℝ)*X 2 0+(5875594451/10000000000 : ℝ)*X 2 1+(543339053/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302060_s4_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_6 : ((1704559631/2500000000 : ℝ)*X 0 0+(2236800451/5000000000 : ℝ)*X 0 1+(-135055721/1250000000 : ℝ)*X 0 2+(1704559631/2500000000 : ℝ)*X 1 0+(2236800451/5000000000 : ℝ)*X 1 1+(-135055721/1250000000 : ℝ)*X 1 2+(1704559631/2500000000 : ℝ)*X 2 0+(2236800451/5000000000 : ℝ)*X 2 1+(-135055721/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302060_s4_s4_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_7 : ((-493615789/2500000000 : ℝ)*X 0 0+(759375899/2000000000 : ℝ)*X 0 1+(-6844319623/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302060_s4_s4_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_8 : ((4067140059/10000000000 : ℝ)*X 1 0+(-795494281/5000000000 : ℝ)*X 1 1+(-3433266001/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302060_s4_s4_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_9 : ((4334637717/10000000000 : ℝ)*X 2 0+(6844624433/10000000000 : ℝ)*X 2 1+(1247375303/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302060_s4_s4_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_13 : ((6227533747/10000000000 : ℝ)*X 0 0+(5572069113/10000000000 : ℝ)*X 0 1+(-165853839/10000000000 : ℝ)*X 0 2+(6227533747/10000000000 : ℝ)*X 1 0+(5572069113/10000000000 : ℝ)*X 1 1+(-165853839/10000000000 : ℝ)*X 1 2+(6227533747/10000000000 : ℝ)*X 2 0+(5572069113/10000000000 : ℝ)*X 2 1+(-165853839/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302060_s4_s4_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_14 : ((-253465463/2000000000 : ℝ)*X 0 0+(4339834583/10000000000 : ℝ)*X 0 1+(-6828596281/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302060_s4_s4_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_15 : ((505006201/1250000000 : ℝ)*X 1 0+(-413118391/2500000000 : ℝ)*X 1 1+(-3425404909/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302060_s4_s4_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_16 : ((2902331647/5000000000 : ℝ)*X 2 0+(1090912109/2000000000 : ℝ)*X 2 1+(78943643/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302060_s4_s4_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_20 : ((3897188947/5000000000 : ℝ)*X 0 0+(3773094567/10000000000 : ℝ)*X 0 1+(-197038327/10000000000 : ℝ)*X 0 2+(3897188947/5000000000 : ℝ)*X 1 0+(3773094567/10000000000 : ℝ)*X 1 1+(-197038327/10000000000 : ℝ)*X 1 2+(3897188947/5000000000 : ℝ)*X 2 0+(3773094567/10000000000 : ℝ)*X 2 1+(-197038327/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302060_s4_s4_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_21 : ((-121117099/1250000000 : ℝ)*X 0 0+(5426128423/10000000000 : ℝ)*X 0 1+(-1200785887/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302060_s4_s4_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_22 : ((5835555351/10000000000 : ℝ)*X 1 0+(-1412500933/10000000000 : ℝ)*X 1 1+(-5327688709/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302060_s4_s4_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_23 : ((260056739/625000000 : ℝ)*X 2 0+(6511693403/10000000000 : ℝ)*X 2 1+(100550113/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302060_s4_s4_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_27 : ((4042614277/5000000000 : ℝ)*X 0 0+(3354967513/10000000000 : ℝ)*X 0 1+(-147559437/5000000000 : ℝ)*X 0 2+(4042614277/5000000000 : ℝ)*X 1 0+(3354967513/10000000000 : ℝ)*X 1 1+(-147559437/5000000000 : ℝ)*X 1 2+(4042614277/5000000000 : ℝ)*X 2 0+(3354967513/10000000000 : ℝ)*X 2 1+(-147559437/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302060_s4_s4_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s4_0 : (0 : ℝ) ≤ ((26293/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(26293/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1483889276050703531070527079/243978492050000000000000000000000 : ℝ) := by norm_num
    linear_combination (56583/250000000000 : ℝ)*(base5) + (1973053/500000000000 : ℝ)*(base39) + (791879/1000000000000 : ℝ)*(base49) + (176260734739/500000000000 : ℝ)*(base59) + (5184149182931/1000000000000 : ℝ)*(major_s4_0) + (5184149182931/1000000000000 : ℝ)*(major_s4_1) + (5184149182931/1000000000000 : ℝ)*(major_s4_2) + (6892966726029/1000000000000 : ℝ)*(sp_s4_7) + (3445946384997/500000000000 : ℝ)*(sp_s4_8) + (1723225221167/250000000000 : ℝ)*(sp_s4_9) + (695065877229/200000000000 : ℝ)*(sp_s4_13) + (267273509/250000000000 : ℝ)*(sp_s4_15) + (4861999/1000000000000 : ℝ)*(sp_s4_22) + (16516923/250000000000 : ℝ)*(sp_s4_23) + (868832403119/250000000000 : ℝ)*(f.failure) + (6892966726029/1000000000000 : ℝ)*(f.sum) + (39108278279915070047/487956984100000000000000000000000 : ℝ)*base62 + (1534291802228487/3208850000000000000000000000 : ℝ)*base64 + (3187944580116639/7603300000000000000000000000 : ℝ)*base67 + (29336682048759/401106250000000000000000000 : ℝ)*base68 + (9730894639273455687/19165049156000000000000000000000 : ℝ)*base70 + (11810652966631/30850000000000000000000000 : ℝ)*base72 + (212393974850457/1520660000000000000000000000 : ℝ)*base75 + (1535066891737329/7465700000000000000000000000 : ℝ)*base77 + (524387281588626087/4691236100000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (1377/2500000000000000 : ℝ)*base86 + (1377/2500000000000000 : ℝ)*base88 + (1377/2500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s4_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(56531/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(56531/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (243282221263024971237791416463361/18214702280976850000000000000000000000 : ℝ) := by norm_num
    linear_combination (2415307/1000000000000 : ℝ)*(base5) + (167977/1000000000000 : ℝ)*(base18) + (152219187/7812500000 : ℝ)*(base59) + (5023625977721/1000000000000 : ℝ)*(major_s4_0) + (5023625977721/1000000000000 : ℝ)*(major_s4_1) + (5023625977721/1000000000000 : ℝ)*(major_s4_2) + (32083569/1000000000000 : ℝ)*(sp_s4_2) + (2312681/200000000000 : ℝ)*(sp_s4_6) + (75127171/1000000000000 : ℝ)*(sp_s4_7) + (6679453680883/1000000000000 : ℝ)*(sp_s4_14) + (3339764320039/500000000000 : ℝ)*(sp_s4_15) + (417468696237/62500000000 : ℝ)*(sp_s4_16) + (3367524509159/1000000000000 : ℝ)*(sp_s4_20) + (18020739/100000000000 : ℝ)*(sp_s4_27) + (3367718695261/1000000000000 : ℝ)*(f.failure) + (3339764404027/500000000000 : ℝ)*(f.sum) + (101229654236308109117/487956984100000000000000000000000 : ℝ)*base62 + (568347848924803/802212500000000000000000000 : ℝ)*base64 + (1346445706642659/7603300000000000000000000000 : ℝ)*base67 + (498279856147343/802212500000000000000000000 : ℝ)*base68 + (7219330367107242091/19165049156000000000000000000000 : ℝ)*base70 + (15622621912527/15425000000000000000000000 : ℝ)*base73 + (250732269972531/1520660000000000000000000000 : ℝ)*base74 + (259386732433151/7465700000000000000000000000 : ℝ)*base76 + (138877952603554197/4691236100000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (1663/10000000000000000 : ℝ)*base86 + (1663/10000000000000000 : ℝ)*base88 + (1663/10000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s4_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-9979/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-9979/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2687255101234372335584458248669/413970506385837500000000000000000000 : ℝ) := by norm_num
    linear_combination (1320169/200000000000 : ℝ)*(base11) + (11238314851/31250000000 : ℝ)*(base39) + (129473/250000000000 : ℝ)*(base50) + (3872484630443/1000000000000 : ℝ)*(major_s4_0) + (3872484630443/1000000000000 : ℝ)*(major_s4_1) + (3872484630443/1000000000000 : ℝ)*(major_s4_2) + (581633/40000000000 : ℝ)*(sp_s4_0) + (1553783/500000000000 : ℝ)*(sp_s4_1) + (53164673/1000000000000 : ℝ)*(sp_s4_9) + (45049/15625000000 : ℝ)*(sp_s4_20) + (5148924885187/1000000000000 : ℝ)*(sp_s4_21) + (514894291929/100000000000 : ℝ)*(sp_s4_22) + (5148892862183/1000000000000 : ℝ)*(sp_s4_23) + (1298009093541/500000000000 : ℝ)*(sp_s4_27) + (1298010535109/500000000000 : ℝ)*(f.failure) + (643618253357/125000000000 : ℝ)*(f.sum) + (130100773876334060791/487956984100000000000000000000000 : ℝ)*base62 + (694770641961119/802212500000000000000000000 : ℝ)*base64 + (5703377551936787/7603300000000000000000000000 : ℝ)*base67 + (129955285365061/200553125000000000000000000 : ℝ)*base68 + (2137456342323292073/8711385980000000000000000000000 : ℝ)*base70 + (1172432810823/30850000000000000000000000 : ℝ)*base72 + (965305340235907/1520660000000000000000000000 : ℝ)*base74 + (269013249796103/678700000000000000000000000 : ℝ)*base76 + (1702777026437861909/4691236100000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (5953/5000000000000000 : ℝ)*base87 + (5953/5000000000000000 : ℝ)*base89 + (5953/5000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev3 : (0 : ℝ) ≤ ((74657/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(74657/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(76033/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(76033/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-64177/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-64177/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((26293/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(26293/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(56531/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(56531/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-9979/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-9979/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c302060_s4 p hpa hpb X hX hprev3

#print axioms solution
