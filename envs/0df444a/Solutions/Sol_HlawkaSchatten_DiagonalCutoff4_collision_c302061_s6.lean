-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c302061_s6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:24:22.640601+00:00
-- url     : https://prove2.me/submissions/1575b81b-6d31-4190-a8b5-6ce841783bca

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
theorem collision_support_c302061_s6_s6_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2360014547/10000000000 : ℝ)*x 0 + (4592693921/10000000000 : ℝ)*x 1 + (5876555897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2360014547/10000000000 : ℝ)^131 ≤ (14798593305563/100000000000000 : ℝ)^99 := by
    have hnat : (2360014547 : ℕ)^131*100000000000000^99 ≤ 14798593305563^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2360014547 10000000000 14798593305563 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4592693921/10000000000 : ℝ)^131 ≤ (35713860408603/100000000000000 : ℝ)^99 := by
    have hnat : (4592693921 : ℕ)^131*100000000000000^99 ≤ 35713860408603^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4592693921 10000000000 35713860408603 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5876555897/10000000000 : ℝ)^131 ≤ (1546485820937/3125000000000 : ℝ)^99 := by
    have hnat : (5876555897 : ℕ)^131*3125000000000^99 ≤ 1546485820937^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5876555897 10000000000 1546485820937 3125000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2360014547/10000000000 : ℝ), (4592693921/10000000000 : ℝ), (5876555897/10000000000 : ℝ)] ![(14798593305563/100000000000000 : ℝ), (35713860408603/100000000000000 : ℝ), (1546485820937/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2360014547/10000000000 : ℝ)|^131 ≤ (14798593305563/100000000000000 : ℝ)^99
        have hw : |(-2360014547/10000000000 : ℝ)|=(2360014547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4592693921/10000000000 : ℝ)|^131 ≤ (35713860408603/100000000000000 : ℝ)^99
        have hw : |(4592693921/10000000000 : ℝ)|=(4592693921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5876555897/10000000000 : ℝ)|^131 ≤ (1546485820937/3125000000000 : ℝ)^99
        have hw : |(5876555897/10000000000 : ℝ)|=(5876555897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302061_s6_s6_1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4749271721/10000000000 : ℝ)*x 0 + (-1236653447/5000000000 : ℝ)*x 1 + (1411170063/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4749271721/10000000000 : ℝ)^131 ≤ (7466763794793/20000000000000 : ℝ)^99 := by
    have hnat : (4749271721 : ℕ)^131*20000000000000^99 ≤ 7466763794793^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4749271721 10000000000 7466763794793 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1236653447/5000000000 : ℝ)^131 ≤ (1968230067661/12500000000000 : ℝ)^99 := by
    have hnat : (1236653447 : ℕ)^131*12500000000000^99 ≤ 1968230067661^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1236653447 5000000000 1968230067661 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1411170063/2500000000 : ℝ)^131 ≤ (46920340459759/100000000000000 : ℝ)^99 := by
    have hnat : (1411170063 : ℕ)^131*100000000000000^99 ≤ 46920340459759^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1411170063 2500000000 46920340459759 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4749271721/10000000000 : ℝ), (-1236653447/5000000000 : ℝ), (1411170063/2500000000 : ℝ)] ![(7466763794793/20000000000000 : ℝ), (1968230067661/12500000000000 : ℝ), (46920340459759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4749271721/10000000000 : ℝ)|^131 ≤ (7466763794793/20000000000000 : ℝ)^99
        have hw : |(4749271721/10000000000 : ℝ)|=(4749271721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1236653447/5000000000 : ℝ)|^131 ≤ (1968230067661/12500000000000 : ℝ)^99
        have hw : |(-1236653447/5000000000 : ℝ)|=(1236653447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1411170063/2500000000 : ℝ)|^131 ≤ (46920340459759/100000000000000 : ℝ)^99
        have hw : |(1411170063/2500000000 : ℝ)|=(1411170063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302061_s6_s6_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (966820779/2000000000 : ℝ)*x 0 + (125056853/200000000 : ℝ)*x 1 + (-745372161/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (966820779/2000000000 : ℝ)^131 ≤ (19109384776233/50000000000000 : ℝ)^99 := by
    have hnat : (966820779 : ℕ)^131*50000000000000^99 ≤ 19109384776233^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      966820779 2000000000 19109384776233 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (125056853/200000000 : ℝ)^131 ≤ (53723358737043/100000000000000 : ℝ)^99 := by
    have hnat : (125056853 : ℕ)^131*100000000000000^99 ≤ 53723358737043^99*200000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125056853 200000000 53723358737043 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (745372161/5000000000 : ℝ)^131 ≤ (402893585011/5000000000000 : ℝ)^99 := by
    have hnat : (745372161 : ℕ)^131*5000000000000^99 ≤ 402893585011^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      745372161 5000000000 402893585011 5000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(966820779/2000000000 : ℝ), (125056853/200000000 : ℝ), (-745372161/5000000000 : ℝ)] ![(19109384776233/50000000000000 : ℝ), (53723358737043/100000000000000 : ℝ), (402893585011/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(966820779/2000000000 : ℝ)|^131 ≤ (19109384776233/50000000000000 : ℝ)^99
        have hw : |(966820779/2000000000 : ℝ)|=(966820779/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(125056853/200000000 : ℝ)|^131 ≤ (53723358737043/100000000000000 : ℝ)^99
        have hw : |(125056853/200000000 : ℝ)|=(125056853/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-745372161/5000000000 : ℝ)|^131 ≤ (402893585011/5000000000000 : ℝ)^99
        have hw : |(-745372161/5000000000 : ℝ)|=(745372161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302061_s6_s6_6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5938598711/10000000000 : ℝ)*x 0 + (3186697667/10000000000 : ℝ)*x 1 + (3800645463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5938598711/10000000000 : ℝ)^131 ≤ (25090038688219/50000000000000 : ℝ)^99 := by
    have hnat : (5938598711 : ℕ)^131*50000000000000^99 ≤ 25090038688219^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5938598711 10000000000 25090038688219 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3186697667/10000000000 : ℝ)^131 ≤ (11009677049419/50000000000000 : ℝ)^99 := by
    have hnat : (3186697667 : ℕ)^131*50000000000000^99 ≤ 11009677049419^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3186697667 10000000000 11009677049419 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3800645463/10000000000 : ℝ)^131 ≤ (27800568507843/100000000000000 : ℝ)^99 := by
    have hnat : (3800645463 : ℕ)^131*100000000000000^99 ≤ 27800568507843^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3800645463 10000000000 27800568507843 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5938598711/10000000000 : ℝ), (3186697667/10000000000 : ℝ), (3800645463/10000000000 : ℝ)] ![(25090038688219/50000000000000 : ℝ), (11009677049419/50000000000000 : ℝ), (27800568507843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5938598711/10000000000 : ℝ)|^131 ≤ (25090038688219/50000000000000 : ℝ)^99
        have hw : |(5938598711/10000000000 : ℝ)|=(5938598711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3186697667/10000000000 : ℝ)|^131 ≤ (11009677049419/50000000000000 : ℝ)^99
        have hw : |(3186697667/10000000000 : ℝ)|=(3186697667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3800645463/10000000000 : ℝ)|^131 ≤ (27800568507843/100000000000000 : ℝ)^99
        have hw : |(3800645463/10000000000 : ℝ)|=(3800645463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302061_s6_s6_7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2319298447/10000000000 : ℝ)*x 0 + (1929604673/5000000000 : ℝ)*x 1 + (3276822453/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2319298447/10000000000 : ℝ)^131 ≤ (903856334309/6250000000000 : ℝ)^99 := by
    have hnat : (2319298447 : ℕ)^131*6250000000000^99 ≤ 903856334309^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2319298447 10000000000 903856334309 6250000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1929604673/5000000000 : ℝ)^131 ≤ (14184408799877/50000000000000 : ℝ)^99 := by
    have hnat : (1929604673 : ℕ)^131*50000000000000^99 ≤ 14184408799877^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1929604673 5000000000 14184408799877 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3276822453/5000000000 : ℝ)^131 ≤ (7146185130869/12500000000000 : ℝ)^99 := by
    have hnat : (3276822453 : ℕ)^131*12500000000000^99 ≤ 7146185130869^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3276822453 5000000000 7146185130869 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2319298447/10000000000 : ℝ), (1929604673/5000000000 : ℝ), (3276822453/5000000000 : ℝ)] ![(903856334309/6250000000000 : ℝ), (14184408799877/50000000000000 : ℝ), (7146185130869/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2319298447/10000000000 : ℝ)|^131 ≤ (903856334309/6250000000000 : ℝ)^99
        have hw : |(-2319298447/10000000000 : ℝ)|=(2319298447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1929604673/5000000000 : ℝ)|^131 ≤ (14184408799877/50000000000000 : ℝ)^99
        have hw : |(1929604673/5000000000 : ℝ)|=(1929604673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3276822453/5000000000 : ℝ)|^131 ≤ (7146185130869/12500000000000 : ℝ)^99
        have hw : |(3276822453/5000000000 : ℝ)|=(3276822453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302061_s6_s6_8 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2163367759/5000000000 : ℝ)*x 0 + (-1865443423/10000000000 : ℝ)*x 1 + (6465625247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163367759/5000000000 : ℝ)^131 ≤ (660063333881/2000000000000 : ℝ)^99 := by
    have hnat : (2163367759 : ℕ)^131*2000000000000^99 ≤ 660063333881^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163367759 5000000000 660063333881 2000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1865443423/10000000000 : ℝ)^131 ≤ (10841148168019/100000000000000 : ℝ)^99 := by
    have hnat : (1865443423 : ℕ)^131*100000000000000^99 ≤ 10841148168019^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1865443423 10000000000 10841148168019 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6465625247/10000000000 : ℝ)^131 ≤ (56155685125619/100000000000000 : ℝ)^99 := by
    have hnat : (6465625247 : ℕ)^131*100000000000000^99 ≤ 56155685125619^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6465625247 10000000000 56155685125619 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2163367759/5000000000 : ℝ), (-1865443423/10000000000 : ℝ), (6465625247/10000000000 : ℝ)] ![(660063333881/2000000000000 : ℝ), (10841148168019/100000000000000 : ℝ), (56155685125619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2163367759/5000000000 : ℝ)|^131 ≤ (660063333881/2000000000000 : ℝ)^99
        have hw : |(2163367759/5000000000 : ℝ)|=(2163367759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1865443423/10000000000 : ℝ)|^131 ≤ (10841148168019/100000000000000 : ℝ)^99
        have hw : |(-1865443423/10000000000 : ℝ)|=(1865443423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6465625247/10000000000 : ℝ)|^131 ≤ (56155685125619/100000000000000 : ℝ)^99
        have hw : |(6465625247/10000000000 : ℝ)|=(6465625247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302061_s6_s6_9 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4412311103/10000000000 : ℝ)*x 0 + (7051506607/10000000000 : ℝ)*x 1 + (-366058813/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4412311103/10000000000 : ℝ)^131 ≤ (16934825923377/50000000000000 : ℝ)^99 := by
    have hnat : (4412311103 : ℕ)^131*50000000000000^99 ≤ 16934825923377^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4412311103 10000000000 16934825923377 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7051506607/10000000000 : ℝ)^131 ≤ (62985666419719/100000000000000 : ℝ)^99 := by
    have hnat : (7051506607 : ℕ)^131*100000000000000^99 ≤ 62985666419719^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7051506607 10000000000 62985666419719 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (366058813/5000000000 : ℝ)^131 ≤ (786170431963/25000000000000 : ℝ)^99 := by
    have hnat : (366058813 : ℕ)^131*25000000000000^99 ≤ 786170431963^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366058813 5000000000 786170431963 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4412311103/10000000000 : ℝ), (7051506607/10000000000 : ℝ), (-366058813/5000000000 : ℝ)] ![(16934825923377/50000000000000 : ℝ), (62985666419719/100000000000000 : ℝ), (786170431963/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4412311103/10000000000 : ℝ)|^131 ≤ (16934825923377/50000000000000 : ℝ)^99
        have hw : |(4412311103/10000000000 : ℝ)|=(4412311103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7051506607/10000000000 : ℝ)|^131 ≤ (62985666419719/100000000000000 : ℝ)^99
        have hw : |(7051506607/10000000000 : ℝ)|=(7051506607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-366058813/5000000000 : ℝ)|^131 ≤ (786170431963/25000000000000 : ℝ)^99
        have hw : |(-366058813/5000000000 : ℝ)|=(366058813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302061_s6_s6_13 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1454239897/2500000000 : ℝ)*x 0 + (4493767749/10000000000 : ℝ)*x 1 + (1279747783/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1454239897/2500000000 : ℝ)^131 ≤ (48824544818621/100000000000000 : ℝ)^99 := by
    have hnat : (1454239897 : ℕ)^131*100000000000000^99 ≤ 48824544818621^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1454239897 2500000000 48824544818621 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4493767749/10000000000 : ℝ)^131 ≤ (34699494469833/100000000000000 : ℝ)^99 := by
    have hnat : (4493767749 : ℕ)^131*100000000000000^99 ≤ 34699494469833^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493767749 10000000000 34699494469833 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1279747783/5000000000 : ℝ)^131 ≤ (4118990174121/25000000000000 : ℝ)^99 := by
    have hnat : (1279747783 : ℕ)^131*25000000000000^99 ≤ 4118990174121^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1279747783 5000000000 4118990174121 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1454239897/2500000000 : ℝ), (4493767749/10000000000 : ℝ), (1279747783/5000000000 : ℝ)] ![(48824544818621/100000000000000 : ℝ), (34699494469833/100000000000000 : ℝ), (4118990174121/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1454239897/2500000000 : ℝ)|^131 ≤ (48824544818621/100000000000000 : ℝ)^99
        have hw : |(1454239897/2500000000 : ℝ)|=(1454239897/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4493767749/10000000000 : ℝ)|^131 ≤ (34699494469833/100000000000000 : ℝ)^99
        have hw : |(4493767749/10000000000 : ℝ)|=(4493767749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1279747783/5000000000 : ℝ)|^131 ≤ (4118990174121/25000000000000 : ℝ)^99
        have hw : |(1279747783/5000000000 : ℝ)|=(1279747783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302061_s6_s6_14 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-277632043/2000000000 : ℝ)*x 0 + (572447339/1250000000 : ℝ)*x 1 + (818329511/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (277632043/2000000000 : ℝ)^131 ≤ (7332437176469/100000000000000 : ℝ)^99 := by
    have hnat : (277632043 : ℕ)^131*100000000000000^99 ≤ 7332437176469^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277632043 2000000000 7332437176469 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (572447339/1250000000 : ℝ)^131 ≤ (35578970332841/100000000000000 : ℝ)^99 := by
    have hnat : (572447339 : ℕ)^131*100000000000000^99 ≤ 35578970332841^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      572447339 1250000000 35578970332841 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (818329511/1250000000 : ℝ)^131 ≤ (57088592480489/100000000000000 : ℝ)^99 := by
    have hnat : (818329511 : ℕ)^131*100000000000000^99 ≤ 57088592480489^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      818329511 1250000000 57088592480489 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-277632043/2000000000 : ℝ), (572447339/1250000000 : ℝ), (818329511/1250000000 : ℝ)] ![(7332437176469/100000000000000 : ℝ), (35578970332841/100000000000000 : ℝ), (57088592480489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-277632043/2000000000 : ℝ)|^131 ≤ (7332437176469/100000000000000 : ℝ)^99
        have hw : |(-277632043/2000000000 : ℝ)|=(277632043/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(572447339/1250000000 : ℝ)|^131 ≤ (35578970332841/100000000000000 : ℝ)^99
        have hw : |(572447339/1250000000 : ℝ)|=(572447339/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(818329511/1250000000 : ℝ)|^131 ≤ (57088592480489/100000000000000 : ℝ)^99
        have hw : |(818329511/1250000000 : ℝ)|=(818329511/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302061_s6_s6_15 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (522361221/1250000000 : ℝ)*x 0 + (-129093937/625000000 : ℝ)*x 1 + (645861287/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (522361221/1250000000 : ℝ)^131 ≤ (31519226756759/100000000000000 : ℝ)^99 := by
    have hnat : (522361221 : ℕ)^131*100000000000000^99 ≤ 31519226756759^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522361221 1250000000 31519226756759 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129093937/625000000 : ℝ)^131 ≤ (12405664605467/100000000000000 : ℝ)^99 := by
    have hnat : (129093937 : ℕ)^131*100000000000000^99 ≤ 12405664605467^99*625000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129093937 625000000 12405664605467 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (645861287/1000000000 : ℝ)^131 ≤ (1401877715593/2500000000000 : ℝ)^99 := by
    have hnat : (645861287 : ℕ)^131*2500000000000^99 ≤ 1401877715593^99*1000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      645861287 1000000000 1401877715593 2500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(522361221/1250000000 : ℝ), (-129093937/625000000 : ℝ), (645861287/1000000000 : ℝ)] ![(31519226756759/100000000000000 : ℝ), (12405664605467/100000000000000 : ℝ), (1401877715593/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(522361221/1250000000 : ℝ)|^131 ≤ (31519226756759/100000000000000 : ℝ)^99
        have hw : |(522361221/1250000000 : ℝ)|=(522361221/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-129093937/625000000 : ℝ)|^131 ≤ (12405664605467/100000000000000 : ℝ)^99
        have hw : |(-129093937/625000000 : ℝ)|=(129093937/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(645861287/1000000000 : ℝ)|^131 ≤ (1401877715593/2500000000000 : ℝ)^99
        have hw : |(645861287/1000000000 : ℝ)|=(645861287/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302061_s6_s6_16 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5868787391/10000000000 : ℝ)*x 0 + (355596341/625000000 : ℝ)*x 1 + (-739129059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5868787391/10000000000 : ℝ)^131 ≤ (49400998908561/100000000000000 : ℝ)^99 := by
    have hnat : (5868787391 : ℕ)^131*100000000000000^99 ≤ 49400998908561^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5868787391 10000000000 49400998908561 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (355596341/625000000 : ℝ)^131 ≤ (47414406848609/100000000000000 : ℝ)^99 := by
    have hnat : (355596341 : ℕ)^131*100000000000000^99 ≤ 47414406848609^99*625000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      355596341 625000000 47414406848609 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (739129059/10000000000 : ℝ)^131 ≤ (3184594229967/100000000000000 : ℝ)^99 := by
    have hnat : (739129059 : ℕ)^131*100000000000000^99 ≤ 3184594229967^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      739129059 10000000000 3184594229967 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5868787391/10000000000 : ℝ), (355596341/625000000 : ℝ), (-739129059/10000000000 : ℝ)] ![(49400998908561/100000000000000 : ℝ), (47414406848609/100000000000000 : ℝ), (3184594229967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5868787391/10000000000 : ℝ)|^131 ≤ (49400998908561/100000000000000 : ℝ)^99
        have hw : |(5868787391/10000000000 : ℝ)|=(5868787391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(355596341/625000000 : ℝ)|^131 ≤ (47414406848609/100000000000000 : ℝ)^99
        have hw : |(355596341/625000000 : ℝ)|=(355596341/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-739129059/10000000000 : ℝ)|^131 ≤ (3184594229967/100000000000000 : ℝ)^99
        have hw : |(-739129059/10000000000 : ℝ)|=(739129059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302061_s6_s6_20 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (286086403/400000000 : ℝ)*x 0 + (2876346847/10000000000 : ℝ)*x 1 + (40209377/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (286086403/400000000 : ℝ)^131 ≤ (641780670111/1000000000000 : ℝ)^99 := by
    have hnat : (286086403 : ℕ)^131*1000000000000^99 ≤ 641780670111^99*400000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      286086403 400000000 641780670111 1000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2876346847/10000000000 : ℝ)^131 ≤ (9613715382243/50000000000000 : ℝ)^99 := by
    have hnat : (2876346847 : ℕ)^131*50000000000000^99 ≤ 9613715382243^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2876346847 10000000000 9613715382243 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40209377/156250000 : ℝ)^131 ≤ (8297251102719/50000000000000 : ℝ)^99 := by
    have hnat : (40209377 : ℕ)^131*50000000000000^99 ≤ 8297251102719^99*156250000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40209377 156250000 8297251102719 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(286086403/400000000 : ℝ), (2876346847/10000000000 : ℝ), (40209377/156250000 : ℝ)] ![(641780670111/1000000000000 : ℝ), (9613715382243/50000000000000 : ℝ), (8297251102719/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(286086403/400000000 : ℝ)|^131 ≤ (641780670111/1000000000000 : ℝ)^99
        have hw : |(286086403/400000000 : ℝ)|=(286086403/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2876346847/10000000000 : ℝ)|^131 ≤ (9613715382243/50000000000000 : ℝ)^99
        have hw : |(2876346847/10000000000 : ℝ)|=(2876346847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(40209377/156250000 : ℝ)|^131 ≤ (8297251102719/50000000000000 : ℝ)^99
        have hw : |(40209377/156250000 : ℝ)|=(40209377/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302061_s6_s6_21 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-678570263/5000000000 : ℝ)*x 0 + (5320513173/10000000000 : ℝ)*x 1 + (2938624349/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (678570263/5000000000 : ℝ)^131 ≤ (3558206337437/50000000000000 : ℝ)^99 := by
    have hnat : (678570263 : ℕ)^131*50000000000000^99 ≤ 3558206337437^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678570263 5000000000 3558206337437 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5320513173/10000000000 : ℝ)^131 ≤ (21694160437737/50000000000000 : ℝ)^99 := by
    have hnat : (5320513173 : ℕ)^131*50000000000000^99 ≤ 21694160437737^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5320513173 10000000000 21694160437737 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2938624349/5000000000 : ℝ)^131 ≤ (247476332117/500000000000 : ℝ)^99 := by
    have hnat : (2938624349 : ℕ)^131*500000000000^99 ≤ 247476332117^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2938624349 5000000000 247476332117 500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-678570263/5000000000 : ℝ), (5320513173/10000000000 : ℝ), (2938624349/5000000000 : ℝ)] ![(3558206337437/50000000000000 : ℝ), (21694160437737/50000000000000 : ℝ), (247476332117/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-678570263/5000000000 : ℝ)|^131 ≤ (3558206337437/50000000000000 : ℝ)^99
        have hw : |(-678570263/5000000000 : ℝ)|=(678570263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5320513173/10000000000 : ℝ)|^131 ≤ (21694160437737/50000000000000 : ℝ)^99
        have hw : |(5320513173/10000000000 : ℝ)|=(5320513173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2938624349/5000000000 : ℝ)|^131 ≤ (247476332117/500000000000 : ℝ)^99
        have hw : |(2938624349/5000000000 : ℝ)|=(2938624349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302061_s6_s6_22 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2907116533/5000000000 : ℝ)*x 0 + (-736745763/5000000000 : ℝ)*x 1 + (5309640217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2907116533/5000000000 : ℝ)^131 ≤ (48794264923947/100000000000000 : ℝ)^99 := by
    have hnat : (2907116533 : ℕ)^131*100000000000000^99 ≤ 48794264923947^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2907116533 5000000000 48794264923947 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (736745763/5000000000 : ℝ)^131 ≤ (7934703793659/100000000000000 : ℝ)^99 := by
    have hnat : (736745763 : ℕ)^131*100000000000000^99 ≤ 7934703793659^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      736745763 5000000000 7934703793659 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5309640217/10000000000 : ℝ)^131 ≤ (43271031270243/100000000000000 : ℝ)^99 := by
    have hnat : (5309640217 : ℕ)^131*100000000000000^99 ≤ 43271031270243^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309640217 10000000000 43271031270243 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2907116533/5000000000 : ℝ), (-736745763/5000000000 : ℝ), (5309640217/10000000000 : ℝ)] ![(48794264923947/100000000000000 : ℝ), (7934703793659/100000000000000 : ℝ), (43271031270243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2907116533/5000000000 : ℝ)|^131 ≤ (48794264923947/100000000000000 : ℝ)^99
        have hw : |(2907116533/5000000000 : ℝ)|=(2907116533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-736745763/5000000000 : ℝ)|^131 ≤ (7934703793659/100000000000000 : ℝ)^99
        have hw : |(-736745763/5000000000 : ℝ)|=(736745763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5309640217/10000000000 : ℝ)|^131 ≤ (43271031270243/100000000000000 : ℝ)^99
        have hw : |(5309640217/10000000000 : ℝ)|=(5309640217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302061_s6_s6_23 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (103894029/250000000 : ℝ)*x 0 + (3494762143/5000000000 : ℝ)*x 1 + (-630514153/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103894029/250000000 : ℝ)^131 ≤ (391107490617/1250000000000 : ℝ)^99 := by
    have hnat : (103894029 : ℕ)^131*1250000000000^99 ≤ 391107490617^99*250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103894029 250000000 391107490617 1250000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3494762143/5000000000 : ℝ)^131 ≤ (15563528638577/25000000000000 : ℝ)^99 := by
    have hnat : (3494762143 : ℕ)^131*25000000000000^99 ≤ 15563528638577^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3494762143 5000000000 15563528638577 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (630514153/5000000000 : ℝ)^131 ≤ (1614321545523/25000000000000 : ℝ)^99 := by
    have hnat : (630514153 : ℕ)^131*25000000000000^99 ≤ 1614321545523^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      630514153 5000000000 1614321545523 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(103894029/250000000 : ℝ), (3494762143/5000000000 : ℝ), (-630514153/5000000000 : ℝ)] ![(391107490617/1250000000000 : ℝ), (15563528638577/25000000000000 : ℝ), (1614321545523/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(103894029/250000000 : ℝ)|^131 ≤ (391107490617/1250000000000 : ℝ)^99
        have hw : |(103894029/250000000 : ℝ)|=(103894029/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3494762143/5000000000 : ℝ)|^131 ≤ (15563528638577/25000000000000 : ℝ)^99
        have hw : |(3494762143/5000000000 : ℝ)|=(3494762143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-630514153/5000000000 : ℝ)|^131 ≤ (1614321545523/25000000000000 : ℝ)^99
        have hw : |(-630514153/5000000000 : ℝ)|=(630514153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302061_s6_s6_27 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (294710361/400000000 : ℝ)*x 0 + (623937301/2500000000 : ℝ)*x 1 + (2657330989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (294710361/400000000 : ℝ)^131 ≤ (16687602224997/25000000000000 : ℝ)^99 := by
    have hnat : (294710361 : ℕ)^131*25000000000000^99 ≤ 16687602224997^99*400000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      294710361 400000000 16687602224997 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (623937301/2500000000 : ℝ)^131 ≤ (7967586836229/50000000000000 : ℝ)^99 := by
    have hnat : (623937301 : ℕ)^131*50000000000000^99 ≤ 7967586836229^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      623937301 2500000000 7967586836229 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2657330989/10000000000 : ℝ)^131 ≤ (8657208705867/50000000000000 : ℝ)^99 := by
    have hnat : (2657330989 : ℕ)^131*50000000000000^99 ≤ 8657208705867^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2657330989 10000000000 8657208705867 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(294710361/400000000 : ℝ), (623937301/2500000000 : ℝ), (2657330989/10000000000 : ℝ)] ![(16687602224997/25000000000000 : ℝ), (7967586836229/50000000000000 : ℝ), (8657208705867/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(294710361/400000000 : ℝ)|^131 ≤ (16687602224997/25000000000000 : ℝ)^99
        have hw : |(294710361/400000000 : ℝ)|=(294710361/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(623937301/2500000000 : ℝ)|^131 ≤ (7967586836229/50000000000000 : ℝ)^99
        have hw : |(623937301/2500000000 : ℝ)|=(623937301/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2657330989/10000000000 : ℝ)|^131 ≤ (8657208705867/50000000000000 : ℝ)^99
        have hw : |(2657330989/10000000000 : ℝ)|=(2657330989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c302061_s6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev5 : (0 : ℝ) ≤ ((52273/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(52273/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2941/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2941/5000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(26719/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(26719/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((33917/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(33917/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39177/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(39177/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8989/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8989/25000 : ℝ)*X 1 2) := by
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
  have main2 : (4769/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4769/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
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
  rcases hprev5 with ⟨ratio_s5_0,ratio_s5_1,ratio_s5_2⟩
  have s6_pow0 : (52273/100000 : ℝ) ^ (65/16 : ℝ) ≤ (1433943489170614283/20000000000000000000 : ℝ) := by
    have hpowers : (52273/100000 : ℝ)^65 ≤ (1433943489170614283/20000000000000000000 : ℝ)^16 := by
      have hnat : (52273 : ℕ)^65*20000000000000000000^16 ≤ 1433943489170614283^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52273 100000 1433943489170614283 20000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (52273/100000 : ℝ)) (X := (1433943489170614283/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s6_corner0a : (21433943489170614283/20000000000000000000 : ℝ) ≤ (5085953250711343/5000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (21433943489170614283/20000000000000000000 : ℝ)^16 ≤ (5085953250711343/5000000000000000 : ℝ)^65 := by
      have hnat : (21433943489170614283 : ℕ)^16*5000000000000000^65 ≤ 5085953250711343^65*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21433943489170614283 20000000000000000000 5085953250711343 5000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5085953250711343/5000000000000000 : ℝ)) (X := (21433943489170614283/20000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s6_corner0b : (11433943489170614283/10000000000000000000 : ℝ) ≤ (2583837447134699/2500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (11433943489170614283/10000000000000000000 : ℝ)^16 ≤ (2583837447134699/2500000000000000 : ℝ)^65 := by
      have hnat : (11433943489170614283 : ℕ)^16*2500000000000000^65 ≤ 2583837447134699^65*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11433943489170614283 10000000000000000000 2583837447134699 2500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2583837447134699/2500000000000000 : ℝ)) (X := (11433943489170614283/10000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s6_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(85953250711343/2613650000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(16344328711611/522730000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (52273/100000 : ℝ)) (alpha := (85953250711343/2613650000000000 : ℝ)) (beta := (16344328711611/522730000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow0,s6_corner0a]) (by linarith only [s6_pow0,s6_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (52273/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(85953250711343/2613650000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(16344328711611/522730000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s6_pow1 : (2941/5000 : ℝ) ^ (65/16 : ℝ) ≤ (1447456122004627759/12500000000000000000 : ℝ) := by
    have hpowers : (2941/5000 : ℝ)^65 ≤ (1447456122004627759/12500000000000000000 : ℝ)^16 := by
      have hnat : (2941 : ℕ)^65*12500000000000000000^16 ≤ 1447456122004627759^16*5000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2941 5000 1447456122004627759 12500000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2941/5000 : ℝ)) (X := (1447456122004627759/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s6_corner1a : (13947456122004627759/12500000000000000000 : ℝ) ≤ (2054675413648311/2000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (13947456122004627759/12500000000000000000 : ℝ)^16 ≤ (2054675413648311/2000000000000000 : ℝ)^65 := by
      have hnat : (13947456122004627759 : ℕ)^16*2000000000000000^65 ≤ 2054675413648311^65*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13947456122004627759 12500000000000000000 2054675413648311 2000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2054675413648311/2000000000000000 : ℝ)) (X := (13947456122004627759/12500000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s6_corner1b : (7697456122004627759/6250000000000000000 : ℝ) ≤ (2105226586648771/2000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (7697456122004627759/6250000000000000000 : ℝ)^16 ≤ (2105226586648771/2000000000000000 : ℝ)^65 := by
      have hnat : (7697456122004627759 : ℕ)^16*2000000000000000^65 ≤ 2105226586648771^65*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7697456122004627759 6250000000000000000 2105226586648771 2000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2105226586648771/2000000000000000 : ℝ)) (X := (7697456122004627759/6250000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s6_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(54675413648311/1176400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(2527558650023/58820000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (2941/5000 : ℝ)) (alpha := (54675413648311/1176400000000000 : ℝ)) (beta := (2527558650023/58820000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow1,s6_corner1a]) (by linarith only [s6_pow1,s6_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (2941/5000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(54675413648311/1176400000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(2527558650023/58820000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s6_pow2 : (26719/50000 : ℝ) ^ (65/16 : ℝ) ≤ (7841360483655297581/100000000000000000000 : ℝ) := by
    have hpowers : (26719/50000 : ℝ)^65 ≤ (7841360483655297581/100000000000000000000 : ℝ)^16 := by
      have hnat : (26719 : ℕ)^65*100000000000000000000^16 ≤ 7841360483655297581^16*50000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26719 50000 7841360483655297581 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26719/50000 : ℝ)) (X := (7841360483655297581/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s6_corner2a : (107841360483655297581/100000000000000000000 : ℝ) ≤ (2037512292979083/2000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (107841360483655297581/100000000000000000000 : ℝ)^16 ≤ (2037512292979083/2000000000000000 : ℝ)^65 := by
      have hnat : (107841360483655297581 : ℕ)^16*2000000000000000^65 ≤ 2037512292979083^65*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        107841360483655297581 100000000000000000000 2037512292979083 2000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2037512292979083/2000000000000000 : ℝ)) (X := (107841360483655297581/100000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s6_corner2b : (57841360483655297581/50000000000000000000 : ℝ) ≤ (2073021369878381/2000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (57841360483655297581/50000000000000000000 : ℝ)^16 ≤ (2073021369878381/2000000000000000 : ℝ)^65 := by
      have hnat : (57841360483655297581 : ℕ)^16*2000000000000000^65 ≤ 2073021369878381^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57841360483655297581 50000000000000000000 2073021369878381 2000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2073021369878381/2000000000000000 : ℝ)) (X := (57841360483655297581/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s6_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(37512292979083/1068760000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(17754538449649/534380000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (26719/50000 : ℝ)) (alpha := (37512292979083/1068760000000000 : ℝ)) (beta := (17754538449649/534380000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow2,s6_corner2a]) (by linarith only [s6_pow2,s6_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (26719/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(37512292979083/1068760000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(17754538449649/534380000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s6_0 : ((-2360014547/10000000000 : ℝ)*X 0 0+(4592693921/10000000000 : ℝ)*X 0 1+(5876555897/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302061_s6_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_1 : ((4749271721/10000000000 : ℝ)*X 1 0+(-1236653447/5000000000 : ℝ)*X 1 1+(1411170063/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302061_s6_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_2 : ((966820779/2000000000 : ℝ)*X 2 0+(125056853/200000000 : ℝ)*X 2 1+(-745372161/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302061_s6_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_6 : ((5938598711/10000000000 : ℝ)*X 0 0+(3186697667/10000000000 : ℝ)*X 0 1+(3800645463/10000000000 : ℝ)*X 0 2+(5938598711/10000000000 : ℝ)*X 1 0+(3186697667/10000000000 : ℝ)*X 1 1+(3800645463/10000000000 : ℝ)*X 1 2+(5938598711/10000000000 : ℝ)*X 2 0+(3186697667/10000000000 : ℝ)*X 2 1+(3800645463/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302061_s6_s6_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_7 : ((-2319298447/10000000000 : ℝ)*X 0 0+(1929604673/5000000000 : ℝ)*X 0 1+(3276822453/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302061_s6_s6_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_8 : ((2163367759/5000000000 : ℝ)*X 1 0+(-1865443423/10000000000 : ℝ)*X 1 1+(6465625247/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302061_s6_s6_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_9 : ((4412311103/10000000000 : ℝ)*X 2 0+(7051506607/10000000000 : ℝ)*X 2 1+(-366058813/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302061_s6_s6_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_13 : ((1454239897/2500000000 : ℝ)*X 0 0+(4493767749/10000000000 : ℝ)*X 0 1+(1279747783/5000000000 : ℝ)*X 0 2+(1454239897/2500000000 : ℝ)*X 1 0+(4493767749/10000000000 : ℝ)*X 1 1+(1279747783/5000000000 : ℝ)*X 1 2+(1454239897/2500000000 : ℝ)*X 2 0+(4493767749/10000000000 : ℝ)*X 2 1+(1279747783/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302061_s6_s6_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_14 : ((-277632043/2000000000 : ℝ)*X 0 0+(572447339/1250000000 : ℝ)*X 0 1+(818329511/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302061_s6_s6_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_15 : ((522361221/1250000000 : ℝ)*X 1 0+(-129093937/625000000 : ℝ)*X 1 1+(645861287/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302061_s6_s6_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_16 : ((5868787391/10000000000 : ℝ)*X 2 0+(355596341/625000000 : ℝ)*X 2 1+(-739129059/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302061_s6_s6_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_20 : ((286086403/400000000 : ℝ)*X 0 0+(2876346847/10000000000 : ℝ)*X 0 1+(40209377/156250000 : ℝ)*X 0 2+(286086403/400000000 : ℝ)*X 1 0+(2876346847/10000000000 : ℝ)*X 1 1+(40209377/156250000 : ℝ)*X 1 2+(286086403/400000000 : ℝ)*X 2 0+(2876346847/10000000000 : ℝ)*X 2 1+(40209377/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302061_s6_s6_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_21 : ((-678570263/5000000000 : ℝ)*X 0 0+(5320513173/10000000000 : ℝ)*X 0 1+(2938624349/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302061_s6_s6_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_22 : ((2907116533/5000000000 : ℝ)*X 1 0+(-736745763/5000000000 : ℝ)*X 1 1+(5309640217/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302061_s6_s6_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_23 : ((103894029/250000000 : ℝ)*X 2 0+(3494762143/5000000000 : ℝ)*X 2 1+(-630514153/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302061_s6_s6_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_27 : ((294710361/400000000 : ℝ)*X 0 0+(623937301/2500000000 : ℝ)*X 0 1+(2657330989/10000000000 : ℝ)*X 0 2+(294710361/400000000 : ℝ)*X 1 0+(623937301/2500000000 : ℝ)*X 1 1+(2657330989/10000000000 : ℝ)*X 1 2+(294710361/400000000 : ℝ)*X 2 0+(623937301/2500000000 : ℝ)*X 2 1+(2657330989/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302061_s6_s6_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s6_0 : (0 : ℝ) ≤ ((33917/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(33917/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (10273594223577422287346527725021/821528521213400000000000000000000000 : ℝ) := by norm_num
    linear_combination (96011/200000000000 : ℝ)*(base50) + (739969648261/1000000000000 : ℝ)*(base59) + (4855589478511/1000000000000 : ℝ)*(major_s6_0) + (4855589478511/1000000000000 : ℝ)*(major_s6_1) + (4855589478511/1000000000000 : ℝ)*(major_s6_2) + (8933771/250000000000 : ℝ)*(sp_s6_0) + (2618143/50000000000 : ℝ)*(sp_s6_1) + (49853729/1000000000000 : ℝ)*(sp_s6_6) + (403504250499/62500000000 : ℝ)*(sp_s6_7) + (322787233829/50000000000 : ℝ)*(sp_s6_8) + (1291193898109/200000000000 : ℝ)*(sp_s6_9) + (3255021191729/1000000000000 : ℝ)*(sp_s6_13) + (76675907/250000000000 : ℝ)*(sp_s6_15) + (134252523/1000000000000 : ℝ)*(sp_s6_23) + (3255071045459/1000000000000 : ℝ)*(f.failure) + (1614025935767/250000000000 : ℝ)*(f.sum) + (14649826544054607529/31432231600000000000000000000000 : ℝ)*base63 + (126689813386613/106876000000000000000000000 : ℝ)*base65 + (34907475646927/58820000000000000000000000 : ℝ)*base67 + (902909759112513/1068760000000000000000000000 : ℝ)*base69 + (92936826963856616379/139668228700000000000000000000000 : ℝ)*base71 + (92552611282227/130682500000000000000000000 : ℝ)*base73 + (1131832187959881/1176400000000000000000000000 : ℝ)*base75 + (475129965375867/653412500000000000000000000 : ℝ)*base77 + (347060304087816153/3074697860000000000000000000000 : ℝ)*base79 + (1903/10000000000000000 : ℝ)*base87 + (1903/10000000000000000 : ℝ)*base89 + (1903/10000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s6_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39177/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(39177/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2841383226907072790605991967159/164305704242680000000000000000000000 : ℝ) := by norm_num
    linear_combination (282931/250000000000 : ℝ)*(base39) + (227867/250000000000 : ℝ)*(base49) + (381945143113/1000000000000 : ℝ)*(base59) + (187517209197/40000000000 : ℝ)*(major_s6_0) + (187517209197/40000000000 : ℝ)*(major_s6_1) + (187517209197/40000000000 : ℝ)*(major_s6_2) + (19713801/500000000000 : ℝ)*(sp_s6_2) + (12069483/500000000000 : ℝ)*(sp_s6_6) + (88501777/1000000000000 : ℝ)*(sp_s6_7) + (6233089898189/1000000000000 : ℝ)*(sp_s6_14) + (6233178399967/1000000000000 : ℝ)*(sp_s6_15) + (1558284743091/250000000000 : ℝ)*(sp_s6_16) + (3142402404823/1000000000000 : ℝ)*(sp_s6_20) + (124875831/500000000000 : ℝ)*(sp_s6_27) + (785669073863/250000000000 : ℝ)*(f.failure) + (6233178399967/1000000000000 : ℝ)*(f.sum) + (2077746981937707511/6286446320000000000000000000000 : ℝ)*base63 + (114349643907557/534380000000000000000000000 : ℝ)*base65 + (44272722994127/58820000000000000000000000 : ℝ)*base67 + (79343880277643/1068760000000000000000000000 : ℝ)*base69 + (6393194814080619427/27933645740000000000000000000000 : ℝ)*base71 + (82205088457671/104546000000000000000000000 : ℝ)*base72 + (25704645342963/47056000000000000000000000 : ℝ)*base75 + (861702074401/2613650000000000000000000 : ℝ)*base77 + (578514870917983/122987914400000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (1871/2500000000000000 : ℝ)*base87 + (1871/2500000000000000 : ℝ)*base89 + (1871/2500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s6_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8989/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8989/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (379209279057558877427094267/30746978600000000000000000000000 : ℝ) := by norm_num
    linear_combination (708053/100000000000 : ℝ)*(base15) + (27499046589/100000000000 : ℝ)*(base40) + (396888793031/1000000000000 : ℝ)*(base59) + (4312387279537/1000000000000 : ℝ)*(major_s6_0) + (4312387279537/1000000000000 : ℝ)*(major_s6_1) + (4312387279537/1000000000000 : ℝ)*(major_s6_2) + (2583637/500000000000 : ℝ)*(sp_s6_0) + (79168441/500000000000 : ℝ)*(sp_s6_2) + (10355053/200000000000 : ℝ)*(sp_s6_9) + (749561/1562500000 : ℝ)*(sp_s6_20) + (358365249787/62500000000 : ℝ)*(sp_s6_21) + (5733842083337/1000000000000 : ℝ)*(sp_s6_22) + (5733639051719/1000000000000 : ℝ)*(sp_s6_23) + (289044156509/100000000000 : ℝ)*(sp_s6_27) + (289092128413/100000000000 : ℝ)*(f.failure) + (2866924581933/500000000000 : ℝ)*(f.sum) + (446394395736131343/31432231600000000000000000000000 : ℝ)*base63 + (74276577819107/534380000000000000000000000 : ℝ)*base65 + (24916128983983/58820000000000000000000000 : ℝ)*base67 + (243754082194421/1068760000000000000000000000 : ℝ)*base68 + (36484393858964716447/139668228700000000000000000000000 : ℝ)*base70 + (33353580863/653412500000000000000000 : ℝ)*base73 + (440499587773007/1176400000000000000000000000 : ℝ)*base75 + (535154944784303/1306825000000000000000000000 : ℝ)*base77 + (43558530489370341/614939572000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (279/1000000000000000 : ℝ)*base86 + (279/1000000000000000 : ℝ)*base88 + (279/1000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s6_0,ratio_s6_1,ratio_s6_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev5 : (0 : ℝ) ≤ ((52273/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(52273/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2941/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2941/5000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(26719/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(26719/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((33917/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(33917/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39177/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(39177/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8989/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8989/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c302061_s6 p hpa hpb X hX hprev5

#print axioms solution
