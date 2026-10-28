-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304053_s6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:45:12.894299+00:00
-- url     : https://prove2.me/submissions/c4c5987f-07da-4918-b8e4-abc36532a4ac

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
theorem collision_support_c304053_s6_s6_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2395924099/10000000000 : ℝ)*x 0 + (1036584131/2000000000 : ℝ)*x 1 + (5215747451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2395924099/10000000000 : ℝ)^67 ≤ (15303752592971/100000000000000 : ℝ)^51 := by
    have hnat : (2395924099 : ℕ)^67*100000000000000^51 ≤ 15303752592971^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2395924099 10000000000 15303752592971 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036584131/2000000000 : ℝ)^67 ≤ (21086248903671/50000000000000 : ℝ)^51 := by
    have hnat : (1036584131 : ℕ)^67*50000000000000^51 ≤ 21086248903671^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036584131 2000000000 21086248903671 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215747451/10000000000 : ℝ)^67 ≤ (10630937395517/25000000000000 : ℝ)^51 := by
    have hnat : (5215747451 : ℕ)^67*25000000000000^51 ≤ 10630937395517^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215747451 10000000000 10630937395517 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2395924099/10000000000 : ℝ), (1036584131/2000000000 : ℝ), (5215747451/10000000000 : ℝ)] ![(15303752592971/100000000000000 : ℝ), (21086248903671/50000000000000 : ℝ), (10630937395517/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2395924099/10000000000 : ℝ)|^67 ≤ (15303752592971/100000000000000 : ℝ)^51
        have hw : |(-2395924099/10000000000 : ℝ)|=(2395924099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036584131/2000000000 : ℝ)|^67 ≤ (21086248903671/50000000000000 : ℝ)^51
        have hw : |(1036584131/2000000000 : ℝ)|=(1036584131/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215747451/10000000000 : ℝ)|^67 ≤ (10630937395517/25000000000000 : ℝ)^51
        have hw : |(5215747451/10000000000 : ℝ)|=(5215747451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304053_s6_s6_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2278127867/5000000000 : ℝ)*x 0 + (-966343849/5000000000 : ℝ)*x 1 + (307742079/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2278127867/5000000000 : ℝ)^67 ≤ (35604488302871/100000000000000 : ℝ)^51 := by
    have hnat : (2278127867 : ℕ)^67*100000000000000^51 ≤ 35604488302871^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2278127867 5000000000 35604488302871 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (966343849/5000000000 : ℝ)^67 ≤ (5770087651983/50000000000000 : ℝ)^51 := by
    have hnat : (966343849 : ℕ)^67*50000000000000^51 ≤ 5770087651983^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      966343849 5000000000 5770087651983 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (307742079/500000000 : ℝ)^67 ≤ (1321383409609/2500000000000 : ℝ)^51 := by
    have hnat : (307742079 : ℕ)^67*2500000000000^51 ≤ 1321383409609^51*500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      307742079 500000000 1321383409609 2500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2278127867/5000000000 : ℝ), (-966343849/5000000000 : ℝ), (307742079/500000000 : ℝ)] ![(35604488302871/100000000000000 : ℝ), (5770087651983/50000000000000 : ℝ), (1321383409609/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2278127867/5000000000 : ℝ)|^67 ≤ (35604488302871/100000000000000 : ℝ)^51
        have hw : |(2278127867/5000000000 : ℝ)|=(2278127867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-966343849/5000000000 : ℝ)|^67 ≤ (5770087651983/50000000000000 : ℝ)^51
        have hw : |(-966343849/5000000000 : ℝ)|=(966343849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(307742079/500000000 : ℝ)|^67 ≤ (1321383409609/2500000000000 : ℝ)^51
        have hw : |(307742079/500000000 : ℝ)|=(307742079/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304053_s6_s6_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4578206229/10000000000 : ℝ)*x 0 + (6147604817/10000000000 : ℝ)*x 1 + (-1914317603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4578206229/10000000000 : ℝ)^67 ≤ (17915001102053/50000000000000 : ℝ)^51 := by
    have hnat : (4578206229 : ℕ)^67*50000000000000^51 ≤ 17915001102053^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4578206229 10000000000 17915001102053 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6147604817/10000000000 : ℝ)^67 ≤ (2110948322939/4000000000000 : ℝ)^51 := by
    have hnat : (6147604817 : ℕ)^67*4000000000000^51 ≤ 2110948322939^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6147604817 10000000000 2110948322939 4000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1914317603/10000000000 : ℝ)^67 ≤ (11396289703741/100000000000000 : ℝ)^51 := by
    have hnat : (1914317603 : ℕ)^67*100000000000000^51 ≤ 11396289703741^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1914317603 10000000000 11396289703741 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4578206229/10000000000 : ℝ), (6147604817/10000000000 : ℝ), (-1914317603/10000000000 : ℝ)] ![(17915001102053/50000000000000 : ℝ), (2110948322939/4000000000000 : ℝ), (11396289703741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4578206229/10000000000 : ℝ)|^67 ≤ (17915001102053/50000000000000 : ℝ)^51
        have hw : |(4578206229/10000000000 : ℝ)|=(4578206229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6147604817/10000000000 : ℝ)|^67 ≤ (2110948322939/4000000000000 : ℝ)^51
        have hw : |(6147604817/10000000000 : ℝ)|=(6147604817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1914317603/10000000000 : ℝ)|^67 ≤ (11396289703741/100000000000000 : ℝ)^51
        have hw : |(-1914317603/10000000000 : ℝ)|=(1914317603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304053_s6_s6_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6623085377/10000000000 : ℝ)*x 0 + (3059665807/10000000000 : ℝ)*x 1 + (753763763/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6623085377/10000000000 : ℝ)^67 ≤ (29099962512587/50000000000000 : ℝ)^51 := by
    have hnat : (6623085377 : ℕ)^67*50000000000000^51 ≤ 29099962512587^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6623085377 10000000000 29099962512587 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3059665807/10000000000 : ℝ)^67 ≤ (21101669391503/100000000000000 : ℝ)^51 := by
    have hnat : (3059665807 : ℕ)^67*100000000000000^51 ≤ 21101669391503^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3059665807 10000000000 21101669391503 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (753763763/2500000000 : ℝ)^67 ≤ (20698405564587/100000000000000 : ℝ)^51 := by
    have hnat : (753763763 : ℕ)^67*100000000000000^51 ≤ 20698405564587^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      753763763 2500000000 20698405564587 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6623085377/10000000000 : ℝ), (3059665807/10000000000 : ℝ), (753763763/2500000000 : ℝ)] ![(29099962512587/50000000000000 : ℝ), (21101669391503/100000000000000 : ℝ), (20698405564587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6623085377/10000000000 : ℝ)|^67 ≤ (29099962512587/50000000000000 : ℝ)^51
        have hw : |(6623085377/10000000000 : ℝ)|=(6623085377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3059665807/10000000000 : ℝ)|^67 ≤ (21101669391503/100000000000000 : ℝ)^51
        have hw : |(3059665807/10000000000 : ℝ)|=(3059665807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(753763763/2500000000 : ℝ)|^67 ≤ (20698405564587/100000000000000 : ℝ)^51
        have hw : |(753763763/2500000000 : ℝ)|=(753763763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304053_s6_s6_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2268930419/10000000000 : ℝ)*x 0 + (1032471129/2500000000 : ℝ)*x 1 + (1574139137/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2268930419/10000000000 : ℝ)^67 ≤ (14247079929887/100000000000000 : ℝ)^51 := by
    have hnat : (2268930419 : ℕ)^67*100000000000000^51 ≤ 14247079929887^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2268930419 10000000000 14247079929887 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1032471129/2500000000 : ℝ)^67 ≤ (31293046067059/100000000000000 : ℝ)^51 := by
    have hnat : (1032471129 : ℕ)^67*100000000000000^51 ≤ 31293046067059^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032471129 2500000000 31293046067059 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1574139137/2500000000 : ℝ)^67 ≤ (54459873986557/100000000000000 : ℝ)^51 := by
    have hnat : (1574139137 : ℕ)^67*100000000000000^51 ≤ 54459873986557^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1574139137 2500000000 54459873986557 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2268930419/10000000000 : ℝ), (1032471129/2500000000 : ℝ), (1574139137/2500000000 : ℝ)] ![(14247079929887/100000000000000 : ℝ), (31293046067059/100000000000000 : ℝ), (54459873986557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2268930419/10000000000 : ℝ)|^67 ≤ (14247079929887/100000000000000 : ℝ)^51
        have hw : |(-2268930419/10000000000 : ℝ)|=(2268930419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1032471129/2500000000 : ℝ)|^67 ≤ (31293046067059/100000000000000 : ℝ)^51
        have hw : |(1032471129/2500000000 : ℝ)|=(1032471129/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1574139137/2500000000 : ℝ)|^67 ≤ (54459873986557/100000000000000 : ℝ)^51
        have hw : |(1574139137/2500000000 : ℝ)|=(1574139137/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304053_s6_s6_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (513111069/1250000000 : ℝ)*x 0 + (-1347678333/10000000000 : ℝ)*x 1 + (3465023631/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (513111069/1250000000 : ℝ)^67 ≤ (15522231552529/50000000000000 : ℝ)^51 := by
    have hnat : (513111069 : ℕ)^67*50000000000000^51 ≤ 15522231552529^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513111069 1250000000 15522231552529 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347678333/10000000000 : ℝ)^67 ≤ (7186464168687/100000000000000 : ℝ)^51 := by
    have hnat : (1347678333 : ℕ)^67*100000000000000^51 ≤ 7186464168687^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347678333 10000000000 7186464168687 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3465023631/5000000000 : ℝ)^67 ≤ (61769072702223/100000000000000 : ℝ)^51 := by
    have hnat : (3465023631 : ℕ)^67*100000000000000^51 ≤ 61769072702223^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3465023631 5000000000 61769072702223 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(513111069/1250000000 : ℝ), (-1347678333/10000000000 : ℝ), (3465023631/5000000000 : ℝ)] ![(15522231552529/50000000000000 : ℝ), (7186464168687/100000000000000 : ℝ), (61769072702223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(513111069/1250000000 : ℝ)|^67 ≤ (15522231552529/50000000000000 : ℝ)^51
        have hw : |(513111069/1250000000 : ℝ)|=(513111069/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1347678333/10000000000 : ℝ)|^67 ≤ (7186464168687/100000000000000 : ℝ)^51
        have hw : |(-1347678333/10000000000 : ℝ)|=(1347678333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3465023631/5000000000 : ℝ)|^67 ≤ (61769072702223/100000000000000 : ℝ)^51
        have hw : |(3465023631/5000000000 : ℝ)|=(3465023631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304053_s6_s6_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2063543739/5000000000 : ℝ)*x 0 + (3577623103/5000000000 : ℝ)*x 1 + (-457042381/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2063543739/5000000000 : ℝ)^67 ≤ (3908150778047/12500000000000 : ℝ)^51 := by
    have hnat : (2063543739 : ℕ)^67*12500000000000^51 ≤ 3908150778047^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063543739 5000000000 3908150778047 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3577623103/5000000000 : ℝ)^67 ≤ (1006552968107/1562500000000 : ℝ)^51 := by
    have hnat : (3577623103 : ℕ)^67*1562500000000^51 ≤ 1006552968107^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3577623103 5000000000 1006552968107 1562500000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (457042381/5000000000 : ℝ)^67 ≤ (4315403802889/100000000000000 : ℝ)^51 := by
    have hnat : (457042381 : ℕ)^67*100000000000000^51 ≤ 4315403802889^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      457042381 5000000000 4315403802889 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2063543739/5000000000 : ℝ), (3577623103/5000000000 : ℝ), (-457042381/5000000000 : ℝ)] ![(3908150778047/12500000000000 : ℝ), (1006552968107/1562500000000 : ℝ), (4315403802889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2063543739/5000000000 : ℝ)|^67 ≤ (3908150778047/12500000000000 : ℝ)^51
        have hw : |(2063543739/5000000000 : ℝ)|=(2063543739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3577623103/5000000000 : ℝ)|^67 ≤ (1006552968107/1562500000000 : ℝ)^51
        have hw : |(3577623103/5000000000 : ℝ)|=(3577623103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-457042381/5000000000 : ℝ)|^67 ≤ (4315403802889/100000000000000 : ℝ)^51
        have hw : |(-457042381/5000000000 : ℝ)|=(457042381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304053_s6_s6_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (63097931/100000000 : ℝ)*x 0 + (1161585171/2500000000 : ℝ)*x 1 + (1580157009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (63097931/100000000 : ℝ)^67 ≤ (54610325353959/100000000000000 : ℝ)^51 := by
    have hnat : (63097931 : ℕ)^67*100000000000000^51 ≤ 54610325353959^51*100000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63097931 100000000 54610325353959 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1161585171/2500000000 : ℝ)^67 ≤ (4566519479491/12500000000000 : ℝ)^51 := by
    have hnat : (1161585171 : ℕ)^67*12500000000000^51 ≤ 4566519479491^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1161585171 2500000000 4566519479491 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1580157009/10000000000 : ℝ)^67 ≤ (8857518792953/100000000000000 : ℝ)^51 := by
    have hnat : (1580157009 : ℕ)^67*100000000000000^51 ≤ 8857518792953^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1580157009 10000000000 8857518792953 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(63097931/100000000 : ℝ), (1161585171/2500000000 : ℝ), (1580157009/10000000000 : ℝ)] ![(54610325353959/100000000000000 : ℝ), (4566519479491/12500000000000 : ℝ), (8857518792953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(63097931/100000000 : ℝ)|^67 ≤ (54610325353959/100000000000000 : ℝ)^51
        have hw : |(63097931/100000000 : ℝ)|=(63097931/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1161585171/2500000000 : ℝ)|^67 ≤ (4566519479491/12500000000000 : ℝ)^51
        have hw : |(1161585171/2500000000 : ℝ)|=(1161585171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1580157009/10000000000 : ℝ)|^67 ≤ (8857518792953/100000000000000 : ℝ)^51
        have hw : |(1580157009/10000000000 : ℝ)|=(1580157009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304053_s6_s6_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-247969099/2000000000 : ℝ)*x 0 + (982759819/2000000000 : ℝ)*x 1 + (251087377/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (247969099/2000000000 : ℝ)^67 ≤ (3220355884533/50000000000000 : ℝ)^51 := by
    have hnat : (247969099 : ℕ)^67*50000000000000^51 ≤ 3220355884533^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      247969099 2000000000 3220355884533 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (982759819/2000000000 : ℝ)^67 ≤ (1965971291299/5000000000000 : ℝ)^51 := by
    have hnat : (982759819 : ℕ)^67*5000000000000^51 ≤ 1965971291299^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      982759819 2000000000 1965971291299 5000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (251087377/400000000 : ℝ)^67 ≤ (13559965597007/25000000000000 : ℝ)^51 := by
    have hnat : (251087377 : ℕ)^67*25000000000000^51 ≤ 13559965597007^51*400000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251087377 400000000 13559965597007 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-247969099/2000000000 : ℝ), (982759819/2000000000 : ℝ), (251087377/400000000 : ℝ)] ![(3220355884533/50000000000000 : ℝ), (1965971291299/5000000000000 : ℝ), (13559965597007/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-247969099/2000000000 : ℝ)|^67 ≤ (3220355884533/50000000000000 : ℝ)^51
        have hw : |(-247969099/2000000000 : ℝ)|=(247969099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(982759819/2000000000 : ℝ)|^67 ≤ (1965971291299/5000000000000 : ℝ)^51
        have hw : |(982759819/2000000000 : ℝ)|=(982759819/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(251087377/400000000 : ℝ)|^67 ≤ (13559965597007/25000000000000 : ℝ)^51
        have hw : |(251087377/400000000 : ℝ)|=(251087377/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304053_s6_s6_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (401679697/1000000000 : ℝ)*x 0 + (-750928557/5000000000 : ℝ)*x 1 + (6910677099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (401679697/1000000000 : ℝ)^67 ≤ (30172194744591/100000000000000 : ℝ)^51 := by
    have hnat : (401679697 : ℕ)^67*100000000000000^51 ≤ 30172194744591^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401679697 1000000000 30172194744591 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (750928557/5000000000 : ℝ)^67 ≤ (4142724276773/50000000000000 : ℝ)^51 := by
    have hnat : (750928557 : ℕ)^67*50000000000000^51 ≤ 4142724276773^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      750928557 5000000000 4142724276773 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6910677099/10000000000 : ℝ)^67 ≤ (30771178341259/50000000000000 : ℝ)^51 := by
    have hnat : (6910677099 : ℕ)^67*50000000000000^51 ≤ 30771178341259^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6910677099 10000000000 30771178341259 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(401679697/1000000000 : ℝ), (-750928557/5000000000 : ℝ), (6910677099/10000000000 : ℝ)] ![(30172194744591/100000000000000 : ℝ), (4142724276773/50000000000000 : ℝ), (30771178341259/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(401679697/1000000000 : ℝ)|^67 ≤ (30172194744591/100000000000000 : ℝ)^51
        have hw : |(401679697/1000000000 : ℝ)|=(401679697/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-750928557/5000000000 : ℝ)|^67 ≤ (4142724276773/50000000000000 : ℝ)^51
        have hw : |(-750928557/5000000000 : ℝ)|=(750928557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6910677099/10000000000 : ℝ)|^67 ≤ (30771178341259/50000000000000 : ℝ)^51
        have hw : |(6910677099/10000000000 : ℝ)|=(6910677099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304053_s6_s6_16 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (363318757/625000000 : ℝ)*x 0 + (558574857/1000000000 : ℝ)*x 1 + (-233364221/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (363318757/625000000 : ℝ)^67 ≤ (24516954947377/50000000000000 : ℝ)^51 := by
    have hnat : (363318757 : ℕ)^67*50000000000000^51 ≤ 24516954947377^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      363318757 625000000 24516954947377 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (558574857/1000000000 : ℝ)^67 ≤ (46530140714797/100000000000000 : ℝ)^51 := by
    have hnat : (558574857 : ℕ)^67*100000000000000^51 ≤ 46530140714797^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      558574857 1000000000 46530140714797 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (233364221/2500000000 : ℝ)^67 ≤ (35487594957/800000000000 : ℝ)^51 := by
    have hnat : (233364221 : ℕ)^67*800000000000^51 ≤ 35487594957^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233364221 2500000000 35487594957 800000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(363318757/625000000 : ℝ), (558574857/1000000000 : ℝ), (-233364221/2500000000 : ℝ)] ![(24516954947377/50000000000000 : ℝ), (46530140714797/100000000000000 : ℝ), (35487594957/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(363318757/625000000 : ℝ)|^67 ≤ (24516954947377/50000000000000 : ℝ)^51
        have hw : |(363318757/625000000 : ℝ)|=(363318757/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(558574857/1000000000 : ℝ)|^67 ≤ (46530140714797/100000000000000 : ℝ)^51
        have hw : |(558574857/1000000000 : ℝ)|=(558574857/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-233364221/2500000000 : ℝ)|^67 ≤ (35487594957/800000000000 : ℝ)^51
        have hw : |(-233364221/2500000000 : ℝ)|=(233364221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304053_s6_s6_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7824740671/10000000000 : ℝ)*x 0 + (344576299/1250000000 : ℝ)*x 1 + (404887317/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7824740671/10000000000 : ℝ)^67 ≤ (72451730295247/100000000000000 : ℝ)^51 := by
    have hnat : (7824740671 : ℕ)^67*100000000000000^51 ≤ 72451730295247^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7824740671 10000000000 72451730295247 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (344576299/1250000000 : ℝ)^67 ≤ (4599884132899/25000000000000 : ℝ)^51 := by
    have hnat : (344576299 : ℕ)^67*25000000000000^51 ≤ 4599884132899^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344576299 1250000000 4599884132899 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (404887317/2500000000 : ℝ)^67 ≤ (571795822453/6250000000000 : ℝ)^51 := by
    have hnat : (404887317 : ℕ)^67*6250000000000^51 ≤ 571795822453^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404887317 2500000000 571795822453 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7824740671/10000000000 : ℝ), (344576299/1250000000 : ℝ), (404887317/2500000000 : ℝ)] ![(72451730295247/100000000000000 : ℝ), (4599884132899/25000000000000 : ℝ), (571795822453/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7824740671/10000000000 : ℝ)|^67 ≤ (72451730295247/100000000000000 : ℝ)^51
        have hw : |(7824740671/10000000000 : ℝ)|=(7824740671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(344576299/1250000000 : ℝ)|^67 ≤ (4599884132899/25000000000000 : ℝ)^51
        have hw : |(344576299/1250000000 : ℝ)|=(344576299/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(404887317/2500000000 : ℝ)|^67 ≤ (571795822453/6250000000000 : ℝ)^51
        have hw : |(404887317/2500000000 : ℝ)|=(404887317/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304053_s6_s6_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-247362537/2000000000 : ℝ)*x 0 + (5920542563/10000000000 : ℝ)*x 1 + (5292899941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (247362537/2000000000 : ℝ)^67 ≤ (6420022299347/100000000000000 : ℝ)^51 := by
    have hnat : (247362537 : ℕ)^67*100000000000000^51 ≤ 6420022299347^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      247362537 2000000000 6420022299347 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5920542563/10000000000 : ℝ)^67 ≤ (25113978282013/50000000000000 : ℝ)^51 := by
    have hnat : (5920542563 : ℕ)^67*50000000000000^51 ≤ 25113978282013^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5920542563 10000000000 25113978282013 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5292899941/10000000000 : ℝ)^67 ≤ (43352021118743/100000000000000 : ℝ)^51 := by
    have hnat : (5292899941 : ℕ)^67*100000000000000^51 ≤ 43352021118743^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5292899941 10000000000 43352021118743 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-247362537/2000000000 : ℝ), (5920542563/10000000000 : ℝ), (5292899941/10000000000 : ℝ)] ![(6420022299347/100000000000000 : ℝ), (25113978282013/50000000000000 : ℝ), (43352021118743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-247362537/2000000000 : ℝ)|^67 ≤ (6420022299347/100000000000000 : ℝ)^51
        have hw : |(-247362537/2000000000 : ℝ)|=(247362537/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5920542563/10000000000 : ℝ)|^67 ≤ (25113978282013/50000000000000 : ℝ)^51
        have hw : |(5920542563/10000000000 : ℝ)|=(5920542563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5292899941/10000000000 : ℝ)|^67 ≤ (43352021118743/100000000000000 : ℝ)^51
        have hw : |(5292899941/10000000000 : ℝ)|=(5292899941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304053_s6_s6_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5793934033/10000000000 : ℝ)*x 0 + (-473336769/5000000000 : ℝ)*x 1 + (1399396389/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5793934033/10000000000 : ℝ)^67 ≤ (6102704182511/12500000000000 : ℝ)^51 := by
    have hnat : (5793934033 : ℕ)^67*12500000000000^51 ≤ 6102704182511^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5793934033 10000000000 6102704182511 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (473336769/5000000000 : ℝ)^67 ≤ (4518644295349/100000000000000 : ℝ)^51 := by
    have hnat : (473336769 : ℕ)^67*100000000000000^51 ≤ 4518644295349^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      473336769 5000000000 4518644295349 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1399396389/2500000000 : ℝ)^67 ≤ (46659722218471/100000000000000 : ℝ)^51 := by
    have hnat : (1399396389 : ℕ)^67*100000000000000^51 ≤ 46659722218471^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1399396389 2500000000 46659722218471 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5793934033/10000000000 : ℝ), (-473336769/5000000000 : ℝ), (1399396389/2500000000 : ℝ)] ![(6102704182511/12500000000000 : ℝ), (4518644295349/100000000000000 : ℝ), (46659722218471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5793934033/10000000000 : ℝ)|^67 ≤ (6102704182511/12500000000000 : ℝ)^51
        have hw : |(5793934033/10000000000 : ℝ)|=(5793934033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-473336769/5000000000 : ℝ)|^67 ≤ (4518644295349/100000000000000 : ℝ)^51
        have hw : |(-473336769/5000000000 : ℝ)|=(473336769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1399396389/2500000000 : ℝ)|^67 ≤ (46659722218471/100000000000000 : ℝ)^51
        have hw : |(1399396389/2500000000 : ℝ)|=(1399396389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304053_s6_s6_23 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (987464843/2500000000 : ℝ)*x 0 + (6997108429/10000000000 : ℝ)*x 1 + (-90794419/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (987464843/2500000000 : ℝ)^67 ≤ (14756692011517/50000000000000 : ℝ)^51 := by
    have hnat : (987464843 : ℕ)^67*50000000000000^51 ≤ 14756692011517^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      987464843 2500000000 14756692011517 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6997108429/10000000000 : ℝ)^67 ≤ (12511103375651/20000000000000 : ℝ)^51 := by
    have hnat : (6997108429 : ℕ)^67*20000000000000^51 ≤ 12511103375651^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6997108429 10000000000 12511103375651 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (90794419/625000000 : ℝ)^67 ≤ (1982774770427/25000000000000 : ℝ)^51 := by
    have hnat : (90794419 : ℕ)^67*25000000000000^51 ≤ 1982774770427^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90794419 625000000 1982774770427 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(987464843/2500000000 : ℝ), (6997108429/10000000000 : ℝ), (-90794419/625000000 : ℝ)] ![(14756692011517/50000000000000 : ℝ), (12511103375651/20000000000000 : ℝ), (1982774770427/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(987464843/2500000000 : ℝ)|^67 ≤ (14756692011517/50000000000000 : ℝ)^51
        have hw : |(987464843/2500000000 : ℝ)|=(987464843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6997108429/10000000000 : ℝ)|^67 ≤ (12511103375651/20000000000000 : ℝ)^51
        have hw : |(6997108429/10000000000 : ℝ)|=(6997108429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-90794419/625000000 : ℝ)|^67 ≤ (1982774770427/25000000000000 : ℝ)^51
        have hw : |(-90794419/625000000 : ℝ)|=(90794419/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304053_s6_s6_27 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4002996759/5000000000 : ℝ)*x 0 + (2142121393/10000000000 : ℝ)*x 1 + (1003412501/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4002996759/5000000000 : ℝ)^67 ≤ (74664494841669/100000000000000 : ℝ)^51 := by
    have hnat : (4002996759 : ℕ)^67*100000000000000^51 ≤ 74664494841669^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4002996759 5000000000 74664494841669 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2142121393/10000000000 : ℝ)^67 ≤ (3302575977863/25000000000000 : ℝ)^51 := by
    have hnat : (2142121393 : ℕ)^67*25000000000000^51 ≤ 3302575977863^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142121393 10000000000 3302575977863 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1003412501/5000000000 : ℝ)^67 ≤ (12125201232351/100000000000000 : ℝ)^51 := by
    have hnat : (1003412501 : ℕ)^67*100000000000000^51 ≤ 12125201232351^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003412501 5000000000 12125201232351 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4002996759/5000000000 : ℝ), (2142121393/10000000000 : ℝ), (1003412501/5000000000 : ℝ)] ![(74664494841669/100000000000000 : ℝ), (3302575977863/25000000000000 : ℝ), (12125201232351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4002996759/5000000000 : ℝ)|^67 ≤ (74664494841669/100000000000000 : ℝ)^51
        have hw : |(4002996759/5000000000 : ℝ)|=(4002996759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2142121393/10000000000 : ℝ)|^67 ≤ (3302575977863/25000000000000 : ℝ)^51
        have hw : |(2142121393/10000000000 : ℝ)|=(2142121393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1003412501/5000000000 : ℝ)|^67 ≤ (12125201232351/100000000000000 : ℝ)^51
        have hw : |(1003412501/5000000000 : ℝ)|=(1003412501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304053_s6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev5 : (0 : ℝ) ≤ ((5447/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5447/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12847/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(12847/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6307/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6307/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((9557/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9557/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43987/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(43987/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(42537/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(42537/100000 : ℝ)*X 1 2) := by
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
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  rcases hprev5 with ⟨ratio_s5_0,ratio_s5_1,ratio_s5_2⟩
  have s6_pow0 : (5447/10000 : ℝ) ^ (33/8 : ℝ) ≤ (407961497558563013/5000000000000000000 : ℝ) := by
    have hpowers : (5447/10000 : ℝ)^33 ≤ (407961497558563013/5000000000000000000 : ℝ)^8 := by
      have hnat : (5447 : ℕ)^33*5000000000000000000^8 ≤ 407961497558563013^8*10000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5447 10000 407961497558563013 5000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5447/10000 : ℝ)) (X := (407961497558563013/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s6_corner0a : (5407961497558563013/5000000000000000000 : ℝ) ≤ (10191963018980451/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (5407961497558563013/5000000000000000000 : ℝ)^8 ≤ (10191963018980451/10000000000000000 : ℝ)^33 := by
      have hnat : (5407961497558563013 : ℕ)^8*10000000000000000^33 ≤ 10191963018980451^33*5000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5407961497558563013 5000000000000000000 10191963018980451 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10191963018980451/10000000000000000 : ℝ)) (X := (5407961497558563013/5000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s6_corner0b : (2907961497558563013/2500000000000000000 : ℝ) ≤ (10373249472456967/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (2907961497558563013/2500000000000000000 : ℝ)^8 ≤ (10373249472456967/10000000000000000 : ℝ)^33 := by
      have hnat : (2907961497558563013 : ℕ)^8*10000000000000000^33 ≤ 10373249472456967^33*2500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2907961497558563013 2500000000000000000 10373249472456967 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10373249472456967/10000000000000000 : ℝ)) (X := (2907961497558563013/2500000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s6_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(191963018980451/5447000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(45321613369129/1361750000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (5447/10000 : ℝ)) (alpha := (191963018980451/5447000000000000 : ℝ)) (beta := (45321613369129/1361750000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow0,s6_corner0a]) (by linarith only [s6_pow0,s6_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (5447/10000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(191963018980451/5447000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(45321613369129/1361750000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s6_pow1 : (12847/20000 : ℝ) ^ (33/8 : ℝ) ≤ (4027155400570111013/25000000000000000000 : ℝ) := by
    have hpowers : (12847/20000 : ℝ)^33 ≤ (4027155400570111013/25000000000000000000 : ℝ)^8 := by
      have hnat : (12847 : ℕ)^33*25000000000000000000^8 ≤ 4027155400570111013^8*20000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12847 20000 4027155400570111013 25000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12847/20000 : ℝ)) (X := (4027155400570111013/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s6_corner1a : (29027155400570111013/25000000000000000000 : ℝ) ≤ (5184354902891871/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (29027155400570111013/25000000000000000000 : ℝ)^8 ≤ (5184354902891871/5000000000000000 : ℝ)^33 := by
      have hnat : (29027155400570111013 : ℕ)^8*5000000000000000^33 ≤ 5184354902891871^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29027155400570111013 25000000000000000000 5184354902891871 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5184354902891871/5000000000000000 : ℝ)) (X := (29027155400570111013/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s6_corner1b : (16527155400570111013/12500000000000000000 : ℝ) ≤ (2140095583967011/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (16527155400570111013/12500000000000000000 : ℝ)^8 ≤ (2140095583967011/2000000000000000 : ℝ)^33 := by
      have hnat : (16527155400570111013 : ℕ)^8*2000000000000000^33 ≤ 2140095583967011^33*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16527155400570111013 12500000000000000000 2140095583967011 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2140095583967011/2000000000000000 : ℝ)) (X := (16527155400570111013/12500000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s6_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(184354902891871/3211750000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(331768114051313/6423500000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (12847/20000 : ℝ)) (alpha := (184354902891871/3211750000000000 : ℝ)) (beta := (331768114051313/6423500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow1,s6_corner1a]) (by linarith only [s6_pow1,s6_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (12847/20000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(184354902891871/3211750000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(331768114051313/6423500000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s6_pow2 : (6307/10000 : ℝ) ^ (33/8 : ℝ) ≤ (466787480519024431/3125000000000000000 : ℝ) := by
    have hpowers : (6307/10000 : ℝ)^33 ≤ (466787480519024431/3125000000000000000 : ℝ)^8 := by
      have hnat : (6307 : ℕ)^33*3125000000000000000^8 ≤ 466787480519024431^8*10000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6307 10000 466787480519024431 3125000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6307/10000 : ℝ)) (X := (466787480519024431/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s6_corner2a : (3591787480519024431/3125000000000000000 : ℝ) ≤ (10343252283398193/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (3591787480519024431/3125000000000000000 : ℝ)^8 ≤ (10343252283398193/10000000000000000 : ℝ)^33 := by
      have hnat : (3591787480519024431 : ℕ)^8*10000000000000000^33 ≤ 10343252283398193^33*3125000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3591787480519024431 3125000000000000000 10343252283398193 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10343252283398193/10000000000000000 : ℝ)) (X := (3591787480519024431/3125000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s6_corner2b : (2029287480519024431/1562500000000000000 : ℝ) ≤ (10654200381162691/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (2029287480519024431/1562500000000000000 : ℝ)^8 ≤ (10654200381162691/10000000000000000 : ℝ)^33 := by
      have hnat : (2029287480519024431 : ℕ)^8*10000000000000000^33 ≤ 10654200381162691^33*1562500000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2029287480519024431 1562500000000000000 10654200381162691 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10654200381162691/10000000000000000 : ℝ)) (X := (2029287480519024431/1562500000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s6_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(20191310788129/371000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(155474048882249/3153500000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (6307/10000 : ℝ)) (alpha := (20191310788129/371000000000000 : ℝ)) (beta := (155474048882249/3153500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow2,s6_corner2a]) (by linarith only [s6_pow2,s6_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (6307/10000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(20191310788129/371000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(155474048882249/3153500000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s6_0 : ((-2395924099/10000000000 : ℝ)*X 0 0+(1036584131/2000000000 : ℝ)*X 0 1+(5215747451/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304053_s6_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_1 : ((2278127867/5000000000 : ℝ)*X 1 0+(-966343849/5000000000 : ℝ)*X 1 1+(307742079/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304053_s6_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_2 : ((4578206229/10000000000 : ℝ)*X 2 0+(6147604817/10000000000 : ℝ)*X 2 1+(-1914317603/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304053_s6_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_6 : ((6623085377/10000000000 : ℝ)*X 0 0+(3059665807/10000000000 : ℝ)*X 0 1+(753763763/2500000000 : ℝ)*X 0 2+(6623085377/10000000000 : ℝ)*X 1 0+(3059665807/10000000000 : ℝ)*X 1 1+(753763763/2500000000 : ℝ)*X 1 2+(6623085377/10000000000 : ℝ)*X 2 0+(3059665807/10000000000 : ℝ)*X 2 1+(753763763/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304053_s6_s6_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_7 : ((-2268930419/10000000000 : ℝ)*X 0 0+(1032471129/2500000000 : ℝ)*X 0 1+(1574139137/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304053_s6_s6_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_8 : ((513111069/1250000000 : ℝ)*X 1 0+(-1347678333/10000000000 : ℝ)*X 1 1+(3465023631/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304053_s6_s6_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_9 : ((2063543739/5000000000 : ℝ)*X 2 0+(3577623103/5000000000 : ℝ)*X 2 1+(-457042381/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304053_s6_s6_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_13 : ((63097931/100000000 : ℝ)*X 0 0+(1161585171/2500000000 : ℝ)*X 0 1+(1580157009/10000000000 : ℝ)*X 0 2+(63097931/100000000 : ℝ)*X 1 0+(1161585171/2500000000 : ℝ)*X 1 1+(1580157009/10000000000 : ℝ)*X 1 2+(63097931/100000000 : ℝ)*X 2 0+(1161585171/2500000000 : ℝ)*X 2 1+(1580157009/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304053_s6_s6_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_14 : ((-247969099/2000000000 : ℝ)*X 0 0+(982759819/2000000000 : ℝ)*X 0 1+(251087377/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304053_s6_s6_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_15 : ((401679697/1000000000 : ℝ)*X 1 0+(-750928557/5000000000 : ℝ)*X 1 1+(6910677099/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304053_s6_s6_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_16 : ((363318757/625000000 : ℝ)*X 2 0+(558574857/1000000000 : ℝ)*X 2 1+(-233364221/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304053_s6_s6_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_20 : ((7824740671/10000000000 : ℝ)*X 0 0+(344576299/1250000000 : ℝ)*X 0 1+(404887317/2500000000 : ℝ)*X 0 2+(7824740671/10000000000 : ℝ)*X 1 0+(344576299/1250000000 : ℝ)*X 1 1+(404887317/2500000000 : ℝ)*X 1 2+(7824740671/10000000000 : ℝ)*X 2 0+(344576299/1250000000 : ℝ)*X 2 1+(404887317/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304053_s6_s6_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_21 : ((-247362537/2000000000 : ℝ)*X 0 0+(5920542563/10000000000 : ℝ)*X 0 1+(5292899941/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304053_s6_s6_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_22 : ((5793934033/10000000000 : ℝ)*X 1 0+(-473336769/5000000000 : ℝ)*X 1 1+(1399396389/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304053_s6_s6_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_23 : ((987464843/2500000000 : ℝ)*X 2 0+(6997108429/10000000000 : ℝ)*X 2 1+(-90794419/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304053_s6_s6_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_27 : ((4002996759/5000000000 : ℝ)*X 0 0+(2142121393/10000000000 : ℝ)*X 0 1+(1003412501/5000000000 : ℝ)*X 0 2+(4002996759/5000000000 : ℝ)*X 1 0+(2142121393/10000000000 : ℝ)*X 1 1+(1003412501/5000000000 : ℝ)*X 1 2+(4002996759/5000000000 : ℝ)*X 2 0+(2142121393/10000000000 : ℝ)*X 2 1+(1003412501/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304053_s6_s6_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s6_0 : (0 : ℝ) ≤ ((9557/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9557/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (43657335381782068959857157/10128253625000000000000000000000 : ℝ) := by norm_num
    linear_combination (2695089/1000000000000 : ℝ)*(base49) + (196775249071/500000000000 : ℝ)*(base59) + (231227/1000000000000 : ℝ)*(base60) + (1085117207289/250000000000 : ℝ)*(major_s6_0) + (1085117207289/250000000000 : ℝ)*(major_s6_1) + (1085117207289/250000000000 : ℝ)*(major_s6_2) + (221381/7812500000 : ℝ)*(sp_s6_0) + (992509/100000000000 : ℝ)*(sp_s6_6) + (5819160937919/1000000000000 : ℝ)*(sp_s6_7) + (2909540543963/500000000000 : ℝ)*(sp_s6_8) + (5819110754501/1000000000000 : ℝ)*(sp_s6_9) + (1430868510857/500000000000 : ℝ)*(sp_s6_13) + (108186761/1000000000000 : ℝ)*(sp_s6_15) + (39260093/500000000000 : ℝ)*(sp_s6_23) + (715436736701/250000000000 : ℝ)*(f.failure) + (5819189274687/1000000000000 : ℝ)*(f.sum) + (463240150773172611/595779625000000000000000000000 : ℝ)*base62 + (72604139133709/197093750000000000000000000 : ℝ)*base64 + (362912701777991/802937500000000000000000000 : ℝ)*base66 + (58024841300019/92750000000000000000000000 : ℝ)*base68 + (4283154720158678211/8588557250000000000000000000000 : ℝ)*base70 + (76286780988149/1361750000000000000000000000 : ℝ)*base73 + (123169374252281/802937500000000000000000000 : ℝ)*base74 + (80707775965289/1361750000000000000000000000 : ℝ)*base77 + (1102182591122525553/1749440225000000000000000000000 : ℝ)*base78 + (1759/3125000000000000 : ℝ)*base87 + (1759/3125000000000000 : ℝ)*base89 + (1759/3125000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s6_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43987/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(43987/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2498245987309254540519477/330329125000000000000000000000 : ℝ) := by norm_num
    linear_combination (182099899/7812500000 : ℝ)*(base59) + (4204329961299/1000000000000 : ℝ)*(major_s6_0) + (4204329961299/1000000000000 : ℝ)*(major_s6_1) + (4204329961299/1000000000000 : ℝ)*(major_s6_2) + (2476491/500000000000 : ℝ)*(sp_s6_0) + (8934581/500000000000 : ℝ)*(sp_s6_1) + (24466291/1000000000000 : ℝ)*(sp_s6_2) + (4566627/125000000000 : ℝ)*(sp_s6_7) + (7984527/1000000000000 : ℝ)*(sp_s6_8) + (704578462921/125000000000 : ℝ)*(sp_s6_14) + (2818321667839/500000000000 : ℝ)*(sp_s6_15) + (2818322361537/500000000000 : ℝ)*(sp_s6_16) + (346491662779/125000000000 : ℝ)*(sp_s6_20) + (13727507/250000000000 : ℝ)*(sp_s6_27) + (138599410613/50000000000 : ℝ)*(f.failure) + (2818334594683/500000000000 : ℝ)*(f.sum) + (662512700294962527/4766237000000000000000000000000 : ℝ)*base62 + (1438023474327649/3153500000000000000000000000 : ℝ)*base65 + (1291001371271713/6423500000000000000000000000 : ℝ)*base67 + (98007430521229/371000000000000000000000000 : ℝ)*base68 + (780645888207741873/2642633000000000000000000000000 : ℝ)*base71 + (40147221586333/104750000000000000000000000 : ℝ)*base72 + (544379659723601/802937500000000000000000000 : ℝ)*base75 + (349764251634873/419000000000000000000000000 : ℝ)*base77 + (92204764866878361/538289300000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base84 + (1/78125000000000 : ℝ)*base86 + (1/78125000000000 : ℝ)*base88 + (1/78125000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s6_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(42537/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(42537/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (11026108500319970043321890613/760946172350000000000000000000000 : ℝ) := by norm_num
    linear_combination (176189878233/1000000000000 : ℝ)*(base40) + (683583/125000000000 : ℝ)*(base49) + (31381534329/500000000000 : ℝ)*(base59) + (3996713162693/1000000000000 : ℝ)*(major_s6_0) + (3996713162693/1000000000000 : ℝ)*(major_s6_1) + (3996713162693/1000000000000 : ℝ)*(major_s6_2) + (26966827/1000000000000 : ℝ)*(sp_s6_0) + (119381301/1000000000000 : ℝ)*(sp_s6_2) + (66319967/1000000000000 : ℝ)*(sp_s6_9) + (317341449/1000000000000 : ℝ)*(sp_s6_20) + (5358291699629/1000000000000 : ℝ)*(sp_s6_21) + (669789833307/125000000000 : ℝ)*(sp_s6_22) + (1339533241297/250000000000 : ℝ)*(sp_s6_23) + (65869637187/25000000000 : ℝ)*(sp_s6_27) + (2635102828929/1000000000000 : ℝ)*(f.failure) + (669789833307/125000000000 : ℝ)*(f.sum) + (528493451106745589/4766237000000000000000000000000 : ℝ)*base62 + (839396386902443/3153500000000000000000000000 : ℝ)*base65 + (2215241876342791/6423500000000000000000000000 : ℝ)*base67 + (4858499104303/371000000000000000000000000 : ℝ)*base68 + (9158793887052442743/34354229000000000000000000000000 : ℝ)*base71 + (63931196323503/1361750000000000000000000000 : ℝ)*base72 + (234165935593147/3211750000000000000000000000 : ℝ)*base74 + (471134382985243/5447000000000000000000000000 : ℝ)*base77 + (1906508184785583569/6997760900000000000000000000000 : ℝ)*base79 + (2411/12500000000000000 : ℝ)*base87 + (2411/12500000000000000 : ℝ)*base89 + (2411/12500000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s6_0,ratio_s6_1,ratio_s6_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev5 : (0 : ℝ) ≤ ((5447/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5447/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12847/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(12847/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6307/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6307/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((9557/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9557/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43987/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(43987/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(42537/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(42537/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304053_s6 p hpa hpb X hX hprev5

#print axioms solution
