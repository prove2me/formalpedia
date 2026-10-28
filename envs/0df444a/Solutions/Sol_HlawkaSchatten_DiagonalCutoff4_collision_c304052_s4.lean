-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304052_s4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:45:03.715474+00:00
-- url     : https://prove2.me/submissions/61b8c46c-9a07-4364-b480-5c979418427d

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
theorem collision_support_c304052_s4_s4_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1372085361/5000000000 : ℝ)*x 0 + (761392939/2000000000 : ℝ)*x 1 + (-3089525563/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1372085361/5000000000 : ℝ)^17 ≤ (4608446591101/25000000000000 : ℝ)^13 := by
    have hnat : (1372085361 : ℕ)^17*25000000000000^13 ≤ 4608446591101^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372085361 5000000000 4608446591101 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (761392939/2000000000 : ℝ)^17 ≤ (28283046497963/100000000000000 : ℝ)^13 := by
    have hnat : (761392939 : ℕ)^17*100000000000000^13 ≤ 28283046497963^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      761392939 2000000000 28283046497963 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3089525563/5000000000 : ℝ)^17 ≤ (26641583568239/50000000000000 : ℝ)^13 := by
    have hnat : (3089525563 : ℕ)^17*50000000000000^13 ≤ 26641583568239^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3089525563 5000000000 26641583568239 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1372085361/5000000000 : ℝ), (761392939/2000000000 : ℝ), (-3089525563/5000000000 : ℝ)] ![(4608446591101/25000000000000 : ℝ), (28283046497963/100000000000000 : ℝ), (26641583568239/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1372085361/5000000000 : ℝ)|^17 ≤ (4608446591101/25000000000000 : ℝ)^13
        have hw : |(-1372085361/5000000000 : ℝ)|=(1372085361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(761392939/2000000000 : ℝ)|^17 ≤ (28283046497963/100000000000000 : ℝ)^13
        have hw : |(761392939/2000000000 : ℝ)|=(761392939/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3089525563/5000000000 : ℝ)|^17 ≤ (26641583568239/50000000000000 : ℝ)^13
        have hw : |(-3089525563/5000000000 : ℝ)|=(3089525563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s4_s4_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4649410533/10000000000 : ℝ)*x 0 + (-3601101333/10000000000 : ℝ)*x 1 + (-2336007179/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4649410533/10000000000 : ℝ)^17 ≤ (18366600953993/50000000000000 : ℝ)^13 := by
    have hnat : (4649410533 : ℕ)^17*50000000000000^13 ≤ 18366600953993^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4649410533 10000000000 18366600953993 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3601101333/10000000000 : ℝ)^17 ≤ (13149944309081/50000000000000 : ℝ)^13 := by
    have hnat : (3601101333 : ℕ)^17*50000000000000^13 ≤ 13149944309081^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3601101333 10000000000 13149944309081 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2336007179/5000000000 : ℝ)^17 ≤ (36966909456839/100000000000000 : ℝ)^13 := by
    have hnat : (2336007179 : ℕ)^17*100000000000000^13 ≤ 36966909456839^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2336007179 5000000000 36966909456839 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4649410533/10000000000 : ℝ), (-3601101333/10000000000 : ℝ), (-2336007179/5000000000 : ℝ)] ![(18366600953993/50000000000000 : ℝ), (13149944309081/50000000000000 : ℝ), (36966909456839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4649410533/10000000000 : ℝ)|^17 ≤ (18366600953993/50000000000000 : ℝ)^13
        have hw : |(4649410533/10000000000 : ℝ)|=(4649410533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3601101333/10000000000 : ℝ)|^17 ≤ (13149944309081/50000000000000 : ℝ)^13
        have hw : |(-3601101333/10000000000 : ℝ)|=(3601101333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2336007179/5000000000 : ℝ)|^17 ≤ (36966909456839/100000000000000 : ℝ)^13
        have hw : |(-2336007179/5000000000 : ℝ)|=(2336007179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s4_s4_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (939773197/2000000000 : ℝ)*x 0 + (1077052267/2000000000 : ℝ)*x 1 + (2722144989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (939773197/2000000000 : ℝ)^17 ≤ (9311247159821/25000000000000 : ℝ)^13 := by
    have hnat : (939773197 : ℕ)^17*25000000000000^13 ≤ 9311247159821^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      939773197 2000000000 9311247159821 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1077052267/2000000000 : ℝ)^17 ≤ (2782154192479/6250000000000 : ℝ)^13 := by
    have hnat : (1077052267 : ℕ)^17*6250000000000^13 ≤ 2782154192479^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077052267 2000000000 2782154192479 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2722144989/10000000000 : ℝ)^17 ≤ (18240544261319/100000000000000 : ℝ)^13 := by
    have hnat : (2722144989 : ℕ)^17*100000000000000^13 ≤ 18240544261319^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2722144989 10000000000 18240544261319 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(939773197/2000000000 : ℝ), (1077052267/2000000000 : ℝ), (2722144989/10000000000 : ℝ)] ![(9311247159821/25000000000000 : ℝ), (2782154192479/6250000000000 : ℝ), (18240544261319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(939773197/2000000000 : ℝ)|^17 ≤ (9311247159821/25000000000000 : ℝ)^13
        have hw : |(939773197/2000000000 : ℝ)|=(939773197/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1077052267/2000000000 : ℝ)|^17 ≤ (2782154192479/6250000000000 : ℝ)^13
        have hw : |(1077052267/2000000000 : ℝ)|=(1077052267/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2722144989/10000000000 : ℝ)|^17 ≤ (18240544261319/100000000000000 : ℝ)^13
        have hw : |(2722144989/10000000000 : ℝ)|=(2722144989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s4_s4_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5740187749/10000000000 : ℝ)*x 0 + (4314704513/10000000000 : ℝ)*x 1 + (-2728535707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5740187749/10000000000 : ℝ)^17 ≤ (12097329802461/25000000000000 : ℝ)^13 := by
    have hnat : (5740187749 : ℕ)^17*25000000000000^13 ≤ 12097329802461^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5740187749 10000000000 12097329802461 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4314704513/10000000000 : ℝ)^17 ≤ (33314117093841/100000000000000 : ℝ)^13 := by
    have hnat : (4314704513 : ℕ)^17*100000000000000^13 ≤ 33314117093841^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4314704513 10000000000 33314117093841 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2728535707/10000000000 : ℝ)^17 ≤ (18296563668467/100000000000000 : ℝ)^13 := by
    have hnat : (2728535707 : ℕ)^17*100000000000000^13 ≤ 18296563668467^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728535707 10000000000 18296563668467 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5740187749/10000000000 : ℝ), (4314704513/10000000000 : ℝ), (-2728535707/10000000000 : ℝ)] ![(12097329802461/25000000000000 : ℝ), (33314117093841/100000000000000 : ℝ), (18296563668467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5740187749/10000000000 : ℝ)|^17 ≤ (12097329802461/25000000000000 : ℝ)^13
        have hw : |(5740187749/10000000000 : ℝ)|=(5740187749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4314704513/10000000000 : ℝ)|^17 ≤ (33314117093841/100000000000000 : ℝ)^13
        have hw : |(4314704513/10000000000 : ℝ)|=(4314704513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2728535707/10000000000 : ℝ)|^17 ≤ (18296563668467/100000000000000 : ℝ)^13
        have hw : |(-2728535707/10000000000 : ℝ)|=(2728535707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s4_s4_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-684188953/2500000000 : ℝ)*x 0 + (3687794551/10000000000 : ℝ)*x 1 + (-3143355059/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (684188953/2500000000 : ℝ)^17 ≤ (734747135567/4000000000000 : ℝ)^13 := by
    have hnat : (684188953 : ℕ)^17*4000000000000^13 ≤ 734747135567^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684188953 2500000000 734747135567 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3687794551/10000000000 : ℝ)^17 ≤ (6782724522387/25000000000000 : ℝ)^13 := by
    have hnat : (3687794551 : ℕ)^17*25000000000000^13 ≤ 6782724522387^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3687794551 10000000000 6782724522387 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3143355059/5000000000 : ℝ)^17 ≤ (1703138234417/3125000000000 : ℝ)^13 := by
    have hnat : (3143355059 : ℕ)^17*3125000000000^13 ≤ 1703138234417^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3143355059 5000000000 1703138234417 3125000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-684188953/2500000000 : ℝ), (3687794551/10000000000 : ℝ), (-3143355059/5000000000 : ℝ)] ![(734747135567/4000000000000 : ℝ), (6782724522387/25000000000000 : ℝ), (1703138234417/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-684188953/2500000000 : ℝ)|^17 ≤ (734747135567/4000000000000 : ℝ)^13
        have hw : |(-684188953/2500000000 : ℝ)|=(684188953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3687794551/10000000000 : ℝ)|^17 ≤ (6782724522387/25000000000000 : ℝ)^13
        have hw : |(3687794551/10000000000 : ℝ)|=(3687794551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3143355059/5000000000 : ℝ)|^17 ≤ (1703138234417/3125000000000 : ℝ)^13
        have hw : |(-3143355059/5000000000 : ℝ)|=(3143355059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s4_s4_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4612237387/10000000000 : ℝ)*x 0 + (-1724794517/5000000000 : ℝ)*x 1 + (-2423510301/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4612237387/10000000000 : ℝ)^17 ≤ (36349618105381/100000000000000 : ℝ)^13 := by
    have hnat : (4612237387 : ℕ)^17*100000000000000^13 ≤ 36349618105381^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4612237387 10000000000 36349618105381 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1724794517/5000000000 : ℝ)^17 ≤ (24862335946031/100000000000000 : ℝ)^13 := by
    have hnat : (1724794517 : ℕ)^17*100000000000000^13 ≤ 24862335946031^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1724794517 5000000000 24862335946031 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2423510301/5000000000 : ℝ)^17 ≤ (38788045935789/100000000000000 : ℝ)^13 := by
    have hnat : (2423510301 : ℕ)^17*100000000000000^13 ≤ 38788045935789^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2423510301 5000000000 38788045935789 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4612237387/10000000000 : ℝ), (-1724794517/5000000000 : ℝ), (-2423510301/5000000000 : ℝ)] ![(36349618105381/100000000000000 : ℝ), (24862335946031/100000000000000 : ℝ), (38788045935789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4612237387/10000000000 : ℝ)|^17 ≤ (36349618105381/100000000000000 : ℝ)^13
        have hw : |(4612237387/10000000000 : ℝ)|=(4612237387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1724794517/5000000000 : ℝ)|^17 ≤ (24862335946031/100000000000000 : ℝ)^13
        have hw : |(-1724794517/5000000000 : ℝ)|=(1724794517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2423510301/5000000000 : ℝ)|^17 ≤ (38788045935789/100000000000000 : ℝ)^13
        have hw : |(-2423510301/5000000000 : ℝ)|=(2423510301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s4_s4_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (291356427/625000000 : ℝ)*x 0 + (5559257329/10000000000 : ℝ)*x 1 + (2548627061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (291356427/625000000 : ℝ)^17 ≤ (4607531540041/12500000000000 : ℝ)^13 := by
    have hnat : (291356427 : ℕ)^17*12500000000000^13 ≤ 4607531540041^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      291356427 625000000 4607531540041 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5559257329/10000000000 : ℝ)^17 ≤ (46404532427247/100000000000000 : ℝ)^13 := by
    have hnat : (5559257329 : ℕ)^17*100000000000000^13 ≤ 46404532427247^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5559257329 10000000000 46404532427247 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2548627061/10000000000 : ℝ)^17 ≤ (2091901905011/12500000000000 : ℝ)^13 := by
    have hnat : (2548627061 : ℕ)^17*12500000000000^13 ≤ 2091901905011^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2548627061 10000000000 2091901905011 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(291356427/625000000 : ℝ), (5559257329/10000000000 : ℝ), (2548627061/10000000000 : ℝ)] ![(4607531540041/12500000000000 : ℝ), (46404532427247/100000000000000 : ℝ), (2091901905011/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(291356427/625000000 : ℝ)|^17 ≤ (4607531540041/12500000000000 : ℝ)^13
        have hw : |(291356427/625000000 : ℝ)|=(291356427/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5559257329/10000000000 : ℝ)|^17 ≤ (46404532427247/100000000000000 : ℝ)^13
        have hw : |(5559257329/10000000000 : ℝ)|=(5559257329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2548627061/10000000000 : ℝ)|^17 ≤ (2091901905011/12500000000000 : ℝ)^13
        have hw : |(2548627061/10000000000 : ℝ)|=(2548627061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s4_s4_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5723986803/10000000000 : ℝ)*x 0 + (564567869/1250000000 : ℝ)*x 1 + (-2512145951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5723986803/10000000000 : ℝ)^17 ≤ (1205270044571/2500000000000 : ℝ)^13 := by
    have hnat : (5723986803 : ℕ)^17*2500000000000^13 ≤ 1205270044571^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5723986803 10000000000 1205270044571 2500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (564567869/1250000000 : ℝ)^17 ≤ (35366546271817/100000000000000 : ℝ)^13 := by
    have hnat : (564567869 : ℕ)^17*100000000000000^13 ≤ 35366546271817^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564567869 1250000000 35366546271817 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2512145951/10000000000 : ℝ)^17 ≤ (16422651927869/100000000000000 : ℝ)^13 := by
    have hnat : (2512145951 : ℕ)^17*100000000000000^13 ≤ 16422651927869^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2512145951 10000000000 16422651927869 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5723986803/10000000000 : ℝ), (564567869/1250000000 : ℝ), (-2512145951/10000000000 : ℝ)] ![(1205270044571/2500000000000 : ℝ), (35366546271817/100000000000000 : ℝ), (16422651927869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5723986803/10000000000 : ℝ)|^17 ≤ (1205270044571/2500000000000 : ℝ)^13
        have hw : |(5723986803/10000000000 : ℝ)|=(5723986803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(564567869/1250000000 : ℝ)|^17 ≤ (35366546271817/100000000000000 : ℝ)^13
        have hw : |(564567869/1250000000 : ℝ)|=(564567869/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2512145951/10000000000 : ℝ)|^17 ≤ (16422651927869/100000000000000 : ℝ)^13
        have hw : |(-2512145951/10000000000 : ℝ)|=(2512145951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s4_s4_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-258764389/1000000000 : ℝ)*x 0 + (380825893/1000000000 : ℝ)*x 1 + (-3149216033/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (258764389/1000000000 : ℝ)^17 ≤ (4267757663831/25000000000000 : ℝ)^13 := by
    have hnat : (258764389 : ℕ)^17*25000000000000^13 ≤ 4267757663831^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258764389 1000000000 4267757663831 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (380825893/1000000000 : ℝ)^17 ≤ (28295620941057/100000000000000 : ℝ)^13 := by
    have hnat : (380825893 : ℕ)^17*100000000000000^13 ≤ 28295620941057^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      380825893 1000000000 28295620941057 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3149216033/5000000000 : ℝ)^17 ≤ (54633348391311/100000000000000 : ℝ)^13 := by
    have hnat : (3149216033 : ℕ)^17*100000000000000^13 ≤ 54633348391311^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3149216033 5000000000 54633348391311 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-258764389/1000000000 : ℝ), (380825893/1000000000 : ℝ), (-3149216033/5000000000 : ℝ)] ![(4267757663831/25000000000000 : ℝ), (28295620941057/100000000000000 : ℝ), (54633348391311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-258764389/1000000000 : ℝ)|^17 ≤ (4267757663831/25000000000000 : ℝ)^13
        have hw : |(-258764389/1000000000 : ℝ)|=(258764389/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(380825893/1000000000 : ℝ)|^17 ≤ (28295620941057/100000000000000 : ℝ)^13
        have hw : |(380825893/1000000000 : ℝ)|=(380825893/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3149216033/5000000000 : ℝ)|^17 ≤ (54633348391311/100000000000000 : ℝ)^13
        have hw : |(-3149216033/5000000000 : ℝ)|=(3149216033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s4_s4_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4538258667/10000000000 : ℝ)*x 0 + (-3550416521/10000000000 : ℝ)*x 1 + (-2414235687/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4538258667/10000000000 : ℝ)^17 ≤ (35589075458739/100000000000000 : ℝ)^13 := by
    have hnat : (4538258667 : ℕ)^17*100000000000000^13 ≤ 35589075458739^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4538258667 10000000000 35589075458739 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3550416521/10000000000 : ℝ)^17 ≤ (3227109639209/12500000000000 : ℝ)^13 := by
    have hnat : (3550416521 : ℕ)^17*12500000000000^13 ≤ 3227109639209^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3550416521 10000000000 3227109639209 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2414235687/5000000000 : ℝ)^17 ≤ (19297023700989/50000000000000 : ℝ)^13 := by
    have hnat : (2414235687 : ℕ)^17*50000000000000^13 ≤ 19297023700989^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2414235687 5000000000 19297023700989 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4538258667/10000000000 : ℝ), (-3550416521/10000000000 : ℝ), (-2414235687/5000000000 : ℝ)] ![(35589075458739/100000000000000 : ℝ), (3227109639209/12500000000000 : ℝ), (19297023700989/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4538258667/10000000000 : ℝ)|^17 ≤ (35589075458739/100000000000000 : ℝ)^13
        have hw : |(4538258667/10000000000 : ℝ)|=(4538258667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3550416521/10000000000 : ℝ)|^17 ≤ (3227109639209/12500000000000 : ℝ)^13
        have hw : |(-3550416521/10000000000 : ℝ)|=(3550416521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2414235687/5000000000 : ℝ)|^17 ≤ (19297023700989/50000000000000 : ℝ)^13
        have hw : |(-2414235687/5000000000 : ℝ)|=(2414235687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s4_s4_16 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4856891853/10000000000 : ℝ)*x 0 + (13393593/25000000 : ℝ)*x 1 + (2567176837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4856891853/10000000000 : ℝ)^17 ≤ (4861422300001/12500000000000 : ℝ)^13 := by
    have hnat : (4856891853 : ℕ)^17*12500000000000^13 ≤ 4861422300001^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4856891853 10000000000 4861422300001 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13393593/25000000 : ℝ)^17 ≤ (44213945354173/100000000000000 : ℝ)^13 := by
    have hnat : (13393593 : ℕ)^17*100000000000000^13 ≤ 44213945354173^13*25000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13393593 25000000 44213945354173 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2567176837/10000000000 : ℝ)^17 ≤ (42236690583/250000000000 : ℝ)^13 := by
    have hnat : (2567176837 : ℕ)^17*250000000000^13 ≤ 42236690583^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2567176837 10000000000 42236690583 250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4856891853/10000000000 : ℝ), (13393593/25000000 : ℝ), (2567176837/10000000000 : ℝ)] ![(4861422300001/12500000000000 : ℝ), (44213945354173/100000000000000 : ℝ), (42236690583/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4856891853/10000000000 : ℝ)|^17 ≤ (4861422300001/12500000000000 : ℝ)^13
        have hw : |(4856891853/10000000000 : ℝ)|=(4856891853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(13393593/25000000 : ℝ)|^17 ≤ (44213945354173/100000000000000 : ℝ)^13
        have hw : |(13393593/25000000 : ℝ)|=(13393593/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2567176837/10000000000 : ℝ)|^17 ≤ (42236690583/250000000000 : ℝ)^13
        have hw : |(2567176837/10000000000 : ℝ)|=(2567176837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s4_s4_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1193621887/2000000000 : ℝ)*x 0 + (533753197/1250000000 : ℝ)*x 1 + (-1244155897/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1193621887/2000000000 : ℝ)^17 ≤ (10183415748019/20000000000000 : ℝ)^13 := by
    have hnat : (1193621887 : ℕ)^17*20000000000000^13 ≤ 10183415748019^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1193621887 2000000000 10183415748019 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (533753197/1250000000 : ℝ)^17 ≤ (32863724160599/100000000000000 : ℝ)^13 := by
    have hnat : (533753197 : ℕ)^17*100000000000000^13 ≤ 32863724160599^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533753197 1250000000 32863724160599 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1244155897/5000000000 : ℝ)^17 ≤ (16219197090797/100000000000000 : ℝ)^13 := by
    have hnat : (1244155897 : ℕ)^17*100000000000000^13 ≤ 16219197090797^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1244155897 5000000000 16219197090797 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1193621887/2000000000 : ℝ), (533753197/1250000000 : ℝ), (-1244155897/5000000000 : ℝ)] ![(10183415748019/20000000000000 : ℝ), (32863724160599/100000000000000 : ℝ), (16219197090797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1193621887/2000000000 : ℝ)|^17 ≤ (10183415748019/20000000000000 : ℝ)^13
        have hw : |(1193621887/2000000000 : ℝ)|=(1193621887/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(533753197/1250000000 : ℝ)|^17 ≤ (32863724160599/100000000000000 : ℝ)^13
        have hw : |(533753197/1250000000 : ℝ)|=(533753197/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1244155897/5000000000 : ℝ)|^17 ≤ (16219197090797/100000000000000 : ℝ)^13
        have hw : |(-1244155897/5000000000 : ℝ)|=(1244155897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s4_s4_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2550024489/10000000000 : ℝ)*x 0 + (3923273939/10000000000 : ℝ)*x 1 + (-12455767/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2550024489/10000000000 : ℝ)^17 ≤ (4186803916437/25000000000000 : ℝ)^13 := by
    have hnat : (2550024489 : ℕ)^17*25000000000000^13 ≤ 4186803916437^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2550024489 10000000000 4186803916437 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3923273939/10000000000 : ℝ)^17 ≤ (14709145637903/50000000000000 : ℝ)^13 := by
    have hnat : (3923273939 : ℕ)^17*50000000000000^13 ≤ 14709145637903^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3923273939 10000000000 14709145637903 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12455767/20000000 : ℝ)^17 ≤ (26917246520451/50000000000000 : ℝ)^13 := by
    have hnat : (12455767 : ℕ)^17*50000000000000^13 ≤ 26917246520451^13*20000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12455767 20000000 26917246520451 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2550024489/10000000000 : ℝ), (3923273939/10000000000 : ℝ), (-12455767/20000000 : ℝ)] ![(4186803916437/25000000000000 : ℝ), (14709145637903/50000000000000 : ℝ), (26917246520451/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2550024489/10000000000 : ℝ)|^17 ≤ (4186803916437/25000000000000 : ℝ)^13
        have hw : |(-2550024489/10000000000 : ℝ)|=(2550024489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3923273939/10000000000 : ℝ)|^17 ≤ (14709145637903/50000000000000 : ℝ)^13
        have hw : |(3923273939/10000000000 : ℝ)|=(3923273939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-12455767/20000000 : ℝ)|^17 ≤ (26917246520451/50000000000000 : ℝ)^13
        have hw : |(-12455767/20000000 : ℝ)|=(12455767/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s4_s4_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2422522271/5000000000 : ℝ)*x 0 + (-3486281867/10000000000 : ℝ)*x 1 + (-4580599721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2422522271/5000000000 : ℝ)^17 ≤ (38767368271073/100000000000000 : ℝ)^13 := by
    have hnat : (2422522271 : ℕ)^17*100000000000000^13 ≤ 38767368271073^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2422522271 5000000000 38767368271073 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3486281867/10000000000 : ℝ)^17 ≤ (12604364736609/50000000000000 : ℝ)^13 := by
    have hnat : (3486281867 : ℕ)^17*50000000000000^13 ≤ 12604364736609^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3486281867 10000000000 12604364736609 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4580599721/10000000000 : ℝ)^17 ≤ (9005975558453/25000000000000 : ℝ)^13 := by
    have hnat : (4580599721 : ℕ)^17*25000000000000^13 ≤ 9005975558453^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4580599721 10000000000 9005975558453 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2422522271/5000000000 : ℝ), (-3486281867/10000000000 : ℝ), (-4580599721/10000000000 : ℝ)] ![(38767368271073/100000000000000 : ℝ), (12604364736609/50000000000000 : ℝ), (9005975558453/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2422522271/5000000000 : ℝ)|^17 ≤ (38767368271073/100000000000000 : ℝ)^13
        have hw : |(2422522271/5000000000 : ℝ)|=(2422522271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3486281867/10000000000 : ℝ)|^17 ≤ (12604364736609/50000000000000 : ℝ)^13
        have hw : |(-3486281867/10000000000 : ℝ)|=(3486281867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4580599721/10000000000 : ℝ)|^17 ≤ (9005975558453/25000000000000 : ℝ)^13
        have hw : |(-4580599721/10000000000 : ℝ)|=(4580599721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s4_s4_23 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (913980107/2000000000 : ℝ)*x 0 + (5459870581/10000000000 : ℝ)*x 1 + (2781618973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (913980107/2000000000 : ℝ)^17 ≤ (35913908348069/100000000000000 : ℝ)^13 := by
    have hnat : (913980107 : ℕ)^17*100000000000000^13 ≤ 35913908348069^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      913980107 2000000000 35913908348069 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5459870581/10000000000 : ℝ)^17 ≤ (1812906349641/4000000000000 : ℝ)^13 := by
    have hnat : (5459870581 : ℕ)^17*4000000000000^13 ≤ 1812906349641^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5459870581 10000000000 1812906349641 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2781618973/10000000000 : ℝ)^17 ≤ (18763432895237/100000000000000 : ℝ)^13 := by
    have hnat : (2781618973 : ℕ)^17*100000000000000^13 ≤ 18763432895237^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2781618973 10000000000 18763432895237 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(913980107/2000000000 : ℝ), (5459870581/10000000000 : ℝ), (2781618973/10000000000 : ℝ)] ![(35913908348069/100000000000000 : ℝ), (1812906349641/4000000000000 : ℝ), (18763432895237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(913980107/2000000000 : ℝ)|^17 ≤ (35913908348069/100000000000000 : ℝ)^13
        have hw : |(913980107/2000000000 : ℝ)|=(913980107/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5459870581/10000000000 : ℝ)|^17 ≤ (1812906349641/4000000000000 : ℝ)^13
        have hw : |(5459870581/10000000000 : ℝ)|=(5459870581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2781618973/10000000000 : ℝ)|^17 ≤ (18763432895237/100000000000000 : ℝ)^13
        have hw : |(2781618973/10000000000 : ℝ)|=(2781618973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304052_s4_s4_27 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (375272061/625000000 : ℝ)*x 0 + (2082596817/5000000000 : ℝ)*x 1 + (-2563790233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (375272061/625000000 : ℝ)^17 ≤ (3207613191549/6250000000000 : ℝ)^13 := by
    have hnat : (375272061 : ℕ)^17*6250000000000^13 ≤ 3207613191549^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375272061 625000000 3207613191549 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2082596817/5000000000 : ℝ)^17 ≤ (31812651772691/100000000000000 : ℝ)^13 := by
    have hnat : (2082596817 : ℕ)^17*100000000000000^13 ≤ 31812651772691^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082596817 5000000000 31812651772691 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2563790233/10000000000 : ℝ)^17 ≤ (8432768574553/50000000000000 : ℝ)^13 := by
    have hnat : (2563790233 : ℕ)^17*50000000000000^13 ≤ 8432768574553^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2563790233 10000000000 8432768574553 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(375272061/625000000 : ℝ), (2082596817/5000000000 : ℝ), (-2563790233/10000000000 : ℝ)] ![(3207613191549/6250000000000 : ℝ), (31812651772691/100000000000000 : ℝ), (8432768574553/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(375272061/625000000 : ℝ)|^17 ≤ (3207613191549/6250000000000 : ℝ)^13
        have hw : |(375272061/625000000 : ℝ)|=(375272061/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2082596817/5000000000 : ℝ)|^17 ≤ (31812651772691/100000000000000 : ℝ)^13
        have hw : |(2082596817/5000000000 : ℝ)|=(2082596817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2563790233/10000000000 : ℝ)|^17 ≤ (8432768574553/50000000000000 : ℝ)^13
        have hw : |(-2563790233/10000000000 : ℝ)|=(2563790233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304052_s4 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]])
    (hprev3 : (0 : ℝ) ≤ ((15809/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15809/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8587/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8587/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-21281/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-21281/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((16929/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16929/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18903/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(18903/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-10299/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-10299/100000 : ℝ)*X 1 2) := by
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
  have main2 : (76617/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76617/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
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
  rcases hprev3 with ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩
  have s4_pow0 : (15809/50000 : ℝ) ^ (33/8 : ℝ) ≤ (43271244333662369/5000000000000000000 : ℝ) := by
    have hpowers : (15809/50000 : ℝ)^33 ≤ (43271244333662369/5000000000000000000 : ℝ)^8 := by
      have hnat : (15809 : ℕ)^33*5000000000000000000^8 ≤ 43271244333662369^8*50000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15809 50000 43271244333662369 5000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15809/50000 : ℝ)) (X := (43271244333662369/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s4_corner0a : (5043271244333662369/5000000000000000000 : ℝ) ≤ (5010455784421057/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (5043271244333662369/5000000000000000000 : ℝ)^8 ≤ (5010455784421057/5000000000000000 : ℝ)^33 := by
      have hnat : (5043271244333662369 : ℕ)^8*5000000000000000^33 ≤ 5010455784421057^33*5000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5043271244333662369 5000000000000000000 5010455784421057 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5010455784421057/5000000000000000 : ℝ)) (X := (5043271244333662369/5000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s4_corner0b : (2543271244333662369/2500000000000000000 : ℝ) ≤ (2510421912768761/2500000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (2543271244333662369/2500000000000000000 : ℝ)^8 ≤ (2510421912768761/2500000000000000 : ℝ)^33 := by
      have hnat : (2543271244333662369 : ℕ)^8*2500000000000000^33 ≤ 2510421912768761^33*2500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2543271244333662369 2500000000000000000 2510421912768761 2500000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2510421912768761/2500000000000000 : ℝ)) (X := (2543271244333662369/2500000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s4_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(10455784421057/1580900000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(2077608223293/316180000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (15809/50000 : ℝ)) (alpha := (10455784421057/1580900000000000 : ℝ)) (beta := (2077608223293/316180000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow0,s4_corner0a]) (by linarith only [s4_pow0,s4_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (15809/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(10455784421057/1580900000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(2077608223293/316180000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow1 : (8587/25000 : ℝ) ^ (33/8 : ℝ) ≤ (1217849153758977401/100000000000000000000 : ℝ) := by
    have hpowers : (8587/25000 : ℝ)^33 ≤ (1217849153758977401/100000000000000000000 : ℝ)^8 := by
      have hnat : (8587 : ℕ)^33*100000000000000000000^8 ≤ 1217849153758977401^8*25000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8587 25000 1217849153758977401 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8587/25000 : ℝ)) (X := (1217849153758977401/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s4_corner1a : (101217849153758977401/100000000000000000000 : ℝ) ≤ (10029388385135547/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (101217849153758977401/100000000000000000000 : ℝ)^8 ≤ (10029388385135547/10000000000000000 : ℝ)^33 := by
      have hnat : (101217849153758977401 : ℕ)^8*10000000000000000^33 ≤ 10029388385135547^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101217849153758977401 100000000000000000000 10029388385135547 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10029388385135547/10000000000000000 : ℝ)) (X := (101217849153758977401/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s4_corner1b : (51217849153758977401/50000000000000000000 : ℝ) ≤ (10058510099910253/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (51217849153758977401/50000000000000000000 : ℝ)^8 ≤ (10058510099910253/10000000000000000 : ℝ)^33 := by
      have hnat : (51217849153758977401 : ℕ)^8*10000000000000000^33 ≤ 10058510099910253^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51217849153758977401 50000000000000000000 10058510099910253 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10058510099910253/10000000000000000 : ℝ)) (X := (51217849153758977401/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s4_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(29388385135547/3434800000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(14560857387353/1717400000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (8587/25000 : ℝ)) (alpha := (29388385135547/3434800000000000 : ℝ)) (beta := (14560857387353/1717400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow1,s4_corner1a]) (by linarith only [s4_pow1,s4_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (8587/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(29388385135547/3434800000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(14560857387353/1717400000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow2 : (21281/100000 : ℝ) ^ (33/8 : ℝ) ≤ (84515649854452153/50000000000000000000 : ℝ) := by
    have hpowers : (21281/100000 : ℝ)^33 ≤ (84515649854452153/50000000000000000000 : ℝ)^8 := by
      have hnat : (21281 : ℕ)^33*50000000000000000000^8 ≤ 84515649854452153^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21281 100000 84515649854452153 50000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21281/100000 : ℝ)) (X := (84515649854452153/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s4_corner2a : (50084515649854452153/50000000000000000000 : ℝ) ≤ (2501023776855003/2500000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (50084515649854452153/50000000000000000000 : ℝ)^8 ≤ (2501023776855003/2500000000000000 : ℝ)^33 := by
      have hnat : (50084515649854452153 : ℕ)^8*2500000000000000^33 ≤ 2501023776855003^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50084515649854452153 50000000000000000000 2501023776855003 2500000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501023776855003/2500000000000000 : ℝ)) (X := (50084515649854452153/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s4_corner2b : (25084515649854452153/25000000000000000000 : ℝ) ≤ (10008184983080891/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (25084515649854452153/25000000000000000000 : ℝ)^8 ≤ (10008184983080891/10000000000000000 : ℝ)^33 := by
      have hnat : (25084515649854452153 : ℕ)^8*10000000000000000^33 ≤ 10008184983080891^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25084515649854452153 25000000000000000000 10008184983080891 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008184983080891/10000000000000000 : ℝ)) (X := (25084515649854452153/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s4_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1023776855003/532025000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(4089875660879/2128100000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (21281/100000 : ℝ)) (alpha := (1023776855003/532025000000000 : ℝ)) (beta := (4089875660879/2128100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow2,s4_corner2a]) (by linarith only [s4_pow2,s4_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (21281/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1023776855003/532025000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(4089875660879/2128100000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s4_0 : ((-1372085361/5000000000 : ℝ)*X 0 0+(761392939/2000000000 : ℝ)*X 0 1+(-3089525563/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s4_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_1 : ((4649410533/10000000000 : ℝ)*X 1 0+(-3601101333/10000000000 : ℝ)*X 1 1+(-2336007179/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s4_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_2 : ((939773197/2000000000 : ℝ)*X 2 0+(1077052267/2000000000 : ℝ)*X 2 1+(2722144989/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s4_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_6 : ((5740187749/10000000000 : ℝ)*X 0 0+(4314704513/10000000000 : ℝ)*X 0 1+(-2728535707/10000000000 : ℝ)*X 0 2+(5740187749/10000000000 : ℝ)*X 1 0+(4314704513/10000000000 : ℝ)*X 1 1+(-2728535707/10000000000 : ℝ)*X 1 2+(5740187749/10000000000 : ℝ)*X 2 0+(4314704513/10000000000 : ℝ)*X 2 1+(-2728535707/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s4_s4_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_7 : ((-684188953/2500000000 : ℝ)*X 0 0+(3687794551/10000000000 : ℝ)*X 0 1+(-3143355059/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s4_s4_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_8 : ((4612237387/10000000000 : ℝ)*X 1 0+(-1724794517/5000000000 : ℝ)*X 1 1+(-2423510301/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s4_s4_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_9 : ((291356427/625000000 : ℝ)*X 2 0+(5559257329/10000000000 : ℝ)*X 2 1+(2548627061/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s4_s4_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_13 : ((5723986803/10000000000 : ℝ)*X 0 0+(564567869/1250000000 : ℝ)*X 0 1+(-2512145951/10000000000 : ℝ)*X 0 2+(5723986803/10000000000 : ℝ)*X 1 0+(564567869/1250000000 : ℝ)*X 1 1+(-2512145951/10000000000 : ℝ)*X 1 2+(5723986803/10000000000 : ℝ)*X 2 0+(564567869/1250000000 : ℝ)*X 2 1+(-2512145951/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s4_s4_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_14 : ((-258764389/1000000000 : ℝ)*X 0 0+(380825893/1000000000 : ℝ)*X 0 1+(-3149216033/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s4_s4_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_15 : ((4538258667/10000000000 : ℝ)*X 1 0+(-3550416521/10000000000 : ℝ)*X 1 1+(-2414235687/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s4_s4_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_16 : ((4856891853/10000000000 : ℝ)*X 2 0+(13393593/25000000 : ℝ)*X 2 1+(2567176837/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s4_s4_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_20 : ((1193621887/2000000000 : ℝ)*X 0 0+(533753197/1250000000 : ℝ)*X 0 1+(-1244155897/5000000000 : ℝ)*X 0 2+(1193621887/2000000000 : ℝ)*X 1 0+(533753197/1250000000 : ℝ)*X 1 1+(-1244155897/5000000000 : ℝ)*X 1 2+(1193621887/2000000000 : ℝ)*X 2 0+(533753197/1250000000 : ℝ)*X 2 1+(-1244155897/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s4_s4_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_21 : ((-2550024489/10000000000 : ℝ)*X 0 0+(3923273939/10000000000 : ℝ)*X 0 1+(-12455767/20000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s4_s4_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_22 : ((2422522271/5000000000 : ℝ)*X 1 0+(-3486281867/10000000000 : ℝ)*X 1 1+(-4580599721/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s4_s4_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_23 : ((913980107/2000000000 : ℝ)*X 2 0+(5459870581/10000000000 : ℝ)*X 2 1+(2781618973/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s4_s4_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_27 : ((375272061/625000000 : ℝ)*X 0 0+(2082596817/5000000000 : ℝ)*X 0 1+(-2563790233/10000000000 : ℝ)*X 0 2+(375272061/625000000 : ℝ)*X 1 0+(2082596817/5000000000 : ℝ)*X 1 1+(-2563790233/10000000000 : ℝ)*X 1 2+(375272061/625000000 : ℝ)*X 2 0+(2082596817/5000000000 : ℝ)*X 2 1+(-2563790233/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304052_s4_s4_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s4_0 : (0 : ℝ) ≤ ((16929/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16929/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1862392298955245313757950281361/577787164424600000000000000000000000 : ℝ) := by norm_num
    linear_combination (4877211515439/1000000000000 : ℝ)*(base39) + (2821060090763/500000000000 : ℝ)*(base59) + (178093/250000000000 : ℝ)*(base60) + (27405097036233/1000000000000 : ℝ)*(major_s4_0) + (27405097036233/1000000000000 : ℝ)*(major_s4_1) + (27405097036233/1000000000000 : ℝ)*(major_s4_2) + (1524853/20000000000 : ℝ)*(sp_s4_1) + (55030837/1000000000000 : ℝ)*(sp_s4_6) + (9185383407571/250000000000 : ℝ)*(sp_s4_7) + (293930339753/8000000000 : ℝ)*(sp_s4_8) + (36741416906231/1000000000000 : ℝ)*(sp_s4_9) + (180686043369/10000000000 : ℝ)*(sp_s4_13) + (164918509/1000000000000 : ℝ)*(sp_s4_15) + (29181013/250000000000 : ℝ)*(sp_s4_23) + (2258582420967/125000000000 : ℝ)*(f.failure) + (9185383407571/250000000000 : ℝ)*(f.sum) + (21088016116790424661/73095978800000000000000000000000 : ℝ)*base62 + (893398367327457/2128100000000000000000000000 : ℝ)*base64 + (708879945886291/1717400000000000000000000000 : ℝ)*base67 + (596973436889707/1064050000000000000000000000 : ℝ)*base68 + (2471645172038201291/16821566450000000000000000000000 : ℝ)*base70 + (16674602639181/316180000000000000000000000 : ℝ)*base72 + (369115572200549/3434800000000000000000000000 : ℝ)*base74 + (55908116757001/1580900000000000000000000000 : ℝ)*base77 + (1762449283968310891/27150376600000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (1419/3125000000000000 : ℝ)*base86 + (1419/3125000000000000 : ℝ)*base88 + (1419/3125000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s4_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18903/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(18903/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7004547321146947671852916595763/577787164424600000000000000000000000 : ℝ) := by norm_num
    linear_combination (5044116643919/1000000000000 : ℝ)*(base39) + (1103784904597/200000000000 : ℝ)*(base59) + (27711029148081/1000000000000 : ℝ)*(major_s4_0) + (27711029148081/1000000000000 : ℝ)*(major_s4_1) + (27711029148081/1000000000000 : ℝ)*(major_s4_2) + (19878563/500000000000 : ℝ)*(sp_s4_1) + (6606043/62500000000 : ℝ)*(sp_s4_2) + (121128371/1000000000000 : ℝ)*(sp_s4_8) + (37151457256857/1000000000000 : ℝ)*(sp_s4_14) + (37151527614533/1000000000000 : ℝ)*(sp_s4_15) + (37151582803341/1000000000000 : ℝ)*(sp_s4_16) + (2283769992327/125000000000 : ℝ)*(sp_s4_20) + (231243173/1000000000000 : ℝ)*(sp_s4_21) + (205816489/1000000000000 : ℝ)*(sp_s4_27) + (570948929847/31250000000 : ℝ)*(f.failure) + (37151688500029/1000000000000 : ℝ)*(f.sum) + (28623505523412235837/73095978800000000000000000000000 : ℝ)*base62 + (1571748509503389/2128100000000000000000000000 : ℝ)*base64 + (1861949579209627/1717400000000000000000000000 : ℝ)*base67 + (1348005734411/1039111328125000000000000 : ℝ)*base68 + (782252672900042507/4205391612500000000000000000000 : ℝ)*base71 + (283633926446527/316180000000000000000000000 : ℝ)*base73 + (2860172502428653/3434800000000000000000000000 : ℝ)*base74 + (1028074065511363/1580900000000000000000000000 : ℝ)*base76 + (6552774322440327693/27150376600000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (1059/3125000000000000 : ℝ)*base87 + (1059/3125000000000000 : ℝ)*base89 + (1059/3125000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s4_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-10299/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-10299/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1278047583689060504469183048891/115557432884920000000000000000000000 : ℝ) := by norm_num
    linear_combination (4728876078141/1000000000000 : ℝ)*(base39) + (163723/50000000000 : ℝ)*(base40) + (4537557696217/1000000000000 : ℝ)*(base59) + (22978111748611/1000000000000 : ℝ)*(major_s4_0) + (22978111748611/1000000000000 : ℝ)*(major_s4_1) + (22978111748611/1000000000000 : ℝ)*(major_s4_2) + (39888541/500000000000 : ℝ)*(sp_s4_0) + (90231811/500000000000 : ℝ)*(sp_s4_2) + (75372069/500000000000 : ℝ)*(sp_s4_9) + (130699929/250000000000 : ℝ)*(sp_s4_20) + (3080626942549/100000000000 : ℝ)*(sp_s4_21) + (7701587300643/250000000000 : ℝ)*(sp_s4_22) + (7701504498703/250000000000 : ℝ)*(sp_s4_23) + (7574673904157/500000000000 : ℝ)*(sp_s4_27) + (1514987060803/100000000000 : ℝ)*(f.failure) + (7701587300643/250000000000 : ℝ)*(f.sum) + (9353570527408526287/73095978800000000000000000000000 : ℝ)*base62 + (756528836812589/2128100000000000000000000000 : ℝ)*base64 + (71110107880163/1717400000000000000000000000 : ℝ)*base66 + (21678651895137/532025000000000000000000000 : ℝ)*base68 + (15690361828218845077/16821566450000000000000000000000 : ℝ)*base70 + (283602220202227/316180000000000000000000000 : ℝ)*base73 + (150106929953183/3434800000000000000000000000 : ℝ)*base74 + (765209758809413/1580900000000000000000000000 : ℝ)*base76 + (26779968603632840703/27150376600000000000000000000000 : ℝ)*base79 + (327/1250000000000000 : ℝ)*base87 + (327/1250000000000000 : ℝ)*base89 + (327/1250000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]])
    (hprev3 : (0 : ℝ) ≤ ((15809/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15809/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8587/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8587/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-21281/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-21281/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((16929/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16929/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18903/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(18903/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-10299/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-10299/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304052_s4 p hpa hpb X hX hprev3

#print axioms solution
