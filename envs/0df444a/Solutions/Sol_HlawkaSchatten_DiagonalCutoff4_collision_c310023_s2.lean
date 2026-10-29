-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c310023_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:23:21.015526+00:00
-- url     : https://prove2.me/submissions/ba79cae1-e4fc-4dcf-b813-84481c8201d2

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
theorem collision_support_c310023_s2_s2_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-704114217/2000000000 : ℝ)*x 0 + (5363030059/10000000000 : ℝ)*x 1 + (477143547/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (704114217/2000000000 : ℝ)^9 ≤ (26126065330331/100000000000000 : ℝ)^7 := by
    have hnat : (704114217 : ℕ)^9*100000000000000^7 ≤ 26126065330331^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      704114217 2000000000 26126065330331 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5363030059/10000000000 : ℝ)^9 ≤ (44884755995181/100000000000000 : ℝ)^7 := by
    have hnat : (5363030059 : ℕ)^9*100000000000000^7 ≤ 44884755995181^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363030059 10000000000 44884755995181 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (477143547/1250000000 : ℝ)^9 ≤ (28989178655441/100000000000000 : ℝ)^7 := by
    have hnat : (477143547 : ℕ)^9*100000000000000^7 ≤ 28989178655441^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      477143547 1250000000 28989178655441 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-704114217/2000000000 : ℝ), (5363030059/10000000000 : ℝ), (477143547/1250000000 : ℝ)] ![(26126065330331/100000000000000 : ℝ), (44884755995181/100000000000000 : ℝ), (28989178655441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-704114217/2000000000 : ℝ)|^9 ≤ (26126065330331/100000000000000 : ℝ)^7
        have hw : |(-704114217/2000000000 : ℝ)|=(704114217/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5363030059/10000000000 : ℝ)|^9 ≤ (44884755995181/100000000000000 : ℝ)^7
        have hw : |(5363030059/10000000000 : ℝ)|=(5363030059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(477143547/1250000000 : ℝ)|^9 ≤ (28989178655441/100000000000000 : ℝ)^7
        have hw : |(477143547/1250000000 : ℝ)|=(477143547/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310023_s2_s2_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (5769082927/10000000000 : ℝ)*x 0 + (-1144444161/10000000000 : ℝ)*x 1 + (1332715097/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5769082927/10000000000 : ℝ)^9 ≤ (49300528678199/100000000000000 : ℝ)^7 := by
    have hnat : (5769082927 : ℕ)^9*100000000000000^7 ≤ 49300528678199^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5769082927 10000000000 49300528678199 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1144444161/10000000000 : ℝ)^9 ≤ (770072565383/12500000000000 : ℝ)^7 := by
    have hnat : (1144444161 : ℕ)^9*12500000000000^7 ≤ 770072565383^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1144444161 10000000000 770072565383 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1332715097/2500000000 : ℝ)^9 ≤ (44538890785051/100000000000000 : ℝ)^7 := by
    have hnat : (1332715097 : ℕ)^9*100000000000000^7 ≤ 44538890785051^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1332715097 2500000000 44538890785051 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5769082927/10000000000 : ℝ), (-1144444161/10000000000 : ℝ), (1332715097/2500000000 : ℝ)] ![(49300528678199/100000000000000 : ℝ), (770072565383/12500000000000 : ℝ), (44538890785051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5769082927/10000000000 : ℝ)|^9 ≤ (49300528678199/100000000000000 : ℝ)^7
        have hw : |(5769082927/10000000000 : ℝ)|=(5769082927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1144444161/10000000000 : ℝ)|^9 ≤ (770072565383/12500000000000 : ℝ)^7
        have hw : |(-1144444161/10000000000 : ℝ)|=(1144444161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1332715097/2500000000 : ℝ)|^9 ≤ (44538890785051/100000000000000 : ℝ)^7
        have hw : |(1332715097/2500000000 : ℝ)|=(1332715097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310023_s2_s2_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (33193843/100000000 : ℝ)*x 0 + (1433166007/2500000000 : ℝ)*x 1 + (-1799506683/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33193843/100000000 : ℝ)^9 ≤ (12111190511999/50000000000000 : ℝ)^7 := by
    have hnat : (33193843 : ℕ)^9*50000000000000^7 ≤ 12111190511999^7*100000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33193843 100000000 12111190511999 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1433166007/2500000000 : ℝ)^9 ≤ (24450373147969/50000000000000 : ℝ)^7 := by
    have hnat : (1433166007 : ℕ)^9*50000000000000^7 ≤ 24450373147969^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1433166007 2500000000 24450373147969 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1799506683/5000000000 : ℝ)^9 ≤ (13438436330611/50000000000000 : ℝ)^7 := by
    have hnat : (1799506683 : ℕ)^9*50000000000000^7 ≤ 13438436330611^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1799506683 5000000000 13438436330611 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33193843/100000000 : ℝ), (1433166007/2500000000 : ℝ), (-1799506683/5000000000 : ℝ)] ![(12111190511999/50000000000000 : ℝ), (24450373147969/50000000000000 : ℝ), (13438436330611/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33193843/100000000 : ℝ)|^9 ≤ (12111190511999/50000000000000 : ℝ)^7
        have hw : |(33193843/100000000 : ℝ)|=(33193843/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1433166007/2500000000 : ℝ)|^9 ≤ (24450373147969/50000000000000 : ℝ)^7
        have hw : |(1433166007/2500000000 : ℝ)|=(1433166007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1799506683/5000000000 : ℝ)|^9 ≤ (13438436330611/50000000000000 : ℝ)^7
        have hw : |(-1799506683/5000000000 : ℝ)|=(1799506683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310023_s2_s2_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4074745849/10000000000 : ℝ)*x 0 + (4902234239/10000000000 : ℝ)*x 1 + (753045207/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4074745849/10000000000 : ℝ)^9 ≤ (15764154427963/50000000000000 : ℝ)^7 := by
    have hnat : (4074745849 : ℕ)^9*50000000000000^7 ≤ 15764154427963^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4074745849 10000000000 15764154427963 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4902234239/10000000000 : ℝ)^9 ≤ (4998563707201/12500000000000 : ℝ)^7 := by
    have hnat : (4902234239 : ℕ)^9*12500000000000^7 ≤ 4998563707201^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4902234239 10000000000 4998563707201 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (753045207/2000000000 : ℝ)^9 ≤ (2848318146253/10000000000000 : ℝ)^7 := by
    have hnat : (753045207 : ℕ)^9*10000000000000^7 ≤ 2848318146253^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      753045207 2000000000 2848318146253 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4074745849/10000000000 : ℝ), (4902234239/10000000000 : ℝ), (753045207/2000000000 : ℝ)] ![(15764154427963/50000000000000 : ℝ), (4998563707201/12500000000000 : ℝ), (2848318146253/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4074745849/10000000000 : ℝ)|^9 ≤ (15764154427963/50000000000000 : ℝ)^7
        have hw : |(4074745849/10000000000 : ℝ)|=(4074745849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4902234239/10000000000 : ℝ)|^9 ≤ (4998563707201/12500000000000 : ℝ)^7
        have hw : |(4902234239/10000000000 : ℝ)|=(4902234239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(753045207/2000000000 : ℝ)|^9 ≤ (2848318146253/10000000000000 : ℝ)^7
        have hw : |(753045207/2000000000 : ℝ)|=(753045207/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310023_s2_s2_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-908989887/2500000000 : ℝ)*x 0 + (1044842417/2000000000 : ℝ)*x 1 + (1928113357/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (908989887/2500000000 : ℝ)^9 ≤ (6808032732749/25000000000000 : ℝ)^7 := by
    have hnat : (908989887 : ℕ)^9*25000000000000^7 ≤ 6808032732749^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      908989887 2500000000 6808032732749 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1044842417/2000000000 : ℝ)^9 ≤ (10849140220209/25000000000000 : ℝ)^7 := by
    have hnat : (1044842417 : ℕ)^9*25000000000000^7 ≤ 10849140220209^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044842417 2000000000 10849140220209 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1928113357/5000000000 : ℝ)^9 ≤ (14685654084039/50000000000000 : ℝ)^7 := by
    have hnat : (1928113357 : ℕ)^9*50000000000000^7 ≤ 14685654084039^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1928113357 5000000000 14685654084039 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-908989887/2500000000 : ℝ), (1044842417/2000000000 : ℝ), (1928113357/5000000000 : ℝ)] ![(6808032732749/25000000000000 : ℝ), (10849140220209/25000000000000 : ℝ), (14685654084039/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-908989887/2500000000 : ℝ)|^9 ≤ (6808032732749/25000000000000 : ℝ)^7
        have hw : |(-908989887/2500000000 : ℝ)|=(908989887/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1044842417/2000000000 : ℝ)|^9 ≤ (10849140220209/25000000000000 : ℝ)^7
        have hw : |(1044842417/2000000000 : ℝ)|=(1044842417/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1928113357/5000000000 : ℝ)|^9 ≤ (14685654084039/50000000000000 : ℝ)^7
        have hw : |(1928113357/5000000000 : ℝ)|=(1928113357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310023_s2_s2_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (5688256693/10000000000 : ℝ)*x 0 + (-238375741/5000000000 : ℝ)*x 1 + (2897589777/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5688256693/10000000000 : ℝ)^9 ≤ (48414253492657/100000000000000 : ℝ)^7 := by
    have hnat : (5688256693 : ℕ)^9*100000000000000^7 ≤ 48414253492657^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5688256693 10000000000 48414253492657 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (238375741/5000000000 : ℝ)^9 ≤ (999151198639/50000000000000 : ℝ)^7 := by
    have hnat : (238375741 : ℕ)^9*50000000000000^7 ≤ 999151198639^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238375741 5000000000 999151198639 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2897589777/5000000000 : ℝ)^9 ≤ (9917488820949/20000000000000 : ℝ)^7 := by
    have hnat : (2897589777 : ℕ)^9*20000000000000^7 ≤ 9917488820949^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2897589777 5000000000 9917488820949 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5688256693/10000000000 : ℝ), (-238375741/5000000000 : ℝ), (2897589777/5000000000 : ℝ)] ![(48414253492657/100000000000000 : ℝ), (999151198639/50000000000000 : ℝ), (9917488820949/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5688256693/10000000000 : ℝ)|^9 ≤ (48414253492657/100000000000000 : ℝ)^7
        have hw : |(5688256693/10000000000 : ℝ)|=(5688256693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-238375741/5000000000 : ℝ)|^9 ≤ (999151198639/50000000000000 : ℝ)^7
        have hw : |(-238375741/5000000000 : ℝ)|=(238375741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2897589777/5000000000 : ℝ)|^9 ≤ (9917488820949/20000000000000 : ℝ)^7
        have hw : |(2897589777/5000000000 : ℝ)|=(2897589777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310023_s2_s2_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (591510371/2000000000 : ℝ)*x 0 + (6422753749/10000000000 : ℝ)*x 1 + (-1568360473/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (591510371/2000000000 : ℝ)^9 ≤ (20881908444123/100000000000000 : ℝ)^7 := by
    have hnat : (591510371 : ℕ)^9*100000000000000^7 ≤ 20881908444123^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      591510371 2000000000 20881908444123 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6422753749/10000000000 : ℝ)^9 ≤ (56595837594429/100000000000000 : ℝ)^7 := by
    have hnat : (6422753749 : ℕ)^9*100000000000000^7 ≤ 56595837594429^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6422753749 10000000000 56595837594429 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1568360473/5000000000 : ℝ)^9 ≤ (5630563485131/25000000000000 : ℝ)^7 := by
    have hnat : (1568360473 : ℕ)^9*25000000000000^7 ≤ 5630563485131^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1568360473 5000000000 5630563485131 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(591510371/2000000000 : ℝ), (6422753749/10000000000 : ℝ), (-1568360473/5000000000 : ℝ)] ![(20881908444123/100000000000000 : ℝ), (56595837594429/100000000000000 : ℝ), (5630563485131/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(591510371/2000000000 : ℝ)|^9 ≤ (20881908444123/100000000000000 : ℝ)^7
        have hw : |(591510371/2000000000 : ℝ)|=(591510371/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6422753749/10000000000 : ℝ)|^9 ≤ (56595837594429/100000000000000 : ℝ)^7
        have hw : |(6422753749/10000000000 : ℝ)|=(6422753749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1568360473/5000000000 : ℝ)|^9 ≤ (5630563485131/25000000000000 : ℝ)^7
        have hw : |(-1568360473/5000000000 : ℝ)|=(1568360473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310023_s2_s2_12 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3696652197/10000000000 : ℝ)*x 0 + (5251664601/10000000000 : ℝ)*x 1 + (3766138623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3696652197/10000000000 : ℝ)^9 ≤ (13908981716891/50000000000000 : ℝ)^7 := by
    have hnat : (3696652197 : ℕ)^9*50000000000000^7 ≤ 13908981716891^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3696652197 10000000000 13908981716891 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5251664601/10000000000 : ℝ)^9 ≤ (8737995759671/20000000000000 : ℝ)^7 := by
    have hnat : (5251664601 : ℕ)^9*20000000000000^7 ≤ 8737995759671^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251664601 10000000000 8737995759671 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3766138623/10000000000 : ℝ)^9 ≤ (28492057757033/100000000000000 : ℝ)^7 := by
    have hnat : (3766138623 : ℕ)^9*100000000000000^7 ≤ 28492057757033^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3766138623 10000000000 28492057757033 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3696652197/10000000000 : ℝ), (5251664601/10000000000 : ℝ), (3766138623/10000000000 : ℝ)] ![(13908981716891/50000000000000 : ℝ), (8737995759671/20000000000000 : ℝ), (28492057757033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3696652197/10000000000 : ℝ)|^9 ≤ (13908981716891/50000000000000 : ℝ)^7
        have hw : |(3696652197/10000000000 : ℝ)|=(3696652197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5251664601/10000000000 : ℝ)|^9 ≤ (8737995759671/20000000000000 : ℝ)^7
        have hw : |(5251664601/10000000000 : ℝ)|=(5251664601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3766138623/10000000000 : ℝ)|^9 ≤ (28492057757033/100000000000000 : ℝ)^7
        have hw : |(3766138623/10000000000 : ℝ)|=(3766138623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310023_s2_s2_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-1878128807/5000000000 : ℝ)*x 0 + (523719927/1000000000 : ℝ)*x 1 + (3722541807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1878128807/5000000000 : ℝ)^9 ≤ (3549497845261/12500000000000 : ℝ)^7 := by
    have hnat : (1878128807 : ℕ)^9*12500000000000^7 ≤ 3549497845261^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1878128807 5000000000 3549497845261 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (523719927/1000000000 : ℝ)^9 ≤ (10883828929027/25000000000000 : ℝ)^7 := by
    have hnat : (523719927 : ℕ)^9*25000000000000^7 ≤ 10883828929027^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523719927 1000000000 10883828929027 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3722541807/10000000000 : ℝ)^9 ≤ (438573461123/1562500000000 : ℝ)^7 := by
    have hnat : (3722541807 : ℕ)^9*1562500000000^7 ≤ 438573461123^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3722541807 10000000000 438573461123 1562500000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1878128807/5000000000 : ℝ), (523719927/1000000000 : ℝ), (3722541807/10000000000 : ℝ)] ![(3549497845261/12500000000000 : ℝ), (10883828929027/25000000000000 : ℝ), (438573461123/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1878128807/5000000000 : ℝ)|^9 ≤ (3549497845261/12500000000000 : ℝ)^7
        have hw : |(-1878128807/5000000000 : ℝ)|=(1878128807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(523719927/1000000000 : ℝ)|^9 ≤ (10883828929027/25000000000000 : ℝ)^7
        have hw : |(523719927/1000000000 : ℝ)|=(523719927/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3722541807/10000000000 : ℝ)|^9 ≤ (438573461123/1562500000000 : ℝ)^7
        have hw : |(3722541807/10000000000 : ℝ)|=(3722541807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310023_s2_s2_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2961461131/5000000000 : ℝ)*x 0 + (-559382329/5000000000 : ℝ)*x 1 + (5188861559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2961461131/5000000000 : ℝ)^9 ≤ (25498599752821/50000000000000 : ℝ)^7 := by
    have hnat : (2961461131 : ℕ)^9*50000000000000^7 ≤ 25498599752821^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2961461131 5000000000 25498599752821 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (559382329/5000000000 : ℝ)^9 ≤ (1495856094727/25000000000000 : ℝ)^7 := by
    have hnat : (559382329 : ℕ)^9*25000000000000^7 ≤ 1495856094727^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559382329 5000000000 1495856094727 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5188861559/10000000000 : ℝ)^9 ≤ (5377422012217/12500000000000 : ℝ)^7 := by
    have hnat : (5188861559 : ℕ)^9*12500000000000^7 ≤ 5377422012217^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5188861559 10000000000 5377422012217 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2961461131/5000000000 : ℝ), (-559382329/5000000000 : ℝ), (5188861559/10000000000 : ℝ)] ![(25498599752821/50000000000000 : ℝ), (1495856094727/25000000000000 : ℝ), (5377422012217/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2961461131/5000000000 : ℝ)|^9 ≤ (25498599752821/50000000000000 : ℝ)^7
        have hw : |(2961461131/5000000000 : ℝ)|=(2961461131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-559382329/5000000000 : ℝ)|^9 ≤ (1495856094727/25000000000000 : ℝ)^7
        have hw : |(-559382329/5000000000 : ℝ)|=(559382329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5188861559/10000000000 : ℝ)|^9 ≤ (5377422012217/12500000000000 : ℝ)^7
        have hw : |(5188861559/10000000000 : ℝ)|=(5188861559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310023_s2_s2_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (776493489/2500000000 : ℝ)*x 0 + (5714556911/10000000000 : ℝ)*x 1 + (-1912145791/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (776493489/2500000000 : ℝ)^9 ≤ (2779850772003/12500000000000 : ℝ)^7 := by
    have hnat : (776493489 : ℕ)^9*12500000000000^7 ≤ 2779850772003^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      776493489 2500000000 2779850772003 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5714556911/10000000000 : ℝ)^9 ≤ (3043890504729/6250000000000 : ℝ)^7 := by
    have hnat : (5714556911 : ℕ)^9*6250000000000^7 ≤ 3043890504729^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5714556911 10000000000 3043890504729 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1912145791/5000000000 : ℝ)^9 ≤ (29058945735703/100000000000000 : ℝ)^7 := by
    have hnat : (1912145791 : ℕ)^9*100000000000000^7 ≤ 29058945735703^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1912145791 5000000000 29058945735703 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(776493489/2500000000 : ℝ), (5714556911/10000000000 : ℝ), (-1912145791/5000000000 : ℝ)] ![(2779850772003/12500000000000 : ℝ), (3043890504729/6250000000000 : ℝ), (29058945735703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(776493489/2500000000 : ℝ)|^9 ≤ (2779850772003/12500000000000 : ℝ)^7
        have hw : |(776493489/2500000000 : ℝ)|=(776493489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5714556911/10000000000 : ℝ)|^9 ≤ (3043890504729/6250000000000 : ℝ)^7
        have hw : |(5714556911/10000000000 : ℝ)|=(5714556911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1912145791/5000000000 : ℝ)|^9 ≤ (29058945735703/100000000000000 : ℝ)^7
        have hw : |(-1912145791/5000000000 : ℝ)|=(1912145791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310023_s2_s2_19 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (377279241/1000000000 : ℝ)*x 0 + (2537325381/5000000000 : ℝ)*x 1 + (3883372793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (377279241/1000000000 : ℝ)^9 ≤ (14278397219083/50000000000000 : ℝ)^7 := by
    have hnat : (377279241 : ℕ)^9*50000000000000^7 ≤ 14278397219083^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      377279241 1000000000 14278397219083 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2537325381/5000000000 : ℝ)^9 ≤ (10451448848077/25000000000000 : ℝ)^7 := by
    have hnat : (2537325381 : ℕ)^9*25000000000000^7 ≤ 10451448848077^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2537325381 5000000000 10451448848077 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3883372793/10000000000 : ℝ)^9 ≤ (2963741014959/10000000000000 : ℝ)^7 := by
    have hnat : (3883372793 : ℕ)^9*10000000000000^7 ≤ 2963741014959^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3883372793 10000000000 2963741014959 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(377279241/1000000000 : ℝ), (2537325381/5000000000 : ℝ), (3883372793/10000000000 : ℝ)] ![(14278397219083/50000000000000 : ℝ), (10451448848077/25000000000000 : ℝ), (2963741014959/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(377279241/1000000000 : ℝ)|^9 ≤ (14278397219083/50000000000000 : ℝ)^7
        have hw : |(377279241/1000000000 : ℝ)|=(377279241/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2537325381/5000000000 : ℝ)|^9 ≤ (10451448848077/25000000000000 : ℝ)^7
        have hw : |(2537325381/5000000000 : ℝ)|=(2537325381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3883372793/10000000000 : ℝ)|^9 ≤ (2963741014959/10000000000000 : ℝ)^7
        have hw : |(3883372793/10000000000 : ℝ)|=(3883372793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310023_s2_s2_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-3062797039/10000000000 : ℝ)*x 0 + (2792801159/5000000000 : ℝ)*x 1 + (4007818147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3062797039/10000000000 : ℝ)^9 ≤ (5460530800417/25000000000000 : ℝ)^7 := by
    have hnat : (3062797039 : ℕ)^9*25000000000000^7 ≤ 5460530800417^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3062797039 10000000000 5460530800417 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2792801159/5000000000 : ℝ)^9 ≤ (11823452458387/25000000000000 : ℝ)^7 := by
    have hnat : (2792801159 : ℕ)^9*25000000000000^7 ≤ 11823452458387^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2792801159 5000000000 11823452458387 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4007818147/10000000000 : ℝ)^9 ≤ (6172813389753/20000000000000 : ℝ)^7 := by
    have hnat : (4007818147 : ℕ)^9*20000000000000^7 ≤ 6172813389753^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4007818147 10000000000 6172813389753 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3062797039/10000000000 : ℝ), (2792801159/5000000000 : ℝ), (4007818147/10000000000 : ℝ)] ![(5460530800417/25000000000000 : ℝ), (11823452458387/25000000000000 : ℝ), (6172813389753/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3062797039/10000000000 : ℝ)|^9 ≤ (5460530800417/25000000000000 : ℝ)^7
        have hw : |(-3062797039/10000000000 : ℝ)|=(3062797039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2792801159/5000000000 : ℝ)|^9 ≤ (11823452458387/25000000000000 : ℝ)^7
        have hw : |(2792801159/5000000000 : ℝ)|=(2792801159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4007818147/10000000000 : ℝ)|^9 ≤ (6172813389753/20000000000000 : ℝ)^7
        have hw : |(4007818147/10000000000 : ℝ)|=(4007818147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310023_s2_s2_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (6581842499/10000000000 : ℝ)*x 0 + (-57530631/1000000000 : ℝ)*x 1 + (4812613019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6581842499/10000000000 : ℝ)^9 ≤ (11680912288351/20000000000000 : ℝ)^7 := by
    have hnat : (6581842499 : ℕ)^9*20000000000000^7 ≤ 11680912288351^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6581842499 10000000000 11680912288351 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (57530631/1000000000 : ℝ)^9 ≤ (2544395420583/100000000000000 : ℝ)^7 := by
    have hnat : (57530631 : ℕ)^9*100000000000000^7 ≤ 2544395420583^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57530631 1000000000 2544395420583 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4812613019/10000000000 : ℝ)^9 ≤ (39051043124347/100000000000000 : ℝ)^7 := by
    have hnat : (4812613019 : ℕ)^9*100000000000000^7 ≤ 39051043124347^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4812613019 10000000000 39051043124347 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6581842499/10000000000 : ℝ), (-57530631/1000000000 : ℝ), (4812613019/10000000000 : ℝ)] ![(11680912288351/20000000000000 : ℝ), (2544395420583/100000000000000 : ℝ), (39051043124347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6581842499/10000000000 : ℝ)|^9 ≤ (11680912288351/20000000000000 : ℝ)^7
        have hw : |(6581842499/10000000000 : ℝ)|=(6581842499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-57530631/1000000000 : ℝ)|^9 ≤ (2544395420583/100000000000000 : ℝ)^7
        have hw : |(-57530631/1000000000 : ℝ)|=(57530631/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4812613019/10000000000 : ℝ)|^9 ≤ (39051043124347/100000000000000 : ℝ)^7
        have hw : |(4812613019/10000000000 : ℝ)|=(4812613019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310023_s2_s2_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (671473731/2500000000 : ℝ)*x 0 + (126483971/200000000 : ℝ)*x 1 + (-3514623489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671473731/2500000000 : ℝ)^9 ≤ (9224473753351/50000000000000 : ℝ)^7 := by
    have hnat : (671473731 : ℕ)^9*50000000000000^7 ≤ 9224473753351^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671473731 2500000000 9224473753351 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (126483971/200000000 : ℝ)^9 ≤ (5548172096039/10000000000000 : ℝ)^7 := by
    have hnat : (126483971 : ℕ)^9*10000000000000^7 ≤ 5548172096039^7*200000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126483971 200000000 5548172096039 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3514623489/10000000000 : ℝ)^9 ≤ (13034665759951/50000000000000 : ℝ)^7 := by
    have hnat : (3514623489 : ℕ)^9*50000000000000^7 ≤ 13034665759951^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3514623489 10000000000 13034665759951 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671473731/2500000000 : ℝ), (126483971/200000000 : ℝ), (-3514623489/10000000000 : ℝ)] ![(9224473753351/50000000000000 : ℝ), (5548172096039/10000000000000 : ℝ), (13034665759951/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671473731/2500000000 : ℝ)|^9 ≤ (9224473753351/50000000000000 : ℝ)^7
        have hw : |(671473731/2500000000 : ℝ)|=(671473731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(126483971/200000000 : ℝ)|^9 ≤ (5548172096039/10000000000000 : ℝ)^7
        have hw : |(126483971/200000000 : ℝ)|=(126483971/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3514623489/10000000000 : ℝ)|^9 ≤ (13034665759951/50000000000000 : ℝ)^7
        have hw : |(-3514623489/10000000000 : ℝ)|=(3514623489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310023_s2_s2_25 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4789247759/10000000000 : ℝ)*x 0 + (4443650217/10000000000 : ℝ)*x 1 + (140075039/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4789247759/10000000000 : ℝ)^9 ≤ (38807449948897/100000000000000 : ℝ)^7 := by
    have hnat : (4789247759 : ℕ)^9*100000000000000^7 ≤ 38807449948897^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4789247759 10000000000 38807449948897 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4443650217/10000000000 : ℝ)^9 ≤ (8811180989419/25000000000000 : ℝ)^7 := by
    have hnat : (4443650217 : ℕ)^9*25000000000000^7 ≤ 8811180989419^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4443650217 10000000000 8811180989419 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (140075039/400000000 : ℝ)^9 ≤ (6486956516257/25000000000000 : ℝ)^7 := by
    have hnat : (140075039 : ℕ)^9*25000000000000^7 ≤ 6486956516257^7*400000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140075039 400000000 6486956516257 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4789247759/10000000000 : ℝ), (4443650217/10000000000 : ℝ), (140075039/400000000 : ℝ)] ![(38807449948897/100000000000000 : ℝ), (8811180989419/25000000000000 : ℝ), (6486956516257/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4789247759/10000000000 : ℝ)|^9 ≤ (38807449948897/100000000000000 : ℝ)^7
        have hw : |(4789247759/10000000000 : ℝ)|=(4789247759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4443650217/10000000000 : ℝ)|^9 ≤ (8811180989419/25000000000000 : ℝ)^7
        have hw : |(4443650217/10000000000 : ℝ)|=(4443650217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(140075039/400000000 : ℝ)|^9 ≤ (6486956516257/25000000000000 : ℝ)^7
        have hw : |(140075039/400000000 : ℝ)|=(140075039/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310023_s2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((58423/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(58423/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(12529/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(12529/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6547/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6547/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((843/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(843/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(2711/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(2711/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6413/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6413/25000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s2_pow0 : (58423/100000 : ℝ) ^ (35/8 : ℝ) ≤ (9523670506782653179/100000000000000000000 : ℝ) := by
    have hpowers : (58423/100000 : ℝ)^35 ≤ (9523670506782653179/100000000000000000000 : ℝ)^8 := by
      have hnat : (58423 : ℕ)^35*100000000000000000000^8 ≤ 9523670506782653179^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        58423 100000 9523670506782653179 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (58423/100000 : ℝ)) (X := (9523670506782653179/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner0a : (109523670506782653179/100000000000000000000 : ℝ) ≤ (10210109451776069/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (109523670506782653179/100000000000000000000 : ℝ)^8 ≤ (10210109451776069/10000000000000000 : ℝ)^35 := by
      have hnat : (109523670506782653179 : ℕ)^8*10000000000000000^35 ≤ 10210109451776069^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        109523670506782653179 100000000000000000000 10210109451776069 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10210109451776069/10000000000000000 : ℝ)) (X := (109523670506782653179/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner0b : (59523670506782653179/50000000000000000000 : ℝ) ≤ (2601641002716967/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (59523670506782653179/50000000000000000000 : ℝ)^8 ≤ (2601641002716967/2500000000000000 : ℝ)^35 := by
      have hnat : (59523670506782653179 : ℕ)^8*2500000000000000^35 ≤ 2601641002716967^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59523670506782653179 50000000000000000000 2601641002716967 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2601641002716967/2500000000000000 : ℝ)) (X := (59523670506782653179/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(210109451776069/5842300000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(196454559091799/5842300000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (58423/100000 : ℝ)) (alpha := (210109451776069/5842300000000000 : ℝ)) (beta := (196454559091799/5842300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (58423/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(210109451776069/5842300000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(196454559091799/5842300000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (12529/100000 : ℝ) ^ (35/8 : ℝ) ≤ (11307960698757283/100000000000000000000 : ℝ) := by
    have hpowers : (12529/100000 : ℝ)^35 ≤ (11307960698757283/100000000000000000000 : ℝ)^8 := by
      have hnat : (12529 : ℕ)^35*100000000000000000000^8 ≤ 11307960698757283^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12529 100000 11307960698757283 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12529/100000 : ℝ)) (X := (11307960698757283/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner1a : (100011307960698757283/100000000000000000000 : ℝ) ≤ (10000258456400433/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (100011307960698757283/100000000000000000000 : ℝ)^8 ≤ (10000258456400433/10000000000000000 : ℝ)^35 := by
      have hnat : (100011307960698757283 : ℕ)^8*10000000000000000^35 ≤ 10000258456400433^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100011307960698757283 100000000000000000000 10000258456400433 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000258456400433/10000000000000000 : ℝ)) (X := (100011307960698757283/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner1b : (50011307960698757283/50000000000000000000 : ℝ) ≤ (625032305641157/625000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (50011307960698757283/50000000000000000000 : ℝ)^8 ≤ (625032305641157/625000000000000 : ℝ)^35 := by
      have hnat : (50011307960698757283 : ℕ)^8*625000000000000^35 ≤ 625032305641157^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50011307960698757283 50000000000000000000 625032305641157 625000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625032305641157/625000000000000 : ℝ)) (X := (50011307960698757283/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(23496036403/113900000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(258433858079/1252900000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (12529/100000 : ℝ)) (alpha := (23496036403/113900000000000 : ℝ)) (beta := (258433858079/1252900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (12529/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(23496036403/113900000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(258433858079/1252900000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (6547/10000 : ℝ) ^ (35/8 : ℝ) ≤ (15674194858676934521/100000000000000000000 : ℝ) := by
    have hpowers : (6547/10000 : ℝ)^35 ≤ (15674194858676934521/100000000000000000000 : ℝ)^8 := by
      have hnat : (6547 : ℕ)^35*100000000000000000000^8 ≤ 15674194858676934521^8*10000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6547 10000 15674194858676934521 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6547/10000 : ℝ)) (X := (15674194858676934521/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner2a : (115674194858676934521/100000000000000000000 : ℝ) ≤ (10338417198395183/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (115674194858676934521/100000000000000000000 : ℝ)^8 ≤ (10338417198395183/10000000000000000 : ℝ)^35 := by
      have hnat : (115674194858676934521 : ℕ)^8*10000000000000000^35 ≤ 10338417198395183^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        115674194858676934521 100000000000000000000 10338417198395183 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10338417198395183/10000000000000000 : ℝ)) (X := (115674194858676934521/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner2b : (65674194858676934521/50000000000000000000 : ℝ) ≤ (5321554561229897/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (65674194858676934521/50000000000000000000 : ℝ)^8 ≤ (5321554561229897/5000000000000000 : ℝ)^35 := by
      have hnat : (65674194858676934521 : ℕ)^8*5000000000000000^35 ≤ 5321554561229897^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        65674194858676934521 50000000000000000000 5321554561229897 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5321554561229897/5000000000000000 : ℝ)) (X := (65674194858676934521/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(338417198395183/6547000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(304691924064611/6547000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (6547/10000 : ℝ)) (alpha := (338417198395183/6547000000000000 : ℝ)) (beta := (304691924064611/6547000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (6547/10000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(338417198395183/6547000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(304691924064611/6547000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-704114217/2000000000 : ℝ)*X 0 0+(5363030059/10000000000 : ℝ)*X 0 1+(477143547/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310023_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((5769082927/10000000000 : ℝ)*X 1 0+(-1144444161/10000000000 : ℝ)*X 1 1+(1332715097/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310023_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((33193843/100000000 : ℝ)*X 2 0+(1433166007/2500000000 : ℝ)*X 2 1+(-1799506683/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310023_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((4074745849/10000000000 : ℝ)*X 0 0+(4902234239/10000000000 : ℝ)*X 0 1+(753045207/2000000000 : ℝ)*X 0 2+(4074745849/10000000000 : ℝ)*X 1 0+(4902234239/10000000000 : ℝ)*X 1 1+(753045207/2000000000 : ℝ)*X 1 2+(4074745849/10000000000 : ℝ)*X 2 0+(4902234239/10000000000 : ℝ)*X 2 1+(753045207/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310023_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-908989887/2500000000 : ℝ)*X 0 0+(1044842417/2000000000 : ℝ)*X 0 1+(1928113357/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310023_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((5688256693/10000000000 : ℝ)*X 1 0+(-238375741/5000000000 : ℝ)*X 1 1+(2897589777/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310023_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((591510371/2000000000 : ℝ)*X 2 0+(6422753749/10000000000 : ℝ)*X 2 1+(-1568360473/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310023_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_12 : ((3696652197/10000000000 : ℝ)*X 0 0+(5251664601/10000000000 : ℝ)*X 0 1+(3766138623/10000000000 : ℝ)*X 0 2+(3696652197/10000000000 : ℝ)*X 1 0+(5251664601/10000000000 : ℝ)*X 1 1+(3766138623/10000000000 : ℝ)*X 1 2+(3696652197/10000000000 : ℝ)*X 2 0+(5251664601/10000000000 : ℝ)*X 2 1+(3766138623/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310023_s2_s2_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((-1878128807/5000000000 : ℝ)*X 0 0+(523719927/1000000000 : ℝ)*X 0 1+(3722541807/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310023_s2_s2_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((2961461131/5000000000 : ℝ)*X 1 0+(-559382329/5000000000 : ℝ)*X 1 1+(5188861559/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310023_s2_s2_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((776493489/2500000000 : ℝ)*X 2 0+(5714556911/10000000000 : ℝ)*X 2 1+(-1912145791/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310023_s2_s2_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_19 : ((377279241/1000000000 : ℝ)*X 0 0+(2537325381/5000000000 : ℝ)*X 0 1+(3883372793/10000000000 : ℝ)*X 0 2+(377279241/1000000000 : ℝ)*X 1 0+(2537325381/5000000000 : ℝ)*X 1 1+(3883372793/10000000000 : ℝ)*X 1 2+(377279241/1000000000 : ℝ)*X 2 0+(2537325381/5000000000 : ℝ)*X 2 1+(3883372793/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310023_s2_s2_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((-3062797039/10000000000 : ℝ)*X 0 0+(2792801159/5000000000 : ℝ)*X 0 1+(4007818147/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310023_s2_s2_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((6581842499/10000000000 : ℝ)*X 1 0+(-57530631/1000000000 : ℝ)*X 1 1+(4812613019/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310023_s2_s2_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((671473731/2500000000 : ℝ)*X 2 0+(126483971/200000000 : ℝ)*X 2 1+(-3514623489/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310023_s2_s2_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_25 : ((4789247759/10000000000 : ℝ)*X 0 0+(4443650217/10000000000 : ℝ)*X 0 1+(140075039/400000000 : ℝ)*X 0 2+(4789247759/10000000000 : ℝ)*X 1 0+(4443650217/10000000000 : ℝ)*X 1 1+(140075039/400000000 : ℝ)*X 1 2+(4789247759/10000000000 : ℝ)*X 2 0+(4443650217/10000000000 : ℝ)*X 2 1+(140075039/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310023_s2_s2_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((843/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(843/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7061936564955748492640991041451/2396142314274500000000000000000000000 : ℝ) := by norm_num
    linear_combination (2138251/1000000000000 : ℝ)*(base40) + (3175758340711/1000000000000 : ℝ)*(base49) + (461773883321/250000000000 : ℝ)*(base50) + (312197/250000000000 : ℝ)*(base60) + (5675221535713/1000000000000 : ℝ)*(major_s2_0) + (5675221535713/1000000000000 : ℝ)*(major_s2_1) + (5675221535713/1000000000000 : ℝ)*(major_s2_2) + (11096911/250000000000 : ℝ)*(sp_s2_1) + (392136842551/50000000000 : ℝ)*(sp_s2_7) + (7842692463377/1000000000000 : ℝ)*(sp_s2_8) + (7842670597861/1000000000000 : ℝ)*(sp_s2_9) + (3507657851127/1000000000000 : ℝ)*(sp_s2_12) + (4738687/100000000000 : ℝ)*(sp_s2_19) + (66253159/1000000000000 : ℝ)*(sp_s2_22) + (3507705237997/1000000000000 : ℝ)*(f.failure) + (392136842551/50000000000 : ℝ)*(f.sum) + (117993297011576551/7457033000000000000000000000000 : ℝ)*base63 + (323027310657743/6547000000000000000000000000 : ℝ)*base65 + (665322976299483/1252900000000000000000000000 : ℝ)*base67 + (797794673320879/6547000000000000000000000000 : ℝ)*base69 + (137959304810172809321/382495381000000000000000000000000 : ℝ)*base70 + (246055190968657/5842300000000000000000000000 : ℝ)*base73 + (3877604368439/113900000000000000000000000 : ℝ)*base74 + (1122528468208817/5842300000000000000000000000 : ℝ)*base77 + (17419584276082902261/36599088350000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (51379/100000000000000000 : ℝ)*base86 + (51379/100000000000000000 : ℝ)*base88 + (51379/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(2711/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(2711/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (129259964892717548522148801/36599088350000000000000000000000 : ℝ) := by norm_num
    linear_combination (226871428183/1000000000000 : ℝ)*(base40) + (363599871961/500000000000 : ℝ)*(base49) + (9751/20000000000 : ℝ)*(base60) + (2963983776459/1000000000000 : ℝ)*(major_s2_0) + (2963983776459/1000000000000 : ℝ)*(major_s2_1) + (2963983776459/1000000000000 : ℝ)*(major_s2_2) + (8503567/500000000000 : ℝ)*(sp_s2_0) + (14314747/100000000000 : ℝ)*(sp_s2_1) + (100778643/1000000000000 : ℝ)*(sp_s2_6) + (3092963/200000000000 : ℝ)*(sp_s2_12) + (4095988915063/1000000000000 : ℝ)*(sp_s2_13) + (4095862774727/1000000000000 : ℝ)*(sp_s2_14) + (4096005922197/1000000000000 : ℝ)*(sp_s2_15) + (1831844209997/1000000000000 : ℝ)*(sp_s2_19) + (114497528341/62500000000 : ℝ)*(f.failure) + (4096005922197/1000000000000 : ℝ)*(f.sum) + (2060847288490567393/7457033000000000000000000000000 : ℝ)*base63 + (1339428647880951/6547000000000000000000000000 : ℝ)*base64 + (311033518840101/1252900000000000000000000000 : ℝ)*base66 + (1023653662564203/6547000000000000000000000000 : ℝ)*base68 + (214187505729953631297/382495381000000000000000000000000 : ℝ)*base71 + (3351490042269779/5842300000000000000000000000 : ℝ)*base72 + (23629439110937/113900000000000000000000000 : ℝ)*base74 + (1188410648412881/5842300000000000000000000000 : ℝ)*base77 + (3113729229274608451/18299544175000000000000000000000 : ℝ)*base78 + (6663/6250000000000000 : ℝ)*base87 + (6663/6250000000000000 : ℝ)*base89 + (6663/6250000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6413/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6413/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (24724177096320861488541/1636750000000000000000000000 : ℝ) := by norm_num
    linear_combination (366010218291/500000000000 : ℝ)*(base40) + (424551707009/125000000000 : ℝ)*(base49) + (2161493040121/1000000000000 : ℝ)*(base50) + (3249307484009/500000000000 : ℝ)*(major_s2_0) + (3249307484009/500000000000 : ℝ)*(major_s2_1) + (3249307484009/500000000000 : ℝ)*(major_s2_2) + (251940693/1000000000000 : ℝ)*(sp_s2_2) + (52902169/125000000000 : ℝ)*(sp_s2_9) + (15536101/1000000000000 : ℝ)*(sp_s2_12) + (137814389/500000000000 : ℝ)*(sp_s2_14) + (561287614257/62500000000 : ℝ)*(sp_s2_20) + (1796065239867/200000000000 : ℝ)*(sp_s2_21) + (8979926670067/1000000000000 : ℝ)*(sp_s2_22) + (2008303768301/500000000000 : ℝ)*(sp_s2_25) + (4016623072703/1000000000000 : ℝ)*(f.failure) + (561287614257/62500000000 : ℝ)*(f.sum) + (364935613970721/55649500000000000000000000000 : ℝ)*base62 + (1123667503895649/3273500000000000000000000000 : ℝ)*base65 + (557817406343/2337500000000000000000000 : ℝ)*base67 + (831852607188953/3273500000000000000000000000 : ℝ)*base68 + (71278355595240562103/191247690500000000000000000000000 : ℝ)*base70 + (355349918051091/2921150000000000000000000000 : ℝ)*base73 + (116446884441/212500000000000000000000 : ℝ)*base75 + (138173099949683/1460575000000000000000000000 : ℝ)*base77 + (22114581060699571/273127525000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (36479/100000000000000000 : ℝ)*base87 + (36479/100000000000000000 : ℝ)*base89 + (36479/100000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((58423/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(58423/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(12529/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(12529/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6547/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6547/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((843/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(843/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(2711/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(2711/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6413/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6413/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c310023_s2 p hpa hpb X hX hprev1

#print axioms solution
