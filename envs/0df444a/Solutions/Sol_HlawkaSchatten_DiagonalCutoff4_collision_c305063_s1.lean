-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c305063_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:32:47.329976+00:00
-- url     : https://prove2.me/submissions/fb63501d-3a3a-4f44-8cea-b994c9e5d675

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
theorem collision_support_c305063_s1_s1_0 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-169925243/10000000000 : ℝ)*x 0 + (2841210303/5000000000 : ℝ)*x 1 + (379573143/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (169925243/10000000000 : ℝ)^67 ≤ (236599975891/50000000000000 : ℝ)^51 := by
    have hnat : (169925243 : ℕ)^67*50000000000000^51 ≤ 236599975891^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169925243 10000000000 236599975891 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2841210303/5000000000 : ℝ)^67 ≤ (47590935270861/100000000000000 : ℝ)^51 := by
    have hnat : (2841210303 : ℕ)^67*100000000000000^51 ≤ 47590935270861^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2841210303 5000000000 47590935270861 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (379573143/625000000 : ℝ)^67 ≤ (51935864758589/100000000000000 : ℝ)^51 := by
    have hnat : (379573143 : ℕ)^67*100000000000000^51 ≤ 51935864758589^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      379573143 625000000 51935864758589 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-169925243/10000000000 : ℝ), (2841210303/5000000000 : ℝ), (379573143/625000000 : ℝ)] ![(236599975891/50000000000000 : ℝ), (47590935270861/100000000000000 : ℝ), (51935864758589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-169925243/10000000000 : ℝ)|^67 ≤ (236599975891/50000000000000 : ℝ)^51
        have hw : |(-169925243/10000000000 : ℝ)|=(169925243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2841210303/5000000000 : ℝ)|^67 ≤ (47590935270861/100000000000000 : ℝ)^51
        have hw : |(2841210303/5000000000 : ℝ)|=(2841210303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(379573143/625000000 : ℝ)|^67 ≤ (51935864758589/100000000000000 : ℝ)^51
        have hw : |(379573143/625000000 : ℝ)|=(379573143/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s1_s1_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1136190031/2000000000 : ℝ)*x 0 + (-37832787/2500000000 : ℝ)*x 1 + (760069649/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1136190031/2000000000 : ℝ)^67 ≤ (47574757137291/100000000000000 : ℝ)^51 := by
    have hnat : (1136190031 : ℕ)^67*100000000000000^51 ≤ 47574757137291^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136190031 2000000000 47574757137291 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (37832787/2500000000 : ℝ)^67 ≤ (406373564837/100000000000000 : ℝ)^51 := by
    have hnat : (37832787 : ℕ)^67*100000000000000^51 ≤ 406373564837^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37832787 2500000000 406373564837 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (760069649/1250000000 : ℝ)^67 ≤ (52018869293487/100000000000000 : ℝ)^51 := by
    have hnat : (760069649 : ℕ)^67*100000000000000^51 ≤ 52018869293487^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      760069649 1250000000 52018869293487 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1136190031/2000000000 : ℝ), (-37832787/2500000000 : ℝ), (760069649/1250000000 : ℝ)] ![(47574757137291/100000000000000 : ℝ), (406373564837/100000000000000 : ℝ), (52018869293487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1136190031/2000000000 : ℝ)|^67 ≤ (47574757137291/100000000000000 : ℝ)^51
        have hw : |(1136190031/2000000000 : ℝ)|=(1136190031/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-37832787/2500000000 : ℝ)|^67 ≤ (406373564837/100000000000000 : ℝ)^51
        have hw : |(-37832787/2500000000 : ℝ)|=(37832787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(760069649/1250000000 : ℝ)|^67 ≤ (52018869293487/100000000000000 : ℝ)^51
        have hw : |(760069649/1250000000 : ℝ)|=(760069649/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s1_s1_7 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-134687499/2000000000 : ℝ)*x 0 + (499168349/2500000000 : ℝ)*x 1 + (8841644127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134687499/2000000000 : ℝ)^67 ≤ (1444356137313/50000000000000 : ℝ)^51 := by
    have hnat : (134687499 : ℕ)^67*50000000000000^51 ≤ 1444356137313^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134687499 2000000000 1444356137313 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (499168349/2500000000 : ℝ)^67 ≤ (602234340473/5000000000000 : ℝ)^51 := by
    have hnat : (499168349 : ℕ)^67*5000000000000^51 ≤ 602234340473^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499168349 2500000000 602234340473 5000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8841644127/10000000000 : ℝ)^67 ≤ (85066600902273/100000000000000 : ℝ)^51 := by
    have hnat : (8841644127 : ℕ)^67*100000000000000^51 ≤ 85066600902273^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8841644127 10000000000 85066600902273 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-134687499/2000000000 : ℝ), (499168349/2500000000 : ℝ), (8841644127/10000000000 : ℝ)] ![(1444356137313/50000000000000 : ℝ), (602234340473/5000000000000 : ℝ), (85066600902273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-134687499/2000000000 : ℝ)|^67 ≤ (1444356137313/50000000000000 : ℝ)^51
        have hw : |(-134687499/2000000000 : ℝ)|=(134687499/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(499168349/2500000000 : ℝ)|^67 ≤ (602234340473/5000000000000 : ℝ)^51
        have hw : |(499168349/2500000000 : ℝ)|=(499168349/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8841644127/10000000000 : ℝ)|^67 ≤ (85066600902273/100000000000000 : ℝ)^51
        have hw : |(8841644127/10000000000 : ℝ)|=(8841644127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s1_s1_8 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2272212491/10000000000 : ℝ)*x 0 + (-180955989/10000000000 : ℝ)*x 1 + (44265679/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2272212491/10000000000 : ℝ)^67 ≤ (7137080191113/50000000000000 : ℝ)^51 := by
    have hnat : (2272212491 : ℕ)^67*50000000000000^51 ≤ 7137080191113^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2272212491 10000000000 7137080191113 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (180955989/10000000000 : ℝ)^67 ≤ (513959839041/100000000000000 : ℝ)^51 := by
    have hnat : (180955989 : ℕ)^67*100000000000000^51 ≤ 513959839041^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180955989 10000000000 513959839041 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (44265679/50000000 : ℝ)^67 ≤ (42605939884371/50000000000000 : ℝ)^51 := by
    have hnat : (44265679 : ℕ)^67*50000000000000^51 ≤ 42605939884371^51*50000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44265679 50000000 42605939884371 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2272212491/10000000000 : ℝ), (-180955989/10000000000 : ℝ), (44265679/50000000 : ℝ)] ![(7137080191113/50000000000000 : ℝ), (513959839041/100000000000000 : ℝ), (42605939884371/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2272212491/10000000000 : ℝ)|^67 ≤ (7137080191113/50000000000000 : ℝ)^51
        have hw : |(2272212491/10000000000 : ℝ)|=(2272212491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-180955989/10000000000 : ℝ)|^67 ≤ (513959839041/100000000000000 : ℝ)^51
        have hw : |(-180955989/10000000000 : ℝ)|=(180955989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(44265679/50000000 : ℝ)|^67 ≤ (42605939884371/50000000000000 : ℝ)^51
        have hw : |(44265679/50000000 : ℝ)|=(44265679/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s1_s1_9 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (114316929/500000000 : ℝ)*x 0 + (8883277747/10000000000 : ℝ)*x 1 + (-642763/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (114316929/500000000 : ℝ)^67 ≤ (7195427511373/50000000000000 : ℝ)^51 := by
    have hnat : (114316929 : ℕ)^67*50000000000000^51 ≤ 7195427511373^51*500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114316929 500000000 7195427511373 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8883277747/10000000000 : ℝ)^67 ≤ (10699152282897/12500000000000 : ℝ)^51 := by
    have hnat : (8883277747 : ℕ)^67*12500000000000^51 ≤ 10699152282897^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8883277747 10000000000 10699152282897 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (642763/500000000 : ℝ)^67 ≤ (15926701551/100000000000000 : ℝ)^51 := by
    have hnat : (642763 : ℕ)^67*100000000000000^51 ≤ 15926701551^51*500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      642763 500000000 15926701551 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(114316929/500000000 : ℝ), (8883277747/10000000000 : ℝ), (-642763/500000000 : ℝ)] ![(7195427511373/50000000000000 : ℝ), (10699152282897/12500000000000 : ℝ), (15926701551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(114316929/500000000 : ℝ)|^67 ≤ (7195427511373/50000000000000 : ℝ)^51
        have hw : |(114316929/500000000 : ℝ)|=(114316929/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8883277747/10000000000 : ℝ)|^67 ≤ (10699152282897/12500000000000 : ℝ)^51
        have hw : |(8883277747/10000000000 : ℝ)|=(8883277747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-642763/500000000 : ℝ)|^67 ≤ (15926701551/100000000000000 : ℝ)^51
        have hw : |(-642763/500000000 : ℝ)|=(642763/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s1_s1_13 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (596726923/2000000000 : ℝ)*x 0 + (3754782569/5000000000 : ℝ)*x 1 + (927986323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (596726923/2000000000 : ℝ)^67 ≤ (20415496885623/100000000000000 : ℝ)^51 := by
    have hnat : (596726923 : ℕ)^67*100000000000000^51 ≤ 20415496885623^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      596726923 2000000000 20415496885623 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3754782569/5000000000 : ℝ)^67 ≤ (34321161880123/50000000000000 : ℝ)^51 := by
    have hnat : (3754782569 : ℕ)^67*50000000000000^51 ≤ 34321161880123^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3754782569 5000000000 34321161880123 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (927986323/5000000000 : ℝ)^67 ≤ (5471089673253/50000000000000 : ℝ)^51 := by
    have hnat : (927986323 : ℕ)^67*50000000000000^51 ≤ 5471089673253^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      927986323 5000000000 5471089673253 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(596726923/2000000000 : ℝ), (3754782569/5000000000 : ℝ), (927986323/5000000000 : ℝ)] ![(20415496885623/100000000000000 : ℝ), (34321161880123/50000000000000 : ℝ), (5471089673253/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(596726923/2000000000 : ℝ)|^67 ≤ (20415496885623/100000000000000 : ℝ)^51
        have hw : |(596726923/2000000000 : ℝ)|=(596726923/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3754782569/5000000000 : ℝ)|^67 ≤ (34321161880123/50000000000000 : ℝ)^51
        have hw : |(3754782569/5000000000 : ℝ)|=(3754782569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(927986323/5000000000 : ℝ)|^67 ≤ (5471089673253/50000000000000 : ℝ)^51
        have hw : |(927986323/5000000000 : ℝ)|=(927986323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s1_s1_14 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-15358439/1000000000 : ℝ)*x 0 + (1087938523/5000000000 : ℝ)*x 1 + (8923380537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (15358439/1000000000 : ℝ)^67 ≤ (5179262679/1250000000000 : ℝ)^51 := by
    have hnat : (15358439 : ℕ)^67*1250000000000^51 ≤ 5179262679^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15358439 1000000000 5179262679 1250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087938523/5000000000 : ℝ)^67 ≤ (13484453894029/100000000000000 : ℝ)^51 := by
    have hnat : (1087938523 : ℕ)^67*100000000000000^51 ≤ 13484453894029^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087938523 5000000000 13484453894029 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8923380537/10000000000 : ℝ)^67 ≤ (3444048203431/4000000000000 : ℝ)^51 := by
    have hnat : (8923380537 : ℕ)^67*4000000000000^51 ≤ 3444048203431^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8923380537 10000000000 3444048203431 4000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-15358439/1000000000 : ℝ), (1087938523/5000000000 : ℝ), (8923380537/10000000000 : ℝ)] ![(5179262679/1250000000000 : ℝ), (13484453894029/100000000000000 : ℝ), (3444048203431/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-15358439/1000000000 : ℝ)|^67 ≤ (5179262679/1250000000000 : ℝ)^51
        have hw : |(-15358439/1000000000 : ℝ)|=(15358439/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1087938523/5000000000 : ℝ)|^67 ≤ (13484453894029/100000000000000 : ℝ)^51
        have hw : |(1087938523/5000000000 : ℝ)|=(1087938523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8923380537/10000000000 : ℝ)|^67 ≤ (3444048203431/4000000000000 : ℝ)^51
        have hw : |(8923380537/10000000000 : ℝ)|=(8923380537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s1_s1_15 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (932001767/5000000000 : ℝ)*x 0 + (-129435837/2000000000 : ℝ)*x 1 + (1787085147/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (932001767/5000000000 : ℝ)^67 ≤ (275110574157/2500000000000 : ℝ)^51 := by
    have hnat : (932001767 : ℕ)^67*2500000000000^51 ≤ 275110574157^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      932001767 5000000000 275110574157 2500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129435837/2000000000 : ℝ)^67 ≤ (342706739391/12500000000000 : ℝ)^51 := by
    have hnat : (129435837 : ℕ)^67*12500000000000^51 ≤ 342706739391^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129435837 2000000000 342706739391 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1787085147/2000000000 : ℝ)^67 ≤ (43126961556583/50000000000000 : ℝ)^51 := by
    have hnat : (1787085147 : ℕ)^67*50000000000000^51 ≤ 43126961556583^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1787085147 2000000000 43126961556583 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(932001767/5000000000 : ℝ), (-129435837/2000000000 : ℝ), (1787085147/2000000000 : ℝ)] ![(275110574157/2500000000000 : ℝ), (342706739391/12500000000000 : ℝ), (43126961556583/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(932001767/5000000000 : ℝ)|^67 ≤ (275110574157/2500000000000 : ℝ)^51
        have hw : |(932001767/5000000000 : ℝ)|=(932001767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-129435837/2000000000 : ℝ)|^67 ≤ (342706739391/12500000000000 : ℝ)^51
        have hw : |(-129435837/2000000000 : ℝ)|=(129435837/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1787085147/2000000000 : ℝ)|^67 ≤ (43126961556583/50000000000000 : ℝ)^51
        have hw : |(1787085147/2000000000 : ℝ)|=(1787085147/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s1_s1_16 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2166498571/2500000000 : ℝ)*x 0 + (2607593229/10000000000 : ℝ)*x 1 + (-13570909/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2166498571/2500000000 : ℝ)^67 ≤ (10356677617799/12500000000000 : ℝ)^51 := by
    have hnat : (2166498571 : ℕ)^67*12500000000000^51 ≤ 10356677617799^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166498571 2500000000 10356677617799 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2607593229/10000000000 : ℝ)^67 ≤ (17104067578307/100000000000000 : ℝ)^51 := by
    have hnat : (2607593229 : ℕ)^67*100000000000000^51 ≤ 17104067578307^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607593229 10000000000 17104067578307 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13570909/5000000000 : ℝ)^67 ≤ (21255731471/50000000000000 : ℝ)^51 := by
    have hnat : (13570909 : ℕ)^67*50000000000000^51 ≤ 21255731471^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13570909 5000000000 21255731471 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2166498571/2500000000 : ℝ), (2607593229/10000000000 : ℝ), (-13570909/5000000000 : ℝ)] ![(10356677617799/12500000000000 : ℝ), (17104067578307/100000000000000 : ℝ), (21255731471/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2166498571/2500000000 : ℝ)|^67 ≤ (10356677617799/12500000000000 : ℝ)^51
        have hw : |(2166498571/2500000000 : ℝ)|=(2166498571/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2607593229/10000000000 : ℝ)|^67 ≤ (17104067578307/100000000000000 : ℝ)^51
        have hw : |(2607593229/10000000000 : ℝ)|=(2607593229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-13570909/5000000000 : ℝ)|^67 ≤ (21255731471/50000000000000 : ℝ)^51
        have hw : |(-13570909/5000000000 : ℝ)|=(13570909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s1_s1_20 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1958463823/2500000000 : ℝ)*x 0 + (39934559/156250000 : ℝ)*x 1 + (1834752967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1958463823/2500000000 : ℝ)^67 ≤ (36281311295741/50000000000000 : ℝ)^51 := by
    have hnat : (1958463823 : ℕ)^67*50000000000000^51 ≤ 36281311295741^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1958463823 2500000000 36281311295741 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (39934559/156250000 : ℝ)^67 ≤ (8329627389757/50000000000000 : ℝ)^51 := by
    have hnat : (39934559 : ℕ)^67*50000000000000^51 ≤ 8329627389757^51*156250000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39934559 156250000 8329627389757 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1834752967/10000000000 : ℝ)^67 ≤ (10778122612061/100000000000000 : ℝ)^51 := by
    have hnat : (1834752967 : ℕ)^67*100000000000000^51 ≤ 10778122612061^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1834752967 10000000000 10778122612061 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1958463823/2500000000 : ℝ), (39934559/156250000 : ℝ), (1834752967/10000000000 : ℝ)] ![(36281311295741/50000000000000 : ℝ), (8329627389757/50000000000000 : ℝ), (10778122612061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1958463823/2500000000 : ℝ)|^67 ≤ (36281311295741/50000000000000 : ℝ)^51
        have hw : |(1958463823/2500000000 : ℝ)|=(1958463823/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(39934559/156250000 : ℝ)|^67 ≤ (8329627389757/50000000000000 : ℝ)^51
        have hw : |(39934559/156250000 : ℝ)|=(39934559/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1834752967/10000000000 : ℝ)|^67 ≤ (10778122612061/100000000000000 : ℝ)^51
        have hw : |(1834752967/10000000000 : ℝ)|=(1834752967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s1_s1_21 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-219668841/10000000000 : ℝ)*x 0 + (324797339/400000000 : ℝ)*x 1 + (3296531147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (219668841/10000000000 : ℝ)^67 ≤ (663038818453/100000000000000 : ℝ)^51 := by
    have hnat : (219668841 : ℕ)^67*100000000000000^51 ≤ 663038818453^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219668841 10000000000 663038818453 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (324797339/400000000 : ℝ)^67 ≤ (1188493475361/1562500000000 : ℝ)^51 := by
    have hnat : (324797339 : ℕ)^67*1562500000000^51 ≤ 1188493475361^51*400000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324797339 400000000 1188493475361 1562500000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3296531147/10000000000 : ℝ)^67 ≤ (11636689371771/50000000000000 : ℝ)^51 := by
    have hnat : (3296531147 : ℕ)^67*50000000000000^51 ≤ 11636689371771^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3296531147 10000000000 11636689371771 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-219668841/10000000000 : ℝ), (324797339/400000000 : ℝ), (3296531147/10000000000 : ℝ)] ![(663038818453/100000000000000 : ℝ), (1188493475361/1562500000000 : ℝ), (11636689371771/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-219668841/10000000000 : ℝ)|^67 ≤ (663038818453/100000000000000 : ℝ)^51
        have hw : |(-219668841/10000000000 : ℝ)|=(219668841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(324797339/400000000 : ℝ)|^67 ≤ (1188493475361/1562500000000 : ℝ)^51
        have hw : |(324797339/400000000 : ℝ)|=(324797339/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3296531147/10000000000 : ℝ)|^67 ≤ (11636689371771/50000000000000 : ℝ)^51
        have hw : |(3296531147/10000000000 : ℝ)|=(3296531147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s1_s1_22 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (535006519/625000000 : ℝ)*x 0 + (-16556791/5000000000 : ℝ)*x 1 + (1379404537/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535006519/625000000 : ℝ)^67 ≤ (40762988819477/50000000000000 : ℝ)^51 := by
    have hnat : (535006519 : ℕ)^67*50000000000000^51 ≤ 40762988819477^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535006519 625000000 40762988819477 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16556791/5000000000 : ℝ)^67 ≤ (55203788063/100000000000000 : ℝ)^51 := by
    have hnat : (16556791 : ℕ)^67*100000000000000^51 ≤ 55203788063^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16556791 5000000000 55203788063 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1379404537/5000000000 : ℝ)^67 ≤ (143897020051/781250000000 : ℝ)^51 := by
    have hnat : (1379404537 : ℕ)^67*781250000000^51 ≤ 143897020051^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379404537 5000000000 143897020051 781250000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535006519/625000000 : ℝ), (-16556791/5000000000 : ℝ), (1379404537/5000000000 : ℝ)] ![(40762988819477/50000000000000 : ℝ), (55203788063/100000000000000 : ℝ), (143897020051/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535006519/625000000 : ℝ)|^67 ≤ (40762988819477/50000000000000 : ℝ)^51
        have hw : |(535006519/625000000 : ℝ)|=(535006519/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-16556791/5000000000 : ℝ)|^67 ≤ (55203788063/100000000000000 : ℝ)^51
        have hw : |(-16556791/5000000000 : ℝ)|=(16556791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1379404537/5000000000 : ℝ)|^67 ≤ (143897020051/781250000000 : ℝ)^51
        have hw : |(1379404537/5000000000 : ℝ)|=(1379404537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s1_s1_23 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (800961209/5000000000 : ℝ)*x 0 + (9178984297/10000000000 : ℝ)*x 1 + (-434853747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (800961209/5000000000 : ℝ)^67 ≤ (4509072742709/50000000000000 : ℝ)^51 := by
    have hnat : (800961209 : ℕ)^67*50000000000000^51 ≤ 4509072742709^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      800961209 5000000000 4509072742709 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9178984297/10000000000 : ℝ)^67 ≤ (71484575077/80000000000 : ℝ)^51 := by
    have hnat : (9178984297 : ℕ)^67*80000000000^51 ≤ 71484575077^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9178984297 10000000000 71484575077 80000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (434853747/10000000000 : ℝ)^67 ≤ (162613566401/10000000000000 : ℝ)^51 := by
    have hnat : (434853747 : ℕ)^67*10000000000000^51 ≤ 162613566401^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434853747 10000000000 162613566401 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(800961209/5000000000 : ℝ), (9178984297/10000000000 : ℝ), (-434853747/10000000000 : ℝ)] ![(4509072742709/50000000000000 : ℝ), (71484575077/80000000000 : ℝ), (162613566401/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(800961209/5000000000 : ℝ)|^67 ≤ (4509072742709/50000000000000 : ℝ)^51
        have hw : |(800961209/5000000000 : ℝ)|=(800961209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(9178984297/10000000000 : ℝ)|^67 ≤ (71484575077/80000000000 : ℝ)^51
        have hw : |(9178984297/10000000000 : ℝ)|=(9178984297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-434853747/10000000000 : ℝ)|^67 ≤ (162613566401/10000000000000 : ℝ)^51
        have hw : |(-434853747/10000000000 : ℝ)|=(434853747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s1_s1_27 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7932473131/10000000000 : ℝ)*x 0 + (505567139/2000000000 : ℝ)*x 1 + (427138149/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7932473131/10000000000 : ℝ)^67 ≤ (36882515265523/50000000000000 : ℝ)^51 := by
    have hnat : (7932473131 : ℕ)^67*50000000000000^51 ≤ 36882515265523^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7932473131 10000000000 36882515265523 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (505567139/2000000000 : ℝ)^67 ≤ (16420104997109/100000000000000 : ℝ)^51 := by
    have hnat : (505567139 : ℕ)^67*100000000000000^51 ≤ 16420104997109^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505567139 2000000000 16420104997109 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (427138149/2500000000 : ℝ)^67 ≤ (9814864457621/100000000000000 : ℝ)^51 := by
    have hnat : (427138149 : ℕ)^67*100000000000000^51 ≤ 9814864457621^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427138149 2500000000 9814864457621 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7932473131/10000000000 : ℝ), (505567139/2000000000 : ℝ), (427138149/2500000000 : ℝ)] ![(36882515265523/50000000000000 : ℝ), (16420104997109/100000000000000 : ℝ), (9814864457621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7932473131/10000000000 : ℝ)|^67 ≤ (36882515265523/50000000000000 : ℝ)^51
        have hw : |(7932473131/10000000000 : ℝ)|=(7932473131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(505567139/2000000000 : ℝ)|^67 ≤ (16420104997109/100000000000000 : ℝ)^51
        have hw : |(505567139/2000000000 : ℝ)|=(505567139/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(427138149/2500000000 : ℝ)|^67 ≤ (9814864457621/100000000000000 : ℝ)^51
        have hw : |(427138149/2500000000 : ℝ)|=(427138149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c305063_s1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((381/400 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(381/400 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(94637/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(94637/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(92999/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(92999/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((44627/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(44627/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22231/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(22231/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43199/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(43199/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76771/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76771/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (93447/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  have s1_pow0 : (381/400 : ℝ) ^ (133/32 : ℝ) ≤ (40843936801623485781/50000000000000000000 : ℝ) := by
    have hpowers : (381/400 : ℝ)^133 ≤ (40843936801623485781/50000000000000000000 : ℝ)^32 := by
      have hnat : (381 : ℕ)^133*50000000000000000000^32 ≤ 40843936801623485781^32*400^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        381 400 40843936801623485781 50000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (381/400 : ℝ)) (X := (40843936801623485781/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (90843936801623485781/50000000000000000000 : ℝ) ≤ (5772503647133483/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (90843936801623485781/50000000000000000000 : ℝ)^32 ≤ (5772503647133483/5000000000000000 : ℝ)^133 := by
      have hnat : (90843936801623485781 : ℕ)^32*5000000000000000^133 ≤ 5772503647133483^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        90843936801623485781 50000000000000000000 5772503647133483 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5772503647133483/5000000000000000 : ℝ)) (X := (90843936801623485781/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (65843936801623485781/25000000000000000000 : ℝ) ≤ (12623830809547833/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (65843936801623485781/25000000000000000000 : ℝ)^32 ≤ (12623830809547833/10000000000000000 : ℝ)^133 := by
      have hnat : (65843936801623485781 : ℕ)^32*10000000000000000^133 ≤ 12623830809547833^133*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        65843936801623485781 25000000000000000000 12623830809547833 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12623830809547833/10000000000000000 : ℝ)) (X := (65843936801623485781/25000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(257501215711161/1587500000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1078823515280867/9525000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (381/400 : ℝ)) (alpha := (257501215711161/1587500000000000 : ℝ)) (beta := (1078823515280867/9525000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (381/400 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(257501215711161/1587500000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1078823515280867/9525000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (94637/100000 : ℝ) ^ (133/32 : ℝ) ≤ (79524946280506757231/100000000000000000000 : ℝ) := by
    have hpowers : (94637/100000 : ℝ)^133 ≤ (79524946280506757231/100000000000000000000 : ℝ)^32 := by
      have hnat : (94637 : ℕ)^133*100000000000000000000^32 ≤ 79524946280506757231^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        94637 100000 79524946280506757231 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (94637/100000 : ℝ)) (X := (79524946280506757231/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (179524946280506757231/100000000000000000000 : ℝ) ≤ (11511788722484749/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (179524946280506757231/100000000000000000000 : ℝ)^32 ≤ (11511788722484749/10000000000000000 : ℝ)^133 := by
      have hnat : (179524946280506757231 : ℕ)^32*10000000000000000^133 ≤ 11511788722484749^133*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        179524946280506757231 100000000000000000000 11511788722484749 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11511788722484749/10000000000000000 : ℝ)) (X := (179524946280506757231/100000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (129524946280506757231/50000000000000000000 : ℝ) ≤ (12573629863228039/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (129524946280506757231/50000000000000000000 : ℝ)^32 ≤ (12573629863228039/10000000000000000 : ℝ)^133 := by
      have hnat : (129524946280506757231 : ℕ)^32*10000000000000000^133 ≤ 12573629863228039^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        129524946280506757231 50000000000000000000 12573629863228039 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12573629863228039/10000000000000000 : ℝ)) (X := (129524946280506757231/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1511788722484749/9463700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(106184114074329/946370000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (94637/100000 : ℝ)) (alpha := (1511788722484749/9463700000000000 : ℝ)) (beta := (106184114074329/946370000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (94637/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1511788722484749/9463700000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(106184114074329/946370000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (92999/100000 : ℝ) ^ (133/32 : ℝ) ≤ (36979228837249373343/50000000000000000000 : ℝ) := by
    have hpowers : (92999/100000 : ℝ)^133 ≤ (36979228837249373343/50000000000000000000 : ℝ)^32 := by
      have hnat : (92999 : ℕ)^133*50000000000000000000^32 ≤ 36979228837249373343^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        92999 100000 36979228837249373343 50000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (92999/100000 : ℝ)) (X := (36979228837249373343/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (86979228837249373343/50000000000000000000 : ℝ) ≤ (2284975544095561/2000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (86979228837249373343/50000000000000000000 : ℝ)^32 ≤ (2284975544095561/2000000000000000 : ℝ)^133 := by
      have hnat : (86979228837249373343 : ℕ)^32*2000000000000000^133 ≤ 2284975544095561^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        86979228837249373343 50000000000000000000 2284975544095561 2000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2284975544095561/2000000000000000 : ℝ)) (X := (86979228837249373343/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (61979228837249373343/25000000000000000000 : ℝ) ≤ (6220720078473041/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (61979228837249373343/25000000000000000000 : ℝ)^32 ≤ (6220720078473041/5000000000000000 : ℝ)^133 := by
      have hnat : (61979228837249373343 : ℕ)^32*5000000000000000^133 ≤ 6220720078473041^133*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61979228837249373343 25000000000000000000 6220720078473041 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6220720078473041/5000000000000000 : ℝ)) (X := (61979228837249373343/25000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(284975544095561/1859980000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1016562436468277/9299900000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (92999/100000 : ℝ)) (alpha := (284975544095561/1859980000000000 : ℝ)) (beta := (1016562436468277/9299900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (92999/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(284975544095561/1859980000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1016562436468277/9299900000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-169925243/10000000000 : ℝ)*X 0 0+(2841210303/5000000000 : ℝ)*X 0 1+(379573143/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1136190031/2000000000 : ℝ)*X 1 0+(-37832787/2500000000 : ℝ)*X 1 1+(760069649/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-134687499/2000000000 : ℝ)*X 0 0+(499168349/2500000000 : ℝ)*X 0 1+(8841644127/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((2272212491/10000000000 : ℝ)*X 1 0+(-180955989/10000000000 : ℝ)*X 1 1+(44265679/50000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((114316929/500000000 : ℝ)*X 2 0+(8883277747/10000000000 : ℝ)*X 2 1+(-642763/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((596726923/2000000000 : ℝ)*X 0 0+(3754782569/5000000000 : ℝ)*X 0 1+(927986323/5000000000 : ℝ)*X 0 2+(596726923/2000000000 : ℝ)*X 1 0+(3754782569/5000000000 : ℝ)*X 1 1+(927986323/5000000000 : ℝ)*X 1 2+(596726923/2000000000 : ℝ)*X 2 0+(3754782569/5000000000 : ℝ)*X 2 1+(927986323/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-15358439/1000000000 : ℝ)*X 0 0+(1087938523/5000000000 : ℝ)*X 0 1+(8923380537/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((932001767/5000000000 : ℝ)*X 1 0+(-129435837/2000000000 : ℝ)*X 1 1+(1787085147/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((2166498571/2500000000 : ℝ)*X 2 0+(2607593229/10000000000 : ℝ)*X 2 1+(-13570909/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((1958463823/2500000000 : ℝ)*X 0 0+(39934559/156250000 : ℝ)*X 0 1+(1834752967/10000000000 : ℝ)*X 0 2+(1958463823/2500000000 : ℝ)*X 1 0+(39934559/156250000 : ℝ)*X 1 1+(1834752967/10000000000 : ℝ)*X 1 2+(1958463823/2500000000 : ℝ)*X 2 0+(39934559/156250000 : ℝ)*X 2 1+(1834752967/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-219668841/10000000000 : ℝ)*X 0 0+(324797339/400000000 : ℝ)*X 0 1+(3296531147/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((535006519/625000000 : ℝ)*X 1 0+(-16556791/5000000000 : ℝ)*X 1 1+(1379404537/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((800961209/5000000000 : ℝ)*X 2 0+(9178984297/10000000000 : ℝ)*X 2 1+(-434853747/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((7932473131/10000000000 : ℝ)*X 0 0+(505567139/2000000000 : ℝ)*X 0 1+(427138149/2500000000 : ℝ)*X 0 2+(7932473131/10000000000 : ℝ)*X 1 0+(505567139/2000000000 : ℝ)*X 1 1+(427138149/2500000000 : ℝ)*X 1 2+(7932473131/10000000000 : ℝ)*X 2 0+(505567139/2000000000 : ℝ)*X 2 1+(427138149/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((44627/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(44627/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (436039116820158173544207561/36908978125000000000000000000000 : ℝ) := by norm_num
    linear_combination (445810581653/500000000000 : ℝ)*(base7) + (197997/125000000000 : ℝ)*(base50) + (13606821459/125000000000 : ℝ)*(base53) + (306791/200000000000 : ℝ)*(base60) + (392599917329/250000000000 : ℝ)*(major_s1_0) + (392599917329/250000000000 : ℝ)*(major_s1_1) + (292309019529/200000000000 : ℝ)*(major_s1_2) + (902347/100000000000 : ℝ)*(sp_s1_0) + (1449481884399/1000000000000 : ℝ)*(sp_s1_7) + (144958952301/100000000000 : ℝ)*(sp_s1_8) + (194805624273/125000000000 : ℝ)*(sp_s1_9) + (1918509417463/1000000000000 : ℝ)*(sp_s1_13) + (99514643/1000000000000 : ℝ)*(sp_s1_14) + (449751/500000000000 : ℝ)*(sp_s1_15) + (256722063539/250000000000 : ℝ)*(f.failure) + (194805624273/125000000000 : ℝ)*(f.sum) + (326074888348773502841/880114636300000000000000000000000 : ℝ)*base63 + (2110904753203/2975968000000000000000000 : ℝ)*base64 + (8125095563083/18927400000000000000000000 : ℝ)*base67 + (156073673655291/1859980000000000000000000000 : ℝ)*base69 + (107353323041466013501/147635912500000000000000000000000 : ℝ)*base70 + (1589776537376743/2381250000000000000000000000 : ℝ)*base73 + (1683533506900183/4731850000000000000000000000 : ℝ)*base74 + (52667083053539/99218750000000000000000000 : ℝ)*base76 + (58538044364481638959/225354356250000000000000000000000 : ℝ)*base78 + (61/195312500000000 : ℝ)*base86 + (61/195312500000000 : ℝ)*base88 + (4101/3125000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22231/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(22231/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (43217269115224125083564631811323/2794363970252500000000000000000000000 : ℝ) := by norm_num
    linear_combination (889601615239/1000000000000 : ℝ)*(base7) + (831313/250000000000 : ℝ)*(base40) + (148265548323/1000000000000 : ℝ)*(base53) + (497033/250000000000 : ℝ)*(base59) + (301856128563/200000000000 : ℝ)*(major_s1_0) + (301856128563/200000000000 : ℝ)*(major_s1_1) + (340253773623/250000000000 : ℝ)*(major_s1_2) + (7349159/1000000000000 : ℝ)*(sp_s1_1) + (8648569/62500000000 : ℝ)*(sp_s1_8) + (1329164197213/1000000000000 : ℝ)*(sp_s1_14) + (1329018470951/1000000000000 : ℝ)*(sp_s1_15) + (11542419887/7812500000 : ℝ)*(sp_s1_16) + (1876446935719/1000000000000 : ℝ)*(sp_s1_20) + (77050057/1000000000000 : ℝ)*(sp_s1_27) + (986922370537/1000000000000 : ℝ)*(f.failure) + (11542419887/7812500000 : ℝ)*(f.sum) + (26374727297490487513/176022927260000000000000000000000 : ℝ)*base62 + (1921941740868073/4649950000000000000000000000 : ℝ)*base64 + (264606453599627/946370000000000000000000000 : ℝ)*base66 + (105221883877259/232497500000000000000000000 : ℝ)*base68 + (5197580998204547943/29527182500000000000000000000000 : ℝ)*base70 + (850434257798293/635000000000000000000000000 : ℝ)*base72 + (523471131626399/1892740000000000000000000000 : ℝ)*base74 + (70135343121393/317500000000000000000000000 : ℝ)*base77 + (18610889513367612641/60094495000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (69/390625000000000 : ℝ)*base86 + (69/390625000000000 : ℝ)*base88 + (69/390625000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43199/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(43199/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (19195656782474055667719/4649950000000000000000000000 : ℝ) := by norm_num
    linear_combination (2830746729/3125000000 : ℝ)*(base7) + (15639/1000000000000 : ℝ)*(base34) + (33715079947/500000000000 : ℝ)*(base40) + (49059659581/1000000000000 : ℝ)*(base43) + (393117/1000000000000 : ℝ)*(base49) + (229299/1000000000000 : ℝ)*(base59) + (1476556723251/1000000000000 : ℝ)*(major_s1_0) + (1427497079309/1000000000000 : ℝ)*(major_s1_1) + (1476556738891/1000000000000 : ℝ)*(major_s1_2) + (8916967/250000000000 : ℝ)*(sp_s1_9) + (274841749423/200000000000 : ℝ)*(sp_s1_21) + (22238569099/15625000000 : ℝ)*(sp_s1_22) + (1374173094887/1000000000000 : ℝ)*(sp_s1_23) + (1871363065917/1000000000000 : ℝ)*(sp_s1_27) + (965524128277/1000000000000 : ℝ)*(f.failure) + (22238569099/15625000000 : ℝ)*(f.sum) + (136474444253188764717/440057318150000000000000000000000 : ℝ)*base63 + (3992649576280207/9299900000000000000000000000 : ℝ)*base65 + (12351966911323/236592500000000000000000000 : ℝ)*base67 + (237342254177393/1859980000000000000000000000 : ℝ)*base69 + (22646418231398188991/36908978125000000000000000000000 : ℝ)*base71 + (125002686549539/3175000000000000000000000000 : ℝ)*base73 + (1568927791182769/9463700000000000000000000000 : ℝ)*base74 + (233559707408089/1587500000000000000000000000 : ℝ)*base76 + (225189020589237492657/300472475000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (4533/3125000000000000 : ℝ)*base87 + (4533/3125000000000000 : ℝ)*base89 + (11/24414062500000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((381/400 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(381/400 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(94637/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(94637/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(92999/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(92999/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((44627/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(44627/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22231/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(22231/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43199/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(43199/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c305063_s1 p hpa hpb X hX hprev0

#print axioms solution
