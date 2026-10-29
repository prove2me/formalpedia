-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c306054_s4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:56:04.094303+00:00
-- url     : https://prove2.me/submissions/e5687814-cf9a-49ac-b5a9-ec3a772bbcf1

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
theorem collision_support_c306054_s4_s4_0 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-79685521/500000000 : ℝ)*x 0 + (56377069/125000000 : ℝ)*x 1 + (-798389633/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (79685521/500000000 : ℝ)^17 ≤ (9057261849771/100000000000000 : ℝ)^13 := by
    have hnat : (79685521 : ℕ)^17*100000000000000^13 ≤ 9057261849771^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79685521 500000000 9057261849771 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56377069/125000000 : ℝ)^17 ≤ (7060251348807/20000000000000 : ℝ)^13 := by
    have hnat : (56377069 : ℕ)^17*20000000000000^13 ≤ 7060251348807^13*125000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56377069 125000000 7060251348807 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (798389633/1250000000 : ℝ)^17 ≤ (27820740694631/50000000000000 : ℝ)^13 := by
    have hnat : (798389633 : ℕ)^17*50000000000000^13 ≤ 27820740694631^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      798389633 1250000000 27820740694631 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-79685521/500000000 : ℝ), (56377069/125000000 : ℝ), (-798389633/1250000000 : ℝ)] ![(9057261849771/100000000000000 : ℝ), (7060251348807/20000000000000 : ℝ), (27820740694631/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-79685521/500000000 : ℝ)|^17 ≤ (9057261849771/100000000000000 : ℝ)^13
        have hw : |(-79685521/500000000 : ℝ)|=(79685521/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(56377069/125000000 : ℝ)|^17 ≤ (7060251348807/20000000000000 : ℝ)^13
        have hw : |(56377069/125000000 : ℝ)|=(56377069/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-798389633/1250000000 : ℝ)|^17 ≤ (27820740694631/50000000000000 : ℝ)^13
        have hw : |(-798389633/1250000000 : ℝ)|=(798389633/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306054_s4_s4_2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (161444689/312500000 : ℝ)*x 0 + (256960383/500000000 : ℝ)*x 1 + (1229186693/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (161444689/312500000 : ℝ)^17 ≤ (21080917655599/50000000000000 : ℝ)^13 := by
    have hnat : (161444689 : ℕ)^17*50000000000000^13 ≤ 21080917655599^13*312500000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161444689 312500000 21080917655599 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (256960383/500000000 : ℝ)^17 ≤ (1674947242741/4000000000000 : ℝ)^13 := by
    have hnat : (256960383 : ℕ)^17*4000000000000^13 ≤ 1674947242741^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256960383 500000000 1674947242741 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1229186693/5000000000 : ℝ)^17 ≤ (7982241800621/50000000000000 : ℝ)^13 := by
    have hnat : (1229186693 : ℕ)^17*50000000000000^13 ≤ 7982241800621^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1229186693 5000000000 7982241800621 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(161444689/312500000 : ℝ), (256960383/500000000 : ℝ), (1229186693/5000000000 : ℝ)] ![(21080917655599/50000000000000 : ℝ), (1674947242741/4000000000000 : ℝ), (7982241800621/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(161444689/312500000 : ℝ)|^17 ≤ (21080917655599/50000000000000 : ℝ)^13
        have hw : |(161444689/312500000 : ℝ)|=(161444689/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(256960383/500000000 : ℝ)|^17 ≤ (1674947242741/4000000000000 : ℝ)^13
        have hw : |(256960383/500000000 : ℝ)|=(256960383/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1229186693/5000000000 : ℝ)|^17 ≤ (7982241800621/50000000000000 : ℝ)^13
        have hw : |(1229186693/5000000000 : ℝ)|=(1229186693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306054_s4_s4_7 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1439090421/10000000000 : ℝ)*x 0 + (4014907891/10000000000 : ℝ)*x 1 + (-691706347/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1439090421/10000000000 : ℝ)^17 ≤ (3962855767027/50000000000000 : ℝ)^13 := by
    have hnat : (1439090421 : ℕ)^17*50000000000000^13 ≤ 3962855767027^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1439090421 10000000000 3962855767027 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4014907891/10000000000 : ℝ)^17 ≤ (15160014515637/50000000000000 : ℝ)^13 := by
    have hnat : (4014907891 : ℕ)^17*50000000000000^13 ≤ 15160014515637^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4014907891 10000000000 15160014515637 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (691706347/1000000000 : ℝ)^17 ≤ (61754259420483/100000000000000 : ℝ)^13 := by
    have hnat : (691706347 : ℕ)^17*100000000000000^13 ≤ 61754259420483^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      691706347 1000000000 61754259420483 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1439090421/10000000000 : ℝ), (4014907891/10000000000 : ℝ), (-691706347/1000000000 : ℝ)] ![(3962855767027/50000000000000 : ℝ), (15160014515637/50000000000000 : ℝ), (61754259420483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1439090421/10000000000 : ℝ)|^17 ≤ (3962855767027/50000000000000 : ℝ)^13
        have hw : |(-1439090421/10000000000 : ℝ)|=(1439090421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4014907891/10000000000 : ℝ)|^17 ≤ (15160014515637/50000000000000 : ℝ)^13
        have hw : |(4014907891/10000000000 : ℝ)|=(4014907891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-691706347/1000000000 : ℝ)|^17 ≤ (61754259420483/100000000000000 : ℝ)^13
        have hw : |(-691706347/1000000000 : ℝ)|=(691706347/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306054_s4_s4_8 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (65685929/125000000 : ℝ)*x 0 + (-1819115201/10000000000 : ℝ)*x 1 + (-5533346813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65685929/125000000 : ℝ)^17 ≤ (21555173228639/50000000000000 : ℝ)^13 := by
    have hnat : (65685929 : ℕ)^17*50000000000000^13 ≤ 21555173228639^13*125000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65685929 125000000 21555173228639 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1819115201/10000000000 : ℝ)^17 ≤ (10767747942373/100000000000000 : ℝ)^13 := by
    have hnat : (1819115201 : ℕ)^17*100000000000000^13 ≤ 10767747942373^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1819115201 10000000000 10767747942373 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5533346813/10000000000 : ℝ)^17 ≤ (46121905589777/100000000000000 : ℝ)^13 := by
    have hnat : (5533346813 : ℕ)^17*100000000000000^13 ≤ 46121905589777^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5533346813 10000000000 46121905589777 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(65685929/125000000 : ℝ), (-1819115201/10000000000 : ℝ), (-5533346813/10000000000 : ℝ)] ![(21555173228639/50000000000000 : ℝ), (10767747942373/100000000000000 : ℝ), (46121905589777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(65685929/125000000 : ℝ)|^17 ≤ (21555173228639/50000000000000 : ℝ)^13
        have hw : |(65685929/125000000 : ℝ)|=(65685929/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1819115201/10000000000 : ℝ)|^17 ≤ (10767747942373/100000000000000 : ℝ)^13
        have hw : |(-1819115201/10000000000 : ℝ)|=(1819115201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5533346813/10000000000 : ℝ)|^17 ≤ (46121905589777/100000000000000 : ℝ)^13
        have hw : |(-5533346813/10000000000 : ℝ)|=(5533346813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306054_s4_s4_9 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4830791627/10000000000 : ℝ)*x 0 + (1518824971/2500000000 : ℝ)*x 1 + (101353011/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4830791627/10000000000 : ℝ)^17 ≤ (4827287677381/12500000000000 : ℝ)^13 := by
    have hnat : (4830791627 : ℕ)^17*12500000000000^13 ≤ 4827287677381^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4830791627 10000000000 4827287677381 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1518824971/2500000000 : ℝ)^17 ≤ (6514531455701/12500000000000 : ℝ)^13 := by
    have hnat : (1518824971 : ℕ)^17*12500000000000^13 ≤ 6514531455701^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1518824971 2500000000 6514531455701 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (101353011/625000000 : ℝ)^17 ≤ (9265446925377/100000000000000 : ℝ)^13 := by
    have hnat : (101353011 : ℕ)^17*100000000000000^13 ≤ 9265446925377^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101353011 625000000 9265446925377 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4830791627/10000000000 : ℝ), (1518824971/2500000000 : ℝ), (101353011/625000000 : ℝ)] ![(4827287677381/12500000000000 : ℝ), (6514531455701/12500000000000 : ℝ), (9265446925377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4830791627/10000000000 : ℝ)|^17 ≤ (4827287677381/12500000000000 : ℝ)^13
        have hw : |(4830791627/10000000000 : ℝ)|=(4830791627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1518824971/2500000000 : ℝ)|^17 ≤ (6514531455701/12500000000000 : ℝ)^13
        have hw : |(1518824971/2500000000 : ℝ)|=(1518824971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(101353011/625000000 : ℝ)|^17 ≤ (9265446925377/100000000000000 : ℝ)^13
        have hw : |(101353011/625000000 : ℝ)|=(101353011/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306054_s4_s4_13 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (310208947/625000000 : ℝ)*x 0 + (120430121/200000000 : ℝ)*x 1 + (-1514969519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (310208947/625000000 : ℝ)^17 ≤ (20004900677229/50000000000000 : ℝ)^13 := by
    have hnat : (310208947 : ℕ)^17*50000000000000^13 ≤ 20004900677229^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      310208947 625000000 20004900677229 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (120430121/200000000 : ℝ)^17 ≤ (25756811139637/50000000000000 : ℝ)^13 := by
    have hnat : (120430121 : ℕ)^17*50000000000000^13 ≤ 25756811139637^13*200000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120430121 200000000 25756811139637 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1514969519/10000000000 : ℝ)^17 ≤ (8476576348179/100000000000000 : ℝ)^13 := by
    have hnat : (1514969519 : ℕ)^17*100000000000000^13 ≤ 8476576348179^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1514969519 10000000000 8476576348179 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(310208947/625000000 : ℝ), (120430121/200000000 : ℝ), (-1514969519/10000000000 : ℝ)] ![(20004900677229/50000000000000 : ℝ), (25756811139637/50000000000000 : ℝ), (8476576348179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(310208947/625000000 : ℝ)|^17 ≤ (20004900677229/50000000000000 : ℝ)^13
        have hw : |(310208947/625000000 : ℝ)|=(310208947/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(120430121/200000000 : ℝ)|^17 ≤ (25756811139637/50000000000000 : ℝ)^13
        have hw : |(120430121/200000000 : ℝ)|=(120430121/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1514969519/10000000000 : ℝ)|^17 ≤ (8476576348179/100000000000000 : ℝ)^13
        have hw : |(-1514969519/10000000000 : ℝ)|=(1514969519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306054_s4_s4_14 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-933358733/10000000000 : ℝ)*x 0 + (221175587/500000000 : ℝ)*x 1 + (-1714890279/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (933358733/10000000000 : ℝ)^17 ≤ (4499253579089/100000000000000 : ℝ)^13 := by
    have hnat : (933358733 : ℕ)^17*100000000000000^13 ≤ 4499253579089^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      933358733 10000000000 4499253579089 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (221175587/500000000 : ℝ)^17 ≤ (17208478597111/50000000000000 : ℝ)^13 := by
    have hnat : (221175587 : ℕ)^17*50000000000000^13 ≤ 17208478597111^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221175587 500000000 17208478597111 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1714890279/2500000000 : ℝ)^17 ≤ (61083789209361/100000000000000 : ℝ)^13 := by
    have hnat : (1714890279 : ℕ)^17*100000000000000^13 ≤ 61083789209361^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1714890279 2500000000 61083789209361 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-933358733/10000000000 : ℝ), (221175587/500000000 : ℝ), (-1714890279/2500000000 : ℝ)] ![(4499253579089/100000000000000 : ℝ), (17208478597111/50000000000000 : ℝ), (61083789209361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-933358733/10000000000 : ℝ)|^17 ≤ (4499253579089/100000000000000 : ℝ)^13
        have hw : |(-933358733/10000000000 : ℝ)|=(933358733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(221175587/500000000 : ℝ)|^17 ≤ (17208478597111/50000000000000 : ℝ)^13
        have hw : |(221175587/500000000 : ℝ)|=(221175587/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1714890279/2500000000 : ℝ)|^17 ≤ (61083789209361/100000000000000 : ℝ)^13
        have hw : |(-1714890279/2500000000 : ℝ)|=(1714890279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306054_s4_s4_15 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4868753849/10000000000 : ℝ)*x 0 + (-572777729/2500000000 : ℝ)*x 1 + (-5561148241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4868753849/10000000000 : ℝ)^17 ≤ (39015635525791/100000000000000 : ℝ)^13 := by
    have hnat : (4868753849 : ℕ)^17*100000000000000^13 ≤ 39015635525791^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4868753849 10000000000 39015635525791 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (572777729/2500000000 : ℝ)^17 ≤ (727959521779/5000000000000 : ℝ)^13 := by
    have hnat : (572777729 : ℕ)^17*5000000000000^13 ≤ 727959521779^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      572777729 2500000000 727959521779 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5561148241/10000000000 : ℝ)^17 ≤ (9285034804277/20000000000000 : ℝ)^13 := by
    have hnat : (5561148241 : ℕ)^17*20000000000000^13 ≤ 9285034804277^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5561148241 10000000000 9285034804277 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4868753849/10000000000 : ℝ), (-572777729/2500000000 : ℝ), (-5561148241/10000000000 : ℝ)] ![(39015635525791/100000000000000 : ℝ), (727959521779/5000000000000 : ℝ), (9285034804277/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4868753849/10000000000 : ℝ)|^17 ≤ (39015635525791/100000000000000 : ℝ)^13
        have hw : |(4868753849/10000000000 : ℝ)|=(4868753849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-572777729/2500000000 : ℝ)|^17 ≤ (727959521779/5000000000000 : ℝ)^13
        have hw : |(-572777729/2500000000 : ℝ)|=(572777729/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5561148241/10000000000 : ℝ)|^17 ≤ (9285034804277/20000000000000 : ℝ)^13
        have hw : |(-5561148241/10000000000 : ℝ)|=(5561148241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306054_s4_s4_16 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1529846553/2500000000 : ℝ)*x 0 + (120080597/250000000 : ℝ)*x 1 + (1593847259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1529846553/2500000000 : ℝ)^17 ≤ (26305679125019/50000000000000 : ℝ)^13 := by
    have hnat : (1529846553 : ℕ)^17*50000000000000^13 ≤ 26305679125019^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1529846553 2500000000 26305679125019 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (120080597/250000000 : ℝ)^17 ≤ (38330362913277/100000000000000 : ℝ)^13 := by
    have hnat : (120080597 : ℕ)^17*100000000000000^13 ≤ 38330362913277^13*250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120080597 250000000 38330362913277 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1593847259/10000000000 : ℝ)^17 ≤ (90582788211/1000000000000 : ℝ)^13 := by
    have hnat : (1593847259 : ℕ)^17*1000000000000^13 ≤ 90582788211^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1593847259 10000000000 90582788211 1000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1529846553/2500000000 : ℝ), (120080597/250000000 : ℝ), (1593847259/10000000000 : ℝ)] ![(26305679125019/50000000000000 : ℝ), (38330362913277/100000000000000 : ℝ), (90582788211/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1529846553/2500000000 : ℝ)|^17 ≤ (26305679125019/50000000000000 : ℝ)^13
        have hw : |(1529846553/2500000000 : ℝ)|=(1529846553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(120080597/250000000 : ℝ)|^17 ≤ (38330362913277/100000000000000 : ℝ)^13
        have hw : |(120080597/250000000 : ℝ)|=(120080597/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1593847259/10000000000 : ℝ)|^17 ≤ (90582788211/1000000000000 : ℝ)^13
        have hw : |(1593847259/10000000000 : ℝ)|=(1593847259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306054_s4_s4_20 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5996134377/10000000000 : ℝ)*x 0 + (490598877/1000000000 : ℝ)*x 1 + (-13078307/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5996134377/10000000000 : ℝ)^17 ≤ (25614983866939/50000000000000 : ℝ)^13 := by
    have hnat : (5996134377 : ℕ)^17*50000000000000^13 ≤ 25614983866939^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5996134377 10000000000 25614983866939 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (490598877/1000000000 : ℝ)^17 ≤ (985157111739/2500000000000 : ℝ)^13 := by
    have hnat : (490598877 : ℕ)^17*2500000000000^13 ≤ 985157111739^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490598877 1000000000 985157111739 2500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13078307/80000000 : ℝ)^17 ≤ (23409369453/250000000000 : ℝ)^13 := by
    have hnat : (13078307 : ℕ)^17*250000000000^13 ≤ 23409369453^13*80000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13078307 80000000 23409369453 250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5996134377/10000000000 : ℝ), (490598877/1000000000 : ℝ), (-13078307/80000000 : ℝ)] ![(25614983866939/50000000000000 : ℝ), (985157111739/2500000000000 : ℝ), (23409369453/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5996134377/10000000000 : ℝ)|^17 ≤ (25614983866939/50000000000000 : ℝ)^13
        have hw : |(5996134377/10000000000 : ℝ)|=(5996134377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(490598877/1000000000 : ℝ)|^17 ≤ (985157111739/2500000000000 : ℝ)^13
        have hw : |(490598877/1000000000 : ℝ)|=(490598877/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-13078307/80000000 : ℝ)|^17 ≤ (23409369453/250000000000 : ℝ)^13
        have hw : |(-13078307/80000000 : ℝ)|=(13078307/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306054_s4_s4_21 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-360006399/5000000000 : ℝ)*x 0 + (207328019/400000000 : ℝ)*x 1 + (-6282484043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (360006399/5000000000 : ℝ)^17 ≤ (50069426399/1562500000000 : ℝ)^13 := by
    have hnat : (360006399 : ℕ)^17*1562500000000^13 ≤ 50069426399^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      360006399 5000000000 50069426399 1562500000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207328019/400000000 : ℝ)^17 ≤ (5292879683437/12500000000000 : ℝ)^13 := by
    have hnat : (207328019 : ℕ)^17*12500000000000^13 ≤ 5292879683437^13*400000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207328019 400000000 5292879683437 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6282484043/10000000000 : ℝ)^17 ≤ (54452519224631/100000000000000 : ℝ)^13 := by
    have hnat : (6282484043 : ℕ)^17*100000000000000^13 ≤ 54452519224631^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6282484043 10000000000 54452519224631 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-360006399/5000000000 : ℝ), (207328019/400000000 : ℝ), (-6282484043/10000000000 : ℝ)] ![(50069426399/1562500000000 : ℝ), (5292879683437/12500000000000 : ℝ), (54452519224631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-360006399/5000000000 : ℝ)|^17 ≤ (50069426399/1562500000000 : ℝ)^13
        have hw : |(-360006399/5000000000 : ℝ)|=(360006399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207328019/400000000 : ℝ)|^17 ≤ (5292879683437/12500000000000 : ℝ)^13
        have hw : |(207328019/400000000 : ℝ)|=(207328019/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6282484043/10000000000 : ℝ)|^17 ≤ (54452519224631/100000000000000 : ℝ)^13
        have hw : |(-6282484043/10000000000 : ℝ)|=(6282484043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306054_s4_s4_22 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (802518409/1250000000 : ℝ)*x 0 + (-1994834801/10000000000 : ℝ)*x 1 + (-104183899/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (802518409/1250000000 : ℝ)^17 ≤ (28009030005019/50000000000000 : ℝ)^13 := by
    have hnat : (802518409 : ℕ)^17*50000000000000^13 ≤ 28009030005019^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      802518409 1250000000 28009030005019 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1994834801/10000000000 : ℝ)^17 ≤ (3036922396369/25000000000000 : ℝ)^13 := by
    have hnat : (1994834801 : ℕ)^17*25000000000000^13 ≤ 3036922396369^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1994834801 10000000000 3036922396369 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104183899/250000000 : ℝ)^17 ≤ (3979281299659/12500000000000 : ℝ)^13 := by
    have hnat : (104183899 : ℕ)^17*12500000000000^13 ≤ 3979281299659^13*250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104183899 250000000 3979281299659 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(802518409/1250000000 : ℝ), (-1994834801/10000000000 : ℝ), (-104183899/250000000 : ℝ)] ![(28009030005019/50000000000000 : ℝ), (3036922396369/25000000000000 : ℝ), (3979281299659/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(802518409/1250000000 : ℝ)|^17 ≤ (28009030005019/50000000000000 : ℝ)^13
        have hw : |(802518409/1250000000 : ℝ)|=(802518409/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1994834801/10000000000 : ℝ)|^17 ≤ (3036922396369/25000000000000 : ℝ)^13
        have hw : |(-1994834801/10000000000 : ℝ)|=(1994834801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-104183899/250000000 : ℝ)|^17 ≤ (3979281299659/12500000000000 : ℝ)^13
        have hw : |(-104183899/250000000 : ℝ)|=(104183899/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306054_s4_s4_23 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (974858467/2000000000 : ℝ)*x 0 + (1062235057/2000000000 : ℝ)*x 1 + (1301924731/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (974858467/2000000000 : ℝ)^17 ≤ (19536842178331/50000000000000 : ℝ)^13 := by
    have hnat : (974858467 : ℕ)^17*50000000000000^13 ≤ 19536842178331^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      974858467 2000000000 19536842178331 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1062235057/2000000000 : ℝ)^17 ≤ (43715344671823/100000000000000 : ℝ)^13 := by
    have hnat : (1062235057 : ℕ)^17*100000000000000^13 ≤ 43715344671823^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062235057 2000000000 43715344671823 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1301924731/5000000000 : ℝ)^17 ≤ (2151371369429/12500000000000 : ℝ)^13 := by
    have hnat : (1301924731 : ℕ)^17*12500000000000^13 ≤ 2151371369429^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1301924731 5000000000 2151371369429 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(974858467/2000000000 : ℝ), (1062235057/2000000000 : ℝ), (1301924731/5000000000 : ℝ)] ![(19536842178331/50000000000000 : ℝ), (43715344671823/100000000000000 : ℝ), (2151371369429/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(974858467/2000000000 : ℝ)|^17 ≤ (19536842178331/50000000000000 : ℝ)^13
        have hw : |(974858467/2000000000 : ℝ)|=(974858467/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1062235057/2000000000 : ℝ)|^17 ≤ (43715344671823/100000000000000 : ℝ)^13
        have hw : |(1062235057/2000000000 : ℝ)|=(1062235057/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1301924731/5000000000 : ℝ)|^17 ≤ (2151371369429/12500000000000 : ℝ)^13
        have hw : |(1301924731/5000000000 : ℝ)|=(1301924731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306054_s4_s4_27 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5802445103/10000000000 : ℝ)*x 0 + (2406591101/5000000000 : ℝ)*x 1 + (-1018772183/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5802445103/10000000000 : ℝ)^17 ≤ (49076770447397/100000000000000 : ℝ)^13 := by
    have hnat : (5802445103 : ℕ)^17*100000000000000^13 ≤ 49076770447397^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5802445103 10000000000 49076770447397 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2406591101/5000000000 : ℝ)^17 ≤ (7686863337941/20000000000000 : ℝ)^13 := by
    have hnat : (2406591101 : ℕ)^17*20000000000000^13 ≤ 7686863337941^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2406591101 5000000000 7686863337941 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1018772183/5000000000 : ℝ)^17 ≤ (3122228213503/25000000000000 : ℝ)^13 := by
    have hnat : (1018772183 : ℕ)^17*25000000000000^13 ≤ 3122228213503^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018772183 5000000000 3122228213503 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5802445103/10000000000 : ℝ), (2406591101/5000000000 : ℝ), (-1018772183/5000000000 : ℝ)] ![(49076770447397/100000000000000 : ℝ), (7686863337941/20000000000000 : ℝ), (3122228213503/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5802445103/10000000000 : ℝ)|^17 ≤ (49076770447397/100000000000000 : ℝ)^13
        have hw : |(5802445103/10000000000 : ℝ)|=(5802445103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2406591101/5000000000 : ℝ)|^17 ≤ (7686863337941/20000000000000 : ℝ)^13
        have hw : |(2406591101/5000000000 : ℝ)|=(2406591101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1018772183/5000000000 : ℝ)|^17 ≤ (3122228213503/25000000000000 : ℝ)^13
        have hw : |(-1018772183/5000000000 : ℝ)|=(1018772183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c306054_s4 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev3 : (0 : ℝ) ≤ ((52539/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(52539/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(55307/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(55307/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-40081/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-40081/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((33199/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(33199/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17317/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(17317/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-11221/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-11221/50000 : ℝ)*X 1 2) := by
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
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  rcases hprev3 with ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩
  have s4_pow0 : (52539/100000 : ℝ) ^ (67/16 : ℝ) ≤ (6753323400199115253/100000000000000000000 : ℝ) := by
    have hpowers : (52539/100000 : ℝ)^67 ≤ (6753323400199115253/100000000000000000000 : ℝ)^16 := by
      have hnat : (52539 : ℕ)^67*100000000000000000000^16 ≤ 6753323400199115253^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52539 100000 6753323400199115253 100000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (52539/100000 : ℝ)) (X := (6753323400199115253/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s4_corner0a : (106753323400199115253/100000000000000000000 : ℝ) ≤ (1015728524341631/1000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (106753323400199115253/100000000000000000000 : ℝ)^16 ≤ (1015728524341631/1000000000000000 : ℝ)^67 := by
      have hnat : (106753323400199115253 : ℕ)^16*1000000000000000^67 ≤ 1015728524341631^67*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        106753323400199115253 100000000000000000000 1015728524341631 1000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1015728524341631/1000000000000000 : ℝ)) (X := (106753323400199115253/100000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s4_corner0b : (56753323400199115253/50000000000000000000 : ℝ) ≤ (10307169392525951/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (56753323400199115253/50000000000000000000 : ℝ)^16 ≤ (10307169392525951/10000000000000000 : ℝ)^67 := by
      have hnat : (56753323400199115253 : ℕ)^16*10000000000000000^67 ≤ 10307169392525951^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56753323400199115253 50000000000000000000 10307169392525951 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10307169392525951/10000000000000000 : ℝ)) (X := (56753323400199115253/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s4_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(15728524341631/525390000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(49961383036547/1751300000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (52539/100000 : ℝ)) (alpha := (15728524341631/525390000000000 : ℝ)) (beta := (49961383036547/1751300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow0,s4_corner0a]) (by linarith only [s4_pow0,s4_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (52539/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(15728524341631/525390000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(49961383036547/1751300000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow1 : (55307/100000 : ℝ) ^ (67/16 : ℝ) ≤ (837320407885969657/10000000000000000000 : ℝ) := by
    have hpowers : (55307/100000 : ℝ)^67 ≤ (837320407885969657/10000000000000000000 : ℝ)^16 := by
      have hnat : (55307 : ℕ)^67*10000000000000000000^16 ≤ 837320407885969657^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55307 100000 837320407885969657 10000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (55307/100000 : ℝ)) (X := (837320407885969657/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s4_corner1a : (10837320407885969657/10000000000000000000 : ℝ) ≤ (10193881046443983/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (10837320407885969657/10000000000000000000 : ℝ)^16 ≤ (10193881046443983/10000000000000000 : ℝ)^67 := by
      have hnat : (10837320407885969657 : ℕ)^16*10000000000000000^67 ≤ 10193881046443983^67*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10837320407885969657 10000000000000000000 10193881046443983 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10193881046443983/10000000000000000 : ℝ)) (X := (10837320407885969657/10000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s4_corner1b : (5837320407885969657/5000000000000000000 : ℝ) ≤ (10376673594328539/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (5837320407885969657/5000000000000000000 : ℝ)^16 ≤ (10376673594328539/10000000000000000 : ℝ)^67 := by
      have hnat : (5837320407885969657 : ℕ)^16*10000000000000000^67 ≤ 10376673594328539^67*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5837320407885969657 5000000000000000000 10376673594328539 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10376673594328539/10000000000000000 : ℝ)) (X := (5837320407885969657/5000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s4_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(193881046443983/5530700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(45698136971139/1382675000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (55307/100000 : ℝ)) (alpha := (193881046443983/5530700000000000 : ℝ)) (beta := (45698136971139/1382675000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow1,s4_corner1a]) (by linarith only [s4_pow1,s4_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (55307/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(193881046443983/5530700000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(45698136971139/1382675000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow2 : (40081/100000 : ℝ) ^ (67/16 : ℝ) ≤ (16986159658266963/781250000000000000 : ℝ) := by
    have hpowers : (40081/100000 : ℝ)^67 ≤ (16986159658266963/781250000000000000 : ℝ)^16 := by
      have hnat : (40081 : ℕ)^67*781250000000000000^16 ≤ 16986159658266963^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        40081 100000 16986159658266963 781250000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (40081/100000 : ℝ)) (X := (16986159658266963/781250000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s4_corner2a : (798236159658266963/781250000000000000 : ℝ) ≤ (314109300633823/312500000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (798236159658266963/781250000000000000 : ℝ)^16 ≤ (314109300633823/312500000000000 : ℝ)^67 := by
      have hnat : (798236159658266963 : ℕ)^16*312500000000000^67 ≤ 314109300633823^67*781250000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        798236159658266963 781250000000000000 314109300633823 312500000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (314109300633823/312500000000000 : ℝ)) (X := (798236159658266963/781250000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s4_corner2b : (407611159658266963/390625000000000000 : ℝ) ≤ (2525541930070731/2500000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (407611159658266963/390625000000000000 : ℝ)^16 ≤ (2525541930070731/2500000000000000 : ℝ)^67 := by
      have hnat : (407611159658266963 : ℕ)^16*2500000000000000^67 ≤ 2525541930070731^67*390625000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        407611159658266963 390625000000000000 2525541930070731 2500000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2525541930070731/2500000000000000 : ℝ)) (X := (407611159658266963/390625000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s4_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1609300633823/125253125000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(12667525000147/1002025000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (40081/100000 : ℝ)) (alpha := (1609300633823/125253125000000 : ℝ)) (beta := (12667525000147/1002025000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow2,s4_corner2a]) (by linarith only [s4_pow2,s4_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (40081/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1609300633823/125253125000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(12667525000147/1002025000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s4_0 : ((-79685521/500000000 : ℝ)*X 0 0+(56377069/125000000 : ℝ)*X 0 1+(-798389633/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s4_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_2 : ((161444689/312500000 : ℝ)*X 2 0+(256960383/500000000 : ℝ)*X 2 1+(1229186693/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s4_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_7 : ((-1439090421/10000000000 : ℝ)*X 0 0+(4014907891/10000000000 : ℝ)*X 0 1+(-691706347/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s4_s4_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_8 : ((65685929/125000000 : ℝ)*X 1 0+(-1819115201/10000000000 : ℝ)*X 1 1+(-5533346813/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s4_s4_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_9 : ((4830791627/10000000000 : ℝ)*X 2 0+(1518824971/2500000000 : ℝ)*X 2 1+(101353011/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s4_s4_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_13 : ((310208947/625000000 : ℝ)*X 0 0+(120430121/200000000 : ℝ)*X 0 1+(-1514969519/10000000000 : ℝ)*X 0 2+(310208947/625000000 : ℝ)*X 1 0+(120430121/200000000 : ℝ)*X 1 1+(-1514969519/10000000000 : ℝ)*X 1 2+(310208947/625000000 : ℝ)*X 2 0+(120430121/200000000 : ℝ)*X 2 1+(-1514969519/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s4_s4_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_14 : ((-933358733/10000000000 : ℝ)*X 0 0+(221175587/500000000 : ℝ)*X 0 1+(-1714890279/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s4_s4_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_15 : ((4868753849/10000000000 : ℝ)*X 1 0+(-572777729/2500000000 : ℝ)*X 1 1+(-5561148241/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s4_s4_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_16 : ((1529846553/2500000000 : ℝ)*X 2 0+(120080597/250000000 : ℝ)*X 2 1+(1593847259/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s4_s4_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_20 : ((5996134377/10000000000 : ℝ)*X 0 0+(490598877/1000000000 : ℝ)*X 0 1+(-13078307/80000000 : ℝ)*X 0 2+(5996134377/10000000000 : ℝ)*X 1 0+(490598877/1000000000 : ℝ)*X 1 1+(-13078307/80000000 : ℝ)*X 1 2+(5996134377/10000000000 : ℝ)*X 2 0+(490598877/1000000000 : ℝ)*X 2 1+(-13078307/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s4_s4_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_21 : ((-360006399/5000000000 : ℝ)*X 0 0+(207328019/400000000 : ℝ)*X 0 1+(-6282484043/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s4_s4_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_22 : ((802518409/1250000000 : ℝ)*X 1 0+(-1994834801/10000000000 : ℝ)*X 1 1+(-104183899/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s4_s4_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_23 : ((974858467/2000000000 : ℝ)*X 2 0+(1062235057/2000000000 : ℝ)*X 2 1+(1301924731/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s4_s4_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_27 : ((5802445103/10000000000 : ℝ)*X 0 0+(2406591101/5000000000 : ℝ)*X 0 1+(-1018772183/5000000000 : ℝ)*X 0 2+(5802445103/10000000000 : ℝ)*X 1 0+(2406591101/5000000000 : ℝ)*X 1 1+(-1018772183/5000000000 : ℝ)*X 1 2+(5802445103/10000000000 : ℝ)*X 2 0+(2406591101/5000000000 : ℝ)*X 2 1+(-1018772183/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306054_s4_s4_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s4_0 : (0 : ℝ) ≤ ((33199/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(33199/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (127157235442822525333867021/35096927650000000000000000000000 : ℝ) := by norm_num
    linear_combination (138103616081/200000000000 : ℝ)*(base39) + (1419837/1000000000000 : ℝ)*(base50) + (218898917177/500000000000 : ℝ)*(base60) + (5505584973973/1000000000000 : ℝ)*(major_s4_0) + (5505584973973/1000000000000 : ℝ)*(major_s4_1) + (5505584973973/1000000000000 : ℝ)*(major_s4_2) + (1095779/100000000000 : ℝ)*(sp_s4_0) + (7440404597147/1000000000000 : ℝ)*(sp_s4_7) + (7440379210549/1000000000000 : ℝ)*(sp_s4_8) + (465025047117/62500000000 : ℝ)*(sp_s4_9) + (1785371231491/500000000000 : ℝ)*(sp_s4_13) + (2144469/200000000000 : ℝ)*(sp_s4_14) + (23533367/500000000000 : ℝ)*(sp_s4_15) + (25523411/1000000000000 : ℝ)*(sp_s4_23) + (1785371231491/500000000000 : ℝ)*(f.failure) + (7440426277283/1000000000000 : ℝ)*(f.sum) + (3891164923353219041/6333599620000000000000000000000 : ℝ)*base63 + (1063915875018623/2004050000000000000000000000 : ℝ)*base64 + (33420280496999/197525000000000000000000000 : ℝ)*base67 + (38010542012043/1002025000000000000000000000 : ℝ)*base68 + (6376759131802514579/13161347868750000000000000000000 : ℝ)*base70 + (324951318181801/1751300000000000000000000000 : ℝ)*base73 + (153303936233293/790100000000000000000000000 : ℝ)*base74 + (137060256380887/262695000000000000000000000 : ℝ)*base76 + (537887454627701041/13837021300000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (10663/25000000000000000 : ℝ)*base87 + (10663/25000000000000000 : ℝ)*base89 + (10663/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s4_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17317/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(17317/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7797334903111767533697/1002025000000000000000000000 : ℝ) := by norm_num
    linear_combination (157459597089/250000000000 : ℝ)*(base39) + (2043193/1000000000000 : ℝ)*(base49) + (47034135593/250000000000 : ℝ)*(base60) + (2765072349473/500000000000 : ℝ)*(major_s4_0) + (2765072349473/500000000000 : ℝ)*(major_s4_1) + (2765072349473/500000000000 : ℝ)*(major_s4_2) + (70255767/1000000000000 : ℝ)*(sp_s4_0) + (38447287/500000000000 : ℝ)*(sp_s4_8) + (7473523806113/1000000000000 : ℝ)*(sp_s4_14) + (7473538811597/1000000000000 : ℝ)*(sp_s4_15) + (7473615706171/1000000000000 : ℝ)*(sp_s4_16) + (448308082853/125000000000 : ℝ)*(sp_s4_20) + (21644291/1000000000000 : ℝ)*(sp_s4_21) + (51608759/250000000000 : ℝ)*(sp_s4_27) + (179333554893/50000000000 : ℝ)*(f.failure) + (7473615706171/1000000000000 : ℝ)*(f.sum) + (1189161615864659/197924988125000000000000000000 : ℝ)*base62 + (474865240556861/2004050000000000000000000000 : ℝ)*base64 + (36494356349359/395050000000000000000000000 : ℝ)*base66 + (517431352373883/2004050000000000000000000000 : ℝ)*base69 + (3326413793683360519/6580673934375000000000000000000 : ℝ)*base70 + (65075802918147/437825000000000000000000000 : ℝ)*base72 + (302485276097/395050000000000000000000000 : ℝ)*base75 + (14481203125439/262695000000000000000000000 : ℝ)*base77 + (716429310481666297/3459255325000000000000000000000 : ℝ)*base79 + (1049/2500000000000000 : ℝ)*base87 + (1049/2500000000000000 : ℝ)*base89 + (1049/2500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s4_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-11221/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-11221/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2413204372790603222629517685163/388221155507710000000000000000000000 : ℝ) := by norm_num
    linear_combination (485176550549/500000000000 : ℝ)*(base39) + (765541/500000000000 : ℝ)*(base40) + (709043/500000000000 : ℝ)*(base50) + (432677209373/100000000000 : ℝ)*(major_s4_0) + (432677209373/100000000000 : ℝ)*(major_s4_1) + (432677209373/100000000000 : ℝ)*(major_s4_2) + (451443/500000000000 : ℝ)*(sp_s4_0) + (3913259/1000000000000 : ℝ)*(sp_s4_2) + (1012049/50000000000 : ℝ)*(sp_s4_9) + (31252203/250000000000 : ℝ)*(sp_s4_20) + (1461834563491/250000000000 : ℝ)*(sp_s4_21) + (116946783137/20000000000 : ℝ)*(sp_s4_22) + (5847315002611/1000000000000 : ℝ)*(sp_s4_23) + (2806077949777/1000000000000 : ℝ)*(sp_s4_27) + (2806202958589/1000000000000 : ℝ)*(f.failure) + (116946783137/20000000000 : ℝ)*(f.sum) + (1417623739938386723/11083799335000000000000000000000 : ℝ)*base62 + (2787699858761/40081000000000000000000000 : ℝ)*base64 + (20109917585861/276535000000000000000000000 : ℝ)*base66 + (40648957828427/400810000000000000000000000 : ℝ)*base68 + (1065875603446002197/2105815659000000000000000000000 : ℝ)*base71 + (50720267302503/175130000000000000000000000 : ℝ)*base72 + (28622935591013/110614000000000000000000000 : ℝ)*base74 + (196550881457159/525390000000000000000000000 : ℝ)*base77 + (5403402808261392841/9685914910000000000000000000000 : ℝ)*base78 + (1777/50000000000000000 : ℝ)*base87 + (1777/50000000000000000 : ℝ)*base89 + (1777/50000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev3 : (0 : ℝ) ≤ ((52539/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(52539/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(55307/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(55307/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-40081/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-40081/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((33199/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(33199/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17317/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(17317/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-11221/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-11221/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c306054_s4 p hpa hpb X hX hprev3

#print axioms solution
