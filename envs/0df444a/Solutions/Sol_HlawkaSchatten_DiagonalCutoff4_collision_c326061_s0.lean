-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c326061_s0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:11:23.685362+00:00
-- url     : https://prove2.me/submissions/404d0ce3-89e6-4a45-94db-e8810674edcc

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
theorem collision_support_c326061_s0_s0_0 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-129860827/1250000000 : ℝ)*x 0 + (578545629/1250000000 : ℝ)*x 1 + (6085924209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129860827/1250000000 : ℝ)^89 ≤ (6324430795509/100000000000000 : ℝ)^73 := by
    have hnat : (129860827 : ℕ)^89*100000000000000^73 ≤ 6324430795509^73*1250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129860827 1250000000 6324430795509 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (578545629/1250000000 : ℝ)^89 ≤ (312742320757/800000000000 : ℝ)^73 := by
    have hnat : (578545629 : ℕ)^89*800000000000^73 ≤ 312742320757^73*1250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      578545629 1250000000 312742320757 800000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6085924209/10000000000 : ℝ)^89 ≤ (54582779099451/100000000000000 : ℝ)^73 := by
    have hnat : (6085924209 : ℕ)^89*100000000000000^73 ≤ 54582779099451^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6085924209 10000000000 54582779099451 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-129860827/1250000000 : ℝ), (578545629/1250000000 : ℝ), (6085924209/10000000000 : ℝ)] ![(6324430795509/100000000000000 : ℝ), (312742320757/800000000000 : ℝ), (54582779099451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-129860827/1250000000 : ℝ)|^89 ≤ (6324430795509/100000000000000 : ℝ)^73
        have hw : |(-129860827/1250000000 : ℝ)|=(129860827/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(578545629/1250000000 : ℝ)|^89 ≤ (312742320757/800000000000 : ℝ)^73
        have hw : |(578545629/1250000000 : ℝ)|=(578545629/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6085924209/10000000000 : ℝ)|^89 ≤ (54582779099451/100000000000000 : ℝ)^73
        have hw : |(6085924209/10000000000 : ℝ)|=(6085924209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326061_s0_s0_1 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2342329153/5000000000 : ℝ)*x 0 + (-208153123/2000000000 : ℝ)*x 1 + (3015754971/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2342329153/5000000000 : ℝ)^89 ≤ (9918311549347/25000000000000 : ℝ)^73 := by
    have hnat : (2342329153 : ℕ)^89*25000000000000^73 ≤ 9918311549347^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2342329153 5000000000 9918311549347 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208153123/2000000000 : ℝ)^89 ≤ (1584594868157/25000000000000 : ℝ)^73 := by
    have hnat : (208153123 : ℕ)^89*25000000000000^73 ≤ 1584594868157^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208153123 2000000000 1584594868157 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3015754971/5000000000 : ℝ)^89 ≤ (53988374319471/100000000000000 : ℝ)^73 := by
    have hnat : (3015754971 : ℕ)^89*100000000000000^73 ≤ 53988374319471^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3015754971 5000000000 53988374319471 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2342329153/5000000000 : ℝ), (-208153123/2000000000 : ℝ), (3015754971/5000000000 : ℝ)] ![(9918311549347/25000000000000 : ℝ), (1584594868157/25000000000000 : ℝ), (53988374319471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2342329153/5000000000 : ℝ)|^89 ≤ (9918311549347/25000000000000 : ℝ)^73
        have hw : |(2342329153/5000000000 : ℝ)|=(2342329153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-208153123/2000000000 : ℝ)|^89 ≤ (1584594868157/25000000000000 : ℝ)^73
        have hw : |(-208153123/2000000000 : ℝ)|=(208153123/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3015754971/5000000000 : ℝ)|^89 ≤ (53988374319471/100000000000000 : ℝ)^73
        have hw : |(3015754971/5000000000 : ℝ)|=(3015754971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326061_s0_s0_6 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (341216289/500000000 : ℝ)*x 0 + (1171021171/5000000000 : ℝ)*x 1 + (53861391/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (341216289/500000000 : ℝ)^89 ≤ (62760917730869/100000000000000 : ℝ)^73 := by
    have hnat : (341216289 : ℕ)^89*100000000000000^73 ≤ 62760917730869^73*500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341216289 500000000 62760917730869 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1171021171/5000000000 : ℝ)^89 ≤ (17038200599299/100000000000000 : ℝ)^73 := by
    have hnat : (1171021171 : ℕ)^89*100000000000000^73 ≤ 17038200599299^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1171021171 5000000000 17038200599299 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53861391/200000000 : ℝ)^89 ≤ (808035266243/4000000000000 : ℝ)^73 := by
    have hnat : (53861391 : ℕ)^89*4000000000000^73 ≤ 808035266243^73*200000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53861391 200000000 808035266243 4000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(341216289/500000000 : ℝ), (1171021171/5000000000 : ℝ), (53861391/200000000 : ℝ)] ![(62760917730869/100000000000000 : ℝ), (17038200599299/100000000000000 : ℝ), (808035266243/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(341216289/500000000 : ℝ)|^89 ≤ (62760917730869/100000000000000 : ℝ)^73
        have hw : |(341216289/500000000 : ℝ)|=(341216289/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1171021171/5000000000 : ℝ)|^89 ≤ (17038200599299/100000000000000 : ℝ)^73
        have hw : |(1171021171/5000000000 : ℝ)|=(1171021171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(53861391/200000000 : ℝ)|^89 ≤ (808035266243/4000000000000 : ℝ)^73
        have hw : |(53861391/200000000 : ℝ)|=(53861391/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326061_s0_s0_7 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-227096743/1250000000 : ℝ)*x 0 + (17584647/156250000 : ℝ)*x 1 + (4186178301/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (227096743/1250000000 : ℝ)^89 ≤ (6250660154447/50000000000000 : ℝ)^73 := by
    have hnat : (227096743 : ℕ)^89*50000000000000^73 ≤ 6250660154447^73*1250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227096743 1250000000 6250660154447 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17584647/156250000 : ℝ)^89 ≤ (3486200600777/50000000000000 : ℝ)^73 := by
    have hnat : (17584647 : ℕ)^89*50000000000000^73 ≤ 3486200600777^73*156250000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17584647 156250000 3486200600777 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4186178301/5000000000 : ℝ)^89 ≤ (20131569619641/25000000000000 : ℝ)^73 := by
    have hnat : (4186178301 : ℕ)^89*25000000000000^73 ≤ 20131569619641^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4186178301 5000000000 20131569619641 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-227096743/1250000000 : ℝ), (17584647/156250000 : ℝ), (4186178301/5000000000 : ℝ)] ![(6250660154447/50000000000000 : ℝ), (3486200600777/50000000000000 : ℝ), (20131569619641/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-227096743/1250000000 : ℝ)|^89 ≤ (6250660154447/50000000000000 : ℝ)^73
        have hw : |(-227096743/1250000000 : ℝ)|=(227096743/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(17584647/156250000 : ℝ)|^89 ≤ (3486200600777/50000000000000 : ℝ)^73
        have hw : |(17584647/156250000 : ℝ)|=(17584647/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4186178301/5000000000 : ℝ)|^89 ≤ (20131569619641/25000000000000 : ℝ)^73
        have hw : |(4186178301/5000000000 : ℝ)|=(4186178301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326061_s0_s0_8 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (264459781/1250000000 : ℝ)*x 0 + (-387276177/5000000000 : ℝ)*x 1 + (261636321/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264459781/1250000000 : ℝ)^89 ≤ (3763075841229/25000000000000 : ℝ)^73 := by
    have hnat : (264459781 : ℕ)^89*25000000000000^73 ≤ 3763075841229^73*1250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264459781 1250000000 3763075841229 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (387276177/5000000000 : ℝ)^89 ≤ (4421351656617/100000000000000 : ℝ)^73 := by
    have hnat : (387276177 : ℕ)^89*100000000000000^73 ≤ 4421351656617^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387276177 5000000000 4421351656617 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (261636321/312500000 : ℝ)^89 ≤ (80526344966087/100000000000000 : ℝ)^73 := by
    have hnat : (261636321 : ℕ)^89*100000000000000^73 ≤ 80526344966087^73*312500000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261636321 312500000 80526344966087 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264459781/1250000000 : ℝ), (-387276177/5000000000 : ℝ), (261636321/312500000 : ℝ)] ![(3763075841229/25000000000000 : ℝ), (4421351656617/100000000000000 : ℝ), (80526344966087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264459781/1250000000 : ℝ)|^89 ≤ (3763075841229/25000000000000 : ℝ)^73
        have hw : |(264459781/1250000000 : ℝ)|=(264459781/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-387276177/5000000000 : ℝ)|^89 ≤ (4421351656617/100000000000000 : ℝ)^73
        have hw : |(-387276177/5000000000 : ℝ)|=(387276177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(261636321/312500000 : ℝ)|^89 ≤ (80526344966087/100000000000000 : ℝ)^73
        have hw : |(261636321/312500000 : ℝ)|=(261636321/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326061_s0_s0_9 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (50596643/250000000 : ℝ)*x 0 + (1101787879/1250000000 : ℝ)*x 1 + (-1424757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (50596643/250000000 : ℝ)^89 ≤ (14259750566047/100000000000000 : ℝ)^73 := by
    have hnat : (50596643 : ℕ)^89*100000000000000^73 ≤ 14259750566047^73*250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50596643 250000000 14259750566047 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1101787879/1250000000 : ℝ)^89 ≤ (10717275534073/12500000000000 : ℝ)^73 := by
    have hnat : (1101787879 : ℕ)^89*12500000000000^73 ≤ 10717275534073^73*1250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101787879 1250000000 10717275534073 12500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1424757/10000000000 : ℝ)^89 ≤ (2045149613/100000000000000 : ℝ)^73 := by
    have hnat : (1424757 : ℕ)^89*100000000000000^73 ≤ 2045149613^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1424757 10000000000 2045149613 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(50596643/250000000 : ℝ), (1101787879/1250000000 : ℝ), (-1424757/10000000000 : ℝ)] ![(14259750566047/100000000000000 : ℝ), (10717275534073/12500000000000 : ℝ), (2045149613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(50596643/250000000 : ℝ)|^89 ≤ (14259750566047/100000000000000 : ℝ)^73
        have hw : |(50596643/250000000 : ℝ)|=(50596643/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1101787879/1250000000 : ℝ)|^89 ≤ (10717275534073/12500000000000 : ℝ)^73
        have hw : |(1101787879/1250000000 : ℝ)|=(1101787879/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1424757/10000000000 : ℝ)|^89 ≤ (2045149613/100000000000000 : ℝ)^73
        have hw : |(-1424757/10000000000 : ℝ)|=(1424757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326061_s0_s0_13 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1933244579/5000000000 : ℝ)*x 0 + (6497571791/10000000000 : ℝ)*x 1 + (90558731/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1933244579/5000000000 : ℝ)^89 ≤ (31395375638803/100000000000000 : ℝ)^73 := by
    have hnat : (1933244579 : ℕ)^89*100000000000000^73 ≤ 31395375638803^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1933244579 5000000000 31395375638803 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6497571791/10000000000 : ℝ)^89 ≤ (59116706260373/100000000000000 : ℝ)^73 := by
    have hnat : (6497571791 : ℕ)^89*100000000000000^73 ≤ 59116706260373^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6497571791 10000000000 59116706260373 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (90558731/625000000 : ℝ)^89 ≤ (4743959046049/50000000000000 : ℝ)^73 := by
    have hnat : (90558731 : ℕ)^89*50000000000000^73 ≤ 4743959046049^73*625000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90558731 625000000 4743959046049 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1933244579/5000000000 : ℝ), (6497571791/10000000000 : ℝ), (90558731/625000000 : ℝ)] ![(31395375638803/100000000000000 : ℝ), (59116706260373/100000000000000 : ℝ), (4743959046049/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1933244579/5000000000 : ℝ)|^89 ≤ (31395375638803/100000000000000 : ℝ)^73
        have hw : |(1933244579/5000000000 : ℝ)|=(1933244579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6497571791/10000000000 : ℝ)|^89 ≤ (59116706260373/100000000000000 : ℝ)^73
        have hw : |(6497571791/10000000000 : ℝ)|=(6497571791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(90558731/625000000 : ℝ)|^89 ≤ (4743959046049/50000000000000 : ℝ)^73
        have hw : |(90558731/625000000 : ℝ)|=(90558731/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326061_s0_s0_14 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-285680653/5000000000 : ℝ)*x 0 + (75204223/400000000 : ℝ)*x 1 + (4330104159/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (285680653/5000000000 : ℝ)^89 ≤ (3051075287431/100000000000000 : ℝ)^73 := by
    have hnat : (285680653 : ℕ)^89*100000000000000^73 ≤ 3051075287431^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285680653 5000000000 3051075287431 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (75204223/400000000 : ℝ)^89 ≤ (6517317763029/50000000000000 : ℝ)^73 := by
    have hnat : (75204223 : ℕ)^89*50000000000000^73 ≤ 6517317763029^73*400000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75204223 400000000 6517317763029 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4330104159/5000000000 : ℝ)^89 ≤ (839142891717/1000000000000 : ℝ)^73 := by
    have hnat : (4330104159 : ℕ)^89*1000000000000^73 ≤ 839142891717^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4330104159 5000000000 839142891717 1000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-285680653/5000000000 : ℝ), (75204223/400000000 : ℝ), (4330104159/5000000000 : ℝ)] ![(3051075287431/100000000000000 : ℝ), (6517317763029/50000000000000 : ℝ), (839142891717/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-285680653/5000000000 : ℝ)|^89 ≤ (3051075287431/100000000000000 : ℝ)^73
        have hw : |(-285680653/5000000000 : ℝ)|=(285680653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(75204223/400000000 : ℝ)|^89 ≤ (6517317763029/50000000000000 : ℝ)^73
        have hw : |(75204223/400000000 : ℝ)|=(75204223/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4330104159/5000000000 : ℝ)|^89 ≤ (839142891717/1000000000000 : ℝ)^73
        have hw : |(4330104159/5000000000 : ℝ)|=(4330104159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326061_s0_s0_15 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (703933889/10000000000 : ℝ)*x 0 + (-887442253/5000000000 : ℝ)*x 1 + (8660207927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (703933889/10000000000 : ℝ)^89 ≤ (1967460963509/50000000000000 : ℝ)^73 := by
    have hnat : (703933889 : ℕ)^89*50000000000000^73 ≤ 1967460963509^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      703933889 10000000000 1967460963509 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (887442253/5000000000 : ℝ)^89 ≤ (12150793502733/100000000000000 : ℝ)^73 := by
    have hnat : (887442253 : ℕ)^89*100000000000000^73 ≤ 12150793502733^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      887442253 5000000000 12150793502733 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8660207927/10000000000 : ℝ)^89 ≤ (83914284552663/100000000000000 : ℝ)^73 := by
    have hnat : (8660207927 : ℕ)^89*100000000000000^73 ≤ 83914284552663^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8660207927 10000000000 83914284552663 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(703933889/10000000000 : ℝ), (-887442253/5000000000 : ℝ), (8660207927/10000000000 : ℝ)] ![(1967460963509/50000000000000 : ℝ), (12150793502733/100000000000000 : ℝ), (83914284552663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(703933889/10000000000 : ℝ)|^89 ≤ (1967460963509/50000000000000 : ℝ)^73
        have hw : |(703933889/10000000000 : ℝ)|=(703933889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-887442253/5000000000 : ℝ)|^89 ≤ (12150793502733/100000000000000 : ℝ)^73
        have hw : |(-887442253/5000000000 : ℝ)|=(887442253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8660207927/10000000000 : ℝ)|^89 ≤ (83914284552663/100000000000000 : ℝ)^73
        have hw : |(8660207927/10000000000 : ℝ)|=(8660207927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326061_s0_s0_16 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1482844317/2000000000 : ℝ)*x 0 + (755967287/2000000000 : ℝ)*x 1 + (-671083/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1482844317/2000000000 : ℝ)^89 ≤ (13887266699181/20000000000000 : ℝ)^73 := by
    have hnat : (1482844317 : ℕ)^89*20000000000000^73 ≤ 13887266699181^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1482844317 2000000000 13887266699181 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (755967287/2000000000 : ℝ)^89 ≤ (30539670779001/100000000000000 : ℝ)^73 := by
    have hnat : (755967287 : ℕ)^89*100000000000000^73 ≤ 30539670779001^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      755967287 2000000000 30539670779001 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (671083/625000000 : ℝ)^89 ≤ (11997858951/50000000000000 : ℝ)^73 := by
    have hnat : (671083 : ℕ)^89*50000000000000^73 ≤ 11997858951^73*625000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671083 625000000 11997858951 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1482844317/2000000000 : ℝ), (755967287/2000000000 : ℝ), (-671083/625000000 : ℝ)] ![(13887266699181/20000000000000 : ℝ), (30539670779001/100000000000000 : ℝ), (11997858951/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1482844317/2000000000 : ℝ)|^89 ≤ (13887266699181/20000000000000 : ℝ)^73
        have hw : |(1482844317/2000000000 : ℝ)|=(1482844317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(755967287/2000000000 : ℝ)|^89 ≤ (30539670779001/100000000000000 : ℝ)^73
        have hw : |(755967287/2000000000 : ℝ)|=(755967287/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-671083/625000000 : ℝ)|^89 ≤ (11997858951/50000000000000 : ℝ)^73
        have hw : |(-671083/625000000 : ℝ)|=(671083/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326061_s0_s0_20 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (407426953/500000000 : ℝ)*x 0 + (1941720733/10000000000 : ℝ)*x 1 + (664113383/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (407426953/500000000 : ℝ)^89 ≤ (77909493720841/100000000000000 : ℝ)^73 := by
    have hnat : (407426953 : ℕ)^89*100000000000000^73 ≤ 77909493720841^73*500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407426953 500000000 77909493720841 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1941720733/10000000000 : ℝ)^89 ≤ (13557290710781/100000000000000 : ℝ)^73 := by
    have hnat : (1941720733 : ℕ)^89*100000000000000^73 ≤ 13557290710781^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1941720733 10000000000 13557290710781 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (664113383/5000000000 : ℝ)^89 ≤ (4266607774309/50000000000000 : ℝ)^73 := by
    have hnat : (664113383 : ℕ)^89*50000000000000^73 ≤ 4266607774309^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664113383 5000000000 4266607774309 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(407426953/500000000 : ℝ), (1941720733/10000000000 : ℝ), (664113383/5000000000 : ℝ)] ![(77909493720841/100000000000000 : ℝ), (13557290710781/100000000000000 : ℝ), (4266607774309/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(407426953/500000000 : ℝ)|^89 ≤ (77909493720841/100000000000000 : ℝ)^73
        have hw : |(407426953/500000000 : ℝ)|=(407426953/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1941720733/10000000000 : ℝ)|^89 ≤ (13557290710781/100000000000000 : ℝ)^73
        have hw : |(1941720733/10000000000 : ℝ)|=(1941720733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(664113383/5000000000 : ℝ)|^89 ≤ (4266607774309/50000000000000 : ℝ)^73
        have hw : |(664113383/5000000000 : ℝ)|=(664113383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326061_s0_s0_21 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-206981927/10000000000 : ℝ)*x 0 + (1649630733/2500000000 : ℝ)*x 1 + (2303692331/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (206981927/10000000000 : ℝ)^89 ≤ (442376174889/50000000000000 : ℝ)^73 := by
    have hnat : (206981927 : ℕ)^89*50000000000000^73 ≤ 442376174889^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206981927 10000000000 442376174889 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1649630733/2500000000 : ℝ)^89 ≤ (60238397639233/100000000000000 : ℝ)^73 := by
    have hnat : (1649630733 : ℕ)^89*100000000000000^73 ≤ 60238397639233^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1649630733 2500000000 60238397639233 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2303692331/5000000000 : ℝ)^89 ≤ (19438424996509/50000000000000 : ℝ)^73 := by
    have hnat : (2303692331 : ℕ)^89*50000000000000^73 ≤ 19438424996509^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2303692331 5000000000 19438424996509 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-206981927/10000000000 : ℝ), (1649630733/2500000000 : ℝ), (2303692331/5000000000 : ℝ)] ![(442376174889/50000000000000 : ℝ), (60238397639233/100000000000000 : ℝ), (19438424996509/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-206981927/10000000000 : ℝ)|^89 ≤ (442376174889/50000000000000 : ℝ)^73
        have hw : |(-206981927/10000000000 : ℝ)|=(206981927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1649630733/2500000000 : ℝ)|^89 ≤ (60238397639233/100000000000000 : ℝ)^73
        have hw : |(1649630733/2500000000 : ℝ)|=(1649630733/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2303692331/5000000000 : ℝ)|^89 ≤ (19438424996509/50000000000000 : ℝ)^73
        have hw : |(2303692331/5000000000 : ℝ)|=(2303692331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326061_s0_s0_22 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3744061791/5000000000 : ℝ)*x 0 + (-129416467/5000000000 : ℝ)*x 1 + (3577353211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3744061791/5000000000 : ℝ)^89 ≤ (70281062592949/100000000000000 : ℝ)^73 := by
    have hnat : (3744061791 : ℕ)^89*100000000000000^73 ≤ 70281062592949^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3744061791 5000000000 70281062592949 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129416467/5000000000 : ℝ)^89 ≤ (1161952034167/100000000000000 : ℝ)^73 := by
    have hnat : (129416467 : ℕ)^89*100000000000000^73 ≤ 1161952034167^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129416467 5000000000 1161952034167 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3577353211/10000000000 : ℝ)^89 ≤ (5711397071881/20000000000000 : ℝ)^73 := by
    have hnat : (3577353211 : ℕ)^89*20000000000000^73 ≤ 5711397071881^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3577353211 10000000000 5711397071881 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3744061791/5000000000 : ℝ), (-129416467/5000000000 : ℝ), (3577353211/10000000000 : ℝ)] ![(70281062592949/100000000000000 : ℝ), (1161952034167/100000000000000 : ℝ), (5711397071881/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3744061791/5000000000 : ℝ)|^89 ≤ (70281062592949/100000000000000 : ℝ)^73
        have hw : |(3744061791/5000000000 : ℝ)|=(3744061791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-129416467/5000000000 : ℝ)|^89 ≤ (1161952034167/100000000000000 : ℝ)^73
        have hw : |(-129416467/5000000000 : ℝ)|=(129416467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3577353211/10000000000 : ℝ)|^89 ≤ (5711397071881/20000000000000 : ℝ)^73
        have hw : |(3577353211/10000000000 : ℝ)|=(3577353211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326061_s0_s0_23 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (223244227/2500000000 : ℝ)*x 0 + (4715161149/5000000000 : ℝ)*x 1 + (-171907831/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (223244227/2500000000 : ℝ)^89 ≤ (5258809050679/100000000000000 : ℝ)^73 := by
    have hnat : (223244227 : ℕ)^89*100000000000000^73 ≤ 5258809050679^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223244227 2500000000 5258809050679 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4715161149/5000000000 : ℝ)^89 ≤ (744789075337/800000000000 : ℝ)^73 := by
    have hnat : (4715161149 : ℕ)^89*800000000000^73 ≤ 744789075337^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4715161149 5000000000 744789075337 800000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (171907831/5000000000 : ℝ)^89 ≤ (410639128473/25000000000000 : ℝ)^73 := by
    have hnat : (171907831 : ℕ)^89*25000000000000^73 ≤ 410639128473^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171907831 5000000000 410639128473 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(223244227/2500000000 : ℝ), (4715161149/5000000000 : ℝ), (-171907831/5000000000 : ℝ)] ![(5258809050679/100000000000000 : ℝ), (744789075337/800000000000 : ℝ), (410639128473/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(223244227/2500000000 : ℝ)|^89 ≤ (5258809050679/100000000000000 : ℝ)^73
        have hw : |(223244227/2500000000 : ℝ)|=(223244227/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4715161149/5000000000 : ℝ)|^89 ≤ (744789075337/800000000000 : ℝ)^73
        have hw : |(4715161149/5000000000 : ℝ)|=(4715161149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-171907831/5000000000 : ℝ)|^89 ≤ (410639128473/25000000000000 : ℝ)^73
        have hw : |(-171907831/5000000000 : ℝ)|=(171907831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326061_s0_s0_27 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (861052607/1000000000 : ℝ)*x 0 + (1422841023/10000000000 : ℝ)*x 1 + (295178143/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (861052607/1000000000 : ℝ)^89 ≤ (83327742692289/100000000000000 : ℝ)^73 := by
    have hnat : (861052607 : ℕ)^89*100000000000000^73 ≤ 83327742692289^73*1000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861052607 1000000000 83327742692289 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1422841023/10000000000 : ℝ)^89 ≤ (9279975234453/100000000000000 : ℝ)^73 := by
    have hnat : (1422841023 : ℕ)^89*100000000000000^73 ≤ 9279975234453^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1422841023 10000000000 9279975234453 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (295178143/2500000000 : ℝ)^89 ≤ (7392282069383/100000000000000 : ℝ)^73 := by
    have hnat : (295178143 : ℕ)^89*100000000000000^73 ≤ 7392282069383^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      295178143 2500000000 7392282069383 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(861052607/1000000000 : ℝ), (1422841023/10000000000 : ℝ), (295178143/2500000000 : ℝ)] ![(83327742692289/100000000000000 : ℝ), (9279975234453/100000000000000 : ℝ), (7392282069383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(861052607/1000000000 : ℝ)|^89 ≤ (83327742692289/100000000000000 : ℝ)^73
        have hw : |(861052607/1000000000 : ℝ)|=(861052607/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1422841023/10000000000 : ℝ)|^89 ≤ (9279975234453/100000000000000 : ℝ)^73
        have hw : |(1422841023/10000000000 : ℝ)|=(1422841023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(295178143/2500000000 : ℝ)|^89 ≤ (7392282069383/100000000000000 : ℝ)^73
        have hw : |(295178143/2500000000 : ℝ)|=(295178143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c326061_s0 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]]) : (0 : ℝ) ≤ ((8289/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8289/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(65707/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(65707/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7599/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(7599/12500 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (10213/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (10213/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (10213/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (10213/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (10213/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (10213/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (163929/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
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
  have s0_pow0 : (1 : ℝ) ^ (87/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^87 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^87*1^16 ≤ 1^16*1^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (227191371846757/200000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (227191371846757/200000000000000 : ℝ)^87 := by
      have hnat : (2 : ℕ)^16*200000000000000^87 ≤ 227191371846757^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 227191371846757 200000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (227191371846757/200000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12239014171413253/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12239014171413253/10000000000000000 : ℝ)^87 := by
      have hnat : (3 : ℕ)^16*10000000000000000^87 ≤ 12239014171413253^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12239014171413253 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12239014171413253/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (27191371846757/200000000000000 : ℝ)) (beta := (879445579075403/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (87/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^87 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^87*1^16 ≤ 1^16*1^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (227191371846757/200000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (227191371846757/200000000000000 : ℝ)^87 := by
      have hnat : (2 : ℕ)^16*200000000000000^87 ≤ 227191371846757^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 227191371846757 200000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (227191371846757/200000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12239014171413253/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12239014171413253/10000000000000000 : ℝ)^87 := by
      have hnat : (3 : ℕ)^16*10000000000000000^87 ≤ 12239014171413253^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12239014171413253 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12239014171413253/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (27191371846757/200000000000000 : ℝ)) (beta := (879445579075403/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(879445579075403/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (87/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^87 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^87*1^16 ≤ 1^16*1^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (227191371846757/200000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (227191371846757/200000000000000 : ℝ)^87 := by
      have hnat : (2 : ℕ)^16*200000000000000^87 ≤ 227191371846757^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 227191371846757 200000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (227191371846757/200000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12239014171413253/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12239014171413253/10000000000000000 : ℝ)^87 := by
      have hnat : (3 : ℕ)^16*10000000000000000^87 ≤ 12239014171413253^87*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12239014171413253 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12239014171413253/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(879445579075403/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (27191371846757/200000000000000 : ℝ)) (beta := (879445579075403/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(27191371846757/200000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(879445579075403/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-129860827/1250000000 : ℝ)*X 0 0+(578545629/1250000000 : ℝ)*X 0 1+(6085924209/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326061_s0_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((2342329153/5000000000 : ℝ)*X 1 0+(-208153123/2000000000 : ℝ)*X 1 1+(3015754971/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326061_s0_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((341216289/500000000 : ℝ)*X 0 0+(1171021171/5000000000 : ℝ)*X 0 1+(53861391/200000000 : ℝ)*X 0 2+(341216289/500000000 : ℝ)*X 1 0+(1171021171/5000000000 : ℝ)*X 1 1+(53861391/200000000 : ℝ)*X 1 2+(341216289/500000000 : ℝ)*X 2 0+(1171021171/5000000000 : ℝ)*X 2 1+(53861391/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326061_s0_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-227096743/1250000000 : ℝ)*X 0 0+(17584647/156250000 : ℝ)*X 0 1+(4186178301/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326061_s0_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((264459781/1250000000 : ℝ)*X 1 0+(-387276177/5000000000 : ℝ)*X 1 1+(261636321/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326061_s0_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((50596643/250000000 : ℝ)*X 2 0+(1101787879/1250000000 : ℝ)*X 2 1+(-1424757/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326061_s0_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((1933244579/5000000000 : ℝ)*X 0 0+(6497571791/10000000000 : ℝ)*X 0 1+(90558731/625000000 : ℝ)*X 0 2+(1933244579/5000000000 : ℝ)*X 1 0+(6497571791/10000000000 : ℝ)*X 1 1+(90558731/625000000 : ℝ)*X 1 2+(1933244579/5000000000 : ℝ)*X 2 0+(6497571791/10000000000 : ℝ)*X 2 1+(90558731/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326061_s0_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-285680653/5000000000 : ℝ)*X 0 0+(75204223/400000000 : ℝ)*X 0 1+(4330104159/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326061_s0_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((703933889/10000000000 : ℝ)*X 1 0+(-887442253/5000000000 : ℝ)*X 1 1+(8660207927/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326061_s0_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((1482844317/2000000000 : ℝ)*X 2 0+(755967287/2000000000 : ℝ)*X 2 1+(-671083/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326061_s0_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((407426953/500000000 : ℝ)*X 0 0+(1941720733/10000000000 : ℝ)*X 0 1+(664113383/5000000000 : ℝ)*X 0 2+(407426953/500000000 : ℝ)*X 1 0+(1941720733/10000000000 : ℝ)*X 1 1+(664113383/5000000000 : ℝ)*X 1 2+(407426953/500000000 : ℝ)*X 2 0+(1941720733/10000000000 : ℝ)*X 2 1+(664113383/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326061_s0_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-206981927/10000000000 : ℝ)*X 0 0+(1649630733/2500000000 : ℝ)*X 0 1+(2303692331/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326061_s0_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((3744061791/5000000000 : ℝ)*X 1 0+(-129416467/5000000000 : ℝ)*X 1 1+(3577353211/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326061_s0_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((223244227/2500000000 : ℝ)*X 2 0+(4715161149/5000000000 : ℝ)*X 2 1+(-171907831/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326061_s0_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((861052607/1000000000 : ℝ)*X 0 0+(1422841023/10000000000 : ℝ)*X 0 1+(295178143/2500000000 : ℝ)*X 0 2+(861052607/1000000000 : ℝ)*X 1 0+(1422841023/10000000000 : ℝ)*X 1 1+(295178143/2500000000 : ℝ)*X 1 2+(861052607/1000000000 : ℝ)*X 2 0+(1422841023/10000000000 : ℝ)*X 2 1+(295178143/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326061_s0_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((8289/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8289/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (817402783979003843223/50000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12030779/160000000 : ℝ)*(base5) + (1186467498733/1000000000000 : ℝ)*(base7) + (282361/200000000000 : ℝ)*(base50) + (15218443903/10000000000 : ℝ)*(major_s0_0) + (15218443903/10000000000 : ℝ)*(major_s0_1) + (15218443903/10000000000 : ℝ)*(major_s0_2) + (705907/62500000000 : ℝ)*(sp_s0_0) + (9043403/1000000000000 : ℝ)*(sp_s0_1) + (828755360433/500000000000 : ℝ)*(sp_s0_7) + (828756373/500000000 : ℝ)*(sp_s0_8) + (86637198839/50000000000 : ℝ)*(sp_s0_9) + (369817083573/200000000000 : ℝ)*(sp_s0_13) + (7398163/250000000000 : ℝ)*(sp_s0_14) + (29818627/1000000000000 : ℝ)*(sp_s0_15) + (368905143941/500000000000 : ℝ)*(f.failure) + (165755160803/100000000000 : ℝ)*(f.sum) + (242114753629/1000000000000000000000000 : ℝ)*base62 + (27323370887909/100000000000000000000000000 : ℝ)*base64 + (25549304542091/100000000000000000000000000 : ℝ)*base66 + (698727305629/2000000000000000000000000 : ℝ)*base68 + (4424125069359/100000000000000000000000000 : ℝ)*base70 + (38495336332091/100000000000000000000000000 : ℝ)*base72 + (1003080881429/2000000000000000000000000 : ℝ)*base74 + (667691662429/2000000000000000000000000 : ℝ)*base76 + (4266529717909/50000000000000000000000000 : ℝ)*base79 + (1927/10000000000000000 : ℝ)*base86 + (1927/10000000000000000 : ℝ)*base88 + (1927/10000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(65707/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(65707/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (19650559374337973503191/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18151633861/15625000000 : ℝ)*(base7) + (478941/250000000000 : ℝ)*(base53) + (257704519/7812500000 : ℝ)*(base60) + (274010729593/200000000000 : ℝ)*(major_s0_0) + (274010729593/200000000000 : ℝ)*(major_s0_1) + (685025866101/500000000000 : ℝ)*(major_s0_2) + (9504473/1000000000000 : ℝ)*(sp_s0_6) + (920003/62500000000 : ℝ)*(sp_s0_7) + (6381413/500000000000 : ℝ)*(sp_s0_8) + (1441077684977/1000000000000 : ℝ)*(sp_s0_14) + (1441079642199/1000000000000 : ℝ)*(sp_s0_15) + (1441094320789/1000000000000 : ℝ)*(sp_s0_16) + (1825872649703/1000000000000 : ℝ)*(sp_s0_20) + (42541387/1000000000000 : ℝ)*(sp_s0_27) + (664220128459/1000000000000 : ℝ)*(f.failure) + (1441094320789/1000000000000 : ℝ)*(f.sum) + (118718507651581/200000000000000000000000000 : ℝ)*base62 + (3014397523113703/5000000000000000000000000000 : ℝ)*base64 + (1148258271700979/2000000000000000000000000000 : ℝ)*base67 + (78451856605543/100000000000000000000000000 : ℝ)*base68 + (1337337836063039/2500000000000000000000000000 : ℝ)*base70 + (1160974959100979/2000000000000000000000000000 : ℝ)*base73 + (24545050120099/40000000000000000000000000 : ℝ)*base74 + (13974055744099/40000000000000000000000000 : ℝ)*base76 + (100864931499021/1000000000000000000000000000 : ℝ)*base78 + (19127/20000000000000000 : ℝ)*base87 + (19127/20000000000000000 : ℝ)*base89 + (873/20000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7599/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(7599/12500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (72559032577486327406583/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (484785025611/500000000000 : ℝ)*(base7) + (3939107/250000000000 : ℝ)*(base27) + (127021977761/1000000000000 : ℝ)*(base40) + (6399109/200000000000 : ℝ)*(base43) + (29153766667/1000000000000 : ℝ)*(base49) + (168798190613/125000000000 : ℝ)*(major_s0_0) + (1350353529359/1000000000000 : ℝ)*(major_s0_1) + (168798190613/125000000000 : ℝ)*(major_s0_2) + (41505441/1000000000000 : ℝ)*(sp_s0_0) + (61340061/1000000000000 : ℝ)*(sp_s0_9) + (303241157237/200000000000 : ℝ)*(sp_s0_21) + (1516279287171/1000000000000 : ℝ)*(sp_s0_22) + (758092975783/500000000000 : ℝ)*(sp_s0_23) + (406059764267/250000000000 : ℝ)*(sp_s0_27) + (327342381137/500000000000 : ℝ)*(f.failure) + (1516279287171/1000000000000 : ℝ)*(f.sum) + (4775811395091/200000000000000000000000000 : ℝ)*base63 + (749718344207961/1250000000000000000000000000 : ℝ)*base65 + (7419286500256677/10000000000000000000000000000 : ℝ)*base67 + (18982588687041/25000000000000000000000000 : ℝ)*base69 + (48795655439989/1250000000000000000000000000 : ℝ)*base70 + (832413021667039/1250000000000000000000000000 : ℝ)*base73 + (73328456278763/200000000000000000000000000 : ℝ)*base75 + (2254298567959/25000000000000000000000000 : ℝ)*base76 + (1712738158592989/10000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (4661/10000000000000000 : ℝ)*base87 + (4661/10000000000000000 : ℝ)*base89 + (4661/10000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]]) : (0 : ℝ) ≤ ((8289/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8289/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(65707/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(65707/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7599/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(7599/12500 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c326061_s0 p hpa hpb X hX

#print axioms solution
