-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c316061_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:07:52.76126+00:00
-- url     : https://prove2.me/submissions/600781dd-de7e-4b97-98ef-7497a029593f

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
theorem collision_support_c316061_s1_s1_0 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-318249213/2000000000 : ℝ)*x 0 + (1138638043/2500000000 : ℝ)*x 1 + (6058117997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (318249213/2000000000 : ℝ)^77 ≤ (9825552342673/100000000000000 : ℝ)^61 := by
    have hnat : (318249213 : ℕ)^77*100000000000000^61 ≤ 9825552342673^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      318249213 2000000000 9825552342673 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1138638043/2500000000 : ℝ)^77 ≤ (9263981345927/25000000000000 : ℝ)^61 := by
    have hnat : (1138638043 : ℕ)^77*25000000000000^61 ≤ 9263981345927^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1138638043 2500000000 9263981345927 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6058117997/10000000000 : ℝ)^77 ≤ (1062370445179/2000000000000 : ℝ)^61 := by
    have hnat : (6058117997 : ℕ)^77*2000000000000^61 ≤ 1062370445179^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6058117997 10000000000 1062370445179 2000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-318249213/2000000000 : ℝ), (1138638043/2500000000 : ℝ), (6058117997/10000000000 : ℝ)] ![(9825552342673/100000000000000 : ℝ), (9263981345927/25000000000000 : ℝ), (1062370445179/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-318249213/2000000000 : ℝ)|^77 ≤ (9825552342673/100000000000000 : ℝ)^61
        have hw : |(-318249213/2000000000 : ℝ)|=(318249213/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1138638043/2500000000 : ℝ)|^77 ≤ (9263981345927/25000000000000 : ℝ)^61
        have hw : |(1138638043/2500000000 : ℝ)|=(1138638043/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6058117997/10000000000 : ℝ)|^77 ≤ (1062370445179/2000000000000 : ℝ)^61
        have hw : |(6058117997/10000000000 : ℝ)|=(6058117997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316061_s1_s1_1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4717453989/10000000000 : ℝ)*x 0 + (-785156017/5000000000 : ℝ)*x 1 + (1184112487/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4717453989/10000000000 : ℝ)^77 ≤ (2421044754553/6250000000000 : ℝ)^61 := by
    have hnat : (4717453989 : ℕ)^77*6250000000000^61 ≤ 2421044754553^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4717453989 10000000000 2421044754553 6250000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (785156017/5000000000 : ℝ)^77 ≤ (9662667382009/100000000000000 : ℝ)^61 := by
    have hnat : (785156017 : ℕ)^77*100000000000000^61 ≤ 9662667382009^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      785156017 5000000000 9662667382009 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1184112487/2000000000 : ℝ)^77 ≤ (3225038532939/6250000000000 : ℝ)^61 := by
    have hnat : (1184112487 : ℕ)^77*6250000000000^61 ≤ 3225038532939^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1184112487 2000000000 3225038532939 6250000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4717453989/10000000000 : ℝ), (-785156017/5000000000 : ℝ), (1184112487/2000000000 : ℝ)] ![(2421044754553/6250000000000 : ℝ), (9662667382009/100000000000000 : ℝ), (3225038532939/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4717453989/10000000000 : ℝ)|^77 ≤ (2421044754553/6250000000000 : ℝ)^61
        have hw : |(4717453989/10000000000 : ℝ)|=(4717453989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-785156017/5000000000 : ℝ)|^77 ≤ (9662667382009/100000000000000 : ℝ)^61
        have hw : |(-785156017/5000000000 : ℝ)|=(785156017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1184112487/2000000000 : ℝ)|^77 ≤ (3225038532939/6250000000000 : ℝ)^61
        have hw : |(1184112487/2000000000 : ℝ)|=(1184112487/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316061_s1_s1_6 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (66085301/100000000 : ℝ)*x 0 + (322111327/1250000000 : ℝ)*x 1 + (3085067927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66085301/100000000 : ℝ)^77 ≤ (59281511074501/100000000000000 : ℝ)^61 := by
    have hnat : (66085301 : ℕ)^77*100000000000000^61 ≤ 59281511074501^61*100000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66085301 100000000 59281511074501 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (322111327/1250000000 : ℝ)^77 ≤ (9028162369579/50000000000000 : ℝ)^61 := by
    have hnat : (322111327 : ℕ)^77*50000000000000^61 ≤ 9028162369579^61*1250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      322111327 1250000000 9028162369579 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3085067927/10000000000 : ℝ)^77 ≤ (2266216417557/10000000000000 : ℝ)^61 := by
    have hnat : (3085067927 : ℕ)^77*10000000000000^61 ≤ 2266216417557^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3085067927 10000000000 2266216417557 10000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66085301/100000000 : ℝ), (322111327/1250000000 : ℝ), (3085067927/10000000000 : ℝ)] ![(59281511074501/100000000000000 : ℝ), (9028162369579/50000000000000 : ℝ), (2266216417557/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66085301/100000000 : ℝ)|^77 ≤ (59281511074501/100000000000000 : ℝ)^61
        have hw : |(66085301/100000000 : ℝ)|=(66085301/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(322111327/1250000000 : ℝ)|^77 ≤ (9028162369579/50000000000000 : ℝ)^61
        have hw : |(322111327/1250000000 : ℝ)|=(322111327/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3085067927/10000000000 : ℝ)|^77 ≤ (2266216417557/10000000000000 : ℝ)^61
        have hw : |(3085067927/10000000000 : ℝ)|=(3085067927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316061_s1_s1_7 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-460586193/2500000000 : ℝ)*x 0 + (1618413503/5000000000 : ℝ)*x 1 + (7030579127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (460586193/2500000000 : ℝ)^77 ≤ (11821737398677/100000000000000 : ℝ)^61 := by
    have hnat : (460586193 : ℕ)^77*100000000000000^61 ≤ 11821737398677^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      460586193 2500000000 11821737398677 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1618413503/5000000000 : ℝ)^77 ≤ (24078323226329/100000000000000 : ℝ)^61 := by
    have hnat : (1618413503 : ℕ)^77*100000000000000^61 ≤ 24078323226329^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1618413503 5000000000 24078323226329 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7030579127/10000000000 : ℝ)^77 ≤ (32049969675509/50000000000000 : ℝ)^61 := by
    have hnat : (7030579127 : ℕ)^77*50000000000000^61 ≤ 32049969675509^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7030579127 10000000000 32049969675509 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-460586193/2500000000 : ℝ), (1618413503/5000000000 : ℝ), (7030579127/10000000000 : ℝ)] ![(11821737398677/100000000000000 : ℝ), (24078323226329/100000000000000 : ℝ), (32049969675509/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-460586193/2500000000 : ℝ)|^77 ≤ (11821737398677/100000000000000 : ℝ)^61
        have hw : |(-460586193/2500000000 : ℝ)|=(460586193/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1618413503/5000000000 : ℝ)|^77 ≤ (24078323226329/100000000000000 : ℝ)^61
        have hw : |(1618413503/5000000000 : ℝ)|=(1618413503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7030579127/10000000000 : ℝ)|^77 ≤ (32049969675509/50000000000000 : ℝ)^61
        have hw : |(7030579127/10000000000 : ℝ)|=(7030579127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316061_s1_s1_8 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1868154491/5000000000 : ℝ)*x 0 + (-1190291719/10000000000 : ℝ)*x 1 + (705048551/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1868154491/5000000000 : ℝ)^77 ≤ (3607502509909/12500000000000 : ℝ)^61 := by
    have hnat : (1868154491 : ℕ)^77*12500000000000^61 ≤ 3607502509909^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1868154491 5000000000 3607502509909 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1190291719/10000000000 : ℝ)^77 ≤ (6810858351371/100000000000000 : ℝ)^61 := by
    have hnat : (1190291719 : ℕ)^77*100000000000000^61 ≤ 6810858351371^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1190291719 10000000000 6810858351371 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (705048551/1000000000 : ℝ)^77 ≤ (64329121553639/100000000000000 : ℝ)^61 := by
    have hnat : (705048551 : ℕ)^77*100000000000000^61 ≤ 64329121553639^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      705048551 1000000000 64329121553639 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1868154491/5000000000 : ℝ), (-1190291719/10000000000 : ℝ), (705048551/1000000000 : ℝ)] ![(3607502509909/12500000000000 : ℝ), (6810858351371/100000000000000 : ℝ), (64329121553639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1868154491/5000000000 : ℝ)|^77 ≤ (3607502509909/12500000000000 : ℝ)^61
        have hw : |(1868154491/5000000000 : ℝ)|=(1868154491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1190291719/10000000000 : ℝ)|^77 ≤ (6810858351371/100000000000000 : ℝ)^61
        have hw : |(-1190291719/10000000000 : ℝ)|=(1190291719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(705048551/1000000000 : ℝ)|^77 ≤ (64329121553639/100000000000000 : ℝ)^61
        have hw : |(705048551/1000000000 : ℝ)|=(705048551/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316061_s1_s1_9 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1908697573/5000000000 : ℝ)*x 0 + (14780741/19531250 : ℝ)*x 1 + (-437669/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1908697573/5000000000 : ℝ)^77 ≤ (14826433463261/50000000000000 : ℝ)^61 := by
    have hnat : (1908697573 : ℕ)^77*50000000000000^61 ≤ 14826433463261^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1908697573 5000000000 14826433463261 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (14780741/19531250 : ℝ)^77 ≤ (70342789900143/100000000000000 : ℝ)^61 := by
    have hnat : (14780741 : ℕ)^77*100000000000000^61 ≤ 70342789900143^61*19531250^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14780741 19531250 70342789900143 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (437669/1250000000 : ℝ)^77 ≤ (4343159839/100000000000000 : ℝ)^61 := by
    have hnat : (437669 : ℕ)^77*100000000000000^61 ≤ 4343159839^61*1250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437669 1250000000 4343159839 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1908697573/5000000000 : ℝ), (14780741/19531250 : ℝ), (-437669/1250000000 : ℝ)] ![(14826433463261/50000000000000 : ℝ), (70342789900143/100000000000000 : ℝ), (4343159839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1908697573/5000000000 : ℝ)|^77 ≤ (14826433463261/50000000000000 : ℝ)^61
        have hw : |(1908697573/5000000000 : ℝ)|=(1908697573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(14780741/19531250 : ℝ)|^77 ≤ (70342789900143/100000000000000 : ℝ)^61
        have hw : |(14780741/19531250 : ℝ)|=(14780741/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-437669/1250000000 : ℝ)|^77 ≤ (4343159839/100000000000000 : ℝ)^61
        have hw : |(-437669/1250000000 : ℝ)|=(437669/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316061_s1_s1_13 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5140056271/10000000000 : ℝ)*x 0 + (5417297963/10000000000 : ℝ)*x 1 + (851567929/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5140056271/10000000000 : ℝ)^77 ≤ (10791856872097/25000000000000 : ℝ)^61 := by
    have hnat : (5140056271 : ℕ)^77*25000000000000^61 ≤ 10791856872097^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5140056271 10000000000 10791856872097 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5417297963/10000000000 : ℝ)^77 ≤ (1441468852963/3125000000000 : ℝ)^61 := by
    have hnat : (5417297963 : ℕ)^77*3125000000000^61 ≤ 1441468852963^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417297963 10000000000 1441468852963 3125000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (851567929/5000000000 : ℝ)^77 ≤ (10705569196949/100000000000000 : ℝ)^61 := by
    have hnat : (851567929 : ℕ)^77*100000000000000^61 ≤ 10705569196949^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      851567929 5000000000 10705569196949 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5140056271/10000000000 : ℝ), (5417297963/10000000000 : ℝ), (851567929/5000000000 : ℝ)] ![(10791856872097/25000000000000 : ℝ), (1441468852963/3125000000000 : ℝ), (10705569196949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5140056271/10000000000 : ℝ)|^77 ≤ (10791856872097/25000000000000 : ℝ)^61
        have hw : |(5140056271/10000000000 : ℝ)|=(5140056271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5417297963/10000000000 : ℝ)|^77 ≤ (1441468852963/3125000000000 : ℝ)^61
        have hw : |(5417297963/10000000000 : ℝ)|=(5417297963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(851567929/5000000000 : ℝ)|^77 ≤ (10705569196949/100000000000000 : ℝ)^61
        have hw : |(851567929/5000000000 : ℝ)|=(851567929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316061_s1_s1_14 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-688929503/10000000000 : ℝ)*x 0 + (456873109/1250000000 : ℝ)*x 1 + (7411559509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (688929503/10000000000 : ℝ)^77 ≤ (426917302043/12500000000000 : ℝ)^61 := by
    have hnat : (688929503 : ℕ)^77*12500000000000^61 ≤ 426917302043^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      688929503 10000000000 426917302043 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (456873109/1250000000 : ℝ)^77 ≤ (5613873442149/20000000000000 : ℝ)^61 := by
    have hnat : (456873109 : ℕ)^77*20000000000000^61 ≤ 5613873442149^61*1250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456873109 1250000000 5613873442149 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7411559509/10000000000 : ℝ)^77 ≤ (34257647176859/50000000000000 : ℝ)^61 := by
    have hnat : (7411559509 : ℕ)^77*50000000000000^61 ≤ 34257647176859^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7411559509 10000000000 34257647176859 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-688929503/10000000000 : ℝ), (456873109/1250000000 : ℝ), (7411559509/10000000000 : ℝ)] ![(426917302043/12500000000000 : ℝ), (5613873442149/20000000000000 : ℝ), (34257647176859/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-688929503/10000000000 : ℝ)|^77 ≤ (426917302043/12500000000000 : ℝ)^61
        have hw : |(-688929503/10000000000 : ℝ)|=(688929503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(456873109/1250000000 : ℝ)|^77 ≤ (5613873442149/20000000000000 : ℝ)^61
        have hw : |(456873109/1250000000 : ℝ)|=(456873109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7411559509/10000000000 : ℝ)|^77 ≤ (34257647176859/50000000000000 : ℝ)^61
        have hw : |(7411559509/10000000000 : ℝ)|=(7411559509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316061_s1_s1_15 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2994659069/10000000000 : ℝ)*x 0 + (-768936133/5000000000 : ℝ)*x 1 + (7432652639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2994659069/10000000000 : ℝ)^77 ≤ (21827092130379/100000000000000 : ℝ)^61 := by
    have hnat : (2994659069 : ℕ)^77*100000000000000^61 ≤ 21827092130379^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2994659069 10000000000 21827092130379 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (768936133/5000000000 : ℝ)^77 ≤ (4705691517509/50000000000000 : ℝ)^61 := by
    have hnat : (768936133 : ℕ)^77*50000000000000^61 ≤ 4705691517509^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      768936133 5000000000 4705691517509 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7432652639/10000000000 : ℝ)^77 ≤ (68761524827739/100000000000000 : ℝ)^61 := by
    have hnat : (7432652639 : ℕ)^77*100000000000000^61 ≤ 68761524827739^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7432652639 10000000000 68761524827739 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2994659069/10000000000 : ℝ), (-768936133/5000000000 : ℝ), (7432652639/10000000000 : ℝ)] ![(21827092130379/100000000000000 : ℝ), (4705691517509/50000000000000 : ℝ), (68761524827739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2994659069/10000000000 : ℝ)|^77 ≤ (21827092130379/100000000000000 : ℝ)^61
        have hw : |(2994659069/10000000000 : ℝ)|=(2994659069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-768936133/5000000000 : ℝ)|^77 ≤ (4705691517509/50000000000000 : ℝ)^61
        have hw : |(-768936133/5000000000 : ℝ)|=(768936133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7432652639/10000000000 : ℝ)|^77 ≤ (68761524827739/100000000000000 : ℝ)^61
        have hw : |(7432652639/10000000000 : ℝ)|=(7432652639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316061_s1_s1_16 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6767739111/10000000000 : ℝ)*x 0 + (4724568317/10000000000 : ℝ)*x 1 + (-20935193/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6767739111/10000000000 : ℝ)^77 ≤ (3054497721971/5000000000000 : ℝ)^61 := by
    have hnat : (6767739111 : ℕ)^77*5000000000000^61 ≤ 3054497721971^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6767739111 10000000000 3054497721971 5000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4724568317/10000000000 : ℝ)^77 ≤ (38810471801323/100000000000000 : ℝ)^61 := by
    have hnat : (4724568317 : ℕ)^77*100000000000000^61 ≤ 38810471801323^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4724568317 10000000000 38810471801323 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20935193/5000000000 : ℝ)^77 ≤ (99573748581/100000000000000 : ℝ)^61 := by
    have hnat : (20935193 : ℕ)^77*100000000000000^61 ≤ 99573748581^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20935193 5000000000 99573748581 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6767739111/10000000000 : ℝ), (4724568317/10000000000 : ℝ), (-20935193/5000000000 : ℝ)] ![(3054497721971/5000000000000 : ℝ), (38810471801323/100000000000000 : ℝ), (99573748581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6767739111/10000000000 : ℝ)|^77 ≤ (3054497721971/5000000000000 : ℝ)^61
        have hw : |(6767739111/10000000000 : ℝ)|=(6767739111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4724568317/10000000000 : ℝ)|^77 ≤ (38810471801323/100000000000000 : ℝ)^61
        have hw : |(4724568317/10000000000 : ℝ)|=(4724568317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-20935193/5000000000 : ℝ)|^77 ≤ (99573748581/100000000000000 : ℝ)^61
        have hw : |(-20935193/5000000000 : ℝ)|=(20935193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316061_s1_s1_20 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1962067461/2500000000 : ℝ)*x 0 + (61932027/250000000 : ℝ)*x 1 + (1506547727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1962067461/2500000000 : ℝ)^77 ≤ (36825075816133/50000000000000 : ℝ)^61 := by
    have hnat : (1962067461 : ℕ)^77*50000000000000^61 ≤ 36825075816133^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1962067461 2500000000 36825075816133 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (61932027/250000000 : ℝ)^77 ≤ (4294948813659/25000000000000 : ℝ)^61 := by
    have hnat : (61932027 : ℕ)^77*25000000000000^61 ≤ 4294948813659^61*250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61932027 250000000 4294948813659 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1506547727/10000000000 : ℝ)^77 ≤ (9170053100049/100000000000000 : ℝ)^61 := by
    have hnat : (1506547727 : ℕ)^77*100000000000000^61 ≤ 9170053100049^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1506547727 10000000000 9170053100049 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1962067461/2500000000 : ℝ), (61932027/250000000 : ℝ), (1506547727/10000000000 : ℝ)] ![(36825075816133/50000000000000 : ℝ), (4294948813659/25000000000000 : ℝ), (9170053100049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1962067461/2500000000 : ℝ)|^77 ≤ (36825075816133/50000000000000 : ℝ)^61
        have hw : |(1962067461/2500000000 : ℝ)|=(1962067461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(61932027/250000000 : ℝ)|^77 ≤ (4294948813659/25000000000000 : ℝ)^61
        have hw : |(61932027/250000000 : ℝ)|=(61932027/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1506547727/10000000000 : ℝ)|^77 ≤ (9170053100049/100000000000000 : ℝ)^61
        have hw : |(1506547727/10000000000 : ℝ)|=(1506547727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316061_s1_s1_21 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-491478581/10000000000 : ℝ)*x 0 + (5957182867/10000000000 : ℝ)*x 1 + (1076741069/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (491478581/10000000000 : ℝ)^77 ≤ (445987495313/20000000000000 : ℝ)^61 := by
    have hnat : (491478581 : ℕ)^77*20000000000000^61 ≤ 445987495313^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491478581 10000000000 445987495313 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5957182867/10000000000 : ℝ)^77 ≤ (2080152934861/4000000000000 : ℝ)^61 := by
    have hnat : (5957182867 : ℕ)^77*4000000000000^61 ≤ 2080152934861^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5957182867 10000000000 2080152934861 4000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1076741069/2000000000 : ℝ)^77 ≤ (45766239133887/100000000000000 : ℝ)^61 := by
    have hnat : (1076741069 : ℕ)^77*100000000000000^61 ≤ 45766239133887^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076741069 2000000000 45766239133887 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-491478581/10000000000 : ℝ), (5957182867/10000000000 : ℝ), (1076741069/2000000000 : ℝ)] ![(445987495313/20000000000000 : ℝ), (2080152934861/4000000000000 : ℝ), (45766239133887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-491478581/10000000000 : ℝ)|^77 ≤ (445987495313/20000000000000 : ℝ)^61
        have hw : |(-491478581/10000000000 : ℝ)|=(491478581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5957182867/10000000000 : ℝ)|^77 ≤ (2080152934861/4000000000000 : ℝ)^61
        have hw : |(5957182867/10000000000 : ℝ)|=(5957182867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1076741069/2000000000 : ℝ)|^77 ≤ (45766239133887/100000000000000 : ℝ)^61
        have hw : |(1076741069/2000000000 : ℝ)|=(1076741069/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316061_s1_s1_22 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1634265331/2500000000 : ℝ)*x 0 + (-43701591/1000000000 : ℝ)*x 1 + (960185423/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1634265331/2500000000 : ℝ)^77 ≤ (58473395313647/100000000000000 : ℝ)^61 := by
    have hnat : (1634265331 : ℕ)^77*100000000000000^61 ≤ 58473395313647^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1634265331 2500000000 58473395313647 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43701591/1000000000 : ℝ)^77 ≤ (384535427773/20000000000000 : ℝ)^61 := by
    have hnat : (43701591 : ℕ)^77*20000000000000^61 ≤ 384535427773^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43701591 1000000000 384535427773 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (960185423/2000000000 : ℝ)^77 ≤ (39603927530523/100000000000000 : ℝ)^61 := by
    have hnat : (960185423 : ℕ)^77*100000000000000^61 ≤ 39603927530523^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      960185423 2000000000 39603927530523 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1634265331/2500000000 : ℝ), (-43701591/1000000000 : ℝ), (960185423/2000000000 : ℝ)] ![(58473395313647/100000000000000 : ℝ), (384535427773/20000000000000 : ℝ), (39603927530523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1634265331/2500000000 : ℝ)|^77 ≤ (58473395313647/100000000000000 : ℝ)^61
        have hw : |(1634265331/2500000000 : ℝ)|=(1634265331/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-43701591/1000000000 : ℝ)|^77 ≤ (384535427773/20000000000000 : ℝ)^61
        have hw : |(-43701591/1000000000 : ℝ)|=(43701591/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(960185423/2000000000 : ℝ)|^77 ≤ (39603927530523/100000000000000 : ℝ)^61
        have hw : |(960185423/2000000000 : ℝ)|=(960185423/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316061_s1_s1_23 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (396130741/1250000000 : ℝ)*x 0 + (3952084353/5000000000 : ℝ)*x 1 + (-493837649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (396130741/1250000000 : ℝ)^77 ≤ (23443612919333/100000000000000 : ℝ)^61 := by
    have hnat : (396130741 : ℕ)^77*100000000000000^61 ≤ 23443612919333^61*1250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396130741 1250000000 23443612919333 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3952084353/5000000000 : ℝ)^77 ≤ (74312930036047/100000000000000 : ℝ)^61 := by
    have hnat : (3952084353 : ℕ)^77*100000000000000^61 ≤ 74312930036047^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3952084353 5000000000 74312930036047 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (493837649/10000000000 : ℝ)^77 ≤ (2243457032319/100000000000000 : ℝ)^61 := by
    have hnat : (493837649 : ℕ)^77*100000000000000^61 ≤ 2243457032319^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      493837649 10000000000 2243457032319 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(396130741/1250000000 : ℝ), (3952084353/5000000000 : ℝ), (-493837649/10000000000 : ℝ)] ![(23443612919333/100000000000000 : ℝ), (74312930036047/100000000000000 : ℝ), (2243457032319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(396130741/1250000000 : ℝ)|^77 ≤ (23443612919333/100000000000000 : ℝ)^61
        have hw : |(396130741/1250000000 : ℝ)|=(396130741/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3952084353/5000000000 : ℝ)|^77 ≤ (74312930036047/100000000000000 : ℝ)^61
        have hw : |(3952084353/5000000000 : ℝ)|=(3952084353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-493837649/10000000000 : ℝ)|^77 ≤ (2243457032319/100000000000000 : ℝ)^61
        have hw : |(-493837649/10000000000 : ℝ)|=(493837649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316061_s1_s1_27 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8528215137/10000000000 : ℝ)*x 0 + (307302267/2000000000 : ℝ)*x 1 + (1458824591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8528215137/10000000000 : ℝ)^77 ≤ (5112138331163/6250000000000 : ℝ)^61 := by
    have hnat : (8528215137 : ℕ)^77*6250000000000^61 ≤ 5112138331163^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8528215137 10000000000 5112138331163 6250000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (307302267/2000000000 : ℝ)^77 ≤ (9400871170283/100000000000000 : ℝ)^61 := by
    have hnat : (307302267 : ℕ)^77*100000000000000^61 ≤ 9400871170283^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      307302267 2000000000 9400871170283 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1458824591/10000000000 : ℝ)^77 ≤ (352196620979/4000000000000 : ℝ)^61 := by
    have hnat : (1458824591 : ℕ)^77*4000000000000^61 ≤ 352196620979^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1458824591 10000000000 352196620979 4000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8528215137/10000000000 : ℝ), (307302267/2000000000 : ℝ), (1458824591/10000000000 : ℝ)] ![(5112138331163/6250000000000 : ℝ), (9400871170283/100000000000000 : ℝ), (352196620979/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8528215137/10000000000 : ℝ)|^77 ≤ (5112138331163/6250000000000 : ℝ)^61
        have hw : |(8528215137/10000000000 : ℝ)|=(8528215137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(307302267/2000000000 : ℝ)|^77 ≤ (9400871170283/100000000000000 : ℝ)^61
        have hw : |(307302267/2000000000 : ℝ)|=(307302267/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1458824591/10000000000 : ℝ)|^77 ≤ (352196620979/4000000000000 : ℝ)^61
        have hw : |(1458824591/10000000000 : ℝ)|=(1458824591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c316061_s1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((79543/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(79543/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9781/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9781/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(74683/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(74683/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((11029/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11029/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(58173/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(58173/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13281/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(13281/25000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (1587/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (1587/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1587/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1587/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (173433/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (79543/100000 : ℝ) ^ (19/4 : ℝ) ≤ (3371780861270587229/10000000000000000000 : ℝ) := by
    have hpowers : (79543/100000 : ℝ)^19 ≤ (3371780861270587229/10000000000000000000 : ℝ)^4 := by
      have hnat : (79543 : ℕ)^19*10000000000000000000^4 ≤ 3371780861270587229^4*100000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        79543 100000 3371780861270587229 10000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (79543/100000 : ℝ)) (X := (3371780861270587229/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (13371780861270587229/10000000000000000000 : ℝ) ≤ (10630805148012249/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (13371780861270587229/10000000000000000000 : ℝ)^4 ≤ (10630805148012249/10000000000000000 : ℝ)^19 := by
      have hnat : (13371780861270587229 : ℕ)^4*10000000000000000^19 ≤ 10630805148012249^19*10000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13371780861270587229 10000000000000000000 10630805148012249 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10630805148012249/10000000000000000 : ℝ)) (X := (13371780861270587229/10000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (8371780861270587229/5000000000000000000 : ℝ) ≤ (11146175134095943/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (8371780861270587229/5000000000000000000 : ℝ)^4 ≤ (11146175134095943/10000000000000000 : ℝ)^19 := by
      have hnat : (8371780861270587229 : ℕ)^4*10000000000000000^19 ≤ 11146175134095943^19*5000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8371780861270587229 5000000000000000000 11146175134095943 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11146175134095943/10000000000000000 : ℝ)) (X := (8371780861270587229/5000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(630805148012249/7954300000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(257684993041847/3977150000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (79543/100000 : ℝ)) (alpha := (630805148012249/7954300000000000 : ℝ)) (beta := (257684993041847/3977150000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (79543/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(630805148012249/7954300000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(257684993041847/3977150000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (9781/12500 : ℝ) ^ (19/4 : ℝ) ≤ (15594373161730480919/50000000000000000000 : ℝ) := by
    have hpowers : (9781/12500 : ℝ)^19 ≤ (15594373161730480919/50000000000000000000 : ℝ)^4 := by
      have hnat : (9781 : ℕ)^19*50000000000000000000^4 ≤ 15594373161730480919^4*12500^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9781 12500 15594373161730480919 50000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9781/12500 : ℝ)) (X := (15594373161730480919/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (65594373161730480919/50000000000000000000 : ℝ) ≤ (1323519505150597/1250000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (65594373161730480919/50000000000000000000 : ℝ)^4 ≤ (1323519505150597/1250000000000000 : ℝ)^19 := by
      have hnat : (65594373161730480919 : ℕ)^4*1250000000000000^19 ≤ 1323519505150597^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        65594373161730480919 50000000000000000000 1323519505150597 1250000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1323519505150597/1250000000000000 : ℝ)) (X := (65594373161730480919/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (40594373161730480919/25000000000000000000 : ℝ) ≤ (11074426052665609/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (40594373161730480919/25000000000000000000 : ℝ)^4 ≤ (11074426052665609/10000000000000000 : ℝ)^19 := by
      have hnat : (40594373161730480919 : ℕ)^4*10000000000000000^19 ≤ 11074426052665609^19*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        40594373161730480919 25000000000000000000 11074426052665609 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11074426052665609/10000000000000000 : ℝ)) (X := (40594373161730480919/25000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(73519505150597/978100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(486270011460833/7824800000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (9781/12500 : ℝ)) (alpha := (73519505150597/978100000000000 : ℝ)) (beta := (486270011460833/7824800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (9781/12500 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(73519505150597/978100000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(486270011460833/7824800000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (74683/100000 : ℝ) ^ (19/4 : ℝ) ≤ (4998426755979030371/20000000000000000000 : ℝ) := by
    have hpowers : (74683/100000 : ℝ)^19 ≤ (4998426755979030371/20000000000000000000 : ℝ)^4 := by
      have hnat : (74683 : ℕ)^19*20000000000000000000^4 ≤ 4998426755979030371^4*100000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        74683 100000 4998426755979030371 20000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (74683/100000 : ℝ)) (X := (4998426755979030371/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (24998426755979030371/20000000000000000000 : ℝ) ≤ (2620211586810737/2500000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (24998426755979030371/20000000000000000000 : ℝ)^4 ≤ (2620211586810737/2500000000000000 : ℝ)^19 := by
      have hnat : (24998426755979030371 : ℕ)^4*2500000000000000^19 ≤ 2620211586810737^19*20000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24998426755979030371 20000000000000000000 2620211586810737 2500000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2620211586810737/2500000000000000 : ℝ)) (X := (24998426755979030371/20000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (14998426755979030371/10000000000000000000 : ℝ) ≤ (10890861973958539/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (14998426755979030371/10000000000000000000 : ℝ)^4 ≤ (10890861973958539/10000000000000000 : ℝ)^19 := by
      have hnat : (14998426755979030371 : ℕ)^4*10000000000000000^19 ≤ 10890861973958539^19*10000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14998426755979030371 10000000000000000000 10890861973958539 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10890861973958539/10000000000000000 : ℝ)) (X := (14998426755979030371/10000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(120211586810737/1867075000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(410015626715591/7468300000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (74683/100000 : ℝ)) (alpha := (120211586810737/1867075000000000 : ℝ)) (beta := (410015626715591/7468300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (74683/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(120211586810737/1867075000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(410015626715591/7468300000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-318249213/2000000000 : ℝ)*X 0 0+(1138638043/2500000000 : ℝ)*X 0 1+(6058117997/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316061_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4717453989/10000000000 : ℝ)*X 1 0+(-785156017/5000000000 : ℝ)*X 1 1+(1184112487/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316061_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((66085301/100000000 : ℝ)*X 0 0+(322111327/1250000000 : ℝ)*X 0 1+(3085067927/10000000000 : ℝ)*X 0 2+(66085301/100000000 : ℝ)*X 1 0+(322111327/1250000000 : ℝ)*X 1 1+(3085067927/10000000000 : ℝ)*X 1 2+(66085301/100000000 : ℝ)*X 2 0+(322111327/1250000000 : ℝ)*X 2 1+(3085067927/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316061_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-460586193/2500000000 : ℝ)*X 0 0+(1618413503/5000000000 : ℝ)*X 0 1+(7030579127/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316061_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((1868154491/5000000000 : ℝ)*X 1 0+(-1190291719/10000000000 : ℝ)*X 1 1+(705048551/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316061_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((1908697573/5000000000 : ℝ)*X 2 0+(14780741/19531250 : ℝ)*X 2 1+(-437669/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316061_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((5140056271/10000000000 : ℝ)*X 0 0+(5417297963/10000000000 : ℝ)*X 0 1+(851567929/5000000000 : ℝ)*X 0 2+(5140056271/10000000000 : ℝ)*X 1 0+(5417297963/10000000000 : ℝ)*X 1 1+(851567929/5000000000 : ℝ)*X 1 2+(5140056271/10000000000 : ℝ)*X 2 0+(5417297963/10000000000 : ℝ)*X 2 1+(851567929/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316061_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-688929503/10000000000 : ℝ)*X 0 0+(456873109/1250000000 : ℝ)*X 0 1+(7411559509/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316061_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((2994659069/10000000000 : ℝ)*X 1 0+(-768936133/5000000000 : ℝ)*X 1 1+(7432652639/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316061_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((6767739111/10000000000 : ℝ)*X 2 0+(4724568317/10000000000 : ℝ)*X 2 1+(-20935193/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316061_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((1962067461/2500000000 : ℝ)*X 0 0+(61932027/250000000 : ℝ)*X 0 1+(1506547727/10000000000 : ℝ)*X 0 2+(1962067461/2500000000 : ℝ)*X 1 0+(61932027/250000000 : ℝ)*X 1 1+(1506547727/10000000000 : ℝ)*X 1 2+(1962067461/2500000000 : ℝ)*X 2 0+(61932027/250000000 : ℝ)*X 2 1+(1506547727/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316061_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-491478581/10000000000 : ℝ)*X 0 0+(5957182867/10000000000 : ℝ)*X 0 1+(1076741069/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316061_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((1634265331/2500000000 : ℝ)*X 1 0+(-43701591/1000000000 : ℝ)*X 1 1+(960185423/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316061_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((396130741/1250000000 : ℝ)*X 2 0+(3952084353/5000000000 : ℝ)*X 2 1+(-493837649/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316061_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((8528215137/10000000000 : ℝ)*X 0 0+(307302267/2000000000 : ℝ)*X 0 1+(1458824591/10000000000 : ℝ)*X 0 2+(8528215137/10000000000 : ℝ)*X 1 0+(307302267/2000000000 : ℝ)*X 1 1+(1458824591/10000000000 : ℝ)*X 1 2+(8528215137/10000000000 : ℝ)*X 2 0+(307302267/2000000000 : ℝ)*X 2 1+(1458824591/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316061_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((11029/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11029/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4218884886565811592343831023/311204033200000000000000000000000 : ℝ) := by norm_num
    linear_combination (553720483391/1000000000000 : ℝ)*(base7) + (26207/40000000000 : ℝ)*(base40) + (369967/500000000000 : ℝ)*(base50) + (329770668777/1000000000000 : ℝ)*(base59) + (3011215492707/1000000000000 : ℝ)*(major_s1_0) + (3011215492707/1000000000000 : ℝ)*(major_s1_1) + (3011215492707/1000000000000 : ℝ)*(major_s1_2) + (1570789/100000000000 : ℝ)*(sp_s1_0) + (2001735345207/500000000000 : ℝ)*(sp_s1_7) + (800704607753/200000000000 : ℝ)*(sp_s1_8) + (2001765012321/500000000000 : ℝ)*(sp_s1_9) + (1126252788311/500000000000 : ℝ)*(sp_s1_13) + (21813169/500000000000 : ℝ)*(sp_s1_14) + (6985877/1000000000000 : ℝ)*(sp_s1_15) + (169878509323/100000000000 : ℝ)*(f.failure) + (2001765012321/500000000000 : ℝ)*(f.sum) + (11907168183692735573/73047442300000000000000000000000 : ℝ)*base63 + (650132188998217/7468300000000000000000000000 : ℝ)*base64 + (3996199887307549/7824800000000000000000000000 : ℝ)*base66 + (866906166381457/3734150000000000000000000000 : ℝ)*base68 + (9764110733755943067/148512746725000000000000000000000 : ℝ)*base71 + (439510394128453/1988575000000000000000000000 : ℝ)*base72 + (141850253399939/978100000000000000000000000 : ℝ)*base75 + (2054538021601457/7954300000000000000000000000 : ℝ)*base76 + (333837136489769249163/622408066400000000000000000000000 : ℝ)*base78 + (2989/10000000000000000 : ℝ)*base86 + (2989/10000000000000000 : ℝ)*base88 + (2989/10000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(58173/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(58173/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (142598281164813589518368667/18261860575000000000000000000000 : ℝ) := by norm_num
    linear_combination (5417260477/8000000000 : ℝ)*(base7) + (6249263/1000000000000 : ℝ)*(base53) + (1596229/500000000000 : ℝ)*(base59) + (540375567941/250000000000 : ℝ)*(major_s1_0) + (540375567941/250000000000 : ℝ)*(major_s1_1) + (2161496022501/1000000000000 : ℝ)*(major_s1_2) + (3414273/1000000000000 : ℝ)*(sp_s1_6) + (3237157/200000000000 : ℝ)*(sp_s1_7) + (7368359/500000000000 : ℝ)*(sp_s1_8) + (2712090790829/1000000000000 : ℝ)*(sp_s1_14) + (542418447979/200000000000 : ℝ)*(sp_s1_15) + (2712113225877/1000000000000 : ℝ)*(sp_s1_16) + (1896528815999/1000000000000 : ℝ)*(sp_s1_20) + (21243679/500000000000 : ℝ)*(sp_s1_27) + (304854289501/250000000000 : ℝ)*(f.failure) + (2712113225877/1000000000000 : ℝ)*(f.sum) + (6062072964926702349/36523721150000000000000000000000 : ℝ)*base62 + (3555809445520371/7468300000000000000000000000 : ℝ)*base64 + (325085924906493/1956200000000000000000000000 : ℝ)*base67 + (823397124519279/3734150000000000000000000000 : ℝ)*base69 + (73910845008210109273/118810197380000000000000000000000 : ℝ)*base70 + (3556517970284103/3977150000000000000000000000 : ℝ)*base73 + (24336428018791/489050000000000000000000000 : ℝ)*base74 + (322007454035313/3977150000000000000000000000 : ℝ)*base77 + (3823935008652254429/155602016600000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (21243/25000000000000000 : ℝ)*base86 + (21243/25000000000000000 : ℝ)*base88 + (21243/25000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13281/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(13281/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (175472998049227225721434230417/24413498751550000000000000000000000 : ℝ) := by norm_num
    linear_combination (114332374481/250000000000 : ℝ)*(base7) + (4056481/1000000000000 : ℝ)*(base11) + (174752476833/1000000000000 : ℝ)*(base40) + (93962549081/1000000000000 : ℝ)*(base59) + (550720194809/250000000000 : ℝ)*(major_s1_0) + (550720194809/250000000000 : ℝ)*(major_s1_1) + (550720194809/250000000000 : ℝ)*(major_s1_2) + (3170053/1000000000000 : ℝ)*(sp_s1_1) + (72737199/1000000000000 : ℝ)*(sp_s1_9) + (40661/1000000000000 : ℝ)*(sp_s1_20) + (2898607398909/1000000000000 : ℝ)*(sp_s1_21) + (1449304142669/500000000000 : ℝ)*(sp_s1_22) + (181158669887/62500000000 : ℝ)*(sp_s1_23) + (340018081689/200000000000 : ℝ)*(sp_s1_27) + (621380475591/500000000000 : ℝ)*(f.failure) + (289861145539/100000000000 : ℝ)*(f.sum) + (6019789786106767949/18261860575000000000000000000000 : ℝ)*base62 + (522250908360577/933537500000000000000000000 : ℝ)*base64 + (430132613880243/1956200000000000000000000000 : ℝ)*base66 + (1845827017829003/1867075000000000000000000000 : ℝ)*base68 + (14725009425657838089/17472087850000000000000000000000 : ℝ)*base70 + (66846291317589/233950000000000000000000000 : ℝ)*base72 + (402381555446549/489050000000000000000000000 : ℝ)*base74 + (322998610223079/233950000000000000000000000 : ℝ)*base76 + (3596660903890364407/9153059800000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (33887/50000000000000000 : ℝ)*base87 + (33887/50000000000000000 : ℝ)*base89 + (33887/50000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((79543/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(79543/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9781/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9781/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(74683/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(74683/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((11029/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11029/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(58173/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(58173/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13281/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(13281/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c316061_s1 p hpa hpb X hX hprev0

#print axioms solution
