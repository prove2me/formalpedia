-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c302052_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:17:21.566552+00:00
-- url     : https://prove2.me/submissions/3c68a03f-0410-4687-802d-c082d2c28dec

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
theorem collision_support_c302052_s2_s2_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2016357411/10000000000 : ℝ)*x 0 + (3405946483/10000000000 : ℝ)*x 1 + (-707785931/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2016357411/10000000000 : ℝ)^67 ≤ (6100460551819/50000000000000 : ℝ)^51 := by
    have hnat : (2016357411 : ℕ)^67*50000000000000^51 ≤ 6100460551819^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016357411 10000000000 6100460551819 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3405946483/10000000000 : ℝ)^67 ≤ (607335838127/2500000000000 : ℝ)^51 := by
    have hnat : (3405946483 : ℕ)^67*2500000000000^51 ≤ 607335838127^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3405946483 10000000000 607335838127 2500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (707785931/1000000000 : ℝ)^67 ≤ (7938205669663/12500000000000 : ℝ)^51 := by
    have hnat : (707785931 : ℕ)^67*12500000000000^51 ≤ 7938205669663^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      707785931 1000000000 7938205669663 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2016357411/10000000000 : ℝ), (3405946483/10000000000 : ℝ), (-707785931/1000000000 : ℝ)] ![(6100460551819/50000000000000 : ℝ), (607335838127/2500000000000 : ℝ), (7938205669663/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2016357411/10000000000 : ℝ)|^67 ≤ (6100460551819/50000000000000 : ℝ)^51
        have hw : |(-2016357411/10000000000 : ℝ)|=(2016357411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3405946483/10000000000 : ℝ)|^67 ≤ (607335838127/2500000000000 : ℝ)^51
        have hw : |(3405946483/10000000000 : ℝ)|=(3405946483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-707785931/1000000000 : ℝ)|^67 ≤ (7938205669663/12500000000000 : ℝ)^51
        have hw : |(-707785931/1000000000 : ℝ)|=(707785931/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302052_s2_s2_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1252724543/2500000000 : ℝ)*x 0 + (5850759649/10000000000 : ℝ)*x 1 + (352002573/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1252724543/2500000000 : ℝ)^67 ≤ (40343302330169/100000000000000 : ℝ)^51 := by
    have hnat : (1252724543 : ℕ)^67*100000000000000^51 ≤ 40343302330169^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1252724543 2500000000 40343302330169 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5850759649/10000000000 : ℝ)^67 ≤ (24725826257997/50000000000000 : ℝ)^51 := by
    have hnat : (5850759649 : ℕ)^67*50000000000000^51 ≤ 24725826257997^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5850759649 10000000000 24725826257997 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (352002573/2000000000 : ℝ)^67 ≤ (204100902833/2000000000000 : ℝ)^51 := by
    have hnat : (352002573 : ℕ)^67*2000000000000^51 ≤ 204100902833^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352002573 2000000000 204100902833 2000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1252724543/2500000000 : ℝ), (5850759649/10000000000 : ℝ), (352002573/2000000000 : ℝ)] ![(40343302330169/100000000000000 : ℝ), (24725826257997/50000000000000 : ℝ), (204100902833/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1252724543/2500000000 : ℝ)|^67 ≤ (40343302330169/100000000000000 : ℝ)^51
        have hw : |(1252724543/2500000000 : ℝ)|=(1252724543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5850759649/10000000000 : ℝ)|^67 ≤ (24725826257997/50000000000000 : ℝ)^51
        have hw : |(5850759649/10000000000 : ℝ)|=(5850759649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(352002573/2000000000 : ℝ)|^67 ≤ (204100902833/2000000000000 : ℝ)^51
        have hw : |(352002573/2000000000 : ℝ)|=(352002573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302052_s2_s2_6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3142150451/5000000000 : ℝ)*x 0 + (1121303827/2500000000 : ℝ)*x 1 + (-1837893037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3142150451/5000000000 : ℝ)^67 ≤ (54320660381103/100000000000000 : ℝ)^51 := by
    have hnat : (3142150451 : ℕ)^67*100000000000000^51 ≤ 54320660381103^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3142150451 5000000000 54320660381103 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1121303827/2500000000 : ℝ)^67 ≤ (34876977364529/100000000000000 : ℝ)^51 := by
    have hnat : (1121303827 : ℕ)^67*100000000000000^51 ≤ 34876977364529^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121303827 2500000000 34876977364529 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1837893037/10000000000 : ℝ)^67 ≤ (2700590560809/25000000000000 : ℝ)^51 := by
    have hnat : (1837893037 : ℕ)^67*25000000000000^51 ≤ 2700590560809^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1837893037 10000000000 2700590560809 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3142150451/5000000000 : ℝ), (1121303827/2500000000 : ℝ), (-1837893037/10000000000 : ℝ)] ![(54320660381103/100000000000000 : ℝ), (34876977364529/100000000000000 : ℝ), (2700590560809/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3142150451/5000000000 : ℝ)|^67 ≤ (54320660381103/100000000000000 : ℝ)^51
        have hw : |(3142150451/5000000000 : ℝ)|=(3142150451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1121303827/2500000000 : ℝ)|^67 ≤ (34876977364529/100000000000000 : ℝ)^51
        have hw : |(1121303827/2500000000 : ℝ)|=(1121303827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1837893037/10000000000 : ℝ)|^67 ≤ (2700590560809/25000000000000 : ℝ)^51
        have hw : |(-1837893037/10000000000 : ℝ)|=(1837893037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302052_s2_s2_7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-417821927/2500000000 : ℝ)*x 0 + (2620798729/10000000000 : ℝ)*x 1 + (-7890069839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (417821927/2500000000 : ℝ)^67 ≤ (9534602279619/100000000000000 : ℝ)^51 := by
    have hnat : (417821927 : ℕ)^67*100000000000000^51 ≤ 9534602279619^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417821927 2500000000 9534602279619 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620798729/10000000000 : ℝ)^67 ≤ (215224397309/1250000000000 : ℝ)^51 := by
    have hnat : (2620798729 : ℕ)^67*1250000000000^51 ≤ 215224397309^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620798729 10000000000 215224397309 1250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7890069839/10000000000 : ℝ)^67 ≤ (73247445919047/100000000000000 : ℝ)^51 := by
    have hnat : (7890069839 : ℕ)^67*100000000000000^51 ≤ 73247445919047^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7890069839 10000000000 73247445919047 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-417821927/2500000000 : ℝ), (2620798729/10000000000 : ℝ), (-7890069839/10000000000 : ℝ)] ![(9534602279619/100000000000000 : ℝ), (215224397309/1250000000000 : ℝ), (73247445919047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-417821927/2500000000 : ℝ)|^67 ≤ (9534602279619/100000000000000 : ℝ)^51
        have hw : |(-417821927/2500000000 : ℝ)|=(417821927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620798729/10000000000 : ℝ)|^67 ≤ (215224397309/1250000000000 : ℝ)^51
        have hw : |(2620798729/10000000000 : ℝ)|=(2620798729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7890069839/10000000000 : ℝ)|^67 ≤ (73247445919047/100000000000000 : ℝ)^51
        have hw : |(-7890069839/10000000000 : ℝ)|=(7890069839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302052_s2_s2_8 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (808727799/2000000000 : ℝ)*x 0 + (-1132032011/5000000000 : ℝ)*x 1 + (-3187621253/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (808727799/2000000000 : ℝ)^67 ≤ (30437350606043/100000000000000 : ℝ)^51 := by
    have hnat : (808727799 : ℕ)^67*100000000000000^51 ≤ 30437350606043^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      808727799 2000000000 30437350606043 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1132032011/5000000000 : ℝ)^67 ≤ (14206949793513/100000000000000 : ℝ)^51 := by
    have hnat : (1132032011 : ℕ)^67*100000000000000^51 ≤ 14206949793513^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132032011 5000000000 14206949793513 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3187621253/5000000000 : ℝ)^67 ≤ (55355699585171/100000000000000 : ℝ)^51 := by
    have hnat : (3187621253 : ℕ)^67*100000000000000^51 ≤ 55355699585171^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3187621253 5000000000 55355699585171 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(808727799/2000000000 : ℝ), (-1132032011/5000000000 : ℝ), (-3187621253/5000000000 : ℝ)] ![(30437350606043/100000000000000 : ℝ), (14206949793513/100000000000000 : ℝ), (55355699585171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(808727799/2000000000 : ℝ)|^67 ≤ (30437350606043/100000000000000 : ℝ)^51
        have hw : |(808727799/2000000000 : ℝ)|=(808727799/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1132032011/5000000000 : ℝ)|^67 ≤ (14206949793513/100000000000000 : ℝ)^51
        have hw : |(-1132032011/5000000000 : ℝ)|=(1132032011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3187621253/5000000000 : ℝ)|^67 ≤ (55355699585171/100000000000000 : ℝ)^51
        have hw : |(-3187621253/5000000000 : ℝ)|=(3187621253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302052_s2_s2_9 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (277035481/625000000 : ℝ)*x 0 + (3540785039/5000000000 : ℝ)*x 1 + (530305769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (277035481/625000000 : ℝ)^67 ≤ (34340147955899/100000000000000 : ℝ)^51 := by
    have hnat : (277035481 : ℕ)^67*100000000000000^51 ≤ 34340147955899^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277035481 625000000 34340147955899 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3540785039/5000000000 : ℝ)^67 ≤ (15887347239989/25000000000000 : ℝ)^51 := by
    have hnat : (3540785039 : ℕ)^67*25000000000000^51 ≤ 15887347239989^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3540785039 5000000000 15887347239989 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (530305769/10000000000 : ℝ)^67 ≤ (2110463065517/100000000000000 : ℝ)^51 := by
    have hnat : (530305769 : ℕ)^67*100000000000000^51 ≤ 2110463065517^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530305769 10000000000 2110463065517 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(277035481/625000000 : ℝ), (3540785039/5000000000 : ℝ), (530305769/10000000000 : ℝ)] ![(34340147955899/100000000000000 : ℝ), (15887347239989/25000000000000 : ℝ), (2110463065517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(277035481/625000000 : ℝ)|^67 ≤ (34340147955899/100000000000000 : ℝ)^51
        have hw : |(277035481/625000000 : ℝ)|=(277035481/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3540785039/5000000000 : ℝ)|^67 ≤ (15887347239989/25000000000000 : ℝ)^51
        have hw : |(3540785039/5000000000 : ℝ)|=(3540785039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(530305769/10000000000 : ℝ)|^67 ≤ (2110463065517/100000000000000 : ℝ)^51
        have hw : |(530305769/10000000000 : ℝ)|=(530305769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302052_s2_s2_13 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1105083571/2000000000 : ℝ)*x 0 + (6099776623/10000000000 : ℝ)*x 1 + (-244185517/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1105083571/2000000000 : ℝ)^67 ≤ (45871030828381/100000000000000 : ℝ)^51 := by
    have hnat : (1105083571 : ℕ)^67*100000000000000^51 ≤ 45871030828381^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105083571 2000000000 45871030828381 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6099776623/10000000000 : ℝ)^67 ≤ (1044699615121/2000000000000 : ℝ)^51 := by
    have hnat : (6099776623 : ℕ)^67*2000000000000^51 ≤ 1044699615121^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6099776623 10000000000 1044699615121 2000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (244185517/5000000000 : ℝ)^67 ≤ (473497101537/25000000000000 : ℝ)^51 := by
    have hnat : (244185517 : ℕ)^67*25000000000000^51 ≤ 473497101537^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      244185517 5000000000 473497101537 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1105083571/2000000000 : ℝ), (6099776623/10000000000 : ℝ), (-244185517/5000000000 : ℝ)] ![(45871030828381/100000000000000 : ℝ), (1044699615121/2000000000000 : ℝ), (473497101537/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1105083571/2000000000 : ℝ)|^67 ≤ (45871030828381/100000000000000 : ℝ)^51
        have hw : |(1105083571/2000000000 : ℝ)|=(1105083571/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6099776623/10000000000 : ℝ)|^67 ≤ (1044699615121/2000000000000 : ℝ)^51
        have hw : |(6099776623/10000000000 : ℝ)|=(6099776623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-244185517/5000000000 : ℝ)|^67 ≤ (473497101537/25000000000000 : ℝ)^51
        have hw : |(-244185517/5000000000 : ℝ)|=(244185517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302052_s2_s2_14 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-834600239/10000000000 : ℝ)*x 0 + (24920573/78125000 : ℝ)*x 1 + (-248188607/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (834600239/10000000000 : ℝ)^67 ≤ (239330934899/6250000000000 : ℝ)^51 := by
    have hnat : (834600239 : ℕ)^67*6250000000000^51 ≤ 239330934899^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834600239 10000000000 239330934899 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (24920573/78125000 : ℝ)^67 ≤ (1393052170777/6250000000000 : ℝ)^51 := by
    have hnat : (24920573 : ℕ)^67*6250000000000^51 ≤ 1393052170777^51*78125000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24920573 78125000 1393052170777 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (248188607/312500000 : ℝ)^67 ≤ (73881870297841/100000000000000 : ℝ)^51 := by
    have hnat : (248188607 : ℕ)^67*100000000000000^51 ≤ 73881870297841^51*312500000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      248188607 312500000 73881870297841 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-834600239/10000000000 : ℝ), (24920573/78125000 : ℝ), (-248188607/312500000 : ℝ)] ![(239330934899/6250000000000 : ℝ), (1393052170777/6250000000000 : ℝ), (73881870297841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-834600239/10000000000 : ℝ)|^67 ≤ (239330934899/6250000000000 : ℝ)^51
        have hw : |(-834600239/10000000000 : ℝ)|=(834600239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(24920573/78125000 : ℝ)|^67 ≤ (1393052170777/6250000000000 : ℝ)^51
        have hw : |(24920573/78125000 : ℝ)|=(24920573/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-248188607/312500000 : ℝ)|^67 ≤ (73881870297841/100000000000000 : ℝ)^51
        have hw : |(-248188607/312500000 : ℝ)|=(248188607/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302052_s2_s2_15 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3998891801/10000000000 : ℝ)*x 0 + (-1252437063/5000000000 : ℝ)*x 1 + (-3118313231/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3998891801/10000000000 : ℝ)^67 ≤ (2999562918901/10000000000000 : ℝ)^51 := by
    have hnat : (3998891801 : ℕ)^67*10000000000000^51 ≤ 2999562918901^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3998891801 10000000000 2999562918901 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1252437063/5000000000 : ℝ)^67 ≤ (16224440184247/100000000000000 : ℝ)^51 := by
    have hnat : (1252437063 : ℕ)^67*100000000000000^51 ≤ 16224440184247^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1252437063 5000000000 16224440184247 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3118313231/5000000000 : ℝ)^67 ≤ (10755986123393/20000000000000 : ℝ)^51 := by
    have hnat : (3118313231 : ℕ)^67*20000000000000^51 ≤ 10755986123393^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3118313231 5000000000 10755986123393 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3998891801/10000000000 : ℝ), (-1252437063/5000000000 : ℝ), (-3118313231/5000000000 : ℝ)] ![(2999562918901/10000000000000 : ℝ), (16224440184247/100000000000000 : ℝ), (10755986123393/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3998891801/10000000000 : ℝ)|^67 ≤ (2999562918901/10000000000000 : ℝ)^51
        have hw : |(3998891801/10000000000 : ℝ)|=(3998891801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1252437063/5000000000 : ℝ)|^67 ≤ (16224440184247/100000000000000 : ℝ)^51
        have hw : |(-1252437063/5000000000 : ℝ)|=(1252437063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3118313231/5000000000 : ℝ)|^67 ≤ (10755986123393/20000000000000 : ℝ)^51
        have hw : |(-3118313231/5000000000 : ℝ)|=(3118313231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302052_s2_s2_16 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1264703283/2000000000 : ℝ)*x 0 + (5219106947/10000000000 : ℝ)*x 1 + (317479813/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1264703283/2000000000 : ℝ)^67 ≤ (54766414020599/100000000000000 : ℝ)^51 := by
    have hnat : (1264703283 : ℕ)^67*100000000000000^51 ≤ 54766414020599^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1264703283 2000000000 54766414020599 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219106947/10000000000 : ℝ)^67 ≤ (42559735917459/100000000000000 : ℝ)^51 := by
    have hnat : (5219106947 : ℕ)^67*100000000000000^51 ≤ 42559735917459^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219106947 10000000000 42559735917459 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (317479813/5000000000 : ℝ)^67 ≤ (1336925025419/50000000000000 : ℝ)^51 := by
    have hnat : (317479813 : ℕ)^67*50000000000000^51 ≤ 1336925025419^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317479813 5000000000 1336925025419 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1264703283/2000000000 : ℝ), (5219106947/10000000000 : ℝ), (317479813/5000000000 : ℝ)] ![(54766414020599/100000000000000 : ℝ), (42559735917459/100000000000000 : ℝ), (1336925025419/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1264703283/2000000000 : ℝ)|^67 ≤ (54766414020599/100000000000000 : ℝ)^51
        have hw : |(1264703283/2000000000 : ℝ)|=(1264703283/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219106947/10000000000 : ℝ)|^67 ≤ (42559735917459/100000000000000 : ℝ)^51
        have hw : |(5219106947/10000000000 : ℝ)|=(5219106947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(317479813/5000000000 : ℝ)|^67 ≤ (1336925025419/50000000000000 : ℝ)^51
        have hw : |(317479813/5000000000 : ℝ)|=(317479813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302052_s2_s2_20 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3852595191/5000000000 : ℝ)*x 0 + (116272353/312500000 : ℝ)*x 1 + (-90532883/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3852595191/5000000000 : ℝ)^67 ≤ (71000994575821/100000000000000 : ℝ)^51 := by
    have hnat : (3852595191 : ℕ)^67*100000000000000^51 ≤ 71000994575821^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3852595191 5000000000 71000994575821 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (116272353/312500000 : ℝ)^67 ≤ (27284814718497/100000000000000 : ℝ)^51 := by
    have hnat : (116272353 : ℕ)^67*100000000000000^51 ≤ 27284814718497^51*312500000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116272353 312500000 27284814718497 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (90532883/2000000000 : ℝ)^67 ≤ (1714190693551/100000000000000 : ℝ)^51 := by
    have hnat : (90532883 : ℕ)^67*100000000000000^51 ≤ 1714190693551^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90532883 2000000000 1714190693551 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3852595191/5000000000 : ℝ), (116272353/312500000 : ℝ), (-90532883/2000000000 : ℝ)] ![(71000994575821/100000000000000 : ℝ), (27284814718497/100000000000000 : ℝ), (1714190693551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3852595191/5000000000 : ℝ)|^67 ≤ (71000994575821/100000000000000 : ℝ)^51
        have hw : |(3852595191/5000000000 : ℝ)|=(3852595191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(116272353/312500000 : ℝ)|^67 ≤ (27284814718497/100000000000000 : ℝ)^51
        have hw : |(116272353/312500000 : ℝ)|=(116272353/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-90532883/2000000000 : ℝ)|^67 ≤ (1714190693551/100000000000000 : ℝ)^51
        have hw : |(-90532883/2000000000 : ℝ)|=(90532883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302052_s2_s2_21 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-19437413/500000000 : ℝ)*x 0 + (4410280647/10000000000 : ℝ)*x 1 + (-1790156081/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (19437413/500000000 : ℝ)^67 ≤ (280699409839/20000000000000 : ℝ)^51 := by
    have hnat : (19437413 : ℕ)^67*20000000000000^51 ≤ 280699409839^51*500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19437413 500000000 280699409839 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4410280647/10000000000 : ℝ)^67 ≤ (34113495245411/100000000000000 : ℝ)^51 := by
    have hnat : (4410280647 : ℕ)^67*100000000000000^51 ≤ 34113495245411^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4410280647 10000000000 34113495245411 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1790156081/2500000000 : ℝ)^67 ≤ (32241503844671/50000000000000 : ℝ)^51 := by
    have hnat : (1790156081 : ℕ)^67*50000000000000^51 ≤ 32241503844671^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1790156081 2500000000 32241503844671 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-19437413/500000000 : ℝ), (4410280647/10000000000 : ℝ), (-1790156081/2500000000 : ℝ)] ![(280699409839/20000000000000 : ℝ), (34113495245411/100000000000000 : ℝ), (32241503844671/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-19437413/500000000 : ℝ)|^67 ≤ (280699409839/20000000000000 : ℝ)^51
        have hw : |(-19437413/500000000 : ℝ)|=(19437413/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4410280647/10000000000 : ℝ)|^67 ≤ (34113495245411/100000000000000 : ℝ)^51
        have hw : |(4410280647/10000000000 : ℝ)|=(4410280647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1790156081/2500000000 : ℝ)|^67 ≤ (32241503844671/50000000000000 : ℝ)^51
        have hw : |(-1790156081/2500000000 : ℝ)|=(1790156081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302052_s2_s2_22 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6380439169/10000000000 : ℝ)*x 0 + (-602619959/2500000000 : ℝ)*x 1 + (-978426427/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6380439169/10000000000 : ℝ)^67 ≤ (27707492668493/50000000000000 : ℝ)^51 := by
    have hnat : (6380439169 : ℕ)^67*50000000000000^51 ≤ 27707492668493^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6380439169 10000000000 27707492668493 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (602619959/2500000000 : ℝ)^67 ≤ (1542601045809/10000000000000 : ℝ)^51 := by
    have hnat : (602619959 : ℕ)^67*10000000000000^51 ≤ 1542601045809^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      602619959 2500000000 1542601045809 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (978426427/2500000000 : ℝ)^67 ≤ (14579502093181/50000000000000 : ℝ)^51 := by
    have hnat : (978426427 : ℕ)^67*50000000000000^51 ≤ 14579502093181^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      978426427 2500000000 14579502093181 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6380439169/10000000000 : ℝ), (-602619959/2500000000 : ℝ), (-978426427/2500000000 : ℝ)] ![(27707492668493/50000000000000 : ℝ), (1542601045809/10000000000000 : ℝ), (14579502093181/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6380439169/10000000000 : ℝ)|^67 ≤ (27707492668493/50000000000000 : ℝ)^51
        have hw : |(6380439169/10000000000 : ℝ)|=(6380439169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-602619959/2500000000 : ℝ)|^67 ≤ (1542601045809/10000000000000 : ℝ)^51
        have hw : |(-602619959/2500000000 : ℝ)|=(602619959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-978426427/2500000000 : ℝ)|^67 ≤ (14579502093181/50000000000000 : ℝ)^51
        have hw : |(-978426427/2500000000 : ℝ)|=(978426427/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302052_s2_s2_23 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4199281519/10000000000 : ℝ)*x 0 + (1669161287/2500000000 : ℝ)*x 1 + (1625822847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4199281519/10000000000 : ℝ)^67 ≤ (31985664666557/100000000000000 : ℝ)^51 := by
    have hnat : (4199281519 : ℕ)^67*100000000000000^51 ≤ 31985664666557^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4199281519 10000000000 31985664666557 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1669161287/2500000000 : ℝ)^67 ≤ (58819016692341/100000000000000 : ℝ)^51 := by
    have hnat : (1669161287 : ℕ)^67*100000000000000^51 ≤ 58819016692341^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1669161287 2500000000 58819016692341 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1625822847/10000000000 : ℝ)^67 ≤ (9195318617553/100000000000000 : ℝ)^51 := by
    have hnat : (1625822847 : ℕ)^67*100000000000000^51 ≤ 9195318617553^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1625822847 10000000000 9195318617553 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4199281519/10000000000 : ℝ), (1669161287/2500000000 : ℝ), (1625822847/10000000000 : ℝ)] ![(31985664666557/100000000000000 : ℝ), (58819016692341/100000000000000 : ℝ), (9195318617553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4199281519/10000000000 : ℝ)|^67 ≤ (31985664666557/100000000000000 : ℝ)^51
        have hw : |(4199281519/10000000000 : ℝ)|=(4199281519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1669161287/2500000000 : ℝ)|^67 ≤ (58819016692341/100000000000000 : ℝ)^51
        have hw : |(1669161287/2500000000 : ℝ)|=(1669161287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1625822847/10000000000 : ℝ)|^67 ≤ (9195318617553/100000000000000 : ℝ)^51
        have hw : |(1625822847/10000000000 : ℝ)|=(1625822847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302052_s2_s2_27 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4039569329/5000000000 : ℝ)*x 0 + (612649127/2000000000 : ℝ)*x 1 + (-745927727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4039569329/5000000000 : ℝ)^67 ≤ (37780971805509/50000000000000 : ℝ)^51 := by
    have hnat : (4039569329 : ℕ)^67*50000000000000^51 ≤ 37780971805509^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4039569329 5000000000 37780971805509 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (612649127/2000000000 : ℝ)^67 ≤ (21134110021989/100000000000000 : ℝ)^51 := by
    have hnat : (612649127 : ℕ)^67*100000000000000^51 ≤ 21134110021989^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      612649127 2000000000 21134110021989 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (745927727/10000000000 : ℝ)^67 ≤ (1651973173581/50000000000000 : ℝ)^51 := by
    have hnat : (745927727 : ℕ)^67*50000000000000^51 ≤ 1651973173581^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      745927727 10000000000 1651973173581 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4039569329/5000000000 : ℝ), (612649127/2000000000 : ℝ), (-745927727/10000000000 : ℝ)] ![(37780971805509/50000000000000 : ℝ), (21134110021989/100000000000000 : ℝ), (1651973173581/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4039569329/5000000000 : ℝ)|^67 ≤ (37780971805509/50000000000000 : ℝ)^51
        have hw : |(4039569329/5000000000 : ℝ)|=(4039569329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(612649127/2000000000 : ℝ)|^67 ≤ (21134110021989/100000000000000 : ℝ)^51
        have hw : |(612649127/2000000000 : ℝ)|=(612649127/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-745927727/10000000000 : ℝ)|^67 ≤ (1651973173581/50000000000000 : ℝ)^51
        have hw : |(-745927727/10000000000 : ℝ)|=(745927727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c302052_s2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]])
    (hprev1 : (0 : ℝ) ≤ ((75381/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(75381/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(38713/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(38713/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-59581/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-59581/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((54459/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(54459/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29087/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(29087/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-38241/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-38241/100000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
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
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (75381/100000 : ℝ) ^ (65/16 : ℝ) ≤ (6344632068275202619/20000000000000000000 : ℝ) := by
    have hpowers : (75381/100000 : ℝ)^65 ≤ (6344632068275202619/20000000000000000000 : ℝ)^16 := by
      have hnat : (75381 : ℕ)^65*20000000000000000000^16 ≤ 6344632068275202619^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        75381 100000 6344632068275202619 20000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (75381/100000 : ℝ)) (X := (6344632068275202619/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (26344632068275202619/20000000000000000000 : ℝ) ≤ (10701762200501111/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (26344632068275202619/20000000000000000000 : ℝ)^16 ≤ (10701762200501111/10000000000000000 : ℝ)^65 := by
      have hnat : (26344632068275202619 : ℕ)^16*10000000000000000^65 ≤ 10701762200501111^65*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26344632068275202619 20000000000000000000 10701762200501111 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10701762200501111/10000000000000000 : ℝ)) (X := (26344632068275202619/20000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (16344632068275202619/10000000000000000000 : ℝ) ≤ (11285559986410157/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (16344632068275202619/10000000000000000000 : ℝ)^16 ≤ (11285559986410157/10000000000000000 : ℝ)^65 := by
      have hnat : (16344632068275202619 : ℕ)^16*10000000000000000^65 ≤ 11285559986410157^65*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16344632068275202619 10000000000000000000 11285559986410157 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11285559986410157/10000000000000000 : ℝ)) (X := (16344632068275202619/10000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(701762200501111/7538100000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(97299630984841/1256350000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (75381/100000 : ℝ)) (alpha := (701762200501111/7538100000000000 : ℝ)) (beta := (97299630984841/1256350000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (75381/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(701762200501111/7538100000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(97299630984841/1256350000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (38713/50000 : ℝ) ^ (65/16 : ℝ) ≤ (7073473242112999629/20000000000000000000 : ℝ) := by
    have hpowers : (38713/50000 : ℝ)^65 ≤ (7073473242112999629/20000000000000000000 : ℝ)^16 := by
      have hnat : (38713 : ℕ)^65*20000000000000000000^16 ≤ 7073473242112999629^16*50000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        38713 50000 7073473242112999629 20000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (38713/50000 : ℝ)) (X := (7073473242112999629/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (27073473242112999629/20000000000000000000 : ℝ) ≤ (430955733600099/400000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (27073473242112999629/20000000000000000000 : ℝ)^16 ≤ (430955733600099/400000000000000 : ℝ)^65 := by
      have hnat : (27073473242112999629 : ℕ)^16*400000000000000^65 ≤ 430955733600099^65*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27073473242112999629 20000000000000000000 430955733600099 400000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (430955733600099/400000000000000 : ℝ)) (X := (27073473242112999629/20000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (17073473242112999629/10000000000000000000 : ℝ) ≤ (5703703329899403/5000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (17073473242112999629/10000000000000000000 : ℝ)^16 ≤ (5703703329899403/5000000000000000 : ℝ)^65 := by
      have hnat : (17073473242112999629 : ℕ)^16*5000000000000000^65 ≤ 5703703329899403^65*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17073473242112999629 10000000000000000000 5703703329899403 5000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5703703329899403/5000000000000000 : ℝ)) (X := (17073473242112999629/10000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(30955733600099/309704000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(633513319796331/7742600000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (38713/50000 : ℝ)) (alpha := (30955733600099/309704000000000 : ℝ)) (beta := (633513319796331/7742600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (38713/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(30955733600099/309704000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(633513319796331/7742600000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (59581/100000 : ℝ) ^ (65/16 : ℝ) ≤ (6100218533844336551/50000000000000000000 : ℝ) := by
    have hpowers : (59581/100000 : ℝ)^65 ≤ (6100218533844336551/50000000000000000000 : ℝ)^16 := by
      have hnat : (59581 : ℕ)^65*50000000000000000000^16 ≤ 6100218533844336551^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59581 100000 6100218533844336551 50000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (59581/100000 : ℝ)) (X := (6100218533844336551/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (56100218533844336551/50000000000000000000 : ℝ) ≤ (1028741714557397/1000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (56100218533844336551/50000000000000000000 : ℝ)^16 ≤ (1028741714557397/1000000000000000 : ℝ)^65 := by
      have hnat : (56100218533844336551 : ℕ)^16*1000000000000000^65 ≤ 1028741714557397^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56100218533844336551 50000000000000000000 1028741714557397 1000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1028741714557397/1000000000000000 : ℝ)) (X := (56100218533844336551/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (31100218533844336551/25000000000000000000 : ℝ) ≤ (10552154771426423/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (31100218533844336551/25000000000000000000 : ℝ)^16 ≤ (10552154771426423/10000000000000000 : ℝ)^65 := by
      have hnat : (31100218533844336551 : ℕ)^16*10000000000000000^65 ≤ 10552154771426423^65*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31100218533844336551 25000000000000000000 10552154771426423 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10552154771426423/10000000000000000 : ℝ)) (X := (31100218533844336551/25000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(28741714557397/595810000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(264737625852453/5958100000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (59581/100000 : ℝ)) (alpha := (28741714557397/595810000000000 : ℝ)) (beta := (264737625852453/5958100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (59581/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(28741714557397/595810000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(264737625852453/5958100000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-2016357411/10000000000 : ℝ)*X 0 0+(3405946483/10000000000 : ℝ)*X 0 1+(-707785931/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302052_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((1252724543/2500000000 : ℝ)*X 2 0+(5850759649/10000000000 : ℝ)*X 2 1+(352002573/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302052_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((3142150451/5000000000 : ℝ)*X 0 0+(1121303827/2500000000 : ℝ)*X 0 1+(-1837893037/10000000000 : ℝ)*X 0 2+(3142150451/5000000000 : ℝ)*X 1 0+(1121303827/2500000000 : ℝ)*X 1 1+(-1837893037/10000000000 : ℝ)*X 1 2+(3142150451/5000000000 : ℝ)*X 2 0+(1121303827/2500000000 : ℝ)*X 2 1+(-1837893037/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302052_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-417821927/2500000000 : ℝ)*X 0 0+(2620798729/10000000000 : ℝ)*X 0 1+(-7890069839/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302052_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((808727799/2000000000 : ℝ)*X 1 0+(-1132032011/5000000000 : ℝ)*X 1 1+(-3187621253/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302052_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((277035481/625000000 : ℝ)*X 2 0+(3540785039/5000000000 : ℝ)*X 2 1+(530305769/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302052_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((1105083571/2000000000 : ℝ)*X 0 0+(6099776623/10000000000 : ℝ)*X 0 1+(-244185517/5000000000 : ℝ)*X 0 2+(1105083571/2000000000 : ℝ)*X 1 0+(6099776623/10000000000 : ℝ)*X 1 1+(-244185517/5000000000 : ℝ)*X 1 2+(1105083571/2000000000 : ℝ)*X 2 0+(6099776623/10000000000 : ℝ)*X 2 1+(-244185517/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302052_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-834600239/10000000000 : ℝ)*X 0 0+(24920573/78125000 : ℝ)*X 0 1+(-248188607/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302052_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((3998891801/10000000000 : ℝ)*X 1 0+(-1252437063/5000000000 : ℝ)*X 1 1+(-3118313231/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302052_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((1264703283/2000000000 : ℝ)*X 2 0+(5219106947/10000000000 : ℝ)*X 2 1+(317479813/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302052_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((3852595191/5000000000 : ℝ)*X 0 0+(116272353/312500000 : ℝ)*X 0 1+(-90532883/2000000000 : ℝ)*X 0 2+(3852595191/5000000000 : ℝ)*X 1 0+(116272353/312500000 : ℝ)*X 1 1+(-90532883/2000000000 : ℝ)*X 1 2+(3852595191/5000000000 : ℝ)*X 2 0+(116272353/312500000 : ℝ)*X 2 1+(-90532883/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302052_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-19437413/500000000 : ℝ)*X 0 0+(4410280647/10000000000 : ℝ)*X 0 1+(-1790156081/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302052_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((6380439169/10000000000 : ℝ)*X 1 0+(-602619959/2500000000 : ℝ)*X 1 1+(-978426427/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302052_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((4199281519/10000000000 : ℝ)*X 2 0+(1669161287/2500000000 : ℝ)*X 2 1+(1625822847/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302052_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((4039569329/5000000000 : ℝ)*X 0 0+(612649127/2000000000 : ℝ)*X 0 1+(-745927727/10000000000 : ℝ)*X 0 2+(4039569329/5000000000 : ℝ)*X 1 0+(612649127/2000000000 : ℝ)*X 1 1+(-745927727/10000000000 : ℝ)*X 1 2+(4039569329/5000000000 : ℝ)*X 2 0+(612649127/2000000000 : ℝ)*X 2 1+(-745927727/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302052_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((54459/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(54459/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (19995498523150054496567191052131/2897845717506550000000000000000000000 : ℝ) := by norm_num
    linear_combination (352009/250000000000 : ℝ)*(base5) + (1279258193/7812500000 : ℝ)*(base39) + (111569/250000000000 : ℝ)*(base50) + (153990159511/200000000000 : ℝ)*(base59) + (60703140529/15625000000 : ℝ)*(major_s2_0) + (60703140529/15625000000 : ℝ)*(major_s2_1) + (60703140529/15625000000 : ℝ)*(major_s2_2) + (10555621/1000000000000 : ℝ)*(sp_s2_6) + (645698493349/125000000000 : ℝ)*(sp_s2_7) + (2582657388071/500000000000 : ℝ)*(sp_s2_8) + (5165536786957/1000000000000 : ℝ)*(sp_s2_9) + (1302199888607/500000000000 : ℝ)*(sp_s2_13) + (273170651/1000000000000 : ℝ)*(sp_s2_15) + (52567871/1000000000000 : ℝ)*(sp_s2_23) + (260441174087/100000000000 : ℝ)*(f.failure) + (645698493349/125000000000 : ℝ)*(f.sum) + (1085952468547437427/1441599533125000000000000000000 : ℝ)*base62 + (899265181381187/1489525000000000000000000000 : ℝ)*base64 + (529223610313919/1935650000000000000000000000 : ℝ)*base66 + (499942665984761/595810000000000000000000000 : ℝ)*base68 + (4096780804346198491/14035235503125000000000000000000 : ℝ)*base70 + (1294923840442441/1256350000000000000000000000 : ℝ)*base73 + (342968533689449/387130000000000000000000000 : ℝ)*base74 + (183654397202789/471131250000000000000000000 : ℝ)*base76 + (619193449804687369/9727415510000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (221/1000000000000000 : ℝ)*base86 + (221/1000000000000000 : ℝ)*base88 + (221/1000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29087/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(29087/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (11774982761310557095291749/720799766562500000000000000000 : ℝ) := by norm_num
    linear_combination (305830093/1250000000 : ℝ)*(base39) + (8773655517/500000000000 : ℝ)*(base49) + (128498510297/250000000000 : ℝ)*(base59) + (194269612807/50000000000 : ℝ)*(major_s2_0) + (194269612807/50000000000 : ℝ)*(major_s2_1) + (194269612807/50000000000 : ℝ)*(major_s2_2) + (20203559/1000000000000 : ℝ)*(sp_s2_6) + (44564121/1000000000000 : ℝ)*(sp_s2_7) + (24300061/200000000000 : ℝ)*(sp_s2_8) + (1291515117269/250000000000 : ℝ)*(sp_s2_14) + (5165983532891/1000000000000 : ℝ)*(sp_s2_15) + (5166105033197/1000000000000 : ℝ)*(sp_s2_16) + (2604535474473/1000000000000 : ℝ)*(sp_s2_20) + (23671143/200000000000 : ℝ)*(sp_s2_27) + (2604674033747/1000000000000 : ℝ)*(f.failure) + (5166105033197/1000000000000 : ℝ)*(f.sum) + (6063507544268994761/23065592530000000000000000000000 : ℝ)*base62 + (6828494015167/29790500000000000000000000 : ℝ)*base64 + (100467848235079/387130000000000000000000000 : ℝ)*base66 + (4339385484871/14895250000000000000000000 : ℝ)*base69 + (26218787253335989297/44912753610000000000000000000000 : ℝ)*base70 + (82954041130367/251270000000000000000000000 : ℝ)*base72 + (14707269635163/96782500000000000000000000 : ℝ)*base74 + (253922383307/75381000000000000000000000 : ℝ)*base77 + (446605329629804869/2431853877500000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (3999/10000000000000000 : ℝ)*base87 + (3999/10000000000000000 : ℝ)*base89 + (3999/10000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-38241/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-38241/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5862436482051829555562236927437/579569143501310000000000000000000000 : ℝ) := by norm_num
    linear_combination (1740181/250000000000 : ℝ)*(base11) + (648167803533/1000000000000 : ℝ)*(base39) + (149106579757/1000000000000 : ℝ)*(base49) + (95874044191/200000000000 : ℝ)*(base59) + (1463168603943/500000000000 : ℝ)*(major_s2_0) + (1463168603943/500000000000 : ℝ)*(major_s2_1) + (1463168603943/500000000000 : ℝ)*(major_s2_2) + (1970557/125000000000 : ℝ)*(sp_s2_0) + (218327/250000000000 : ℝ)*(sp_s2_2) + (2868019/50000000000 : ℝ)*(sp_s2_9) + (1945450924907/500000000000 : ℝ)*(sp_s2_21) + (3890924574993/1000000000000 : ℝ)*(sp_s2_22) + (1945433170653/500000000000 : ℝ)*(sp_s2_23) + (1961746469053/1000000000000 : ℝ)*(sp_s2_27) + (1961746469053/1000000000000 : ℝ)*(f.failure) + (3890924574993/1000000000000 : ℝ)*(f.sum) + (3775508677221911731/46131185060000000000000000000000 : ℝ)*base62 + (69434518500471/744762500000000000000000000 : ℝ)*base64 + (2040749982287377/3871300000000000000000000000 : ℝ)*base67 + (19451559768729/595810000000000000000000000 : ℝ)*base68 + (12094069422058000893/74854589350000000000000000000000 : ℝ)*base71 + (451665419316251/1256350000000000000000000000 : ℝ)*base73 + (431341500949559/774260000000000000000000000 : ℝ)*base74 + (374561610987367/628175000000000000000000000 : ℝ)*base76 + (123151721511108123/778193240800000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (3601/10000000000000000 : ℝ)*base87 + (3601/10000000000000000 : ℝ)*base89 + (3601/10000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]])
    (hprev1 : (0 : ℝ) ≤ ((75381/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(75381/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(38713/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(38713/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-59581/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-59581/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((54459/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(54459/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29087/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(29087/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-38241/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-38241/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c302052_s2 p hpa hpb X hX hprev1

#print axioms solution
