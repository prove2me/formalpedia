-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c307080_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:17:06.621984+00:00
-- url     : https://prove2.me/submissions/cbae3c20-2c83-405f-bc02-d2738a7c50f6

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
theorem collision_support_c307080_s2_s2_1 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6013127569/10000000000 : ℝ)*x 0 + (-388730089/5000000000 : ℝ)*x 1 + (1358390277/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6013127569/10000000000 : ℝ)^17 ≤ (51419910364211/100000000000000 : ℝ)^13 := by
    have hnat : (6013127569 : ℕ)^17*100000000000000^13 ≤ 51419910364211^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6013127569 10000000000 51419910364211 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (388730089/5000000000 : ℝ)^17 ≤ (3542814018713/100000000000000 : ℝ)^13 := by
    have hnat : (388730089 : ℕ)^17*100000000000000^13 ≤ 3542814018713^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      388730089 5000000000 3542814018713 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358390277/2500000000 : ℝ)^17 ≤ (1801491024077/4000000000000 : ℝ)^13 := by
    have hnat : (1358390277 : ℕ)^17*4000000000000^13 ≤ 1801491024077^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358390277 2500000000 1801491024077 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6013127569/10000000000 : ℝ), (-388730089/5000000000 : ℝ), (1358390277/2500000000 : ℝ)] ![(51419910364211/100000000000000 : ℝ), (3542814018713/100000000000000 : ℝ), (1801491024077/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6013127569/10000000000 : ℝ)|^17 ≤ (51419910364211/100000000000000 : ℝ)^13
        have hw : |(6013127569/10000000000 : ℝ)|=(6013127569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-388730089/5000000000 : ℝ)|^17 ≤ (3542814018713/100000000000000 : ℝ)^13
        have hw : |(-388730089/5000000000 : ℝ)|=(388730089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358390277/2500000000 : ℝ)|^17 ≤ (1801491024077/4000000000000 : ℝ)^13
        have hw : |(1358390277/2500000000 : ℝ)|=(1358390277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307080_s2_s2_6 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4197043949/10000000000 : ℝ)*x 0 + (2468202997/5000000000 : ℝ)*x 1 + (3792518037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4197043949/10000000000 : ℝ)^17 ≤ (642622804563/2000000000000 : ℝ)^13 := by
    have hnat : (4197043949 : ℕ)^17*2000000000000^13 ≤ 642622804563^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4197043949 10000000000 642622804563 2000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2468202997/5000000000 : ℝ)^17 ≤ (4965760474699/12500000000000 : ℝ)^13 := by
    have hnat : (2468202997 : ℕ)^17*12500000000000^13 ≤ 4965760474699^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2468202997 5000000000 4965760474699 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3792518037/10000000000 : ℝ)^17 ≤ (7035693990623/25000000000000 : ℝ)^13 := by
    have hnat : (3792518037 : ℕ)^17*25000000000000^13 ≤ 7035693990623^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3792518037 10000000000 7035693990623 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4197043949/10000000000 : ℝ), (2468202997/5000000000 : ℝ), (3792518037/10000000000 : ℝ)] ![(642622804563/2000000000000 : ℝ), (4965760474699/12500000000000 : ℝ), (7035693990623/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4197043949/10000000000 : ℝ)|^17 ≤ (642622804563/2000000000000 : ℝ)^13
        have hw : |(4197043949/10000000000 : ℝ)|=(4197043949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2468202997/5000000000 : ℝ)|^17 ≤ (4965760474699/12500000000000 : ℝ)^13
        have hw : |(2468202997/5000000000 : ℝ)|=(2468202997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3792518037/10000000000 : ℝ)|^17 ≤ (7035693990623/25000000000000 : ℝ)^13
        have hw : |(3792518037/10000000000 : ℝ)|=(3792518037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307080_s2_s2_7 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1758380791/5000000000 : ℝ)*x 0 + (2742738863/5000000000 : ℝ)*x 1 + (3870496003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1758380791/5000000000 : ℝ)^17 ≤ (6374330903519/25000000000000 : ℝ)^13 := by
    have hnat : (1758380791 : ℕ)^17*25000000000000^13 ≤ 6374330903519^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1758380791 5000000000 6374330903519 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2742738863/5000000000 : ℝ)^17 ≤ (45600830267207/100000000000000 : ℝ)^13 := by
    have hnat : (2742738863 : ℕ)^17*100000000000000^13 ≤ 45600830267207^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2742738863 5000000000 45600830267207 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3870496003/10000000000 : ℝ)^17 ≤ (14450923056633/50000000000000 : ℝ)^13 := by
    have hnat : (3870496003 : ℕ)^17*50000000000000^13 ≤ 14450923056633^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3870496003 10000000000 14450923056633 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1758380791/5000000000 : ℝ), (2742738863/5000000000 : ℝ), (3870496003/10000000000 : ℝ)] ![(6374330903519/25000000000000 : ℝ), (45600830267207/100000000000000 : ℝ), (14450923056633/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1758380791/5000000000 : ℝ)|^17 ≤ (6374330903519/25000000000000 : ℝ)^13
        have hw : |(-1758380791/5000000000 : ℝ)|=(1758380791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2742738863/5000000000 : ℝ)|^17 ≤ (45600830267207/100000000000000 : ℝ)^13
        have hw : |(2742738863/5000000000 : ℝ)|=(2742738863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3870496003/10000000000 : ℝ)|^17 ≤ (14450923056633/50000000000000 : ℝ)^13
        have hw : |(3870496003/10000000000 : ℝ)|=(3870496003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307080_s2_s2_8 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2911365227/5000000000 : ℝ)*x 0 + (-16506177/2000000000 : ℝ)*x 1 + (5931599039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2911365227/5000000000 : ℝ)^17 ≤ (49301254949713/100000000000000 : ℝ)^13 := by
    have hnat : (2911365227 : ℕ)^17*100000000000000^13 ≤ 49301254949713^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2911365227 5000000000 49301254949713 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16506177/2000000000 : ℝ)^17 ≤ (94307325843/50000000000000 : ℝ)^13 := by
    have hnat : (16506177 : ℕ)^17*50000000000000^13 ≤ 94307325843^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16506177 2000000000 94307325843 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5931599039/10000000000 : ℝ)^17 ≤ (50510130383941/100000000000000 : ℝ)^13 := by
    have hnat : (5931599039 : ℕ)^17*100000000000000^13 ≤ 50510130383941^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5931599039 10000000000 50510130383941 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2911365227/5000000000 : ℝ), (-16506177/2000000000 : ℝ), (5931599039/10000000000 : ℝ)] ![(49301254949713/100000000000000 : ℝ), (94307325843/50000000000000 : ℝ), (50510130383941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2911365227/5000000000 : ℝ)|^17 ≤ (49301254949713/100000000000000 : ℝ)^13
        have hw : |(2911365227/5000000000 : ℝ)|=(2911365227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-16506177/2000000000 : ℝ)|^17 ≤ (94307325843/50000000000000 : ℝ)^13
        have hw : |(-16506177/2000000000 : ℝ)|=(16506177/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5931599039/10000000000 : ℝ)|^17 ≤ (50510130383941/100000000000000 : ℝ)^13
        have hw : |(5931599039/10000000000 : ℝ)|=(5931599039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307080_s2_s2_9 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1398919961/5000000000 : ℝ)*x 0 + (3368572681/5000000000 : ℝ)*x 1 + (-769815353/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1398919961/5000000000 : ℝ)^17 ≤ (9453323438011/50000000000000 : ℝ)^13 := by
    have hnat : (1398919961 : ℕ)^17*50000000000000^13 ≤ 9453323438011^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1398919961 5000000000 9453323438011 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3368572681/5000000000 : ℝ)^17 ≤ (59662201870137/100000000000000 : ℝ)^13 := by
    have hnat : (3368572681 : ℕ)^17*100000000000000^13 ≤ 59662201870137^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3368572681 5000000000 59662201870137 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (769815353/2500000000 : ℝ)^17 ≤ (334861738069/1562500000000 : ℝ)^13 := by
    have hnat : (769815353 : ℕ)^17*1562500000000^13 ≤ 334861738069^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      769815353 2500000000 334861738069 1562500000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1398919961/5000000000 : ℝ), (3368572681/5000000000 : ℝ), (-769815353/2500000000 : ℝ)] ![(9453323438011/50000000000000 : ℝ), (59662201870137/100000000000000 : ℝ), (334861738069/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1398919961/5000000000 : ℝ)|^17 ≤ (9453323438011/50000000000000 : ℝ)^13
        have hw : |(1398919961/5000000000 : ℝ)|=(1398919961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3368572681/5000000000 : ℝ)|^17 ≤ (59662201870137/100000000000000 : ℝ)^13
        have hw : |(3368572681/5000000000 : ℝ)|=(3368572681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-769815353/2500000000 : ℝ)|^17 ≤ (334861738069/1562500000000 : ℝ)^13
        have hw : |(-769815353/2500000000 : ℝ)|=(769815353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307080_s2_s2_12 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (30088437/78125000 : ℝ)*x 0 + (5138527437/10000000000 : ℝ)*x 1 + (1961664361/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (30088437/78125000 : ℝ)^17 ≤ (7178684509061/25000000000000 : ℝ)^13 := by
    have hnat : (30088437 : ℕ)^17*25000000000000^13 ≤ 7178684509061^13*78125000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30088437 78125000 7178684509061 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5138527437/10000000000 : ℝ)^17 ≤ (334931467909/800000000000 : ℝ)^13 := by
    have hnat : (5138527437 : ℕ)^17*800000000000^13 ≤ 334931467909^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138527437 10000000000 334931467909 800000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1961664361/5000000000 : ℝ)^17 ≤ (147094142287/500000000000 : ℝ)^13 := by
    have hnat : (1961664361 : ℕ)^17*500000000000^13 ≤ 147094142287^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1961664361 5000000000 147094142287 500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(30088437/78125000 : ℝ), (5138527437/10000000000 : ℝ), (1961664361/5000000000 : ℝ)] ![(7178684509061/25000000000000 : ℝ), (334931467909/800000000000 : ℝ), (147094142287/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(30088437/78125000 : ℝ)|^17 ≤ (7178684509061/25000000000000 : ℝ)^13
        have hw : |(30088437/78125000 : ℝ)|=(30088437/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5138527437/10000000000 : ℝ)|^17 ≤ (334931467909/800000000000 : ℝ)^13
        have hw : |(5138527437/10000000000 : ℝ)|=(5138527437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1961664361/5000000000 : ℝ)|^17 ≤ (147094142287/500000000000 : ℝ)^13
        have hw : |(1961664361/5000000000 : ℝ)|=(1961664361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307080_s2_s2_13 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-962399969/2500000000 : ℝ)*x 0 + (5538695681/10000000000 : ℝ)*x 1 + (695417267/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (962399969/2500000000 : ℝ)^17 ≤ (28697968749851/100000000000000 : ℝ)^13 := by
    have hnat : (962399969 : ℕ)^17*100000000000000^13 ≤ 28697968749851^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      962399969 2500000000 28697968749851 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5538695681/10000000000 : ℝ)^17 ≤ (46180216707809/100000000000000 : ℝ)^13 := by
    have hnat : (5538695681 : ℕ)^17*100000000000000^13 ≤ 46180216707809^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5538695681 10000000000 46180216707809 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (695417267/2000000000 : ℝ)^17 ≤ (25121814517281/100000000000000 : ℝ)^13 := by
    have hnat : (695417267 : ℕ)^17*100000000000000^13 ≤ 25121814517281^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      695417267 2000000000 25121814517281 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-962399969/2500000000 : ℝ), (5538695681/10000000000 : ℝ), (695417267/2000000000 : ℝ)] ![(28697968749851/100000000000000 : ℝ), (46180216707809/100000000000000 : ℝ), (25121814517281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-962399969/2500000000 : ℝ)|^17 ≤ (28697968749851/100000000000000 : ℝ)^13
        have hw : |(-962399969/2500000000 : ℝ)|=(962399969/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5538695681/10000000000 : ℝ)|^17 ≤ (46180216707809/100000000000000 : ℝ)^13
        have hw : |(5538695681/10000000000 : ℝ)|=(5538695681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(695417267/2000000000 : ℝ)|^17 ≤ (25121814517281/100000000000000 : ℝ)^13
        have hw : |(695417267/2000000000 : ℝ)|=(695417267/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307080_s2_s2_14 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5795347809/10000000000 : ℝ)*x 0 + (-367173653/5000000000 : ℝ)*x 1 + (1419697209/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5795347809/10000000000 : ℝ)^17 ≤ (24499143186109/50000000000000 : ℝ)^13 := by
    have hnat : (5795347809 : ℕ)^17*50000000000000^13 ≤ 24499143186109^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5795347809 10000000000 24499143186109 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (367173653/5000000000 : ℝ)^17 ≤ (3288123516459/100000000000000 : ℝ)^13 := by
    have hnat : (367173653 : ℕ)^17*100000000000000^13 ≤ 3288123516459^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      367173653 5000000000 3288123516459 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1419697209/2500000000 : ℝ)^17 ≤ (47713590093587/100000000000000 : ℝ)^13 := by
    have hnat : (1419697209 : ℕ)^17*100000000000000^13 ≤ 47713590093587^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1419697209 2500000000 47713590093587 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5795347809/10000000000 : ℝ), (-367173653/5000000000 : ℝ), (1419697209/2500000000 : ℝ)] ![(24499143186109/50000000000000 : ℝ), (3288123516459/100000000000000 : ℝ), (47713590093587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5795347809/10000000000 : ℝ)|^17 ≤ (24499143186109/50000000000000 : ℝ)^13
        have hw : |(5795347809/10000000000 : ℝ)|=(5795347809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-367173653/5000000000 : ℝ)|^17 ≤ (3288123516459/100000000000000 : ℝ)^13
        have hw : |(-367173653/5000000000 : ℝ)|=(367173653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1419697209/2500000000 : ℝ)|^17 ≤ (47713590093587/100000000000000 : ℝ)^13
        have hw : |(1419697209/2500000000 : ℝ)|=(1419697209/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307080_s2_s2_15 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2854088641/10000000000 : ℝ)*x 0 + (5956566631/10000000000 : ℝ)*x 1 + (-3962795481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2854088641/10000000000 : ℝ)^17 ≤ (3881047678303/20000000000000 : ℝ)^13 := by
    have hnat : (2854088641 : ℕ)^17*20000000000000^13 ≤ 3881047678303^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2854088641 10000000000 3881047678303 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5956566631/10000000000 : ℝ)^17 ≤ (50788338507443/100000000000000 : ℝ)^13 := by
    have hnat : (5956566631 : ℕ)^17*100000000000000^13 ≤ 50788338507443^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5956566631 10000000000 50788338507443 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3962795481/10000000000 : ℝ)^17 ≤ (14903211547333/50000000000000 : ℝ)^13 := by
    have hnat : (3962795481 : ℕ)^17*50000000000000^13 ≤ 14903211547333^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3962795481 10000000000 14903211547333 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2854088641/10000000000 : ℝ), (5956566631/10000000000 : ℝ), (-3962795481/10000000000 : ℝ)] ![(3881047678303/20000000000000 : ℝ), (50788338507443/100000000000000 : ℝ), (14903211547333/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2854088641/10000000000 : ℝ)|^17 ≤ (3881047678303/20000000000000 : ℝ)^13
        have hw : |(2854088641/10000000000 : ℝ)|=(2854088641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5956566631/10000000000 : ℝ)|^17 ≤ (50788338507443/100000000000000 : ℝ)^13
        have hw : |(5956566631/10000000000 : ℝ)|=(5956566631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3962795481/10000000000 : ℝ)|^17 ≤ (14903211547333/50000000000000 : ℝ)^13
        have hw : |(-3962795481/10000000000 : ℝ)|=(3962795481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307080_s2_s2_19 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1182408483/2500000000 : ℝ)*x 0 + (4754738833/10000000000 : ℝ)*x 1 + (684569327/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1182408483/2500000000 : ℝ)^17 ≤ (4695528413837/12500000000000 : ℝ)^13 := by
    have hnat : (1182408483 : ℕ)^17*12500000000000^13 ≤ 4695528413837^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1182408483 2500000000 4695528413837 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4754738833/10000000000 : ℝ)^17 ≤ (7565036397867/20000000000000 : ℝ)^13 := by
    have hnat : (4754738833 : ℕ)^17*20000000000000^13 ≤ 7565036397867^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4754738833 10000000000 7565036397867 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (684569327/2000000000 : ℝ)^17 ≤ (3076323836199/12500000000000 : ℝ)^13 := by
    have hnat : (684569327 : ℕ)^17*12500000000000^13 ≤ 3076323836199^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684569327 2000000000 3076323836199 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1182408483/2500000000 : ℝ), (4754738833/10000000000 : ℝ), (684569327/2000000000 : ℝ)] ![(4695528413837/12500000000000 : ℝ), (7565036397867/20000000000000 : ℝ), (3076323836199/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1182408483/2500000000 : ℝ)|^17 ≤ (4695528413837/12500000000000 : ℝ)^13
        have hw : |(1182408483/2500000000 : ℝ)|=(1182408483/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4754738833/10000000000 : ℝ)|^17 ≤ (7565036397867/20000000000000 : ℝ)^13
        have hw : |(4754738833/10000000000 : ℝ)|=(4754738833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(684569327/2000000000 : ℝ)|^17 ≤ (3076323836199/12500000000000 : ℝ)^13
        have hw : |(684569327/2000000000 : ℝ)|=(684569327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307080_s2_s2_20 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2958599367/10000000000 : ℝ)*x 0 + (5833912767/10000000000 : ℝ)*x 1 + (2003159967/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2958599367/10000000000 : ℝ)^17 ≤ (10169824170653/50000000000000 : ℝ)^13 := by
    have hnat : (2958599367 : ℕ)^17*50000000000000^13 ≤ 10169824170653^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2958599367 10000000000 10169824170653 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5833912767/10000000000 : ℝ)^17 ≤ (9885021031537/20000000000000 : ℝ)^13 := by
    have hnat : (5833912767 : ℕ)^17*20000000000000^13 ≤ 9885021031537^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5833912767 10000000000 9885021031537 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2003159967/5000000000 : ℝ)^17 ≤ (6047049297403/20000000000000 : ℝ)^13 := by
    have hnat : (2003159967 : ℕ)^17*20000000000000^13 ≤ 6047049297403^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2003159967 5000000000 6047049297403 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2958599367/10000000000 : ℝ), (5833912767/10000000000 : ℝ), (2003159967/5000000000 : ℝ)] ![(10169824170653/50000000000000 : ℝ), (9885021031537/20000000000000 : ℝ), (6047049297403/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2958599367/10000000000 : ℝ)|^17 ≤ (10169824170653/50000000000000 : ℝ)^13
        have hw : |(-2958599367/10000000000 : ℝ)|=(2958599367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5833912767/10000000000 : ℝ)|^17 ≤ (9885021031537/20000000000000 : ℝ)^13
        have hw : |(5833912767/10000000000 : ℝ)|=(5833912767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2003159967/5000000000 : ℝ)|^17 ≤ (6047049297403/20000000000000 : ℝ)^13
        have hw : |(2003159967/5000000000 : ℝ)|=(2003159967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307080_s2_s2_21 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6881491547/10000000000 : ℝ)*x 0 + (-37431407/2500000000 : ℝ)*x 1 + (1198873117/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6881491547/10000000000 : ℝ)^17 ≤ (30669646037757/50000000000000 : ℝ)^13 := by
    have hnat : (6881491547 : ℕ)^17*50000000000000^13 ≤ 30669646037757^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6881491547 10000000000 30669646037757 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (37431407/2500000000 : ℝ)^17 ≤ (102751651641/25000000000000 : ℝ)^13 := by
    have hnat : (37431407 : ℕ)^17*25000000000000^13 ≤ 102751651641^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37431407 2500000000 102751651641 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1198873117/2500000000 : ℝ)^17 ≤ (38249701303023/100000000000000 : ℝ)^13 := by
    have hnat : (1198873117 : ℕ)^17*100000000000000^13 ≤ 38249701303023^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1198873117 2500000000 38249701303023 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6881491547/10000000000 : ℝ), (-37431407/2500000000 : ℝ), (1198873117/2500000000 : ℝ)] ![(30669646037757/50000000000000 : ℝ), (102751651641/25000000000000 : ℝ), (38249701303023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6881491547/10000000000 : ℝ)|^17 ≤ (30669646037757/50000000000000 : ℝ)^13
        have hw : |(6881491547/10000000000 : ℝ)|=(6881491547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-37431407/2500000000 : ℝ)|^17 ≤ (102751651641/25000000000000 : ℝ)^13
        have hw : |(-37431407/2500000000 : ℝ)|=(37431407/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1198873117/2500000000 : ℝ)|^17 ≤ (38249701303023/100000000000000 : ℝ)^13
        have hw : |(1198873117/2500000000 : ℝ)|=(1198873117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307080_s2_s2_22 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (631321651/2500000000 : ℝ)*x 0 + (6669949549/10000000000 : ℝ)*x 1 + (-106861229/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (631321651/2500000000 : ℝ)^17 ≤ (8267539366913/50000000000000 : ℝ)^13 := by
    have hnat : (631321651 : ℕ)^17*50000000000000^13 ≤ 8267539366913^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      631321651 2500000000 8267539366913 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6669949549/10000000000 : ℝ)^17 ≤ (58885234673751/100000000000000 : ℝ)^13 := by
    have hnat : (6669949549 : ℕ)^17*100000000000000^13 ≤ 58885234673751^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6669949549 10000000000 58885234673751 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (106861229/312500000 : ℝ)^17 ≤ (24579686579453/100000000000000 : ℝ)^13 := by
    have hnat : (106861229 : ℕ)^17*100000000000000^13 ≤ 24579686579453^13*312500000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106861229 312500000 24579686579453 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(631321651/2500000000 : ℝ), (6669949549/10000000000 : ℝ), (-106861229/312500000 : ℝ)] ![(8267539366913/50000000000000 : ℝ), (58885234673751/100000000000000 : ℝ), (24579686579453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(631321651/2500000000 : ℝ)|^17 ≤ (8267539366913/50000000000000 : ℝ)^13
        have hw : |(631321651/2500000000 : ℝ)|=(631321651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6669949549/10000000000 : ℝ)|^17 ≤ (58885234673751/100000000000000 : ℝ)^13
        have hw : |(6669949549/10000000000 : ℝ)|=(6669949549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-106861229/312500000 : ℝ)|^17 ≤ (24579686579453/100000000000000 : ℝ)^13
        have hw : |(-106861229/312500000 : ℝ)|=(106861229/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307080_s2_s2_25 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5011512679/10000000000 : ℝ)*x 0 + (4403689467/10000000000 : ℝ)*x 1 + (3492363703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5011512679/10000000000 : ℝ)^17 ≤ (20259165663363/50000000000000 : ℝ)^13 := by
    have hnat : (5011512679 : ℕ)^17*50000000000000^13 ≤ 20259165663363^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5011512679 10000000000 20259165663363 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4403689467/10000000000 : ℝ)^17 ≤ (34215415691579/100000000000000 : ℝ)^13 := by
    have hnat : (4403689467 : ℕ)^17*100000000000000^13 ≤ 34215415691579^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4403689467 10000000000 34215415691579 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3492363703/10000000000 : ℝ)^17 ≤ (25266252963649/100000000000000 : ℝ)^13 := by
    have hnat : (3492363703 : ℕ)^17*100000000000000^13 ≤ 25266252963649^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3492363703 10000000000 25266252963649 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5011512679/10000000000 : ℝ), (4403689467/10000000000 : ℝ), (3492363703/10000000000 : ℝ)] ![(20259165663363/50000000000000 : ℝ), (34215415691579/100000000000000 : ℝ), (25266252963649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5011512679/10000000000 : ℝ)|^17 ≤ (20259165663363/50000000000000 : ℝ)^13
        have hw : |(5011512679/10000000000 : ℝ)|=(5011512679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4403689467/10000000000 : ℝ)|^17 ≤ (34215415691579/100000000000000 : ℝ)^13
        have hw : |(4403689467/10000000000 : ℝ)|=(4403689467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3492363703/10000000000 : ℝ)|^17 ≤ (25266252963649/100000000000000 : ℝ)^13
        have hw : |(3492363703/10000000000 : ℝ)|=(3492363703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c307080_s2 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((6839/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6839/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((31519/100000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(31519/100000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19189/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19189/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2939/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2939/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((5779/100000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(5779/100000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3543/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3543/10000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4817/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4817/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4817/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4817/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4817/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4817/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s2_pow0 : (6839/10000 : ℝ) ^ (135/32 : ℝ) ≤ (5032862386736864117/25000000000000000000 : ℝ) := by
    have hpowers : (6839/10000 : ℝ)^135 ≤ (5032862386736864117/25000000000000000000 : ℝ)^32 := by
      have hnat : (6839 : ℕ)^135*25000000000000000000^32 ≤ 5032862386736864117^32*10000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6839 10000 5032862386736864117 25000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6839/10000 : ℝ)) (X := (5032862386736864117/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s2_corner0a : (30032862386736864117/25000000000000000000 : ℝ) ≤ (10444354215139349/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (30032862386736864117/25000000000000000000 : ℝ)^32 ≤ (10444354215139349/10000000000000000 : ℝ)^135 := by
      have hnat : (30032862386736864117 : ℕ)^32*10000000000000000^135 ≤ 10444354215139349^135*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30032862386736864117 25000000000000000000 10444354215139349 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10444354215139349/10000000000000000 : ℝ)) (X := (30032862386736864117/25000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s2_corner0b : (17532862386736864117/12500000000000000000 : ℝ) ≤ (1354381152623351/1250000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (17532862386736864117/12500000000000000000 : ℝ)^32 ≤ (1354381152623351/1250000000000000 : ℝ)^135 := by
      have hnat : (17532862386736864117 : ℕ)^32*1250000000000000^135 ≤ 1354381152623351^135*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17532862386736864117 12500000000000000000 1354381152623351 1250000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1354381152623351/1250000000000000 : ℝ)) (X := (17532862386736864117/12500000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(444354215139349/6839000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(390695005847459/6839000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (6839/10000 : ℝ)) (alpha := (444354215139349/6839000000000000 : ℝ)) (beta := (390695005847459/6839000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (6839/10000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(444354215139349/6839000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(390695005847459/6839000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (31519/100000 : ℝ) ^ (135/32 : ℝ) ≤ (2994763109351377/390625000000000000 : ℝ) := by
    have hpowers : (31519/100000 : ℝ)^135 ≤ (2994763109351377/390625000000000000 : ℝ)^32 := by
      have hnat : (31519 : ℕ)^135*390625000000000000^32 ≤ 2994763109351377^32*100000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31519 100000 2994763109351377 390625000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (31519/100000 : ℝ)) (X := (2994763109351377/390625000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s2_corner1a : (393619763109351377/390625000000000000 : ℝ) ≤ (10018119755474607/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (393619763109351377/390625000000000000 : ℝ)^32 ≤ (10018119755474607/10000000000000000 : ℝ)^135 := by
      have hnat : (393619763109351377 : ℕ)^32*10000000000000000^135 ≤ 10018119755474607^135*390625000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        393619763109351377 390625000000000000 10018119755474607 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10018119755474607/10000000000000000 : ℝ)) (X := (393619763109351377/390625000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s2_corner1b : (198307263109351377/195312500000000000 : ℝ) ≤ (2007226926452149/2000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (198307263109351377/195312500000000000 : ℝ)^32 ≤ (2007226926452149/2000000000000000 : ℝ)^135 := by
      have hnat : (198307263109351377 : ℕ)^32*2000000000000000^135 ≤ 2007226926452149^135*195312500000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        198307263109351377 195312500000000000 2007226926452149 2000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2007226926452149/2000000000000000 : ℝ)) (X := (198307263109351377/195312500000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(18119755474607/3151900000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(9007438393069/1575950000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (31519/100000 : ℝ)) (alpha := (18119755474607/3151900000000000 : ℝ)) (beta := (9007438393069/1575950000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (31519/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(18119755474607/3151900000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(9007438393069/1575950000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (19189/25000 : ℝ) ^ (135/32 : ℝ) ≤ (32758021214714707241/100000000000000000000 : ℝ) := by
    have hpowers : (19189/25000 : ℝ)^135 ≤ (32758021214714707241/100000000000000000000 : ℝ)^32 := by
      have hnat : (19189 : ℕ)^135*100000000000000000000^32 ≤ 32758021214714707241^32*25000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19189 25000 32758021214714707241 100000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19189/25000 : ℝ)) (X := (32758021214714707241/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s2_corner2a : (132758021214714707241/100000000000000000000 : ℝ) ≤ (10694733339482153/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (132758021214714707241/100000000000000000000 : ℝ)^32 ≤ (10694733339482153/10000000000000000 : ℝ)^135 := by
      have hnat : (132758021214714707241 : ℕ)^32*10000000000000000^135 ≤ 10694733339482153^135*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        132758021214714707241 100000000000000000000 10694733339482153 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10694733339482153/10000000000000000 : ℝ)) (X := (132758021214714707241/100000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s2_corner2b : (82758021214714707241/50000000000000000000 : ℝ) ≤ (5634342089919743/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (82758021214714707241/50000000000000000000 : ℝ)^32 ≤ (5634342089919743/5000000000000000 : ℝ)^135 := by
      have hnat : (82758021214714707241 : ℕ)^32*5000000000000000^135 ≤ 5634342089919743^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        82758021214714707241 50000000000000000000 5634342089919743 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5634342089919743/5000000000000000 : ℝ)) (X := (82758021214714707241/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(694733339482153/7675600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(573950840357333/7675600000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (19189/25000 : ℝ)) (alpha := (694733339482153/7675600000000000 : ℝ)) (beta := (573950840357333/7675600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (19189/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(694733339482153/7675600000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(573950840357333/7675600000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_1 : ((6013127569/10000000000 : ℝ)*X 1 0+(-388730089/5000000000 : ℝ)*X 1 1+(1358390277/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307080_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((4197043949/10000000000 : ℝ)*X 0 0+(2468202997/5000000000 : ℝ)*X 0 1+(3792518037/10000000000 : ℝ)*X 0 2+(4197043949/10000000000 : ℝ)*X 1 0+(2468202997/5000000000 : ℝ)*X 1 1+(3792518037/10000000000 : ℝ)*X 1 2+(4197043949/10000000000 : ℝ)*X 2 0+(2468202997/5000000000 : ℝ)*X 2 1+(3792518037/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307080_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-1758380791/5000000000 : ℝ)*X 0 0+(2742738863/5000000000 : ℝ)*X 0 1+(3870496003/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307080_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((2911365227/5000000000 : ℝ)*X 1 0+(-16506177/2000000000 : ℝ)*X 1 1+(5931599039/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307080_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((1398919961/5000000000 : ℝ)*X 2 0+(3368572681/5000000000 : ℝ)*X 2 1+(-769815353/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307080_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_12 : ((30088437/78125000 : ℝ)*X 0 0+(5138527437/10000000000 : ℝ)*X 0 1+(1961664361/5000000000 : ℝ)*X 0 2+(30088437/78125000 : ℝ)*X 1 0+(5138527437/10000000000 : ℝ)*X 1 1+(1961664361/5000000000 : ℝ)*X 1 2+(30088437/78125000 : ℝ)*X 2 0+(5138527437/10000000000 : ℝ)*X 2 1+(1961664361/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307080_s2_s2_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((-962399969/2500000000 : ℝ)*X 0 0+(5538695681/10000000000 : ℝ)*X 0 1+(695417267/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307080_s2_s2_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((5795347809/10000000000 : ℝ)*X 1 0+(-367173653/5000000000 : ℝ)*X 1 1+(1419697209/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307080_s2_s2_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((2854088641/10000000000 : ℝ)*X 2 0+(5956566631/10000000000 : ℝ)*X 2 1+(-3962795481/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307080_s2_s2_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_19 : ((1182408483/2500000000 : ℝ)*X 0 0+(4754738833/10000000000 : ℝ)*X 0 1+(684569327/2000000000 : ℝ)*X 0 2+(1182408483/2500000000 : ℝ)*X 1 0+(4754738833/10000000000 : ℝ)*X 1 1+(684569327/2000000000 : ℝ)*X 1 2+(1182408483/2500000000 : ℝ)*X 2 0+(4754738833/10000000000 : ℝ)*X 2 1+(684569327/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307080_s2_s2_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((-2958599367/10000000000 : ℝ)*X 0 0+(5833912767/10000000000 : ℝ)*X 0 1+(2003159967/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307080_s2_s2_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((6881491547/10000000000 : ℝ)*X 1 0+(-37431407/2500000000 : ℝ)*X 1 1+(1198873117/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307080_s2_s2_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((631321651/2500000000 : ℝ)*X 2 0+(6669949549/10000000000 : ℝ)*X 2 1+(-106861229/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307080_s2_s2_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_25 : ((5011512679/10000000000 : ℝ)*X 0 0+(4403689467/10000000000 : ℝ)*X 0 1+(3492363703/10000000000 : ℝ)*X 0 2+(5011512679/10000000000 : ℝ)*X 1 0+(4403689467/10000000000 : ℝ)*X 1 1+(3492363703/10000000000 : ℝ)*X 1 2+(5011512679/10000000000 : ℝ)*X 2 0+(4403689467/10000000000 : ℝ)*X 2 1+(3492363703/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307080_s2_s2_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((2939/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2939/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (31937713934270548367413210797663/2068175462174500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1381853/200000000000 : ℝ)*(base19) + (1657911/500000000000 : ℝ)*(base40) + (1477920537121/500000000000 : ℝ)*(base49) + (1206770450753/1000000000000 : ℝ)*(base50) + (405471/200000000000 : ℝ)*(base60) + (5567476381741/1000000000000 : ℝ)*(major_s2_0) + (5567476381741/1000000000000 : ℝ)*(major_s2_1) + (5567476381741/1000000000000 : ℝ)*(major_s2_2) + (1510675851521/200000000000 : ℝ)*(sp_s2_7) + (472079772981/62500000000 : ℝ)*(sp_s2_8) + (3776567485347/500000000000 : ℝ)*(sp_s2_9) + (223848022399/62500000000 : ℝ)*(sp_s2_12) + (95980643/1000000000000 : ℝ)*(sp_s2_14) + (244286911/1000000000000 : ℝ)*(sp_s2_22) + (223848022399/62500000000 : ℝ)*(f.failure) + (1510675851521/200000000000 : ℝ)*(f.sum) + (121928567499351706579/241927236400000000000000000000000 : ℝ)*base63 + (1138223557790527/7675600000000000000000000000 : ℝ)*base64 + (1805684300172243/3151900000000000000000000000 : ℝ)*base67 + (9711141747790173/7675600000000000000000000000 : ℝ)*base69 + (104125006344278408963/262467142000000000000000000000000 : ℝ)*base70 + (5461886400980119/6839000000000000000000000000 : ℝ)*base73 + (532527022720951/1575950000000000000000000000 : ℝ)*base75 + (1742985416144109/6839000000000000000000000000 : ℝ)*base77 + (70271550087499422631/215558441000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (749/3125000000000000 : ℝ)*base86 + (749/3125000000000000 : ℝ)*base88 + (749/3125000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((5779/100000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(5779/100000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4388249943085113992817049036593/413635092434900000000000000000000000 : ℝ) := by norm_num
    linear_combination (219944537077/1000000000000 : ℝ)*(base40) + (1001618250913/1000000000000 : ℝ)*(base49) + (157063/62500000000 : ℝ)*(base60) + (661545647241/200000000000 : ℝ)*(major_s2_0) + (661545647241/200000000000 : ℝ)*(major_s2_1) + (661545647241/200000000000 : ℝ)*(major_s2_2) + (52634957/1000000000000 : ℝ)*(sp_s2_6) + (8897147/1000000000000 : ℝ)*(sp_s2_7) + (19002781/500000000000 : ℝ)*(sp_s2_8) + (4487576046927/1000000000000 : ℝ)*(sp_s2_13) + (4487546938513/1000000000000 : ℝ)*(sp_s2_14) + (2243792472037/500000000000 : ℝ)*(sp_s2_15) + (1063782114259/500000000000 : ℝ)*(sp_s2_19) + (10045141/40000000000 : ℝ)*(sp_s2_25) + (2127867992001/1000000000000 : ℝ)*(f.failure) + (2243792472037/500000000000 : ℝ)*(f.sum) + (460098620758491281/1935417891200000000000000000000 : ℝ)*base62 + (906096135937021/1535120000000000000000000000 : ℝ)*base65 + (133060961535513/630380000000000000000000000 : ℝ)*base67 + (169187096685387/307024000000000000000000000 : ℝ)*base68 + (23247349959376238177/52493428400000000000000000000000 : ℝ)*base71 + (261100317545381/1367800000000000000000000000 : ℝ)*base72 + (35822026202689/315190000000000000000000000 : ℝ)*base75 + (263139420085729/1367800000000000000000000000 : ℝ)*base77 + (10873001506979649931/43111688200000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (8931/12500000000000000 : ℝ)*base87 + (8931/12500000000000000 : ℝ)*base89 + (8931/12500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3543/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3543/10000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1613655301956970168395102350877/206817546217450000000000000000000000 : ℝ) := by norm_num
    linear_combination (13107761/1000000000000 : ℝ)*(base15) + (744621039339/1000000000000 : ℝ)*(base40) + (3001415534493/1000000000000 : ℝ)*(base49) + (1011643973807/1000000000000 : ℝ)*(base50) + (604265483279/100000000000 : ℝ)*(major_s2_0) + (604265483279/100000000000 : ℝ)*(major_s2_1) + (604265483279/100000000000 : ℝ)*(major_s2_2) + (9573669/500000000000 : ℝ)*(sp_s2_1) + (86518277/1000000000000 : ℝ)*(sp_s2_9) + (45243319/1000000000000 : ℝ)*(sp_s2_19) + (4099027743459/500000000000 : ℝ)*(sp_s2_20) + (8198023231819/1000000000000 : ℝ)*(sp_s2_21) + (8197968968641/1000000000000 : ℝ)*(sp_s2_22) + (777441266913/200000000000 : ℝ)*(sp_s2_25) + (971812894471/250000000000 : ℝ)*(f.failure) + (4099027743459/500000000000 : ℝ)*(f.sum) + (3579144310227973573/24192723640000000000000000000000 : ℝ)*base63 + (176521277586779/767560000000000000000000000 : ℝ)*base65 + (156102837801379/315190000000000000000000000 : ℝ)*base67 + (81602229796639/767560000000000000000000000 : ℝ)*base69 + (15449984726524450983/26246714200000000000000000000000 : ℝ)*base71 + (31195100436779/683900000000000000000000000 : ℝ)*base72 + (42084995731479/315190000000000000000000000 : ℝ)*base75 + (394091918397021/683900000000000000000000000 : ℝ)*base77 + (3476208071417061909/21555844100000000000000000000000 : ℝ)*base79 + (2749/3125000000000000 : ℝ)*base86 + (2749/3125000000000000 : ℝ)*base88 + (2749/3125000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((6839/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6839/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((31519/100000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(31519/100000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19189/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19189/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2939/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2939/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((5779/100000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(5779/100000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3543/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3543/10000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c307080_s2 p hpa hpb X hX hprev1

#print axioms solution
