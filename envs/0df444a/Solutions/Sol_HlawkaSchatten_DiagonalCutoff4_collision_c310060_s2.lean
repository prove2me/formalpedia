-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c310060_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:28:00.026699+00:00
-- url     : https://prove2.me/submissions/1bed5d94-6539-47a2-8589-79d7b2425e9d

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
theorem collision_support_c310060_s2_s2_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2112150607/10000000000 : ℝ)*x 0 + (826384147/2000000000 : ℝ)*x 1 + (-1251767251/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2112150607/10000000000 : ℝ)^71 ≤ (2687269403667/20000000000000 : ℝ)^55 := by
    have hnat : (2112150607 : ℕ)^71*20000000000000^55 ≤ 2687269403667^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112150607 10000000000 2687269403667 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (826384147/2000000000 : ℝ)^71 ≤ (6390238967253/20000000000000 : ℝ)^55 := by
    have hnat : (826384147 : ℕ)^71*20000000000000^55 ≤ 6390238967253^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      826384147 2000000000 6390238967253 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1251767251/2000000000 : ℝ)^71 ≤ (27306229064893/50000000000000 : ℝ)^55 := by
    have hnat : (1251767251 : ℕ)^71*50000000000000^55 ≤ 27306229064893^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1251767251 2000000000 27306229064893 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2112150607/10000000000 : ℝ), (826384147/2000000000 : ℝ), (-1251767251/2000000000 : ℝ)] ![(2687269403667/20000000000000 : ℝ), (6390238967253/20000000000000 : ℝ), (27306229064893/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2112150607/10000000000 : ℝ)|^71 ≤ (2687269403667/20000000000000 : ℝ)^55
        have hw : |(-2112150607/10000000000 : ℝ)|=(2112150607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(826384147/2000000000 : ℝ)|^71 ≤ (6390238967253/20000000000000 : ℝ)^55
        have hw : |(826384147/2000000000 : ℝ)|=(826384147/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1251767251/2000000000 : ℝ)|^71 ≤ (27306229064893/50000000000000 : ℝ)^55
        have hw : |(-1251767251/2000000000 : ℝ)|=(1251767251/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310060_s2_s2_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4701582139/10000000000 : ℝ)*x 0 + (2920483807/5000000000 : ℝ)*x 1 + (394474873/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4701582139/10000000000 : ℝ)^71 ≤ (9437062789319/25000000000000 : ℝ)^55 := by
    have hnat : (4701582139 : ℕ)^71*25000000000000^55 ≤ 9437062789319^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4701582139 10000000000 9437062789319 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2920483807/5000000000 : ℝ)^71 ≤ (49952025511851/100000000000000 : ℝ)^55 := by
    have hnat : (2920483807 : ℕ)^71*100000000000000^55 ≤ 49952025511851^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2920483807 5000000000 49952025511851 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (394474873/2000000000 : ℝ)^71 ≤ (1229972331221/10000000000000 : ℝ)^55 := by
    have hnat : (394474873 : ℕ)^71*10000000000000^55 ≤ 1229972331221^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394474873 2000000000 1229972331221 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4701582139/10000000000 : ℝ), (2920483807/5000000000 : ℝ), (394474873/2000000000 : ℝ)] ![(9437062789319/25000000000000 : ℝ), (49952025511851/100000000000000 : ℝ), (1229972331221/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4701582139/10000000000 : ℝ)|^71 ≤ (9437062789319/25000000000000 : ℝ)^55
        have hw : |(4701582139/10000000000 : ℝ)|=(4701582139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2920483807/5000000000 : ℝ)|^71 ≤ (49952025511851/100000000000000 : ℝ)^55
        have hw : |(2920483807/5000000000 : ℝ)|=(2920483807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(394474873/2000000000 : ℝ)|^71 ≤ (1229972331221/10000000000000 : ℝ)^55
        have hw : |(394474873/2000000000 : ℝ)|=(394474873/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310060_s2_s2_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6885556053/10000000000 : ℝ)*x 0 + (535008709/1250000000 : ℝ)*x 1 + (-1519993/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6885556053/10000000000 : ℝ)^71 ≤ (61772333171639/100000000000000 : ℝ)^55 := by
    have hnat : (6885556053 : ℕ)^71*100000000000000^55 ≤ 61772333171639^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6885556053 10000000000 61772333171639 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (535008709/1250000000 : ℝ)^71 ≤ (33437710788387/100000000000000 : ℝ)^55 := by
    have hnat : (535008709 : ℕ)^71*100000000000000^55 ≤ 33437710788387^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535008709 1250000000 33437710788387 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1519993/16000000 : ℝ)^71 ≤ (4789956029967/100000000000000 : ℝ)^55 := by
    have hnat : (1519993 : ℕ)^71*100000000000000^55 ≤ 4789956029967^55*16000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1519993 16000000 4789956029967 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6885556053/10000000000 : ℝ), (535008709/1250000000 : ℝ), (-1519993/16000000 : ℝ)] ![(61772333171639/100000000000000 : ℝ), (33437710788387/100000000000000 : ℝ), (4789956029967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6885556053/10000000000 : ℝ)|^71 ≤ (61772333171639/100000000000000 : ℝ)^55
        have hw : |(6885556053/10000000000 : ℝ)|=(6885556053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(535008709/1250000000 : ℝ)|^71 ≤ (33437710788387/100000000000000 : ℝ)^55
        have hw : |(535008709/1250000000 : ℝ)|=(535008709/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1519993/16000000 : ℝ)|^71 ≤ (4789956029967/100000000000000 : ℝ)^55
        have hw : |(-1519993/16000000 : ℝ)|=(1519993/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310060_s2_s2_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1913872223/10000000000 : ℝ)*x 0 + (478519399/1250000000 : ℝ)*x 1 + (-6663885793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1913872223/10000000000 : ℝ)^71 ≤ (2366164209759/20000000000000 : ℝ)^55 := by
    have hnat : (1913872223 : ℕ)^71*20000000000000^55 ≤ 2366164209759^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1913872223 10000000000 2366164209759 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (478519399/1250000000 : ℝ)^71 ≤ (904747563421/3125000000000 : ℝ)^55 := by
    have hnat : (478519399 : ℕ)^71*3125000000000^55 ≤ 904747563421^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478519399 1250000000 904747563421 3125000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6663885793/10000000000 : ℝ)^71 ≤ (29608628455337/50000000000000 : ℝ)^55 := by
    have hnat : (6663885793 : ℕ)^71*50000000000000^55 ≤ 29608628455337^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6663885793 10000000000 29608628455337 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1913872223/10000000000 : ℝ), (478519399/1250000000 : ℝ), (-6663885793/10000000000 : ℝ)] ![(2366164209759/20000000000000 : ℝ), (904747563421/3125000000000 : ℝ), (29608628455337/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1913872223/10000000000 : ℝ)|^71 ≤ (2366164209759/20000000000000 : ℝ)^55
        have hw : |(-1913872223/10000000000 : ℝ)|=(1913872223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(478519399/1250000000 : ℝ)|^71 ≤ (904747563421/3125000000000 : ℝ)^55
        have hw : |(478519399/1250000000 : ℝ)|=(478519399/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6663885793/10000000000 : ℝ)|^71 ≤ (29608628455337/50000000000000 : ℝ)^55
        have hw : |(-6663885793/10000000000 : ℝ)|=(6663885793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310060_s2_s2_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4111650701/10000000000 : ℝ)*x 0 + (-1537754229/10000000000 : ℝ)*x 1 + (-1334766967/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4111650701/10000000000 : ℝ)^71 ≤ (31748997750131/100000000000000 : ℝ)^55 := by
    have hnat : (4111650701 : ℕ)^71*100000000000000^55 ≤ 31748997750131^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4111650701 10000000000 31748997750131 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1537754229/10000000000 : ℝ)^71 ≤ (8919591111569/100000000000000 : ℝ)^55 := by
    have hnat : (1537754229 : ℕ)^71*100000000000000^55 ≤ 8919591111569^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1537754229 10000000000 8919591111569 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1334766967/2000000000 : ℝ)^71 ≤ (14832852780119/25000000000000 : ℝ)^55 := by
    have hnat : (1334766967 : ℕ)^71*25000000000000^55 ≤ 14832852780119^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1334766967 2000000000 14832852780119 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4111650701/10000000000 : ℝ), (-1537754229/10000000000 : ℝ), (-1334766967/2000000000 : ℝ)] ![(31748997750131/100000000000000 : ℝ), (8919591111569/100000000000000 : ℝ), (14832852780119/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4111650701/10000000000 : ℝ)|^71 ≤ (31748997750131/100000000000000 : ℝ)^55
        have hw : |(4111650701/10000000000 : ℝ)|=(4111650701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1537754229/10000000000 : ℝ)|^71 ≤ (8919591111569/100000000000000 : ℝ)^55
        have hw : |(-1537754229/10000000000 : ℝ)|=(1537754229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1334766967/2000000000 : ℝ)|^71 ≤ (14832852780119/25000000000000 : ℝ)^55
        have hw : |(-1334766967/2000000000 : ℝ)|=(1334766967/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310060_s2_s2_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1086126287/2500000000 : ℝ)*x 0 + (169228267/250000000 : ℝ)*x 1 + (1054936717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086126287/2500000000 : ℝ)^71 ≤ (17044484352473/50000000000000 : ℝ)^55 := by
    have hnat : (1086126287 : ℕ)^71*50000000000000^55 ≤ 17044484352473^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086126287 2500000000 17044484352473 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169228267/250000000 : ℝ)^71 ≤ (30213663096641/50000000000000 : ℝ)^55 := by
    have hnat : (169228267 : ℕ)^71*50000000000000^55 ≤ 30213663096641^55*250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169228267 250000000 30213663096641 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054936717/10000000000 : ℝ)^71 ≤ (548370508853/10000000000000 : ℝ)^55 := by
    have hnat : (1054936717 : ℕ)^71*10000000000000^55 ≤ 548370508853^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054936717 10000000000 548370508853 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1086126287/2500000000 : ℝ), (169228267/250000000 : ℝ), (1054936717/10000000000 : ℝ)] ![(17044484352473/50000000000000 : ℝ), (30213663096641/50000000000000 : ℝ), (548370508853/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1086126287/2500000000 : ℝ)|^71 ≤ (17044484352473/50000000000000 : ℝ)^55
        have hw : |(1086126287/2500000000 : ℝ)|=(1086126287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169228267/250000000 : ℝ)|^71 ≤ (30213663096641/50000000000000 : ℝ)^55
        have hw : |(169228267/250000000 : ℝ)|=(169228267/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1054936717/10000000000 : ℝ)|^71 ≤ (548370508853/10000000000000 : ℝ)^55
        have hw : |(1054936717/10000000000 : ℝ)|=(1054936717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310060_s2_s2_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1599230109/2500000000 : ℝ)*x 0 + (1045269791/2000000000 : ℝ)*x 1 + (-178634211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1599230109/2500000000 : ℝ)^71 ≤ (56172808005931/100000000000000 : ℝ)^55 := by
    have hnat : (1599230109 : ℕ)^71*100000000000000^55 ≤ 56172808005931^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1599230109 2500000000 56172808005931 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1045269791/2000000000 : ℝ)^71 ≤ (43273274264843/100000000000000 : ℝ)^55 := by
    have hnat : (1045269791 : ℕ)^71*100000000000000^55 ≤ 43273274264843^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045269791 2000000000 43273274264843 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (178634211/10000000000 : ℝ)^71 ≤ (138479429661/25000000000000 : ℝ)^55 := by
    have hnat : (178634211 : ℕ)^71*25000000000000^55 ≤ 138479429661^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      178634211 10000000000 138479429661 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1599230109/2500000000 : ℝ), (1045269791/2000000000 : ℝ), (-178634211/10000000000 : ℝ)] ![(56172808005931/100000000000000 : ℝ), (43273274264843/100000000000000 : ℝ), (138479429661/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1599230109/2500000000 : ℝ)|^71 ≤ (56172808005931/100000000000000 : ℝ)^55
        have hw : |(1599230109/2500000000 : ℝ)|=(1599230109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1045269791/2000000000 : ℝ)|^71 ≤ (43273274264843/100000000000000 : ℝ)^55
        have hw : |(1045269791/2000000000 : ℝ)|=(1045269791/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-178634211/10000000000 : ℝ)|^71 ≤ (138479429661/25000000000000 : ℝ)^55
        have hw : |(-178634211/10000000000 : ℝ)|=(178634211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310060_s2_s2_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1215204729/10000000000 : ℝ)*x 0 + (4370498791/10000000000 : ℝ)*x 1 + (-1662660879/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1215204729/10000000000 : ℝ)^71 ≤ (1316423572871/20000000000000 : ℝ)^55 := by
    have hnat : (1215204729 : ℕ)^71*20000000000000^55 ≤ 1316423572871^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1215204729 10000000000 1316423572871 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4370498791/10000000000 : ℝ)^71 ≤ (8588122180853/25000000000000 : ℝ)^55 := by
    have hnat : (4370498791 : ℕ)^71*25000000000000^55 ≤ 8588122180853^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370498791 10000000000 8588122180853 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1662660879/2500000000 : ℝ)^71 ≤ (59065393391067/100000000000000 : ℝ)^55 := by
    have hnat : (1662660879 : ℕ)^71*100000000000000^55 ≤ 59065393391067^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1662660879 2500000000 59065393391067 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1215204729/10000000000 : ℝ), (4370498791/10000000000 : ℝ), (-1662660879/2500000000 : ℝ)] ![(1316423572871/20000000000000 : ℝ), (8588122180853/25000000000000 : ℝ), (59065393391067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1215204729/10000000000 : ℝ)|^71 ≤ (1316423572871/20000000000000 : ℝ)^55
        have hw : |(-1215204729/10000000000 : ℝ)|=(1215204729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4370498791/10000000000 : ℝ)|^71 ≤ (8588122180853/25000000000000 : ℝ)^55
        have hw : |(4370498791/10000000000 : ℝ)|=(4370498791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1662660879/2500000000 : ℝ)|^71 ≤ (59065393391067/100000000000000 : ℝ)^55
        have hw : |(-1662660879/2500000000 : ℝ)|=(1662660879/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310060_s2_s2_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4088536323/10000000000 : ℝ)*x 0 + (-79427413/500000000 : ℝ)*x 1 + (-1665148083/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4088536323/10000000000 : ℝ)^71 ≤ (787969538011/2500000000000 : ℝ)^55 := by
    have hnat : (4088536323 : ℕ)^71*2500000000000^55 ≤ 787969538011^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4088536323 10000000000 787969538011 2500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (79427413/500000000 : ℝ)^71 ≤ (2325434859293/25000000000000 : ℝ)^55 := by
    have hnat : (79427413 : ℕ)^71*25000000000000^55 ≤ 2325434859293^55*500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79427413 500000000 2325434859293 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1665148083/2500000000 : ℝ)^71 ≤ (59179479020499/100000000000000 : ℝ)^55 := by
    have hnat : (1665148083 : ℕ)^71*100000000000000^55 ≤ 59179479020499^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1665148083 2500000000 59179479020499 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4088536323/10000000000 : ℝ), (-79427413/500000000 : ℝ), (-1665148083/2500000000 : ℝ)] ![(787969538011/2500000000000 : ℝ), (2325434859293/25000000000000 : ℝ), (59179479020499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4088536323/10000000000 : ℝ)|^71 ≤ (787969538011/2500000000000 : ℝ)^55
        have hw : |(4088536323/10000000000 : ℝ)|=(4088536323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-79427413/500000000 : ℝ)|^71 ≤ (2325434859293/25000000000000 : ℝ)^55
        have hw : |(-79427413/500000000 : ℝ)|=(79427413/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1665148083/2500000000 : ℝ)|^71 ≤ (59179479020499/100000000000000 : ℝ)^55
        have hw : |(-1665148083/2500000000 : ℝ)|=(1665148083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310060_s2_s2_16 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5663906379/10000000000 : ℝ)*x 0 + (110370561/200000000 : ℝ)*x 1 + (1068178981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5663906379/10000000000 : ℝ)^71 ≤ (6000746746749/12500000000000 : ℝ)^55 := by
    have hnat : (5663906379 : ℕ)^71*12500000000000^55 ≤ 6000746746749^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5663906379 10000000000 6000746746749 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (110370561/200000000 : ℝ)^71 ≤ (46421299310441/100000000000000 : ℝ)^55 := by
    have hnat : (110370561 : ℕ)^71*100000000000000^55 ≤ 46421299310441^55*200000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110370561 200000000 46421299310441 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1068178981/10000000000 : ℝ)^71 ≤ (5572726705301/100000000000000 : ℝ)^55 := by
    have hnat : (1068178981 : ℕ)^71*100000000000000^55 ≤ 5572726705301^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068178981 10000000000 5572726705301 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5663906379/10000000000 : ℝ), (110370561/200000000 : ℝ), (1068178981/10000000000 : ℝ)] ![(6000746746749/12500000000000 : ℝ), (46421299310441/100000000000000 : ℝ), (5572726705301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5663906379/10000000000 : ℝ)|^71 ≤ (6000746746749/12500000000000 : ℝ)^55
        have hw : |(5663906379/10000000000 : ℝ)|=(5663906379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(110370561/200000000 : ℝ)|^71 ≤ (46421299310441/100000000000000 : ℝ)^55
        have hw : |(110370561/200000000 : ℝ)|=(110370561/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1068178981/10000000000 : ℝ)|^71 ≤ (5572726705301/100000000000000 : ℝ)^55
        have hw : |(1068178981/10000000000 : ℝ)|=(1068178981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310060_s2_s2_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (783647567/1000000000 : ℝ)*x 0 + (3556266277/10000000000 : ℝ)*x 1 + (-104120977/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (783647567/1000000000 : ℝ)^71 ≤ (36499723041273/50000000000000 : ℝ)^55 := by
    have hnat : (783647567 : ℕ)^71*50000000000000^55 ≤ 36499723041273^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      783647567 1000000000 36499723041273 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3556266277/10000000000 : ℝ)^71 ≤ (205666924407/781250000000 : ℝ)^55 := by
    have hnat : (3556266277 : ℕ)^71*781250000000^55 ≤ 205666924407^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3556266277 10000000000 205666924407 781250000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104120977/5000000000 : ℝ)^71 ≤ (135037515311/20000000000000 : ℝ)^55 := by
    have hnat : (104120977 : ℕ)^71*20000000000000^55 ≤ 135037515311^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104120977 5000000000 135037515311 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(783647567/1000000000 : ℝ), (3556266277/10000000000 : ℝ), (-104120977/5000000000 : ℝ)] ![(36499723041273/50000000000000 : ℝ), (205666924407/781250000000 : ℝ), (135037515311/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(783647567/1000000000 : ℝ)|^71 ≤ (36499723041273/50000000000000 : ℝ)^55
        have hw : |(783647567/1000000000 : ℝ)|=(783647567/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3556266277/10000000000 : ℝ)|^71 ≤ (205666924407/781250000000 : ℝ)^55
        have hw : |(3556266277/10000000000 : ℝ)|=(3556266277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-104120977/5000000000 : ℝ)|^71 ≤ (135037515311/20000000000000 : ℝ)^55
        have hw : |(-104120977/5000000000 : ℝ)|=(104120977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310060_s2_s2_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-58043263/625000000 : ℝ)*x 0 + (5271184041/10000000000 : ℝ)*x 1 + (-299462979/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (58043263/625000000 : ℝ)^71 ≤ (2325874783293/50000000000000 : ℝ)^55 := by
    have hnat : (58043263 : ℕ)^71*50000000000000^55 ≤ 2325874783293^55*625000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58043263 625000000 2325874783293 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5271184041/10000000000 : ℝ)^71 ≤ (10938272781089/25000000000000 : ℝ)^55 := by
    have hnat : (5271184041 : ℕ)^71*25000000000000^55 ≤ 10938272781089^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271184041 10000000000 10938272781089 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (299462979/500000000 : ℝ)^71 ≤ (25797579648899/50000000000000 : ℝ)^55 := by
    have hnat : (299462979 : ℕ)^71*50000000000000^55 ≤ 25797579648899^55*500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299462979 500000000 25797579648899 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-58043263/625000000 : ℝ), (5271184041/10000000000 : ℝ), (-299462979/500000000 : ℝ)] ![(2325874783293/50000000000000 : ℝ), (10938272781089/25000000000000 : ℝ), (25797579648899/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-58043263/625000000 : ℝ)|^71 ≤ (2325874783293/50000000000000 : ℝ)^55
        have hw : |(-58043263/625000000 : ℝ)|=(58043263/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5271184041/10000000000 : ℝ)|^71 ≤ (10938272781089/25000000000000 : ℝ)^55
        have hw : |(5271184041/10000000000 : ℝ)|=(5271184041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-299462979/500000000 : ℝ)|^71 ≤ (25797579648899/50000000000000 : ℝ)^55
        have hw : |(-299462979/500000000 : ℝ)|=(299462979/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310060_s2_s2_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1143512929/2000000000 : ℝ)*x 0 + (-278014457/2000000000 : ℝ)*x 1 + (-5254698459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1143512929/2000000000 : ℝ)^71 ≤ (48593880422269/100000000000000 : ℝ)^55 := by
    have hnat : (1143512929 : ℕ)^71*100000000000000^55 ≤ 48593880422269^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1143512929 2000000000 48593880422269 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (278014457/2000000000 : ℝ)^71 ≤ (3914796338679/50000000000000 : ℝ)^55 := by
    have hnat : (278014457 : ℕ)^71*50000000000000^55 ≤ 3914796338679^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278014457 2000000000 3914796338679 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254698459/10000000000 : ℝ)^71 ≤ (21788263442203/50000000000000 : ℝ)^55 := by
    have hnat : (5254698459 : ℕ)^71*50000000000000^55 ≤ 21788263442203^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254698459 10000000000 21788263442203 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1143512929/2000000000 : ℝ), (-278014457/2000000000 : ℝ), (-5254698459/10000000000 : ℝ)] ![(48593880422269/100000000000000 : ℝ), (3914796338679/50000000000000 : ℝ), (21788263442203/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1143512929/2000000000 : ℝ)|^71 ≤ (48593880422269/100000000000000 : ℝ)^55
        have hw : |(1143512929/2000000000 : ℝ)|=(1143512929/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-278014457/2000000000 : ℝ)|^71 ≤ (3914796338679/50000000000000 : ℝ)^55
        have hw : |(-278014457/2000000000 : ℝ)|=(278014457/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5254698459/10000000000 : ℝ)|^71 ≤ (21788263442203/50000000000000 : ℝ)^55
        have hw : |(-5254698459/10000000000 : ℝ)|=(5254698459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310060_s2_s2_23 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2100034157/5000000000 : ℝ)*x 0 + (639059101/1000000000 : ℝ)*x 1 + (1842683159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2100034157/5000000000 : ℝ)^71 ≤ (32633090303163/100000000000000 : ℝ)^55 := by
    have hnat : (2100034157 : ℕ)^71*100000000000000^55 ≤ 32633090303163^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100034157 5000000000 32633090303163 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (639059101/1000000000 : ℝ)^71 ≤ (28050534723501/50000000000000 : ℝ)^55 := by
    have hnat : (639059101 : ℕ)^71*50000000000000^55 ≤ 28050534723501^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      639059101 1000000000 28050534723501 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1842683159/10000000000 : ℝ)^71 ≤ (35205750721/312500000000 : ℝ)^55 := by
    have hnat : (1842683159 : ℕ)^71*312500000000^55 ≤ 35205750721^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1842683159 10000000000 35205750721 312500000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2100034157/5000000000 : ℝ), (639059101/1000000000 : ℝ), (1842683159/10000000000 : ℝ)] ![(32633090303163/100000000000000 : ℝ), (28050534723501/50000000000000 : ℝ), (35205750721/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2100034157/5000000000 : ℝ)|^71 ≤ (32633090303163/100000000000000 : ℝ)^55
        have hw : |(2100034157/5000000000 : ℝ)|=(2100034157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(639059101/1000000000 : ℝ)|^71 ≤ (28050534723501/50000000000000 : ℝ)^55
        have hw : |(639059101/1000000000 : ℝ)|=(639059101/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1842683159/10000000000 : ℝ)|^71 ≤ (35205750721/312500000000 : ℝ)^55
        have hw : |(1842683159/10000000000 : ℝ)|=(1842683159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310060_s2_s2_27 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (202693377/250000000 : ℝ)*x 0 + (3176496827/10000000000 : ℝ)*x 1 + (-34413007/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (202693377/250000000 : ℝ)^71 ≤ (76277701969807/100000000000000 : ℝ)^55 := by
    have hnat : (202693377 : ℕ)^71*100000000000000^55 ≤ 76277701969807^55*250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202693377 250000000 76277701969807 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3176496827/10000000000 : ℝ)^71 ≤ (22754154111683/100000000000000 : ℝ)^55 := by
    have hnat : (3176496827 : ℕ)^71*100000000000000^55 ≤ 22754154111683^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3176496827 10000000000 22754154111683 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34413007/1250000000 : ℝ)^71 ≤ (968143902347/100000000000000 : ℝ)^55 := by
    have hnat : (34413007 : ℕ)^71*100000000000000^55 ≤ 968143902347^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34413007 1250000000 968143902347 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(202693377/250000000 : ℝ), (3176496827/10000000000 : ℝ), (-34413007/1250000000 : ℝ)] ![(76277701969807/100000000000000 : ℝ), (22754154111683/100000000000000 : ℝ), (968143902347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(202693377/250000000 : ℝ)|^71 ≤ (76277701969807/100000000000000 : ℝ)^55
        have hw : |(202693377/250000000 : ℝ)|=(202693377/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3176496827/10000000000 : ℝ)|^71 ≤ (22754154111683/100000000000000 : ℝ)^55
        have hw : |(3176496827/10000000000 : ℝ)|=(3176496827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-34413007/1250000000 : ℝ)|^71 ≤ (968143902347/100000000000000 : ℝ)^55
        have hw : |(-34413007/1250000000 : ℝ)|=(34413007/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310060_s2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev1 : (0 : ℝ) ≤ ((15067/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15067/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(75991/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(75991/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-16129/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-16129/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((47921/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(47921/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(26153/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(26153/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-36073/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-36073/100000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base18 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  have s2_pow0 : (15067/20000 : ℝ) ^ (35/8 : ℝ) ≤ (28964161985144802931/100000000000000000000 : ℝ) := by
    have hpowers : (15067/20000 : ℝ)^35 ≤ (28964161985144802931/100000000000000000000 : ℝ)^8 := by
      have hnat : (15067 : ℕ)^35*100000000000000000000^8 ≤ 28964161985144802931^8*20000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15067 20000 28964161985144802931 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15067/20000 : ℝ)) (X := (28964161985144802931/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner0a : (128964161985144802931/100000000000000000000 : ℝ) ≤ (5299319090857361/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (128964161985144802931/100000000000000000000 : ℝ)^8 ≤ (5299319090857361/5000000000000000 : ℝ)^35 := by
      have hnat : (128964161985144802931 : ℕ)^8*5000000000000000^35 ≤ 5299319090857361^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        128964161985144802931 100000000000000000000 5299319090857361 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5299319090857361/5000000000000000 : ℝ)) (X := (128964161985144802931/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner0b : (78964161985144802931/50000000000000000000 : ℝ) ≤ (5550502416743181/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (78964161985144802931/50000000000000000000 : ℝ)^8 ≤ (5550502416743181/5000000000000000 : ℝ)^35 := by
      have hnat : (78964161985144802931 : ℕ)^8*5000000000000000^35 ≤ 5550502416743181^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        78964161985144802931 50000000000000000000 5550502416743181 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5550502416743181/5000000000000000 : ℝ)) (X := (78964161985144802931/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(299319090857361/3766750000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(12559166294291/188337500000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (15067/20000 : ℝ)) (alpha := (299319090857361/3766750000000000 : ℝ)) (beta := (12559166294291/188337500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (15067/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(299319090857361/3766750000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(12559166294291/188337500000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (75991/100000 : ℝ) ^ (35/8 : ℝ) ≤ (117515318789293487/390625000000000000 : ℝ) := by
    have hpowers : (75991/100000 : ℝ)^35 ≤ (117515318789293487/390625000000000000 : ℝ)^8 := by
      have hnat : (75991 : ℕ)^35*390625000000000000^8 ≤ 117515318789293487^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        75991 100000 117515318789293487 390625000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (75991/100000 : ℝ)) (X := (117515318789293487/390625000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner1a : (508140318789293487/390625000000000000 : ℝ) ≤ (663725148861053/625000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (508140318789293487/390625000000000000 : ℝ)^8 ≤ (663725148861053/625000000000000 : ℝ)^35 := by
      have hnat : (508140318789293487 : ℕ)^8*625000000000000^35 ≤ 663725148861053^35*390625000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        508140318789293487 390625000000000000 663725148861053 625000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (663725148861053/625000000000000 : ℝ)) (X := (508140318789293487/390625000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner1b : (312827818789293487/195312500000000000 : ℝ) ≤ (5568395568802483/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (312827818789293487/195312500000000000 : ℝ)^8 ≤ (5568395568802483/5000000000000000 : ℝ)^35 := by
      have hnat : (312827818789293487 : ℕ)^8*5000000000000000^35 ≤ 5568395568802483^35*195312500000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        312827818789293487 195312500000000000 5568395568802483 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5568395568802483/5000000000000000 : ℝ)) (X := (312827818789293487/195312500000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(38725148861053/474943750000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(258594377914059/3799550000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (75991/100000 : ℝ)) (alpha := (38725148861053/474943750000000 : ℝ)) (beta := (258594377914059/3799550000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (75991/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(38725148861053/474943750000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(258594377914059/3799550000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (16129/25000 : ℝ) ^ (35/8 : ℝ) ≤ (14699244724154883897/100000000000000000000 : ℝ) := by
    have hpowers : (16129/25000 : ℝ)^35 ≤ (14699244724154883897/100000000000000000000 : ℝ)^8 := by
      have hnat : (16129 : ℕ)^35*100000000000000000000^8 ≤ 14699244724154883897^8*25000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16129 25000 14699244724154883897 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16129/25000 : ℝ)) (X := (14699244724154883897/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner2a : (114699244724154883897/100000000000000000000 : ℝ) ≤ (5159217608653343/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (114699244724154883897/100000000000000000000 : ℝ)^8 ≤ (5159217608653343/5000000000000000 : ℝ)^35 := by
      have hnat : (114699244724154883897 : ℕ)^8*5000000000000000^35 ≤ 5159217608653343^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        114699244724154883897 100000000000000000000 5159217608653343 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5159217608653343/5000000000000000 : ℝ)) (X := (114699244724154883897/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s2_corner2b : (64699244724154883897/50000000000000000000 : ℝ) ≤ (10606786291259453/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (64699244724154883897/50000000000000000000 : ℝ)^8 ≤ (10606786291259453/10000000000000000 : ℝ)^35 := by
      have hnat : (64699244724154883897 : ℕ)^8*10000000000000000^35 ≤ 10606786291259453^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64699244724154883897 50000000000000000000 10606786291259453 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10606786291259453/10000000000000000 : ℝ)) (X := (64699244724154883897/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(159217608653343/3225800000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(288351073952767/6451600000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (16129/25000 : ℝ)) (alpha := (159217608653343/3225800000000000 : ℝ)) (beta := (288351073952767/6451600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (16129/25000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(159217608653343/3225800000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(288351073952767/6451600000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-2112150607/10000000000 : ℝ)*X 0 0+(826384147/2000000000 : ℝ)*X 0 1+(-1251767251/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310060_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((4701582139/10000000000 : ℝ)*X 2 0+(2920483807/5000000000 : ℝ)*X 2 1+(394474873/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310060_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((6885556053/10000000000 : ℝ)*X 0 0+(535008709/1250000000 : ℝ)*X 0 1+(-1519993/16000000 : ℝ)*X 0 2+(6885556053/10000000000 : ℝ)*X 1 0+(535008709/1250000000 : ℝ)*X 1 1+(-1519993/16000000 : ℝ)*X 1 2+(6885556053/10000000000 : ℝ)*X 2 0+(535008709/1250000000 : ℝ)*X 2 1+(-1519993/16000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310060_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-1913872223/10000000000 : ℝ)*X 0 0+(478519399/1250000000 : ℝ)*X 0 1+(-6663885793/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310060_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((4111650701/10000000000 : ℝ)*X 1 0+(-1537754229/10000000000 : ℝ)*X 1 1+(-1334766967/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310060_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((1086126287/2500000000 : ℝ)*X 2 0+(169228267/250000000 : ℝ)*X 2 1+(1054936717/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310060_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((1599230109/2500000000 : ℝ)*X 0 0+(1045269791/2000000000 : ℝ)*X 0 1+(-178634211/10000000000 : ℝ)*X 0 2+(1599230109/2500000000 : ℝ)*X 1 0+(1045269791/2000000000 : ℝ)*X 1 1+(-178634211/10000000000 : ℝ)*X 1 2+(1599230109/2500000000 : ℝ)*X 2 0+(1045269791/2000000000 : ℝ)*X 2 1+(-178634211/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310060_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-1215204729/10000000000 : ℝ)*X 0 0+(4370498791/10000000000 : ℝ)*X 0 1+(-1662660879/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310060_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((4088536323/10000000000 : ℝ)*X 1 0+(-79427413/500000000 : ℝ)*X 1 1+(-1665148083/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310060_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((5663906379/10000000000 : ℝ)*X 2 0+(110370561/200000000 : ℝ)*X 2 1+(1068178981/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310060_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((783647567/1000000000 : ℝ)*X 0 0+(3556266277/10000000000 : ℝ)*X 0 1+(-104120977/5000000000 : ℝ)*X 0 2+(783647567/1000000000 : ℝ)*X 1 0+(3556266277/10000000000 : ℝ)*X 1 1+(-104120977/5000000000 : ℝ)*X 1 2+(783647567/1000000000 : ℝ)*X 2 0+(3556266277/10000000000 : ℝ)*X 2 1+(-104120977/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310060_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-58043263/625000000 : ℝ)*X 0 0+(5271184041/10000000000 : ℝ)*X 0 1+(-299462979/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310060_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((1143512929/2000000000 : ℝ)*X 1 0+(-278014457/2000000000 : ℝ)*X 1 1+(-5254698459/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310060_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((2100034157/5000000000 : ℝ)*X 2 0+(639059101/1000000000 : ℝ)*X 2 1+(1842683159/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310060_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((202693377/250000000 : ℝ)*X 0 0+(3176496827/10000000000 : ℝ)*X 0 1+(-34413007/1250000000 : ℝ)*X 0 2+(202693377/250000000 : ℝ)*X 1 0+(3176496827/10000000000 : ℝ)*X 1 1+(-34413007/1250000000 : ℝ)*X 1 2+(202693377/250000000 : ℝ)*X 2 0+(3176496827/10000000000 : ℝ)*X 2 1+(-34413007/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310060_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((47921/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(47921/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (55318140071961891/5000000000000000000000 : ℝ) := by norm_num
    linear_combination (375319/500000000000 : ℝ)*(base5) + (1820341/250000000000 : ℝ)*(base39) + (2365861/1000000000000 : ℝ)*(base49) + (23073204537/40000000000 : ℝ)*(base59) + (2793201202929/500000000000 : ℝ)*(major_s2_0) + (2793201202929/500000000000 : ℝ)*(major_s2_1) + (2793201202929/500000000000 : ℝ)*(major_s2_2) + (7719992655077/1000000000000 : ℝ)*(sp_s2_7) + (7718097774221/1000000000000 : ℝ)*(sp_s2_8) + (7719866614489/1000000000000 : ℝ)*(sp_s2_9) + (86320192953/25000000000 : ℝ)*(sp_s2_13) + (1876363113/1000000000000 : ℝ)*(sp_s2_15) + (18517743/1000000000000 : ℝ)*(sp_s2_22) + (63395613/500000000000 : ℝ)*(sp_s2_23) + (3452808468759/1000000000000 : ℝ)*(f.failure) + (7719992655077/1000000000000 : ℝ)*(f.sum) + (9933260601791661403/122565883900000000000000000000000 : ℝ)*base63 + (795771658845263/3225800000000000000000000000 : ℝ)*base64 + (67085346840477/3799550000000000000000000000 : ℝ)*base67 + (461936029136103/1612900000000000000000000000 : ℝ)*base68 + (28065311293268595103/243015643000000000000000000000000 : ℝ)*base71 + (44516455666049/94168750000000000000000000 : ℝ)*base73 + (43058538948293/237471875000000000000000000 : ℝ)*base74 + (252695831595381/1883375000000000000000000000 : ℝ)*base76 + (12069604151050568329/57247819850000000000000000000000 : ℝ)*base78 + (124887/100000000000000000 : ℝ)*base87 + (124887/100000000000000000 : ℝ)*base89 + (124887/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(26153/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(26153/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (19714232573366027033492847056199/2308375215901625000000000000000000000 : ℝ) := by norm_num
    linear_combination (1088747/1000000000000 : ℝ)*(base5) + (5021/40000000000 : ℝ)*(base18) + (1859144327/10000000000 : ℝ)*(base59) + (336880996937/62500000000 : ℝ)*(major_s2_0) + (336880996937/62500000000 : ℝ)*(major_s2_1) + (336880996937/62500000000 : ℝ)*(major_s2_2) + (5439917/250000000000 : ℝ)*(sp_s2_2) + (12940091/1000000000000 : ℝ)*(sp_s2_6) + (48743683/1000000000000 : ℝ)*(sp_s2_7) + (931082962739/125000000000 : ℝ)*(sp_s2_14) + (744871232007/100000000000 : ℝ)*(sp_s2_15) + (3724345887337/500000000000 : ℝ)*(sp_s2_16) + (1665669038077/500000000000 : ℝ)*(sp_s2_20) + (62252311/500000000000 : ℝ)*(sp_s2_27) + (3331476609613/1000000000000 : ℝ)*(f.failure) + (1489742489119/200000000000 : ℝ)*(f.sum) + (7456551931636375907/30641470975000000000000000000000 : ℝ)*base62 + (132695809033249/403225000000000000000000000 : ℝ)*base64 + (40656314091999/1899775000000000000000000000 : ℝ)*base67 + (258254882059021/806450000000000000000000000 : ℝ)*base68 + (9554711408815729891/30376955375000000000000000000000 : ℝ)*base70 + (11239611579207/753350000000000000000000000 : ℝ)*base72 + (1575645860355647/3799550000000000000000000000 : ℝ)*base74 + (22106686830209/117710937500000000000000000 : ℝ)*base76 + (1327818686842740951/57247819850000000000000000000000 : ℝ)*base78 + (83891/100000000000000000 : ℝ)*base86 + (83891/100000000000000000 : ℝ)*base88 + (83891/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-36073/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-36073/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6723776809841728684813730337777/710269297200500000000000000000000000 : ℝ) := by norm_num
    linear_combination (10263753/1000000000000 : ℝ)*(base11) + (80557/125000000000 : ℝ)*(base15) + (85068862727/200000000000 : ℝ)*(base39) + (126240400983/1000000000000 : ℝ)*(base59) + (4134193384917/1000000000000 : ℝ)*(major_s2_0) + (4134193384917/1000000000000 : ℝ)*(major_s2_1) + (4134193384917/1000000000000 : ℝ)*(major_s2_2) + (4749181/200000000000 : ℝ)*(sp_s2_0) + (856371/100000000000 : ℝ)*(sp_s2_2) + (8177619/125000000000 : ℝ)*(sp_s2_9) + (1142622671063/200000000000 : ℝ)*(sp_s2_21) + (5713146720517/1000000000000 : ℝ)*(sp_s2_22) + (5713073380311/1000000000000 : ℝ)*(sp_s2_23) + (1277618124677/500000000000 : ℝ)*(sp_s2_27) + (1277618124677/500000000000 : ℝ)*(f.failure) + (5713147364973/1000000000000 : ℝ)*(f.sum) + (34605245754112805551/245131767800000000000000000000000 : ℝ)*base62 + (1337453122968981/6451600000000000000000000000 : ℝ)*base65 + (37734937498103/237471875000000000000000000 : ℝ)*base67 + (143310939617769/3225800000000000000000000000 : ℝ)*base68 + (38118129617008333181/486031286000000000000000000000000 : ℝ)*base70 + (11489884607933/753350000000000000000000000 : ℝ)*base73 + (46758061996749/474943750000000000000000000 : ℝ)*base74 + (9178913282363/3766750000000000000000000000 : ℝ)*base76 + (1900218528380784897/28623909925000000000000000000000 : ℝ)*base79 + (15861/50000000000000000 : ℝ)*base87 + (15861/50000000000000000 : ℝ)*base89 + (15861/50000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev1 : (0 : ℝ) ≤ ((15067/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15067/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(75991/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(75991/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-16129/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-16129/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((47921/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(47921/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(26153/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(26153/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-36073/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-36073/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c310060_s2 p hpa hpb X hX hprev1

#print axioms solution
