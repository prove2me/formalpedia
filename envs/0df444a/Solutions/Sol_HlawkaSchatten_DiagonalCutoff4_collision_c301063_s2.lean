-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301063_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:40:01.55238+00:00
-- url     : https://prove2.me/submissions/194a77ef-7bec-48cf-b77c-df2b6ad7ecb1

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
theorem collision_support_c301063_s2_s2_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-303179079/10000000000 : ℝ)*x 0 + (1424434813/2500000000 : ℝ)*x 1 + (1518511063/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (303179079/10000000000 : ℝ)^65 ≤ (193623267479/20000000000000 : ℝ)^49 := by
    have hnat : (303179079 : ℕ)^65*20000000000000^49 ≤ 193623267479^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      303179079 10000000000 193623267479 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1424434813/2500000000 : ℝ)^65 ≤ (23708385795241/50000000000000 : ℝ)^49 := by
    have hnat : (1424434813 : ℕ)^65*50000000000000^49 ≤ 23708385795241^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1424434813 2500000000 23708385795241 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1518511063/2500000000 : ℝ)^65 ≤ (645188900793/1250000000000 : ℝ)^49 := by
    have hnat : (1518511063 : ℕ)^65*1250000000000^49 ≤ 645188900793^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1518511063 2500000000 645188900793 1250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-303179079/10000000000 : ℝ), (1424434813/2500000000 : ℝ), (1518511063/2500000000 : ℝ)] ![(193623267479/20000000000000 : ℝ), (23708385795241/50000000000000 : ℝ), (645188900793/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-303179079/10000000000 : ℝ)|^65 ≤ (193623267479/20000000000000 : ℝ)^49
        have hw : |(-303179079/10000000000 : ℝ)|=(303179079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1424434813/2500000000 : ℝ)|^65 ≤ (23708385795241/50000000000000 : ℝ)^49
        have hw : |(1424434813/2500000000 : ℝ)|=(1424434813/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1518511063/2500000000 : ℝ)|^65 ≤ (645188900793/1250000000000 : ℝ)^49
        have hw : |(1518511063/2500000000 : ℝ)|=(1518511063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s2_s2_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (227869017/400000000 : ℝ)*x 0 + (-4502049/156250000 : ℝ)*x 1 + (1520161061/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (227869017/400000000 : ℝ)^65 ≤ (47405579842469/100000000000000 : ℝ)^49 := by
    have hnat : (227869017 : ℕ)^65*100000000000000^49 ≤ 47405579842469^49*400000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227869017 400000000 47405579842469 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4502049/156250000 : ℝ)^65 ≤ (56556073599/6250000000000 : ℝ)^49 := by
    have hnat : (4502049 : ℕ)^65*6250000000000^49 ≤ 56556073599^49*156250000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502049 156250000 56556073599 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1520161061/2500000000 : ℝ)^65 ≤ (3230595185971/6250000000000 : ℝ)^49 := by
    have hnat : (1520161061 : ℕ)^65*6250000000000^49 ≤ 3230595185971^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1520161061 2500000000 3230595185971 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(227869017/400000000 : ℝ), (-4502049/156250000 : ℝ), (1520161061/2500000000 : ℝ)] ![(47405579842469/100000000000000 : ℝ), (56556073599/6250000000000 : ℝ), (3230595185971/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(227869017/400000000 : ℝ)|^65 ≤ (47405579842469/100000000000000 : ℝ)^49
        have hw : |(227869017/400000000 : ℝ)|=(227869017/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4502049/156250000 : ℝ)|^65 ≤ (56556073599/6250000000000 : ℝ)^49
        have hw : |(-4502049/156250000 : ℝ)|=(4502049/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1520161061/2500000000 : ℝ)|^65 ≤ (3230595185971/6250000000000 : ℝ)^49
        have hw : |(1520161061/2500000000 : ℝ)|=(1520161061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s2_s2_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-181738111/2500000000 : ℝ)*x 0 + (540723841/2500000000 : ℝ)*x 1 + (8752012621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (181738111/2500000000 : ℝ)^65 ≤ (3088537355449/100000000000000 : ℝ)^49 := by
    have hnat : (181738111 : ℕ)^65*100000000000000^49 ≤ 3088537355449^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181738111 2500000000 3088537355449 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540723841/2500000000 : ℝ)^65 ≤ (3279776549397/25000000000000 : ℝ)^49 := by
    have hnat : (540723841 : ℕ)^65*25000000000000^49 ≤ 3279776549397^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540723841 2500000000 3279776549397 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8752012621/10000000000 : ℝ)^65 ≤ (41896178214991/50000000000000 : ℝ)^49 := by
    have hnat : (8752012621 : ℕ)^65*50000000000000^49 ≤ 41896178214991^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8752012621 10000000000 41896178214991 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-181738111/2500000000 : ℝ), (540723841/2500000000 : ℝ), (8752012621/10000000000 : ℝ)] ![(3088537355449/100000000000000 : ℝ), (3279776549397/25000000000000 : ℝ), (41896178214991/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-181738111/2500000000 : ℝ)|^65 ≤ (3088537355449/100000000000000 : ℝ)^49
        have hw : |(-181738111/2500000000 : ℝ)|=(181738111/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540723841/2500000000 : ℝ)|^65 ≤ (3279776549397/25000000000000 : ℝ)^49
        have hw : |(540723841/2500000000 : ℝ)|=(540723841/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8752012621/10000000000 : ℝ)|^65 ≤ (41896178214991/50000000000000 : ℝ)^49
        have hw : |(8752012621/10000000000 : ℝ)|=(8752012621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s2_s2_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1238745279/5000000000 : ℝ)*x 0 + (-150251089/10000000000 : ℝ)*x 1 + (4380631889/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1238745279/5000000000 : ℝ)^65 ≤ (15708632441559/100000000000000 : ℝ)^49 := by
    have hnat : (1238745279 : ℕ)^65*100000000000000^49 ≤ 15708632441559^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1238745279 5000000000 15708632441559 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (150251089/10000000000 : ℝ)^65 ≤ (381498445233/100000000000000 : ℝ)^49 := by
    have hnat : (150251089 : ℕ)^65*100000000000000^49 ≤ 381498445233^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      150251089 10000000000 381498445233 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4380631889/5000000000 : ℝ)^65 ≤ (20977467276857/25000000000000 : ℝ)^49 := by
    have hnat : (4380631889 : ℕ)^65*25000000000000^49 ≤ 20977467276857^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4380631889 5000000000 20977467276857 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1238745279/5000000000 : ℝ), (-150251089/10000000000 : ℝ), (4380631889/5000000000 : ℝ)] ![(15708632441559/100000000000000 : ℝ), (381498445233/100000000000000 : ℝ), (20977467276857/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1238745279/5000000000 : ℝ)|^65 ≤ (15708632441559/100000000000000 : ℝ)^49
        have hw : |(1238745279/5000000000 : ℝ)|=(1238745279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-150251089/10000000000 : ℝ)|^65 ≤ (381498445233/100000000000000 : ℝ)^49
        have hw : |(-150251089/10000000000 : ℝ)|=(150251089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4380631889/5000000000 : ℝ)|^65 ≤ (20977467276857/25000000000000 : ℝ)^49
        have hw : |(4380631889/5000000000 : ℝ)|=(4380631889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s2_s2_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2579723697/10000000000 : ℝ)*x 0 + (2178824597/2500000000 : ℝ)*x 1 + (-87191/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2579723697/10000000000 : ℝ)^65 ≤ (4143561948807/25000000000000 : ℝ)^49 := by
    have hnat : (2579723697 : ℕ)^65*25000000000000^49 ≤ 4143561948807^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2579723697 10000000000 4143561948807 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2178824597/2500000000 : ℝ)^65 ≤ (83326394560899/100000000000000 : ℝ)^49 := by
    have hnat : (2178824597 : ℕ)^65*100000000000000^49 ≤ 83326394560899^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178824597 2500000000 83326394560899 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (87191/16000000 : ℝ)^65 ≤ (19871525049/20000000000000 : ℝ)^49 := by
    have hnat : (87191 : ℕ)^65*20000000000000^49 ≤ 19871525049^49*16000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87191 16000000 19871525049 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2579723697/10000000000 : ℝ), (2178824597/2500000000 : ℝ), (-87191/16000000 : ℝ)] ![(4143561948807/25000000000000 : ℝ), (83326394560899/100000000000000 : ℝ), (19871525049/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2579723697/10000000000 : ℝ)|^65 ≤ (4143561948807/25000000000000 : ℝ)^49
        have hw : |(2579723697/10000000000 : ℝ)|=(2579723697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2178824597/2500000000 : ℝ)|^65 ≤ (83326394560899/100000000000000 : ℝ)^49
        have hw : |(2178824597/2500000000 : ℝ)|=(2178824597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-87191/16000000 : ℝ)|^65 ≤ (19871525049/20000000000000 : ℝ)^49
        have hw : |(-87191/16000000 : ℝ)|=(87191/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s2_s2_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (123078503/400000000 : ℝ)*x 0 + (3736261073/5000000000 : ℝ)*x 1 + (190894239/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (123078503/400000000 : ℝ)^65 ≤ (5235021332781/25000000000000 : ℝ)^49 := by
    have hnat : (123078503 : ℕ)^65*25000000000000^49 ≤ 5235021332781^49*400000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123078503 400000000 5235021332781 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3736261073/5000000000 : ℝ)^65 ≤ (67943885890073/100000000000000 : ℝ)^49 := by
    have hnat : (3736261073 : ℕ)^65*100000000000000^49 ≤ 67943885890073^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3736261073 5000000000 67943885890073 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (190894239/1000000000 : ℝ)^65 ≤ (1389503595369/12500000000000 : ℝ)^49 := by
    have hnat : (190894239 : ℕ)^65*12500000000000^49 ≤ 1389503595369^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190894239 1000000000 1389503595369 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(123078503/400000000 : ℝ), (3736261073/5000000000 : ℝ), (190894239/1000000000 : ℝ)] ![(5235021332781/25000000000000 : ℝ), (67943885890073/100000000000000 : ℝ), (1389503595369/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(123078503/400000000 : ℝ)|^65 ≤ (5235021332781/25000000000000 : ℝ)^49
        have hw : |(123078503/400000000 : ℝ)|=(123078503/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3736261073/5000000000 : ℝ)|^65 ≤ (67943885890073/100000000000000 : ℝ)^49
        have hw : |(3736261073/5000000000 : ℝ)|=(3736261073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(190894239/1000000000 : ℝ)|^65 ≤ (1389503595369/12500000000000 : ℝ)^49
        have hw : |(190894239/1000000000 : ℝ)|=(190894239/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s2_s2_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-56732953/5000000000 : ℝ)*x 0 + (95430053/400000000 : ℝ)*x 1 + (8830876239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (56732953/5000000000 : ℝ)^65 ≤ (262856904129/100000000000000 : ℝ)^49 := by
    have hnat : (56732953 : ℕ)^65*100000000000000^49 ≤ 262856904129^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56732953 5000000000 262856904129 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (95430053/400000000 : ℝ)^65 ≤ (7470862527381/50000000000000 : ℝ)^49 := by
    have hnat : (95430053 : ℕ)^65*50000000000000^49 ≤ 7470862527381^49*400000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95430053 400000000 7470862527381 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8830876239/10000000000 : ℝ)^65 ≤ (84795418037449/100000000000000 : ℝ)^49 := by
    have hnat : (8830876239 : ℕ)^65*100000000000000^49 ≤ 84795418037449^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8830876239 10000000000 84795418037449 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-56732953/5000000000 : ℝ), (95430053/400000000 : ℝ), (8830876239/10000000000 : ℝ)] ![(262856904129/100000000000000 : ℝ), (7470862527381/50000000000000 : ℝ), (84795418037449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-56732953/5000000000 : ℝ)|^65 ≤ (262856904129/100000000000000 : ℝ)^49
        have hw : |(-56732953/5000000000 : ℝ)|=(56732953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(95430053/400000000 : ℝ)|^65 ≤ (7470862527381/50000000000000 : ℝ)^49
        have hw : |(95430053/400000000 : ℝ)|=(95430053/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8830876239/10000000000 : ℝ)|^65 ≤ (84795418037449/100000000000000 : ℝ)^49
        have hw : |(8830876239/10000000000 : ℝ)|=(8830876239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s2_s2_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (513397299/2500000000 : ℝ)*x 0 + (-341040143/5000000000 : ℝ)*x 1 + (1768049661/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (513397299/2500000000 : ℝ)^65 ≤ (12246957372271/100000000000000 : ℝ)^49 := by
    have hnat : (513397299 : ℕ)^65*100000000000000^49 ≤ 12246957372271^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513397299 2500000000 12246957372271 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (341040143/5000000000 : ℝ)^65 ≤ (567645349319/20000000000000 : ℝ)^49 := by
    have hnat : (341040143 : ℕ)^65*20000000000000^49 ≤ 567645349319^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341040143 5000000000 567645349319 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1768049661/2000000000 : ℝ)^65 ≤ (42457407932971/50000000000000 : ℝ)^49 := by
    have hnat : (1768049661 : ℕ)^65*50000000000000^49 ≤ 42457407932971^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1768049661 2000000000 42457407932971 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(513397299/2500000000 : ℝ), (-341040143/5000000000 : ℝ), (1768049661/2000000000 : ℝ)] ![(12246957372271/100000000000000 : ℝ), (567645349319/20000000000000 : ℝ), (42457407932971/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(513397299/2500000000 : ℝ)|^65 ≤ (12246957372271/100000000000000 : ℝ)^49
        have hw : |(513397299/2500000000 : ℝ)|=(513397299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-341040143/5000000000 : ℝ)|^65 ≤ (567645349319/20000000000000 : ℝ)^49
        have hw : |(-341040143/5000000000 : ℝ)|=(341040143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1768049661/2000000000 : ℝ)|^65 ≤ (42457407932971/50000000000000 : ℝ)^49
        have hw : |(1768049661/2000000000 : ℝ)|=(1768049661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s2_s2_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (340404803/400000000 : ℝ)*x 0 + (1433697057/5000000000 : ℝ)*x 1 + (-45516357/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (340404803/400000000 : ℝ)^65 ≤ (10091774975933/12500000000000 : ℝ)^49 := by
    have hnat : (340404803 : ℕ)^65*12500000000000^49 ≤ 10091774975933^49*400000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340404803 400000000 10091774975933 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1433697057/5000000000 : ℝ)^65 ≤ (2383693584073/12500000000000 : ℝ)^49 := by
    have hnat : (1433697057 : ℕ)^65*12500000000000^49 ≤ 2383693584073^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1433697057 5000000000 2383693584073 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (45516357/5000000000 : ℝ)^65 ≤ (49062876477/25000000000000 : ℝ)^49 := by
    have hnat : (45516357 : ℕ)^65*25000000000000^49 ≤ 49062876477^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45516357 5000000000 49062876477 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(340404803/400000000 : ℝ), (1433697057/5000000000 : ℝ), (-45516357/5000000000 : ℝ)] ![(10091774975933/12500000000000 : ℝ), (2383693584073/12500000000000 : ℝ), (49062876477/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(340404803/400000000 : ℝ)|^65 ≤ (10091774975933/12500000000000 : ℝ)^49
        have hw : |(340404803/400000000 : ℝ)|=(340404803/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1433697057/5000000000 : ℝ)|^65 ≤ (2383693584073/12500000000000 : ℝ)^49
        have hw : |(1433697057/5000000000 : ℝ)|=(1433697057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-45516357/5000000000 : ℝ)|^65 ≤ (49062876477/25000000000000 : ℝ)^49
        have hw : |(-45516357/5000000000 : ℝ)|=(45516357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s2_s2_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3875201333/5000000000 : ℝ)*x 0 + (2699037519/10000000000 : ℝ)*x 1 + (1904996337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3875201333/5000000000 : ℝ)^65 ≤ (71315716768443/100000000000000 : ℝ)^49 := by
    have hnat : (3875201333 : ℕ)^65*100000000000000^49 ≤ 71315716768443^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3875201333 5000000000 71315716768443 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2699037519/10000000000 : ℝ)^65 ≤ (8799362857187/50000000000000 : ℝ)^49 := by
    have hnat : (2699037519 : ℕ)^65*50000000000000^49 ≤ 8799362857187^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699037519 10000000000 8799362857187 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1904996337/10000000000 : ℝ)^65 ≤ (11085557506201/100000000000000 : ℝ)^49 := by
    have hnat : (1904996337 : ℕ)^65*100000000000000^49 ≤ 11085557506201^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1904996337 10000000000 11085557506201 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3875201333/5000000000 : ℝ), (2699037519/10000000000 : ℝ), (1904996337/10000000000 : ℝ)] ![(71315716768443/100000000000000 : ℝ), (8799362857187/50000000000000 : ℝ), (11085557506201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3875201333/5000000000 : ℝ)|^65 ≤ (71315716768443/100000000000000 : ℝ)^49
        have hw : |(3875201333/5000000000 : ℝ)|=(3875201333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2699037519/10000000000 : ℝ)|^65 ≤ (8799362857187/50000000000000 : ℝ)^49
        have hw : |(2699037519/10000000000 : ℝ)|=(2699037519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1904996337/10000000000 : ℝ)|^65 ≤ (11085557506201/100000000000000 : ℝ)^49
        have hw : |(1904996337/10000000000 : ℝ)|=(1904996337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s2_s2_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-219285383/10000000000 : ℝ)*x 0 + (1993475093/2500000000 : ℝ)*x 1 + (887482623/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (219285383/10000000000 : ℝ)^65 ≤ (125987818367/20000000000000 : ℝ)^49 := by
    have hnat : (219285383 : ℕ)^65*20000000000000^49 ≤ 125987818367^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219285383 10000000000 125987818367 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1993475093/2500000000 : ℝ)^65 ≤ (14811304435867/20000000000000 : ℝ)^49 := by
    have hnat : (1993475093 : ℕ)^65*20000000000000^49 ≤ 14811304435867^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1993475093 2500000000 14811304435867 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (887482623/2500000000 : ℝ)^65 ≤ (12656769356739/50000000000000 : ℝ)^49 := by
    have hnat : (887482623 : ℕ)^65*50000000000000^49 ≤ 12656769356739^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      887482623 2500000000 12656769356739 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-219285383/10000000000 : ℝ), (1993475093/2500000000 : ℝ), (887482623/2500000000 : ℝ)] ![(125987818367/20000000000000 : ℝ), (14811304435867/20000000000000 : ℝ), (12656769356739/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-219285383/10000000000 : ℝ)|^65 ≤ (125987818367/20000000000000 : ℝ)^49
        have hw : |(-219285383/10000000000 : ℝ)|=(219285383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1993475093/2500000000 : ℝ)|^65 ≤ (14811304435867/20000000000000 : ℝ)^49
        have hw : |(1993475093/2500000000 : ℝ)|=(1993475093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(887482623/2500000000 : ℝ)|^65 ≤ (12656769356739/50000000000000 : ℝ)^49
        have hw : |(887482623/2500000000 : ℝ)|=(887482623/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s2_s2_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4206259671/5000000000 : ℝ)*x 0 + (-85366777/10000000000 : ℝ)*x 1 + (375884743/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4206259671/5000000000 : ℝ)^65 ≤ (19877060060553/25000000000000 : ℝ)^49 := by
    have hnat : (4206259671 : ℕ)^65*25000000000000^49 ≤ 19877060060553^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4206259671 5000000000 19877060060553 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (85366777/10000000000 : ℝ)^65 ≤ (180215183397/100000000000000 : ℝ)^49 := by
    have hnat : (85366777 : ℕ)^65*100000000000000^49 ≤ 180215183397^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85366777 10000000000 180215183397 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (375884743/1250000000 : ℝ)^65 ≤ (2538943069367/12500000000000 : ℝ)^49 := by
    have hnat : (375884743 : ℕ)^65*12500000000000^49 ≤ 2538943069367^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375884743 1250000000 2538943069367 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4206259671/5000000000 : ℝ), (-85366777/10000000000 : ℝ), (375884743/1250000000 : ℝ)] ![(19877060060553/25000000000000 : ℝ), (180215183397/100000000000000 : ℝ), (2538943069367/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4206259671/5000000000 : ℝ)|^65 ≤ (19877060060553/25000000000000 : ℝ)^49
        have hw : |(4206259671/5000000000 : ℝ)|=(4206259671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-85366777/10000000000 : ℝ)|^65 ≤ (180215183397/100000000000000 : ℝ)^49
        have hw : |(-85366777/10000000000 : ℝ)|=(85366777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(375884743/1250000000 : ℝ)|^65 ≤ (2538943069367/12500000000000 : ℝ)^49
        have hw : |(375884743/1250000000 : ℝ)|=(375884743/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s2_s2_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1858265467/10000000000 : ℝ)*x 0 + (9014206751/10000000000 : ℝ)*x 1 + (-55037717/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1858265467/10000000000 : ℝ)^65 ≤ (2681569597433/25000000000000 : ℝ)^49 := by
    have hnat : (1858265467 : ℕ)^65*25000000000000^49 ≤ 2681569597433^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1858265467 10000000000 2681569597433 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9014206751/10000000000 : ℝ)^65 ≤ (87138477727107/100000000000000 : ℝ)^49 := by
    have hnat : (9014206751 : ℕ)^65*100000000000000^49 ≤ 87138477727107^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9014206751 10000000000 87138477727107 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (55037717/1000000000 : ℝ)^65 ≤ (2135243869787/100000000000000 : ℝ)^49 := by
    have hnat : (55037717 : ℕ)^65*100000000000000^49 ≤ 2135243869787^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55037717 1000000000 2135243869787 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1858265467/10000000000 : ℝ), (9014206751/10000000000 : ℝ), (-55037717/1000000000 : ℝ)] ![(2681569597433/25000000000000 : ℝ), (87138477727107/100000000000000 : ℝ), (2135243869787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1858265467/10000000000 : ℝ)|^65 ≤ (2681569597433/25000000000000 : ℝ)^49
        have hw : |(1858265467/10000000000 : ℝ)|=(1858265467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(9014206751/10000000000 : ℝ)|^65 ≤ (87138477727107/100000000000000 : ℝ)^49
        have hw : |(9014206751/10000000000 : ℝ)|=(9014206751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-55037717/1000000000 : ℝ)|^65 ≤ (2135243869787/100000000000000 : ℝ)^49
        have hw : |(-55037717/1000000000 : ℝ)|=(55037717/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s2_s2_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7880159413/10000000000 : ℝ)*x 0 + (522066761/2000000000 : ℝ)*x 1 + (35942101/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7880159413/10000000000 : ℝ)^65 ≤ (14580771704197/20000000000000 : ℝ)^49 := by
    have hnat : (7880159413 : ℕ)^65*20000000000000^49 ≤ 14580771704197^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7880159413 10000000000 14580771704197 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (522066761/2000000000 : ℝ)^65 ≤ (1683563304133/10000000000000 : ℝ)^49 := by
    have hnat : (522066761 : ℕ)^65*10000000000000^49 ≤ 1683563304133^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522066761 2000000000 1683563304133 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35942101/200000000 : ℝ)^65 ≤ (5130254215877/50000000000000 : ℝ)^49 := by
    have hnat : (35942101 : ℕ)^65*50000000000000^49 ≤ 5130254215877^49*200000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35942101 200000000 5130254215877 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7880159413/10000000000 : ℝ), (522066761/2000000000 : ℝ), (35942101/200000000 : ℝ)] ![(14580771704197/20000000000000 : ℝ), (1683563304133/10000000000000 : ℝ), (5130254215877/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7880159413/10000000000 : ℝ)|^65 ≤ (14580771704197/20000000000000 : ℝ)^49
        have hw : |(7880159413/10000000000 : ℝ)|=(7880159413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(522066761/2000000000 : ℝ)|^65 ≤ (1683563304133/10000000000000 : ℝ)^49
        have hw : |(522066761/2000000000 : ℝ)|=(522066761/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(35942101/200000000 : ℝ)|^65 ≤ (5130254215877/50000000000000 : ℝ)^49
        have hw : |(35942101/200000000 : ℝ)|=(35942101/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301063_s2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((18271/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18271/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2839/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2839/3125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17637/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(17637/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((42829/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(42829/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21377/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(21377/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(41229/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(41229/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (92391/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (18271/20000 : ℝ) ^ (129/32 : ℝ) ≤ (13890957050129261929/20000000000000000000 : ℝ) := by
    have hpowers : (18271/20000 : ℝ)^129 ≤ (13890957050129261929/20000000000000000000 : ℝ)^32 := by
      have hnat : (18271 : ℕ)^129*20000000000000000000^32 ≤ 13890957050129261929^32*20000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18271 20000 13890957050129261929 20000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18271/20000 : ℝ)) (X := (13890957050129261929/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner0a : (33890957050129261929/20000000000000000000 : ℝ) ≤ (2279552255497701/2000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (33890957050129261929/20000000000000000000 : ℝ)^32 ≤ (2279552255497701/2000000000000000 : ℝ)^129 := by
      have hnat : (33890957050129261929 : ℕ)^32*2000000000000000^129 ≤ 2279552255497701^129*20000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33890957050129261929 20000000000000000000 2279552255497701 2000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2279552255497701/2000000000000000 : ℝ)) (X := (33890957050129261929/20000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner0b : (23890957050129261929/10000000000000000000 : ℝ) ≤ (12411531565560753/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (23890957050129261929/10000000000000000000 : ℝ)^32 ≤ (12411531565560753/10000000000000000 : ℝ)^129 := by
      have hnat : (23890957050129261929 : ℕ)^32*10000000000000000^129 ≤ 12411531565560753^129*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23890957050129261929 10000000000000000000 12411531565560753 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12411531565560753/10000000000000000 : ℝ)) (X := (23890957050129261929/10000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(279552255497701/1827100000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(126721286009031/1141937500000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (18271/20000 : ℝ)) (alpha := (279552255497701/1827100000000000 : ℝ)) (beta := (126721286009031/1141937500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (18271/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(279552255497701/1827100000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(126721286009031/1141937500000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (2839/3125 : ℝ) ^ (129/32 : ℝ) ≤ (424462039094071783/625000000000000000 : ℝ) := by
    have hpowers : (2839/3125 : ℝ)^129 ≤ (424462039094071783/625000000000000000 : ℝ)^32 := by
      have hnat : (2839 : ℕ)^129*625000000000000000^32 ≤ 424462039094071783^32*3125^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2839 3125 424462039094071783 625000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2839/3125 : ℝ)) (X := (424462039094071783/625000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner1a : (1049462039094071783/625000000000000000 : ℝ) ≤ (2274392739322071/2000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (1049462039094071783/625000000000000000 : ℝ)^32 ≤ (2274392739322071/2000000000000000 : ℝ)^129 := by
      have hnat : (1049462039094071783 : ℕ)^32*2000000000000000^129 ≤ 2274392739322071^129*625000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1049462039094071783 625000000000000000 2274392739322071 2000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2274392739322071/2000000000000000 : ℝ)) (X := (1049462039094071783/625000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner1b : (736962039094071783/312500000000000000 : ℝ) ≤ (12371623377436049/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (736962039094071783/312500000000000000 : ℝ)^32 ≤ (12371623377436049/10000000000000000 : ℝ)^129 := by
      have hnat : (736962039094071783 : ℕ)^32*10000000000000000^129 ≤ 12371623377436049^129*312500000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        736962039094071783 312500000000000000 12371623377436049 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12371623377436049/10000000000000000 : ℝ)) (X := (736962039094071783/312500000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(274392739322071/1816960000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(499829840412847/4542400000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (2839/3125 : ℝ)) (alpha := (274392739322071/1816960000000000 : ℝ)) (beta := (499829840412847/4542400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (2839/3125 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(274392739322071/1816960000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(499829840412847/4542400000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (17637/20000 : ℝ) ^ (129/32 : ℝ) ≤ (12047653201354689643/20000000000000000000 : ℝ) := by
    have hpowers : (17637/20000 : ℝ)^129 ≤ (12047653201354689643/20000000000000000000 : ℝ)^32 := by
      have hnat : (17637 : ℕ)^129*20000000000000000000^32 ≤ 12047653201354689643^32*20000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17637 20000 12047653201354689643 20000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17637/20000 : ℝ)) (X := (12047653201354689643/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner2a : (32047653201354689643/20000000000000000000 : ℝ) ≤ (140509192650339/125000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (32047653201354689643/20000000000000000000 : ℝ)^32 ≤ (140509192650339/125000000000000 : ℝ)^129 := by
      have hnat : (32047653201354689643 : ℕ)^32*125000000000000^129 ≤ 140509192650339^129*20000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32047653201354689643 20000000000000000000 140509192650339 125000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (140509192650339/125000000000000 : ℝ)) (X := (32047653201354689643/20000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner2b : (22047653201354689643/10000000000000000000 : ℝ) ≤ (6083383081864191/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (22047653201354689643/10000000000000000000 : ℝ)^32 ≤ (6083383081864191/5000000000000000 : ℝ)^129 := by
      have hnat : (22047653201354689643 : ℕ)^32*5000000000000000^129 ≤ 6083383081864191^129*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22047653201354689643 10000000000000000000 6083383081864191 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6083383081864191/5000000000000000 : ℝ)) (X := (22047653201354689643/10000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(15509192650339/110231250000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(154338458616877/1469750000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (17637/20000 : ℝ)) (alpha := (15509192650339/110231250000000 : ℝ)) (beta := (154338458616877/1469750000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (17637/20000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(15509192650339/110231250000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(154338458616877/1469750000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-303179079/10000000000 : ℝ)*X 0 0+(1424434813/2500000000 : ℝ)*X 0 1+(1518511063/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((227869017/400000000 : ℝ)*X 1 0+(-4502049/156250000 : ℝ)*X 1 1+(1520161061/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-181738111/2500000000 : ℝ)*X 0 0+(540723841/2500000000 : ℝ)*X 0 1+(8752012621/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((1238745279/5000000000 : ℝ)*X 1 0+(-150251089/10000000000 : ℝ)*X 1 1+(4380631889/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((2579723697/10000000000 : ℝ)*X 2 0+(2178824597/2500000000 : ℝ)*X 2 1+(-87191/16000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((123078503/400000000 : ℝ)*X 0 0+(3736261073/5000000000 : ℝ)*X 0 1+(190894239/1000000000 : ℝ)*X 0 2+(123078503/400000000 : ℝ)*X 1 0+(3736261073/5000000000 : ℝ)*X 1 1+(190894239/1000000000 : ℝ)*X 1 2+(123078503/400000000 : ℝ)*X 2 0+(3736261073/5000000000 : ℝ)*X 2 1+(190894239/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-56732953/5000000000 : ℝ)*X 0 0+(95430053/400000000 : ℝ)*X 0 1+(8830876239/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((513397299/2500000000 : ℝ)*X 1 0+(-341040143/5000000000 : ℝ)*X 1 1+(1768049661/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((340404803/400000000 : ℝ)*X 2 0+(1433697057/5000000000 : ℝ)*X 2 1+(-45516357/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((3875201333/5000000000 : ℝ)*X 0 0+(2699037519/10000000000 : ℝ)*X 0 1+(1904996337/10000000000 : ℝ)*X 0 2+(3875201333/5000000000 : ℝ)*X 1 0+(2699037519/10000000000 : ℝ)*X 1 1+(1904996337/10000000000 : ℝ)*X 1 2+(3875201333/5000000000 : ℝ)*X 2 0+(2699037519/10000000000 : ℝ)*X 2 1+(1904996337/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-219285383/10000000000 : ℝ)*X 0 0+(1993475093/2500000000 : ℝ)*X 0 1+(887482623/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((4206259671/5000000000 : ℝ)*X 1 0+(-85366777/10000000000 : ℝ)*X 1 1+(375884743/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((1858265467/10000000000 : ℝ)*X 2 0+(9014206751/10000000000 : ℝ)*X 2 1+(-55037717/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((7880159413/10000000000 : ℝ)*X 0 0+(522066761/2000000000 : ℝ)*X 0 1+(35942101/200000000 : ℝ)*X 0 2+(7880159413/10000000000 : ℝ)*X 1 0+(522066761/2000000000 : ℝ)*X 1 1+(35942101/200000000 : ℝ)*X 1 2+(7880159413/10000000000 : ℝ)*X 2 0+(522066761/2000000000 : ℝ)*X 2 1+(35942101/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((42829/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(42829/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (17376493092189686474936920415231/1219807113404000000000000000000000000 : ℝ) := by norm_num
    linear_combination (104024711793/125000000000 : ℝ)*(base7) + (523481/250000000000 : ℝ)*(base50) + (350999/200000000000 : ℝ)*(base53) + (1812681/1000000000000 : ℝ)*(base60) + (1630052124009/1000000000000 : ℝ)*(major_s2_0) + (1630052124009/1000000000000 : ℝ)*(major_s2_1) + (815025184507/500000000000 : ℝ)*(major_s2_2) + (434003/40000000000 : ℝ)*(sp_s2_0) + (1645443682447/1000000000000 : ℝ)*(sp_s2_7) + (1645558594091/1000000000000 : ℝ)*(sp_s2_8) + (1645563213989/1000000000000 : ℝ)*(sp_s2_9) + (1934150132089/1000000000000 : ℝ)*(sp_s2_13) + (13365809/125000000000 : ℝ)*(sp_s2_14) + (2864903/1000000000000 : ℝ)*(sp_s2_15) + (220390487549/200000000000 : ℝ)*(f.failure) + (1645563213989/1000000000000 : ℝ)*(f.sum) + (18983616904518837943/160228617600000000000000000000000 : ℝ)*base63 + (63359204818417/91859375000000000000000000 : ℝ)*base64 + (1790113218312423/4542400000000000000000000000 : ℝ)*base67 + (165649798518883/881850000000000000000000000 : ℝ)*base69 + (24151211410715271919/53707604500000000000000000000000 : ℝ)*base70 + (607045014172791/4567750000000000000000000000 : ℝ)*base73 + (506367532734929/1816960000000000000000000000 : ℝ)*base74 + (106357760435849/1827100000000000000000000000 : ℝ)*base77 + (33550353279450173533/414970952000000000000000000000000 : ℝ)*base79 + (4569/5000000000000000 : ℝ)*base87 + (4569/5000000000000000 : ℝ)*base89 + (4569/5000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21377/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(21377/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2125310419959388296113608641547/243961422680800000000000000000000000 : ℝ) := by norm_num
    linear_combination (839969581799/1000000000000 : ℝ)*(base7) + (49719/31250000000 : ℝ)*(base13) + (310619/200000000000 : ℝ)*(base40) + (4104571/1000000000000 : ℝ)*(base53) + (315934280691/200000000000 : ℝ)*(major_s2_0) + (315934280691/200000000000 : ℝ)*(major_s2_1) + (1579667298883/1000000000000 : ℝ)*(major_s2_2) + (1588403/500000000000 : ℝ)*(sp_s2_1) + (56407671/1000000000000 : ℝ)*(sp_s2_8) + (1574069422387/1000000000000 : ℝ)*(sp_s2_14) + (1574011428919/1000000000000 : ℝ)*(sp_s2_15) + (787037558983/500000000000 : ℝ)*(sp_s2_16) + (953872000409/500000000000 : ℝ)*(sp_s2_20) + (14937727/125000000000 : ℝ)*(sp_s2_27) + (533946960417/500000000000 : ℝ)*(f.failure) + (787037558983/500000000000 : ℝ)*(f.sum) + (70163237329045714399/160228617600000000000000000000000 : ℝ)*base62 + (107922301104829/367437500000000000000000000 : ℝ)*base65 + (64078018162791/181696000000000000000000000 : ℝ)*base66 + (20585375243599/55115625000000000000000000 : ℝ)*base68 + (2919857966729697703/53707604500000000000000000000000 : ℝ)*base70 + (1071558949575681/913550000000000000000000000 : ℝ)*base72 + (530569805626089/1816960000000000000000000000 : ℝ)*base75 + (186923641095459/365420000000000000000000000 : ℝ)*base77 + (3534066254311219313/82994190400000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (6423/12500000000000000 : ℝ)*base86 + (6423/12500000000000000 : ℝ)*base88 + (6077/12500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(41229/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(41229/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (525055565158700569439583831233/143506719224000000000000000000000000 : ℝ) := by norm_num
    linear_combination (421924571639/500000000000 : ℝ)*(base7) + (303227/1000000000000 : ℝ)*(base27) + (82944412221/1000000000000 : ℝ)*(base40) + (534579/200000000000 : ℝ)*(base43) + (89127/250000000000 : ℝ)*(base49) + (20139/125000000000 : ℝ)*(base59) + (763400558401/500000000000 : ℝ)*(major_s2_0) + (1526798443907/1000000000000 : ℝ)*(major_s2_1) + (763400558401/500000000000 : ℝ)*(major_s2_2) + (15031487/500000000000 : ℝ)*(sp_s2_9) + (375421374847/250000000000 : ℝ)*(sp_s2_21) + (1501688172283/1000000000000 : ℝ)*(sp_s2_22) + (750827718207/500000000000 : ℝ)*(sp_s2_23) + (938000620237/500000000000 : ℝ)*(sp_s2_27) + (1032152400423/1000000000000 : ℝ)*(f.failure) + (1501688172283/1000000000000 : ℝ)*(f.sum) + (2442144568701689357/9425212800000000000000000000000 : ℝ)*base63 + (15426116954249/367437500000000000000000000 : ℝ)*base64 + (23388973337283/267200000000000000000000000 : ℝ)*base66 + (18391119306661/220462500000000000000000000 : ℝ)*base69 + (2542557009266091973/13426901125000000000000000000000 : ℝ)*base70 + (182537270864537/1141937500000000000000000000 : ℝ)*base73 + (13883014196277/106880000000000000000000000 : ℝ)*base75 + (389204639140479/913550000000000000000000000 : ℝ)*base76 + (9846894423941771247/24410056000000000000000000000000 : ℝ)*base79 + (7037/25000000000000000 : ℝ)*base86 + (7037/25000000000000000 : ℝ)*base88 + (7037/25000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((18271/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18271/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2839/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2839/3125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17637/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(17637/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((42829/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(42829/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21377/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(21377/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(41229/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(41229/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301063_s2 p hpa hpb X hX hprev1

#print axioms solution
