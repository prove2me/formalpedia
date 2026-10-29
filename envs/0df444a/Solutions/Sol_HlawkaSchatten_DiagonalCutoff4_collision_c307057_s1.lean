-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c307057_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:13:39.701856+00:00
-- url     : https://prove2.me/submissions/e5f2af4c-783c-413b-b832-d4781d4e4a46

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
theorem collision_support_c307057_s1_s1_0 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-774776913/2500000000 : ℝ)*x 0 + (3084296699/10000000000 : ℝ)*x 1 + (6498264917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (774776913/2500000000 : ℝ)^17 ≤ (21611957106533/100000000000000 : ℝ)^13 := by
    have hnat : (774776913 : ℕ)^17*100000000000000^13 ≤ 21611957106533^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      774776913 2500000000 21611957106533 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3084296699/10000000000 : ℝ)^17 ≤ (21476990532699/100000000000000 : ℝ)^13 := by
    have hnat : (3084296699 : ℕ)^17*100000000000000^13 ≤ 21476990532699^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3084296699 10000000000 21476990532699 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6498264917/10000000000 : ℝ)^17 ≤ (28455526170911/50000000000000 : ℝ)^13 := by
    have hnat : (6498264917 : ℕ)^17*50000000000000^13 ≤ 28455526170911^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6498264917 10000000000 28455526170911 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-774776913/2500000000 : ℝ), (3084296699/10000000000 : ℝ), (6498264917/10000000000 : ℝ)] ![(21611957106533/100000000000000 : ℝ), (21476990532699/100000000000000 : ℝ), (28455526170911/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-774776913/2500000000 : ℝ)|^17 ≤ (21611957106533/100000000000000 : ℝ)^13
        have hw : |(-774776913/2500000000 : ℝ)|=(774776913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3084296699/10000000000 : ℝ)|^17 ≤ (21476990532699/100000000000000 : ℝ)^13
        have hw : |(3084296699/10000000000 : ℝ)|=(3084296699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6498264917/10000000000 : ℝ)|^17 ≤ (28455526170911/50000000000000 : ℝ)^13
        have hw : |(6498264917/10000000000 : ℝ)|=(6498264917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307057_s1_s1_1 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (309078621/1000000000 : ℝ)*x 0 + (-1538007513/5000000000 : ℝ)*x 1 + (6511466117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (309078621/1000000000 : ℝ)^17 ≤ (2692012810721/12500000000000 : ℝ)^13 := by
    have hnat : (309078621 : ℕ)^17*12500000000000^13 ≤ 2692012810721^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      309078621 1000000000 2692012810721 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1538007513/5000000000 : ℝ)^17 ≤ (10700804811739/50000000000000 : ℝ)^13 := by
    have hnat : (1538007513 : ℕ)^17*50000000000000^13 ≤ 10700804811739^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1538007513 5000000000 10700804811739 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6511466117/10000000000 : ℝ)^17 ≤ (57062287871713/100000000000000 : ℝ)^13 := by
    have hnat : (6511466117 : ℕ)^17*100000000000000^13 ≤ 57062287871713^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6511466117 10000000000 57062287871713 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(309078621/1000000000 : ℝ), (-1538007513/5000000000 : ℝ), (6511466117/10000000000 : ℝ)] ![(2692012810721/12500000000000 : ℝ), (10700804811739/50000000000000 : ℝ), (57062287871713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(309078621/1000000000 : ℝ)|^17 ≤ (2692012810721/12500000000000 : ℝ)^13
        have hw : |(309078621/1000000000 : ℝ)|=(309078621/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1538007513/5000000000 : ℝ)|^17 ≤ (10700804811739/50000000000000 : ℝ)^13
        have hw : |(-1538007513/5000000000 : ℝ)|=(1538007513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6511466117/10000000000 : ℝ)|^17 ≤ (57062287871713/100000000000000 : ℝ)^13
        have hw : |(6511466117/10000000000 : ℝ)|=(6511466117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307057_s1_s1_2 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5874992621/10000000000 : ℝ)*x 0 + (589573531/1000000000 : ℝ)*x 1 + (1866633/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5874992621/10000000000 : ℝ)^17 ≤ (6235089177873/12500000000000 : ℝ)^13 := by
    have hnat : (5874992621 : ℕ)^17*12500000000000^13 ≤ 6235089177873^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5874992621 10000000000 6235089177873 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (589573531/1000000000 : ℝ)^17 ≤ (50111139486407/100000000000000 : ℝ)^13 := by
    have hnat : (589573531 : ℕ)^17*100000000000000^13 ≤ 50111139486407^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      589573531 1000000000 50111139486407 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1866633/2500000000 : ℝ)^17 ≤ (8147074331/100000000000000 : ℝ)^13 := by
    have hnat : (1866633 : ℕ)^17*100000000000000^13 ≤ 8147074331^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1866633 2500000000 8147074331 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5874992621/10000000000 : ℝ), (589573531/1000000000 : ℝ), (1866633/2500000000 : ℝ)] ![(6235089177873/12500000000000 : ℝ), (50111139486407/100000000000000 : ℝ), (8147074331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5874992621/10000000000 : ℝ)|^17 ≤ (6235089177873/12500000000000 : ℝ)^13
        have hw : |(5874992621/10000000000 : ℝ)|=(5874992621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(589573531/1000000000 : ℝ)|^17 ≤ (50111139486407/100000000000000 : ℝ)^13
        have hw : |(589573531/1000000000 : ℝ)|=(589573531/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1866633/2500000000 : ℝ)|^17 ≤ (8147074331/100000000000000 : ℝ)^13
        have hw : |(1866633/2500000000 : ℝ)|=(1866633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307057_s1_s1_6 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4893504647/10000000000 : ℝ)*x 0 + (4910782021/10000000000 : ℝ)*x 1 + (3061336281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4893504647/10000000000 : ℝ)^17 ≤ (39275205689093/100000000000000 : ℝ)^13 := by
    have hnat : (4893504647 : ℕ)^17*100000000000000^13 ≤ 39275205689093^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4893504647 10000000000 39275205689093 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4910782021/10000000000 : ℝ)^17 ≤ (1972831958047/5000000000000 : ℝ)^13 := by
    have hnat : (4910782021 : ℕ)^17*5000000000000^13 ≤ 1972831958047^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4910782021 10000000000 1972831958047 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3061336281/10000000000 : ℝ)^17 ≤ (664629848091/3125000000000 : ℝ)^13 := by
    have hnat : (3061336281 : ℕ)^17*3125000000000^13 ≤ 664629848091^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3061336281 10000000000 664629848091 3125000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4893504647/10000000000 : ℝ), (4910782021/10000000000 : ℝ), (3061336281/10000000000 : ℝ)] ![(39275205689093/100000000000000 : ℝ), (1972831958047/5000000000000 : ℝ), (664629848091/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4893504647/10000000000 : ℝ)|^17 ≤ (39275205689093/100000000000000 : ℝ)^13
        have hw : |(4893504647/10000000000 : ℝ)|=(4893504647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4910782021/10000000000 : ℝ)|^17 ≤ (1972831958047/5000000000000 : ℝ)^13
        have hw : |(4910782021/10000000000 : ℝ)|=(4910782021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3061336281/10000000000 : ℝ)|^17 ≤ (664629848091/3125000000000 : ℝ)^13
        have hw : |(3061336281/10000000000 : ℝ)|=(3061336281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307057_s1_s1_7 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2127044277/10000000000 : ℝ)*x 0 + (311445573/2500000000 : ℝ)*x 1 + (4224720459/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2127044277/10000000000 : ℝ)^17 ≤ (1321108660881/10000000000000 : ℝ)^13 := by
    have hnat : (2127044277 : ℕ)^17*10000000000000^13 ≤ 1321108660881^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127044277 10000000000 1321108660881 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (311445573/2500000000 : ℝ)^17 ≤ (1640803866501/25000000000000 : ℝ)^13 := by
    have hnat : (311445573 : ℕ)^17*25000000000000^13 ≤ 1640803866501^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      311445573 2500000000 1640803866501 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4224720459/5000000000 : ℝ)^17 ≤ (40112848954681/50000000000000 : ℝ)^13 := by
    have hnat : (4224720459 : ℕ)^17*50000000000000^13 ≤ 40112848954681^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224720459 5000000000 40112848954681 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2127044277/10000000000 : ℝ), (311445573/2500000000 : ℝ), (4224720459/5000000000 : ℝ)] ![(1321108660881/10000000000000 : ℝ), (1640803866501/25000000000000 : ℝ), (40112848954681/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2127044277/10000000000 : ℝ)|^17 ≤ (1321108660881/10000000000000 : ℝ)^13
        have hw : |(-2127044277/10000000000 : ℝ)|=(2127044277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(311445573/2500000000 : ℝ)|^17 ≤ (1640803866501/25000000000000 : ℝ)^13
        have hw : |(311445573/2500000000 : ℝ)|=(311445573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4224720459/5000000000 : ℝ)|^17 ≤ (40112848954681/50000000000000 : ℝ)^13
        have hw : |(4224720459/5000000000 : ℝ)|=(4224720459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307057_s1_s1_8 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1688179283/10000000000 : ℝ)*x 0 + (-846042491/5000000000 : ℝ)*x 1 + (1693325247/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1688179283/10000000000 : ℝ)^17 ≤ (9765651057999/100000000000000 : ℝ)^13 := by
    have hnat : (1688179283 : ℕ)^17*100000000000000^13 ≤ 9765651057999^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1688179283 10000000000 9765651057999 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (846042491/5000000000 : ℝ)^17 ≤ (9795206771273/100000000000000 : ℝ)^13 := by
    have hnat : (846042491 : ℕ)^17*100000000000000^13 ≤ 9795206771273^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846042491 5000000000 9795206771273 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1693325247/2000000000 : ℝ)^17 ≤ (40219571078759/50000000000000 : ℝ)^13 := by
    have hnat : (1693325247 : ℕ)^17*50000000000000^13 ≤ 40219571078759^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1693325247 2000000000 40219571078759 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1688179283/10000000000 : ℝ), (-846042491/5000000000 : ℝ), (1693325247/2000000000 : ℝ)] ![(9765651057999/100000000000000 : ℝ), (9795206771273/100000000000000 : ℝ), (40219571078759/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1688179283/10000000000 : ℝ)|^17 ≤ (9765651057999/100000000000000 : ℝ)^13
        have hw : |(1688179283/10000000000 : ℝ)|=(1688179283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-846042491/5000000000 : ℝ)|^17 ≤ (9795206771273/100000000000000 : ℝ)^13
        have hw : |(-846042491/5000000000 : ℝ)|=(846042491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1693325247/2000000000 : ℝ)|^17 ≤ (40219571078759/50000000000000 : ℝ)^13
        have hw : |(1693325247/2000000000 : ℝ)|=(1693325247/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307057_s1_s1_9 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (425838457/1250000000 : ℝ)*x 0 + (1613896981/2000000000 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (425838457/1250000000 : ℝ)^17 ≤ (24458955244971/100000000000000 : ℝ)^13 := by
    have hnat : (425838457 : ℕ)^17*100000000000000^13 ≤ 24458955244971^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425838457 1250000000 24458955244971 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1613896981/2000000000 : ℝ)^17 ≤ (75541044748709/100000000000000 : ℝ)^13 := by
    have hnat : (1613896981 : ℕ)^17*100000000000000^13 ≤ 75541044748709^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1613896981 2000000000 75541044748709 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^17 ≤ (0 : ℝ)^13 := by
    have hnat : (0 : ℕ)^17*1^13 ≤ 0^13*1^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(425838457/1250000000 : ℝ), (1613896981/2000000000 : ℝ), (0 : ℝ)] ![(24458955244971/100000000000000 : ℝ), (75541044748709/100000000000000 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(425838457/1250000000 : ℝ)|^17 ≤ (24458955244971/100000000000000 : ℝ)^13
        have hw : |(425838457/1250000000 : ℝ)|=(425838457/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1613896981/2000000000 : ℝ)|^17 ≤ (75541044748709/100000000000000 : ℝ)^13
        have hw : |(1613896981/2000000000 : ℝ)|=(1613896981/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^17 ≤ (0 : ℝ)^13
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307057_s1_s1_13 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (189534757/625000000 : ℝ)*x 0 + (74073607/100000000 : ℝ)*x 1 + (953505213/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (189534757/625000000 : ℝ)^17 ≤ (10503533323487/50000000000000 : ℝ)^13 := by
    have hnat : (189534757 : ℕ)^17*50000000000000^13 ≤ 10503533323487^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      189534757 625000000 10503533323487 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (74073607/100000000 : ℝ)^17 ≤ (67539828333827/100000000000000 : ℝ)^13 := by
    have hnat : (74073607 : ℕ)^17*100000000000000^13 ≤ 67539828333827^13*100000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74073607 100000000 67539828333827 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (953505213/5000000000 : ℝ)^17 ≤ (5726552496671/50000000000000 : ℝ)^13 := by
    have hnat : (953505213 : ℕ)^17*50000000000000^13 ≤ 5726552496671^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      953505213 5000000000 5726552496671 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(189534757/625000000 : ℝ), (74073607/100000000 : ℝ), (953505213/5000000000 : ℝ)] ![(10503533323487/50000000000000 : ℝ), (67539828333827/100000000000000 : ℝ), (5726552496671/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(189534757/625000000 : ℝ)|^17 ≤ (10503533323487/50000000000000 : ℝ)^13
        have hw : |(189534757/625000000 : ℝ)|=(189534757/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(74073607/100000000 : ℝ)|^17 ≤ (67539828333827/100000000000000 : ℝ)^13
        have hw : |(74073607/100000000 : ℝ)|=(74073607/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(953505213/5000000000 : ℝ)|^17 ≤ (5726552496671/50000000000000 : ℝ)^13
        have hw : |(953505213/5000000000 : ℝ)|=(953505213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307057_s1_s1_14 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-344974907/2000000000 : ℝ)*x 0 + (105424919/625000000 : ℝ)*x 1 + (8447421899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (344974907/2000000000 : ℝ)^17 ≤ (1004416105041/10000000000000 : ℝ)^13 := by
    have hnat : (344974907 : ℕ)^17*10000000000000^13 ≤ 1004416105041^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344974907 2000000000 1004416105041 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105424919/625000000 : ℝ)^17 ≤ (609700549407/6250000000000 : ℝ)^13 := by
    have hnat : (105424919 : ℕ)^17*6250000000000^13 ≤ 609700549407^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105424919 625000000 609700549407 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8447421899/10000000000 : ℝ)^17 ≤ (20050157537189/25000000000000 : ℝ)^13 := by
    have hnat : (8447421899 : ℕ)^17*25000000000000^13 ≤ 20050157537189^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8447421899 10000000000 20050157537189 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-344974907/2000000000 : ℝ), (105424919/625000000 : ℝ), (8447421899/10000000000 : ℝ)] ![(1004416105041/10000000000000 : ℝ), (609700549407/6250000000000 : ℝ), (20050157537189/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-344974907/2000000000 : ℝ)|^17 ≤ (1004416105041/10000000000000 : ℝ)^13
        have hw : |(-344974907/2000000000 : ℝ)|=(344974907/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(105424919/625000000 : ℝ)|^17 ≤ (609700549407/6250000000000 : ℝ)^13
        have hw : |(105424919/625000000 : ℝ)|=(105424919/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8447421899/10000000000 : ℝ)|^17 ≤ (20050157537189/25000000000000 : ℝ)^13
        have hw : |(8447421899/10000000000 : ℝ)|=(8447421899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307057_s1_s1_15 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (625575147/5000000000 : ℝ)*x 0 + (-1049623307/5000000000 : ℝ)*x 1 + (1058075421/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (625575147/5000000000 : ℝ)^17 ≤ (3300111079007/50000000000000 : ℝ)^13 := by
    have hnat : (625575147 : ℕ)^17*50000000000000^13 ≤ 3300111079007^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      625575147 5000000000 3300111079007 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049623307/5000000000 : ℝ)^17 ≤ (129857669143/1000000000000 : ℝ)^13 := by
    have hnat : (1049623307 : ℕ)^17*1000000000000^13 ≤ 129857669143^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049623307 5000000000 129857669143 1000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1058075421/1250000000 : ℝ)^17 ≤ (40207005457057/50000000000000 : ℝ)^13 := by
    have hnat : (1058075421 : ℕ)^17*50000000000000^13 ≤ 40207005457057^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058075421 1250000000 40207005457057 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(625575147/5000000000 : ℝ), (-1049623307/5000000000 : ℝ), (1058075421/1250000000 : ℝ)] ![(3300111079007/50000000000000 : ℝ), (129857669143/1000000000000 : ℝ), (40207005457057/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(625575147/5000000000 : ℝ)|^17 ≤ (3300111079007/50000000000000 : ℝ)^13
        have hw : |(625575147/5000000000 : ℝ)|=(625575147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1049623307/5000000000 : ℝ)|^17 ≤ (129857669143/1000000000000 : ℝ)^13
        have hw : |(-1049623307/5000000000 : ℝ)|=(1049623307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1058075421/1250000000 : ℝ)|^17 ≤ (40207005457057/50000000000000 : ℝ)^13
        have hw : |(1058075421/1250000000 : ℝ)|=(1058075421/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307057_s1_s1_16 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4032127631/5000000000 : ℝ)*x 0 + (68270473/200000000 : ℝ)*x 1 + (1/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4032127631/5000000000 : ℝ)^17 ≤ (37738515631541/50000000000000 : ℝ)^13 := by
    have hnat : (4032127631 : ℕ)^17*50000000000000^13 ≤ 37738515631541^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4032127631 5000000000 37738515631541 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (68270473/200000000 : ℝ)^17 ≤ (24522968719691/100000000000000 : ℝ)^13 := by
    have hnat : (68270473 : ℕ)^17*100000000000000^13 ≤ 24522968719691^13*200000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68270473 200000000 24522968719691 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1/10000000000 : ℝ)^17 ≤ (9/100000000000000 : ℝ)^13 := by
    have hnat : (1 : ℕ)^17*100000000000000^13 ≤ 9^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 10000000000 9 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4032127631/5000000000 : ℝ), (68270473/200000000 : ℝ), (1/10000000000 : ℝ)] ![(37738515631541/50000000000000 : ℝ), (24522968719691/100000000000000 : ℝ), (9/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4032127631/5000000000 : ℝ)|^17 ≤ (37738515631541/50000000000000 : ℝ)^13
        have hw : |(4032127631/5000000000 : ℝ)|=(4032127631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(68270473/200000000 : ℝ)|^17 ≤ (24522968719691/100000000000000 : ℝ)^13
        have hw : |(68270473/200000000 : ℝ)|=(68270473/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1/10000000000 : ℝ)|^17 ≤ (9/100000000000000 : ℝ)^13
        have hw : |(1/10000000000 : ℝ)|=(1/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307057_s1_s1_20 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (7376911001/10000000000 : ℝ)*x 0 + (3071935859/10000000000 : ℝ)*x 1 + (76307913/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7376911001/10000000000 : ℝ)^17 ≤ (67176992620431/100000000000000 : ℝ)^13 := by
    have hnat : (7376911001 : ℕ)^17*100000000000000^13 ≤ 67176992620431^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7376911001 10000000000 67176992620431 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3071935859/10000000000 : ℝ)^17 ≤ (854580137217/4000000000000 : ℝ)^13 := by
    have hnat : (3071935859 : ℕ)^17*4000000000000^13 ≤ 854580137217^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3071935859 10000000000 854580137217 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (76307913/400000000 : ℝ)^17 ≤ (458340157443/4000000000000 : ℝ)^13 := by
    have hnat : (76307913 : ℕ)^17*4000000000000^13 ≤ 458340157443^13*400000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76307913 400000000 458340157443 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7376911001/10000000000 : ℝ), (3071935859/10000000000 : ℝ), (76307913/400000000 : ℝ)] ![(67176992620431/100000000000000 : ℝ), (854580137217/4000000000000 : ℝ), (458340157443/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7376911001/10000000000 : ℝ)|^17 ≤ (67176992620431/100000000000000 : ℝ)^13
        have hw : |(7376911001/10000000000 : ℝ)|=(7376911001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3071935859/10000000000 : ℝ)|^17 ≤ (854580137217/4000000000000 : ℝ)^13
        have hw : |(3071935859/10000000000 : ℝ)|=(3071935859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(76307913/400000000 : ℝ)|^17 ≤ (458340157443/4000000000000 : ℝ)^13
        have hw : |(76307913/400000000 : ℝ)|=(76307913/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307057_s1_s1_21 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-5603000467/10000000000 : ℝ)*x 0 + (442720919/2500000000 : ℝ)*x 1 + (1304646709/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5603000467/10000000000 : ℝ)^17 ≤ (2930162108151/6250000000000 : ℝ)^13 := by
    have hnat : (5603000467 : ℕ)^17*6250000000000^13 ≤ 2930162108151^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5603000467 10000000000 2930162108151 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (442720919/2500000000 : ℝ)^17 ≤ (1039594304323/10000000000000 : ℝ)^13 := by
    have hnat : (442720919 : ℕ)^17*10000000000000^13 ≤ 1039594304323^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442720919 2500000000 1039594304323 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304646709/2500000000 : ℝ)^17 ≤ (42721463209259/100000000000000 : ℝ)^13 := by
    have hnat : (1304646709 : ℕ)^17*100000000000000^13 ≤ 42721463209259^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304646709 2500000000 42721463209259 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5603000467/10000000000 : ℝ), (442720919/2500000000 : ℝ), (1304646709/2500000000 : ℝ)] ![(2930162108151/6250000000000 : ℝ), (1039594304323/10000000000000 : ℝ), (42721463209259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5603000467/10000000000 : ℝ)|^17 ≤ (2930162108151/6250000000000 : ℝ)^13
        have hw : |(-5603000467/10000000000 : ℝ)|=(5603000467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(442720919/2500000000 : ℝ)|^17 ≤ (1039594304323/10000000000000 : ℝ)^13
        have hw : |(442720919/2500000000 : ℝ)|=(442720919/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304646709/2500000000 : ℝ)|^17 ≤ (42721463209259/100000000000000 : ℝ)^13
        have hw : |(1304646709/2500000000 : ℝ)|=(1304646709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307057_s1_s1_22 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (368350649/5000000000 : ℝ)*x 0 + (-215340911/400000000 : ℝ)*x 1 + (6082978921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (368350649/5000000000 : ℝ)^17 ≤ (3301913734587/100000000000000 : ℝ)^13 := by
    have hnat : (368350649 : ℕ)^17*100000000000000^13 ≤ 3301913734587^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      368350649 5000000000 3301913734587 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215340911/400000000 : ℝ)^17 ≤ (4449567529293/10000000000000 : ℝ)^13 := by
    have hnat : (215340911 : ℕ)^17*10000000000000^13 ≤ 4449567529293^13*400000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215340911 400000000 4449567529293 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6082978921/10000000000 : ℝ)^17 ≤ (52202410953319/100000000000000 : ℝ)^13 := by
    have hnat : (6082978921 : ℕ)^17*100000000000000^13 ≤ 52202410953319^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6082978921 10000000000 52202410953319 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(368350649/5000000000 : ℝ), (-215340911/400000000 : ℝ), (6082978921/10000000000 : ℝ)] ![(3301913734587/100000000000000 : ℝ), (4449567529293/10000000000000 : ℝ), (52202410953319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(368350649/5000000000 : ℝ)|^17 ≤ (3301913734587/100000000000000 : ℝ)^13
        have hw : |(368350649/5000000000 : ℝ)|=(368350649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-215340911/400000000 : ℝ)|^17 ≤ (4449567529293/10000000000000 : ℝ)^13
        have hw : |(-215340911/400000000 : ℝ)|=(215340911/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6082978921/10000000000 : ℝ)|^17 ≤ (52202410953319/100000000000000 : ℝ)^13
        have hw : |(6082978921/10000000000 : ℝ)|=(6082978921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307057_s1_s1_23 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6256764787/10000000000 : ℝ)*x 0 + (5474832443/10000000000 : ℝ)*x 1 + (133472751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6256764787/10000000000 : ℝ)^17 ≤ (54161194944217/100000000000000 : ℝ)^13 := by
    have hnat : (6256764787 : ℕ)^17*100000000000000^13 ≤ 54161194944217^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6256764787 10000000000 54161194944217 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5474832443/10000000000 : ℝ)^17 ≤ (9097028292453/20000000000000 : ℝ)^13 := by
    have hnat : (5474832443 : ℕ)^17*20000000000000^13 ≤ 9097028292453^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5474832443 10000000000 9097028292453 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (133472751/10000000000 : ℝ)^17 ≤ (176831789867/50000000000000 : ℝ)^13 := by
    have hnat : (133472751 : ℕ)^17*50000000000000^13 ≤ 176831789867^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133472751 10000000000 176831789867 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6256764787/10000000000 : ℝ), (5474832443/10000000000 : ℝ), (133472751/10000000000 : ℝ)] ![(54161194944217/100000000000000 : ℝ), (9097028292453/20000000000000 : ℝ), (176831789867/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6256764787/10000000000 : ℝ)|^17 ≤ (54161194944217/100000000000000 : ℝ)^13
        have hw : |(6256764787/10000000000 : ℝ)|=(6256764787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5474832443/10000000000 : ℝ)|^17 ≤ (9097028292453/20000000000000 : ℝ)^13
        have hw : |(5474832443/10000000000 : ℝ)|=(5474832443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(133472751/10000000000 : ℝ)|^17 ≤ (176831789867/50000000000000 : ℝ)^13
        have hw : |(133472751/10000000000 : ℝ)|=(133472751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307057_s1_s1_27 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (564367329/2000000000 : ℝ)*x 0 + (5474832443/10000000000 : ℝ)*x 1 + (4519407061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (564367329/2000000000 : ℝ)^17 ≤ (1194936340499/6250000000000 : ℝ)^13 := by
    have hnat : (564367329 : ℕ)^17*6250000000000^13 ≤ 1194936340499^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564367329 2000000000 1194936340499 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5474832443/10000000000 : ℝ)^17 ≤ (9097028292453/20000000000000 : ℝ)^13 := by
    have hnat : (5474832443 : ℕ)^17*20000000000000^13 ≤ 9097028292453^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5474832443 10000000000 9097028292453 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4519407061/10000000000 : ℝ)^17 ≤ (17697938538269/50000000000000 : ℝ)^13 := by
    have hnat : (4519407061 : ℕ)^17*50000000000000^13 ≤ 17697938538269^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4519407061 10000000000 17697938538269 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(564367329/2000000000 : ℝ), (5474832443/10000000000 : ℝ), (4519407061/10000000000 : ℝ)] ![(1194936340499/6250000000000 : ℝ), (9097028292453/20000000000000 : ℝ), (17697938538269/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(564367329/2000000000 : ℝ)|^17 ≤ (1194936340499/6250000000000 : ℝ)^13
        have hw : |(564367329/2000000000 : ℝ)|=(564367329/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5474832443/10000000000 : ℝ)|^17 ≤ (9097028292453/20000000000000 : ℝ)^13
        have hw : |(5474832443/10000000000 : ℝ)|=(5474832443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4519407061/10000000000 : ℝ)|^17 ≤ (17697938538269/50000000000000 : ℝ)^13
        have hw : |(4519407061/10000000000 : ℝ)|=(4519407061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c307057_s1 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((94019/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(94019/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(93/100 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(93/100 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(10719/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(10719/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((20873/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20873/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(83297/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(83297/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(36299/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(36299/100000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4817/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4817/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (92559/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s1_pow0 : (94019/100000 : ℝ) ^ (135/32 : ℝ) ≤ (19272738902945869853/25000000000000000000 : ℝ) := by
    have hpowers : (94019/100000 : ℝ)^135 ≤ (19272738902945869853/25000000000000000000 : ℝ)^32 := by
      have hnat : (94019 : ℕ)^135*25000000000000000000^32 ≤ 19272738902945869853^32*100000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        94019 100000 19272738902945869853 25000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (94019/100000 : ℝ)) (X := (19272738902945869853/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (44272738902945869853/25000000000000000000 : ℝ) ≤ (11450692043960913/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (44272738902945869853/25000000000000000000 : ℝ)^32 ≤ (11450692043960913/10000000000000000 : ℝ)^135 := by
      have hnat : (44272738902945869853 : ℕ)^32*10000000000000000^135 ≤ 11450692043960913^135*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        44272738902945869853 25000000000000000000 11450692043960913 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11450692043960913/10000000000000000 : ℝ)) (X := (44272738902945869853/25000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (31772738902945869853/12500000000000000000 : ℝ) ≤ (2494963984892109/2000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (31772738902945869853/12500000000000000000 : ℝ)^32 ≤ (2494963984892109/2000000000000000 : ℝ)^135 := by
      have hnat : (31772738902945869853 : ℕ)^32*2000000000000000^135 ≤ 2494963984892109^135*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31772738902945869853 12500000000000000000 2494963984892109 2000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2494963984892109/2000000000000000 : ℝ)) (X := (31772738902945869853/12500000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1450692043960913/9401900000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(64007992531227/587618750000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (94019/100000 : ℝ)) (alpha := (1450692043960913/9401900000000000 : ℝ)) (beta := (64007992531227/587618750000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (94019/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1450692043960913/9401900000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(64007992531227/587618750000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (93/100 : ℝ) ^ (135/32 : ℝ) ≤ (73627056641451336699/100000000000000000000 : ℝ) := by
    have hpowers : (93/100 : ℝ)^135 ≤ (73627056641451336699/100000000000000000000 : ℝ)^32 := by
      have hnat : (93 : ℕ)^135*100000000000000000000^32 ≤ 73627056641451336699^32*100^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        93 100 73627056641451336699 100000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (93/100 : ℝ)) (X := (73627056641451336699/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (173627056641451336699/100000000000000000000 : ℝ) ≤ (2849300195713359/2500000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (173627056641451336699/100000000000000000000 : ℝ)^32 ≤ (2849300195713359/2500000000000000 : ℝ)^135 := by
      have hnat : (173627056641451336699 : ℕ)^32*2500000000000000^135 ≤ 2849300195713359^135*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        173627056641451336699 100000000000000000000 2849300195713359 2500000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2849300195713359/2500000000000000 : ℝ)) (X := (173627056641451336699/100000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (123627056641451336699/50000000000000000000 : ℝ) ≤ (12393374586766409/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (123627056641451336699/50000000000000000000 : ℝ)^32 ≤ (12393374586766409/10000000000000000 : ℝ)^135 := by
      have hnat : (123627056641451336699 : ℕ)^32*10000000000000000^135 ≤ 12393374586766409^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        123627056641451336699 50000000000000000000 12393374586766409 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12393374586766409/10000000000000000 : ℝ)) (X := (123627056641451336699/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(349300195713359/2325000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(996173803912973/9300000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (93/100 : ℝ)) (alpha := (349300195713359/2325000000000000 : ℝ)) (beta := (996173803912973/9300000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (93/100 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(349300195713359/2325000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(996173803912973/9300000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (10719/20000 : ℝ) ^ (135/32 : ℝ) ≤ (7198517026969625383/100000000000000000000 : ℝ) := by
    have hpowers : (10719/20000 : ℝ)^135 ≤ (7198517026969625383/100000000000000000000 : ℝ)^32 := by
      have hnat : (10719 : ℕ)^135*100000000000000000000^32 ≤ 7198517026969625383^32*20000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10719 20000 7198517026969625383 100000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10719/20000 : ℝ)) (X := (7198517026969625383/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (107198517026969625383/100000000000000000000 : ℝ) ≤ (508306733359291/500000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (107198517026969625383/100000000000000000000 : ℝ)^32 ≤ (508306733359291/500000000000000 : ℝ)^135 := by
      have hnat : (107198517026969625383 : ℕ)^32*500000000000000^135 ≤ 508306733359291^135*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        107198517026969625383 100000000000000000000 508306733359291 500000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (508306733359291/500000000000000 : ℝ)) (X := (107198517026969625383/100000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (57198517026969625383/50000000000000000000 : ℝ) ≤ (2580990888746029/2500000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (57198517026969625383/50000000000000000000 : ℝ)^32 ≤ (2580990888746029/2500000000000000 : ℝ)^135 := by
      have hnat : (57198517026969625383 : ℕ)^32*2500000000000000^135 ≤ 2580990888746029^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57198517026969625383 50000000000000000000 2580990888746029 2500000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2580990888746029/2500000000000000 : ℝ)) (X := (57198517026969625383/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(8306733359291/267975000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(19728610974787/669937500000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (10719/20000 : ℝ)) (alpha := (8306733359291/267975000000000 : ℝ)) (beta := (19728610974787/669937500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (10719/20000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(8306733359291/267975000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(19728610974787/669937500000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-774776913/2500000000 : ℝ)*X 0 0+(3084296699/10000000000 : ℝ)*X 0 1+(6498264917/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((309078621/1000000000 : ℝ)*X 1 0+(-1538007513/5000000000 : ℝ)*X 1 1+(6511466117/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5874992621/10000000000 : ℝ)*X 2 0+(589573531/1000000000 : ℝ)*X 2 1+(1866633/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((4893504647/10000000000 : ℝ)*X 0 0+(4910782021/10000000000 : ℝ)*X 0 1+(3061336281/10000000000 : ℝ)*X 0 2+(4893504647/10000000000 : ℝ)*X 1 0+(4910782021/10000000000 : ℝ)*X 1 1+(3061336281/10000000000 : ℝ)*X 1 2+(4893504647/10000000000 : ℝ)*X 2 0+(4910782021/10000000000 : ℝ)*X 2 1+(3061336281/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-2127044277/10000000000 : ℝ)*X 0 0+(311445573/2500000000 : ℝ)*X 0 1+(4224720459/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((1688179283/10000000000 : ℝ)*X 1 0+(-846042491/5000000000 : ℝ)*X 1 1+(1693325247/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((425838457/1250000000 : ℝ)*X 2 0+(1613896981/2000000000 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((189534757/625000000 : ℝ)*X 0 0+(74073607/100000000 : ℝ)*X 0 1+(953505213/5000000000 : ℝ)*X 0 2+(189534757/625000000 : ℝ)*X 1 0+(74073607/100000000 : ℝ)*X 1 1+(953505213/5000000000 : ℝ)*X 1 2+(189534757/625000000 : ℝ)*X 2 0+(74073607/100000000 : ℝ)*X 2 1+(953505213/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-344974907/2000000000 : ℝ)*X 0 0+(105424919/625000000 : ℝ)*X 0 1+(8447421899/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((625575147/5000000000 : ℝ)*X 1 0+(-1049623307/5000000000 : ℝ)*X 1 1+(1058075421/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((4032127631/5000000000 : ℝ)*X 2 0+(68270473/200000000 : ℝ)*X 2 1+(1/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((7376911001/10000000000 : ℝ)*X 0 0+(3071935859/10000000000 : ℝ)*X 0 1+(76307913/400000000 : ℝ)*X 0 2+(7376911001/10000000000 : ℝ)*X 1 0+(3071935859/10000000000 : ℝ)*X 1 1+(76307913/400000000 : ℝ)*X 1 2+(7376911001/10000000000 : ℝ)*X 2 0+(3071935859/10000000000 : ℝ)*X 2 1+(76307913/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-5603000467/10000000000 : ℝ)*X 0 0+(442720919/2500000000 : ℝ)*X 0 1+(1304646709/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((368350649/5000000000 : ℝ)*X 1 0+(-215340911/400000000 : ℝ)*X 1 1+(6082978921/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((6256764787/10000000000 : ℝ)*X 2 0+(5474832443/10000000000 : ℝ)*X 2 1+(133472751/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((564367329/2000000000 : ℝ)*X 0 0+(5474832443/10000000000 : ℝ)*X 0 1+(4519407061/10000000000 : ℝ)*X 0 2+(564367329/2000000000 : ℝ)*X 1 0+(5474832443/10000000000 : ℝ)*X 1 1+(4519407061/10000000000 : ℝ)*X 1 2+(564367329/2000000000 : ℝ)*X 2 0+(5474832443/10000000000 : ℝ)*X 2 1+(4519407061/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307057_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((20873/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20873/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1151883830951133648471137/230756250000000000000000000000 : ℝ) := by norm_num
    linear_combination (456809334643/500000000000 : ℝ)*(base7) + (389831/1000000000000 : ℝ)*(base50) + (41577/62500000000 : ℝ)*(base59) + (3644736549/1953125000 : ℝ)*(major_s1_0) + (3644736549/1953125000 : ℝ)*(major_s1_1) + (3644736549/1953125000 : ℝ)*(major_s1_2) + (282559/200000000000 : ℝ)*(sp_s1_0) + (1967940752553/1000000000000 : ℝ)*(sp_s1_7) + (196797501083/100000000000 : ℝ)*(sp_s1_8) + (983990993157/500000000000 : ℝ)*(sp_s1_9) + (528521700133/250000000000 : ℝ)*(sp_s1_13) + (19910483/500000000000 : ℝ)*(sp_s1_14) + (1743871/250000000000 : ℝ)*(sp_s1_15) + (454309/500000000000 : ℝ)*(sp_s1_27) + (150058629983/125000000000 : ℝ)*(f.failure) + (983990993157/500000000000 : ℝ)*(f.sum) + (59747785576059643/692268750000000000000000000000 : ℝ)*base63 + (321673141864817/893250000000000000000000000 : ℝ)*base65 + (34234160362487/193750000000000000000000000 : ℝ)*base66 + (3865653870193/44662500000000000000000000 : ℝ)*base68 + (11911206240200780489/41991235875000000000000000000000 : ℝ)*base71 + (93868118967517/1175237500000000000000000000 : ℝ)*base73 + (15731483373233/96875000000000000000000000 : ℝ)*base75 + (38782080008501/587618750000000000000000000 : ℝ)*base76 + (2156471288819433689/9108090625000000000000000000000 : ℝ)*base78 + (327/1562500000000000 : ℝ)*base86 + (327/1562500000000000 : ℝ)*base88 + (327/1562500000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(83297/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(83297/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1669902252519499393715410816283/130172831212500000000000000000000000 : ℝ) := by norm_num
    linear_combination (228229797693/250000000000 : ℝ)*(base7) + (376597/125000000000 : ℝ)*(base13) + (1506901/1000000000000 : ℝ)*(base40) + (2993191387/1000000000000 : ℝ)*(base60) + (1866245095201/1000000000000 : ℝ)*(major_s1_0) + (1866245095201/1000000000000 : ℝ)*(major_s1_1) + (1866245095201/1000000000000 : ℝ)*(major_s1_2) + (783853/125000000000 : ℝ)*(sp_s1_1) + (2606579/1000000000000 : ℝ)*(sp_s1_6) + (126870597/1000000000000 : ℝ)*(sp_s1_8) + (1968597894821/1000000000000 : ℝ)*(sp_s1_14) + (1968467766177/1000000000000 : ℝ)*(sp_s1_15) + (1968600907597/1000000000000 : ℝ)*(sp_s1_16) + (2113475674823/1000000000000 : ℝ)*(sp_s1_20) + (1200559090629/1000000000000 : ℝ)*(f.failure) + (1968600907597/1000000000000 : ℝ)*(f.sum) + (3723028109217605393/8307225000000000000000000000000 : ℝ)*base62 + (143574749054531/334968750000000000000000000 : ℝ)*base64 + (580595593652573/9300000000000000000000000000 : ℝ)*base67 + (341551790221657/535950000000000000000000000 : ℝ)*base68 + (31844014319020039811/503894830500000000000000000000000 : ℝ)*base71 + (5287594485230719/4700950000000000000000000000 : ℝ)*base72 + (552987197634841/2325000000000000000000000000 : ℝ)*base74 + (268193632163027/9401900000000000000000000000 : ℝ)*base76 + (172568859667009490823113/874376700000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (401/12500000000000000 : ℝ)*base86 + (401/12500000000000000 : ℝ)*base88 + (401/12500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(36299/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(36299/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (134962757955737401117321419899/17356377495000000000000000000000000 : ℝ) := by norm_num
    linear_combination (880270391081/1000000000000 : ℝ)*(base5) + (34279211497/100000000000 : ℝ)*(base7) + (55779/1000000000000 : ℝ)*(base8) + (9758099/1000000000000 : ℝ)*(base40) + (121573646839/1000000000000 : ℝ)*(base50) + (31587343353/40000000000 : ℝ)*(base59) + (121122865437/100000000000 : ℝ)*(major_s1_0) + (121122865437/100000000000 : ℝ)*(major_s1_1) + (121122865437/100000000000 : ℝ)*(major_s1_2) + (88255201/500000000000 : ℝ)*(sp_s1_2) + (1431745615119/1000000000000 : ℝ)*(sp_s1_21) + (715872835449/500000000000 : ℝ)*(sp_s1_22) + (288979943947/125000000000 : ℝ)*(sp_s1_23) + (24170746727/100000000000 : ℝ)*(sp_s1_27) + (38959287169/50000000000 : ℝ)*(f.failure) + (715872835449/500000000000 : ℝ)*(f.sum) + (21908522988618097/276907500000000000000000000000 : ℝ)*base62 + (25177369516753/89325000000000000000000000 : ℝ)*base65 + (61939536964067/310000000000000000000000000 : ℝ)*base67 + (523609654799/17865000000000000000000000 : ℝ)*base68 + (4436552472791663569/16796494350000000000000000000000 : ℝ)*base71 + (7451924326947/58761875000000000000000000 : ℝ)*base73 + (2989844965039/77500000000000000000000000 : ℝ)*base74 + (28414067859419/940190000000000000000000000 : ℝ)*base77 + (17440149991839235273/29145890000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (411/625000000000000 : ℝ)*base86 + (411/625000000000000 : ℝ)*base88 + (411/625000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((94019/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(94019/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(93/100 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(93/100 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(10719/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(10719/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((20873/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20873/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(83297/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(83297/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(36299/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(36299/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c307057_s1 p hpa hpb X hX hprev0

#print axioms solution
