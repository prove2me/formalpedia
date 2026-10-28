-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301086_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:44:46.551152+00:00
-- url     : https://prove2.me/submissions/c7e80f31-fe56-4085-9e55-f8d888fcf5e3

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
theorem collision_support_c301086_s1_s1_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6632125251/10000000000 : ℝ)*x 0 + (3150101441/10000000000 : ℝ)*x 1 + (75419663/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6632125251/10000000000 : ℝ)^65 ≤ (57998514840537/100000000000000 : ℝ)^49 := by
    have hnat : (6632125251 : ℕ)^65*100000000000000^49 ≤ 57998514840537^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6632125251 10000000000 57998514840537 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3150101441/10000000000 : ℝ)^65 ≤ (21602904415189/100000000000000 : ℝ)^49 := by
    have hnat : (3150101441 : ℕ)^65*100000000000000^49 ≤ 21602904415189^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3150101441 10000000000 21602904415189 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (75419663/250000000 : ℝ)^65 ≤ (2039858072513/10000000000000 : ℝ)^49 := by
    have hnat : (75419663 : ℕ)^65*10000000000000^49 ≤ 2039858072513^49*250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75419663 250000000 2039858072513 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6632125251/10000000000 : ℝ), (3150101441/10000000000 : ℝ), (75419663/250000000 : ℝ)] ![(57998514840537/100000000000000 : ℝ), (21602904415189/100000000000000 : ℝ), (2039858072513/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6632125251/10000000000 : ℝ)|^65 ≤ (57998514840537/100000000000000 : ℝ)^49
        have hw : |(6632125251/10000000000 : ℝ)|=(6632125251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3150101441/10000000000 : ℝ)|^65 ≤ (21602904415189/100000000000000 : ℝ)^49
        have hw : |(3150101441/10000000000 : ℝ)|=(3150101441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(75419663/250000000 : ℝ)|^65 ≤ (2039858072513/10000000000000 : ℝ)^49
        have hw : |(75419663/250000000 : ℝ)|=(75419663/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301086_s1_s1_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3115802983/5000000000 : ℝ)*x 0 + (-435357407/1250000000 : ℝ)*x 1 + (-796230481/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3115802983/5000000000 : ℝ)^65 ≤ (53398688614201/100000000000000 : ℝ)^49 := by
    have hnat : (3115802983 : ℕ)^65*100000000000000^49 ≤ 53398688614201^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3115802983 5000000000 53398688614201 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (435357407/1250000000 : ℝ)^65 ≤ (4936213978029/20000000000000 : ℝ)^49 := by
    have hnat : (435357407 : ℕ)^65*20000000000000^49 ≤ 4936213978029^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435357407 1250000000 4936213978029 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (796230481/2500000000 : ℝ)^65 ≤ (21920241481971/100000000000000 : ℝ)^49 := by
    have hnat : (796230481 : ℕ)^65*100000000000000^49 ≤ 21920241481971^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      796230481 2500000000 21920241481971 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3115802983/5000000000 : ℝ), (-435357407/1250000000 : ℝ), (-796230481/2500000000 : ℝ)] ![(53398688614201/100000000000000 : ℝ), (4936213978029/20000000000000 : ℝ), (21920241481971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3115802983/5000000000 : ℝ)|^65 ≤ (53398688614201/100000000000000 : ℝ)^49
        have hw : |(3115802983/5000000000 : ℝ)|=(3115802983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-435357407/1250000000 : ℝ)|^65 ≤ (4936213978029/20000000000000 : ℝ)^49
        have hw : |(-435357407/1250000000 : ℝ)|=(435357407/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-796230481/2500000000 : ℝ)|^65 ≤ (21920241481971/100000000000000 : ℝ)^49
        have hw : |(-796230481/2500000000 : ℝ)|=(796230481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301086_s1_s1_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (912630839/2500000000 : ℝ)*x 0 + (-590489889/2500000000 : ℝ)*x 1 + (3358543533/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (912630839/2500000000 : ℝ)^65 ≤ (13134716059621/50000000000000 : ℝ)^49 := by
    have hnat : (912630839 : ℕ)^65*50000000000000^49 ≤ 13134716059621^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      912630839 2500000000 13134716059621 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (590489889/2500000000 : ℝ)^65 ≤ (737219362077/5000000000000 : ℝ)^49 := by
    have hnat : (590489889 : ℕ)^65*5000000000000^49 ≤ 737219362077^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      590489889 2500000000 737219362077 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3358543533/5000000000 : ℝ)^65 ≤ (58986180631301/100000000000000 : ℝ)^49 := by
    have hnat : (3358543533 : ℕ)^65*100000000000000^49 ≤ 58986180631301^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3358543533 5000000000 58986180631301 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(912630839/2500000000 : ℝ), (-590489889/2500000000 : ℝ), (3358543533/5000000000 : ℝ)] ![(13134716059621/50000000000000 : ℝ), (737219362077/5000000000000 : ℝ), (58986180631301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(912630839/2500000000 : ℝ)|^65 ≤ (13134716059621/50000000000000 : ℝ)^49
        have hw : |(912630839/2500000000 : ℝ)|=(912630839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-590489889/2500000000 : ℝ)|^65 ≤ (737219362077/5000000000000 : ℝ)^49
        have hw : |(-590489889/2500000000 : ℝ)|=(590489889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3358543533/5000000000 : ℝ)|^65 ≤ (58986180631301/100000000000000 : ℝ)^49
        have hw : |(3358543533/5000000000 : ℝ)|=(3358543533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301086_s1_s1_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (39452709/2500000000 : ℝ)*x 0 + (-8542309709/10000000000 : ℝ)*x 1 + (2797258139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (39452709/2500000000 : ℝ)^65 ≤ (203583856823/50000000000000 : ℝ)^49 := by
    have hnat : (39452709 : ℕ)^65*50000000000000^49 ≤ 203583856823^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39452709 2500000000 203583856823 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8542309709/10000000000 : ℝ)^65 ≤ (81139543166823/100000000000000 : ℝ)^49 := by
    have hnat : (8542309709 : ℕ)^65*100000000000000^49 ≤ 81139543166823^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8542309709 10000000000 81139543166823 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2797258139/10000000000 : ℝ)^65 ≤ (1845328910067/10000000000000 : ℝ)^49 := by
    have hnat : (2797258139 : ℕ)^65*10000000000000^49 ≤ 1845328910067^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2797258139 10000000000 1845328910067 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(39452709/2500000000 : ℝ), (-8542309709/10000000000 : ℝ), (2797258139/10000000000 : ℝ)] ![(203583856823/50000000000000 : ℝ), (81139543166823/100000000000000 : ℝ), (1845328910067/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(39452709/2500000000 : ℝ)|^65 ≤ (203583856823/50000000000000 : ℝ)^49
        have hw : |(39452709/2500000000 : ℝ)|=(39452709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8542309709/10000000000 : ℝ)|^65 ≤ (81139543166823/100000000000000 : ℝ)^49
        have hw : |(-8542309709/10000000000 : ℝ)|=(8542309709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2797258139/10000000000 : ℝ)|^65 ≤ (1845328910067/10000000000000 : ℝ)^49
        have hw : |(2797258139/10000000000 : ℝ)|=(2797258139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301086_s1_s1_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (406618901/1250000000 : ℝ)*x 0 + (7154097619/10000000000 : ℝ)*x 1 + (2188597519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (406618901/1250000000 : ℝ)^65 ≤ (2254349456261/10000000000000 : ℝ)^49 := by
    have hnat : (406618901 : ℕ)^65*10000000000000^49 ≤ 2254349456261^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      406618901 1250000000 2254349456261 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7154097619/10000000000 : ℝ)^65 ≤ (12826039337017/20000000000000 : ℝ)^49 := by
    have hnat : (7154097619 : ℕ)^65*20000000000000^49 ≤ 12826039337017^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7154097619 10000000000 12826039337017 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2188597519/10000000000 : ℝ)^65 ≤ (1665788592881/12500000000000 : ℝ)^49 := by
    have hnat : (2188597519 : ℕ)^65*12500000000000^49 ≤ 1665788592881^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188597519 10000000000 1665788592881 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(406618901/1250000000 : ℝ), (7154097619/10000000000 : ℝ), (2188597519/10000000000 : ℝ)] ![(2254349456261/10000000000000 : ℝ), (12826039337017/20000000000000 : ℝ), (1665788592881/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(406618901/1250000000 : ℝ)|^65 ≤ (2254349456261/10000000000000 : ℝ)^49
        have hw : |(406618901/1250000000 : ℝ)|=(406618901/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7154097619/10000000000 : ℝ)|^65 ≤ (12826039337017/20000000000000 : ℝ)^49
        have hw : |(7154097619/10000000000 : ℝ)|=(7154097619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2188597519/10000000000 : ℝ)|^65 ≤ (1665788592881/12500000000000 : ℝ)^49
        have hw : |(2188597519/10000000000 : ℝ)|=(2188597519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301086_s1_s1_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (299237537/312500000 : ℝ)*x 0 + (-13465909/2000000000 : ℝ)*x 1 + (-223356673/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (299237537/312500000 : ℝ)^65 ≤ (94409606710329/100000000000000 : ℝ)^49 := by
    have hnat : (299237537 : ℕ)^65*100000000000000^49 ≤ 94409606710329^49*312500000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299237537 312500000 94409606710329 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13465909/2000000000 : ℝ)^65 ≤ (6576856329/5000000000000 : ℝ)^49 := by
    have hnat : (13465909 : ℕ)^65*5000000000000^49 ≤ 6576856329^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13465909 2000000000 6576856329 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (223356673/2000000000 : ℝ)^65 ≤ (5458856151757/100000000000000 : ℝ)^49 := by
    have hnat : (223356673 : ℕ)^65*100000000000000^49 ≤ 5458856151757^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223356673 2000000000 5458856151757 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(299237537/312500000 : ℝ), (-13465909/2000000000 : ℝ), (-223356673/2000000000 : ℝ)] ![(94409606710329/100000000000000 : ℝ), (6576856329/5000000000000 : ℝ), (5458856151757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(299237537/312500000 : ℝ)|^65 ≤ (94409606710329/100000000000000 : ℝ)^49
        have hw : |(299237537/312500000 : ℝ)|=(299237537/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-13465909/2000000000 : ℝ)|^65 ≤ (6576856329/5000000000000 : ℝ)^49
        have hw : |(-13465909/2000000000 : ℝ)|=(13465909/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-223356673/2000000000 : ℝ)|^65 ≤ (5458856151757/100000000000000 : ℝ)^49
        have hw : |(-223356673/2000000000 : ℝ)|=(223356673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301086_s1_s1_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (943820233/2500000000 : ℝ)*x 0 + (-1433916679/10000000000 : ℝ)*x 1 + (902635847/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (943820233/2500000000 : ℝ)^65 ≤ (13733469473383/50000000000000 : ℝ)^49 := by
    have hnat : (943820233 : ℕ)^65*50000000000000^49 ≤ 13733469473383^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      943820233 2500000000 13733469473383 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1433916679/10000000000 : ℝ)^65 ≤ (14853650243/195312500000 : ℝ)^49 := by
    have hnat : (1433916679 : ℕ)^65*195312500000^49 ≤ 14853650243^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1433916679 10000000000 14853650243 195312500000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (902635847/1250000000 : ℝ)^65 ≤ (507249938377/781250000000 : ℝ)^49 := by
    have hnat : (902635847 : ℕ)^65*781250000000^49 ≤ 507249938377^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902635847 1250000000 507249938377 781250000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(943820233/2500000000 : ℝ), (-1433916679/10000000000 : ℝ), (902635847/1250000000 : ℝ)] ![(13733469473383/50000000000000 : ℝ), (14853650243/195312500000 : ℝ), (507249938377/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(943820233/2500000000 : ℝ)|^65 ≤ (13733469473383/50000000000000 : ℝ)^49
        have hw : |(943820233/2500000000 : ℝ)|=(943820233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1433916679/10000000000 : ℝ)|^65 ≤ (14853650243/195312500000 : ℝ)^49
        have hw : |(-1433916679/10000000000 : ℝ)|=(1433916679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(902635847/1250000000 : ℝ)|^65 ≤ (507249938377/781250000000 : ℝ)^49
        have hw : |(902635847/1250000000 : ℝ)|=(902635847/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301086_s1_s1_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1/5000000000 : ℝ)*x 0 + (-3755929829/10000000000 : ℝ)*x 1 + (7865146063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1/5000000000 : ℝ)^65 ≤ (7/50000000000000 : ℝ)^49 := by
    have hnat : (1 : ℕ)^65*50000000000000^49 ≤ 7^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 5000000000 7 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3755929829/10000000000 : ℝ)^65 ≤ (2728033536501/10000000000000 : ℝ)^49 := by
    have hnat : (3755929829 : ℕ)^65*10000000000000^49 ≤ 2728033536501^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3755929829 10000000000 2728033536501 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7865146063/10000000000 : ℝ)^65 ≤ (18179916156779/25000000000000 : ℝ)^49 := by
    have hnat : (7865146063 : ℕ)^65*25000000000000^49 ≤ 18179916156779^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7865146063 10000000000 18179916156779 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1/5000000000 : ℝ), (-3755929829/10000000000 : ℝ), (7865146063/10000000000 : ℝ)] ![(7/50000000000000 : ℝ), (2728033536501/10000000000000 : ℝ), (18179916156779/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1/5000000000 : ℝ)|^65 ≤ (7/50000000000000 : ℝ)^49
        have hw : |(1/5000000000 : ℝ)|=(1/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3755929829/10000000000 : ℝ)|^65 ≤ (2728033536501/10000000000000 : ℝ)^49
        have hw : |(-3755929829/10000000000 : ℝ)|=(3755929829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7865146063/10000000000 : ℝ)|^65 ≤ (18179916156779/25000000000000 : ℝ)^49
        have hw : |(7865146063/10000000000 : ℝ)|=(7865146063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301086_s1_s1_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4304604389/5000000000 : ℝ)*x 0 + (157890409/625000000 : ℝ)*x 1 + (31456269/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4304604389/5000000000 : ℝ)^65 ≤ (81983555053617/100000000000000 : ℝ)^49 := by
    have hnat : (4304604389 : ℕ)^65*100000000000000^49 ≤ 81983555053617^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4304604389 5000000000 81983555053617 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (157890409/625000000 : ℝ)^65 ≤ (4030006773893/25000000000000 : ℝ)^49 := by
    have hnat : (157890409 : ℕ)^65*25000000000000^49 ≤ 4030006773893^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157890409 625000000 4030006773893 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (31456269/625000000 : ℝ)^65 ≤ (474104458897/25000000000000 : ℝ)^49 := by
    have hnat : (31456269 : ℕ)^65*25000000000000^49 ≤ 474104458897^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31456269 625000000 474104458897 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4304604389/5000000000 : ℝ), (157890409/625000000 : ℝ), (31456269/625000000 : ℝ)] ![(81983555053617/100000000000000 : ℝ), (4030006773893/25000000000000 : ℝ), (474104458897/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4304604389/5000000000 : ℝ)|^65 ≤ (81983555053617/100000000000000 : ℝ)^49
        have hw : |(4304604389/5000000000 : ℝ)|=(4304604389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(157890409/625000000 : ℝ)|^65 ≤ (4030006773893/25000000000000 : ℝ)^49
        have hw : |(157890409/625000000 : ℝ)|=(157890409/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(31456269/625000000 : ℝ)|^65 ≤ (474104458897/25000000000000 : ℝ)^49
        have hw : |(31456269/625000000 : ℝ)|=(31456269/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301086_s1_s1_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7766339279/10000000000 : ℝ)*x 0 + (-1017457247/5000000000 : ℝ)*x 1 + (-2558105193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7766339279/10000000000 : ℝ)^65 ≤ (71510306533569/100000000000000 : ℝ)^49 := by
    have hnat : (7766339279 : ℕ)^65*100000000000000^49 ≤ 71510306533569^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7766339279 10000000000 71510306533569 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1017457247/5000000000 : ℝ)^65 ≤ (12099441415693/100000000000000 : ℝ)^49 := by
    have hnat : (1017457247 : ℕ)^65*100000000000000^49 ≤ 12099441415693^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1017457247 5000000000 12099441415693 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2558105193/10000000000 : ℝ)^65 ≤ (16390252032739/100000000000000 : ℝ)^49 := by
    have hnat : (2558105193 : ℕ)^65*100000000000000^49 ≤ 16390252032739^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2558105193 10000000000 16390252032739 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7766339279/10000000000 : ℝ), (-1017457247/5000000000 : ℝ), (-2558105193/10000000000 : ℝ)] ![(71510306533569/100000000000000 : ℝ), (12099441415693/100000000000000 : ℝ), (16390252032739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7766339279/10000000000 : ℝ)|^65 ≤ (71510306533569/100000000000000 : ℝ)^49
        have hw : |(7766339279/10000000000 : ℝ)|=(7766339279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1017457247/5000000000 : ℝ)|^65 ≤ (12099441415693/100000000000000 : ℝ)^49
        have hw : |(-1017457247/5000000000 : ℝ)|=(1017457247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2558105193/10000000000 : ℝ)|^65 ≤ (16390252032739/100000000000000 : ℝ)^49
        have hw : |(-2558105193/10000000000 : ℝ)|=(2558105193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301086_s1_s1_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (471823601/2000000000 : ℝ)*x 0 + (-164786979/1250000000 : ℝ)*x 1 + (1041262811/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (471823601/2000000000 : ℝ)^65 ≤ (7360430794741/50000000000000 : ℝ)^49 := by
    have hnat : (471823601 : ℕ)^65*50000000000000^49 ≤ 7360430794741^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471823601 2000000000 7360430794741 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164786979/1250000000 : ℝ)^65 ≤ (6802524985367/100000000000000 : ℝ)^49 := by
    have hnat : (164786979 : ℕ)^65*100000000000000^49 ≤ 6802524985367^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164786979 1250000000 6802524985367 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1041262811/1250000000 : ℝ)^65 ≤ (7847661341153/10000000000000 : ℝ)^49 := by
    have hnat : (1041262811 : ℕ)^65*10000000000000^49 ≤ 7847661341153^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041262811 1250000000 7847661341153 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(471823601/2000000000 : ℝ), (-164786979/1250000000 : ℝ), (1041262811/1250000000 : ℝ)] ![(7360430794741/50000000000000 : ℝ), (6802524985367/100000000000000 : ℝ), (7847661341153/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(471823601/2000000000 : ℝ)|^65 ≤ (7360430794741/50000000000000 : ℝ)^49
        have hw : |(471823601/2000000000 : ℝ)|=(471823601/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-164786979/1250000000 : ℝ)|^65 ≤ (6802524985367/100000000000000 : ℝ)^49
        have hw : |(-164786979/1250000000 : ℝ)|=(164786979/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1041262811/1250000000 : ℝ)|^65 ≤ (7847661341153/10000000000000 : ℝ)^49
        have hw : |(1041262811/1250000000 : ℝ)|=(1041262811/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301086_s1_s1_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7839629/2500000000 : ℝ)*x 0 + (-4405781957/5000000000 : ℝ)*x 1 + (1220517733/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7839629/2500000000 : ℝ)^65 ≤ (47735220317/100000000000000 : ℝ)^49 := by
    have hnat : (7839629 : ℕ)^65*100000000000000^49 ≤ 47735220317^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7839629 2500000000 47735220317 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4405781957/5000000000 : ℝ)^65 ≤ (10568689278407/12500000000000 : ℝ)^49 := by
    have hnat : (4405781957 : ℕ)^65*12500000000000^49 ≤ 10568689278407^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4405781957 5000000000 10568689278407 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1220517733/5000000000 : ℝ)^65 ≤ (3850687635731/25000000000000 : ℝ)^49 := by
    have hnat : (1220517733 : ℕ)^65*25000000000000^49 ≤ 3850687635731^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1220517733 5000000000 3850687635731 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7839629/2500000000 : ℝ), (-4405781957/5000000000 : ℝ), (1220517733/5000000000 : ℝ)] ![(47735220317/100000000000000 : ℝ), (10568689278407/12500000000000 : ℝ), (3850687635731/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7839629/2500000000 : ℝ)|^65 ≤ (47735220317/100000000000000 : ℝ)^49
        have hw : |(7839629/2500000000 : ℝ)|=(7839629/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4405781957/5000000000 : ℝ)|^65 ≤ (10568689278407/12500000000000 : ℝ)^49
        have hw : |(-4405781957/5000000000 : ℝ)|=(4405781957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1220517733/5000000000 : ℝ)|^65 ≤ (3850687635731/25000000000000 : ℝ)^49
        have hw : |(1220517733/5000000000 : ℝ)|=(1220517733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301086_s1_s1_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4417274339/5000000000 : ℝ)*x 0 + (1340066999/10000000000 : ℝ)*x 1 + (759252621/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4417274339/5000000000 : ℝ)^65 ≤ (84842199084481/100000000000000 : ℝ)^49 := by
    have hnat : (4417274339 : ℕ)^65*100000000000000^49 ≤ 84842199084481^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4417274339 5000000000 84842199084481 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1340066999/10000000000 : ℝ)^65 ≤ (3475974663347/50000000000000 : ℝ)^49 := by
    have hnat : (1340066999 : ℕ)^65*50000000000000^49 ≤ 3475974663347^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340066999 10000000000 3475974663347 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (759252621/5000000000 : ℝ)^65 ≤ (2051462893519/25000000000000 : ℝ)^49 := by
    have hnat : (759252621 : ℕ)^65*25000000000000^49 ≤ 2051462893519^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      759252621 5000000000 2051462893519 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4417274339/5000000000 : ℝ), (1340066999/10000000000 : ℝ), (759252621/5000000000 : ℝ)] ![(84842199084481/100000000000000 : ℝ), (3475974663347/50000000000000 : ℝ), (2051462893519/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4417274339/5000000000 : ℝ)|^65 ≤ (84842199084481/100000000000000 : ℝ)^49
        have hw : |(4417274339/5000000000 : ℝ)|=(4417274339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1340066999/10000000000 : ℝ)|^65 ≤ (3475974663347/50000000000000 : ℝ)^49
        have hw : |(1340066999/10000000000 : ℝ)|=(1340066999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(759252621/5000000000 : ℝ)|^65 ≤ (2051462893519/25000000000000 : ℝ)^49
        have hw : |(759252621/5000000000 : ℝ)|=(759252621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301086_s1_s1_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3728186843/10000000000 : ℝ)*x 0 + (-694096993/2500000000 : ℝ)*x 1 + (-3173562933/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3728186843/10000000000 : ℝ)^65 ≤ (27013355943131/100000000000000 : ℝ)^49 := by
    have hnat : (3728186843 : ℕ)^65*100000000000000^49 ≤ 27013355943131^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3728186843 10000000000 27013355943131 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (694096993/2500000000 : ℝ)^65 ≤ (18270876763151/100000000000000 : ℝ)^49 := by
    have hnat : (694096993 : ℕ)^65*100000000000000^49 ≤ 18270876763151^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      694096993 2500000000 18270876763151 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3173562933/5000000000 : ℝ)^65 ≤ (54715767276681/100000000000000 : ℝ)^49 := by
    have hnat : (3173562933 : ℕ)^65*100000000000000^49 ≤ 54715767276681^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3173562933 5000000000 54715767276681 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3728186843/10000000000 : ℝ), (-694096993/2500000000 : ℝ), (-3173562933/5000000000 : ℝ)] ![(27013355943131/100000000000000 : ℝ), (18270876763151/100000000000000 : ℝ), (54715767276681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3728186843/10000000000 : ℝ)|^65 ≤ (27013355943131/100000000000000 : ℝ)^49
        have hw : |(3728186843/10000000000 : ℝ)|=(3728186843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-694096993/2500000000 : ℝ)|^65 ≤ (18270876763151/100000000000000 : ℝ)^49
        have hw : |(-694096993/2500000000 : ℝ)|=(694096993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3173562933/5000000000 : ℝ)|^65 ≤ (54715767276681/100000000000000 : ℝ)^49
        have hw : |(-3173562933/5000000000 : ℝ)|=(3173562933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301086_s1_s1_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3847625397/5000000000 : ℝ)*x 0 + (-111181081/1250000000 : ℝ)*x 1 + (1775330771/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3847625397/5000000000 : ℝ)^65 ≤ (70643308793869/100000000000000 : ℝ)^49 := by
    have hnat : (3847625397 : ℕ)^65*100000000000000^49 ≤ 70643308793869^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3847625397 5000000000 70643308793869 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (111181081/1250000000 : ℝ)^65 ≤ (4036237161613/100000000000000 : ℝ)^49 := by
    have hnat : (111181081 : ℕ)^65*100000000000000^49 ≤ 4036237161613^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111181081 1250000000 4036237161613 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1775330771/5000000000 : ℝ)^65 ≤ (12660227014267/50000000000000 : ℝ)^49 := by
    have hnat : (1775330771 : ℕ)^65*50000000000000^49 ≤ 12660227014267^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1775330771 5000000000 12660227014267 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3847625397/5000000000 : ℝ), (-111181081/1250000000 : ℝ), (1775330771/5000000000 : ℝ)] ![(70643308793869/100000000000000 : ℝ), (4036237161613/100000000000000 : ℝ), (12660227014267/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3847625397/5000000000 : ℝ)|^65 ≤ (70643308793869/100000000000000 : ℝ)^49
        have hw : |(3847625397/5000000000 : ℝ)|=(3847625397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-111181081/1250000000 : ℝ)|^65 ≤ (4036237161613/100000000000000 : ℝ)^49
        have hw : |(-111181081/1250000000 : ℝ)|=(111181081/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1775330771/5000000000 : ℝ)|^65 ≤ (12660227014267/50000000000000 : ℝ)^49
        have hw : |(1775330771/5000000000 : ℝ)|=(1775330771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301086_s1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((96039/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(96039/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-97569/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-97569/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(24213/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(24213/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((89341/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(89341/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-94073/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-94073/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(46653/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(46653/50000 : ℝ)*X 1 2) := by
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
  have main1 : (4759/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4759/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base7 : ((1 : ℝ)*T) ≤ (92391/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (96039/100000 : ℝ) ^ (129/32 : ℝ) ≤ (84965380332905241359/100000000000000000000 : ℝ) := by
    have hpowers : (96039/100000 : ℝ)^129 ≤ (84965380332905241359/100000000000000000000 : ℝ)^32 := by
      have hnat : (96039 : ℕ)^129*100000000000000000000^32 ≤ 84965380332905241359^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        96039 100000 84965380332905241359 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (96039/100000 : ℝ)) (X := (84965380332905241359/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (184965380332905241359/100000000000000000000 : ℝ) ≤ (5824048724166961/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (184965380332905241359/100000000000000000000 : ℝ)^32 ≤ (5824048724166961/5000000000000000 : ℝ)^129 := by
      have hnat : (184965380332905241359 : ℕ)^32*5000000000000000^129 ≤ 5824048724166961^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        184965380332905241359 100000000000000000000 5824048724166961 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5824048724166961/5000000000000000 : ℝ)) (X := (184965380332905241359/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (134965380332905241359/50000000000000000000 : ℝ) ≤ (3198286337772579/2500000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (134965380332905241359/50000000000000000000 : ℝ)^32 ≤ (3198286337772579/2500000000000000 : ℝ)^129 := by
      have hnat : (134965380332905241359 : ℕ)^32*2500000000000000^129 ≤ 3198286337772579^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        134965380332905241359 50000000000000000000 3198286337772579 2500000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3198286337772579/2500000000000000 : ℝ)) (X := (134965380332905241359/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(824048724166961/4801950000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(572523951378197/4801950000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (96039/100000 : ℝ)) (alpha := (824048724166961/4801950000000000 : ℝ)) (beta := (572523951378197/4801950000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (96039/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(824048724166961/4801950000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(572523951378197/4801950000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (97569/100000 : ℝ) ^ (129/32 : ℝ) ≤ (90555203499415925347/100000000000000000000 : ℝ) := by
    have hpowers : (97569/100000 : ℝ)^129 ≤ (90555203499415925347/100000000000000000000 : ℝ)^32 := by
      have hnat : (97569 : ℕ)^129*100000000000000000000^32 ≤ 90555203499415925347^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        97569 100000 90555203499415925347 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (97569/100000 : ℝ)) (X := (90555203499415925347/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (190555203499415925347/100000000000000000000 : ℝ) ≤ (11734444281412417/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (190555203499415925347/100000000000000000000 : ℝ)^32 ≤ (11734444281412417/10000000000000000 : ℝ)^129 := by
      have hnat : (190555203499415925347 : ℕ)^32*10000000000000000^129 ≤ 11734444281412417^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        190555203499415925347 100000000000000000000 11734444281412417 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11734444281412417/10000000000000000 : ℝ)) (X := (190555203499415925347/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (140555203499415925347/50000000000000000000 : ℝ) ≤ (6461291264958621/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (140555203499415925347/50000000000000000000 : ℝ)^32 ≤ (6461291264958621/5000000000000000 : ℝ)^129 := by
      have hnat : (140555203499415925347 : ℕ)^32*5000000000000000^129 ≤ 6461291264958621^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        140555203499415925347 50000000000000000000 6461291264958621 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6461291264958621/5000000000000000 : ℝ)) (X := (140555203499415925347/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(578148093804139/3252300000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(47525529940193/390276000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (97569/100000 : ℝ)) (alpha := (578148093804139/3252300000000000 : ℝ)) (beta := (47525529940193/390276000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (97569/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(578148093804139/3252300000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(47525529940193/390276000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (24213/25000 : ℝ) ^ (129/32 : ℝ) ≤ (5493894107388605783/6250000000000000000 : ℝ) := by
    have hpowers : (24213/25000 : ℝ)^129 ≤ (5493894107388605783/6250000000000000000 : ℝ)^32 := by
      have hnat : (24213 : ℕ)^129*6250000000000000000^32 ≤ 5493894107388605783^32*25000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24213 25000 5493894107388605783 6250000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (24213/25000 : ℝ)) (X := (5493894107388605783/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (11743894107388605783/6250000000000000000 : ℝ) ≤ (1461713184091249/1250000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (11743894107388605783/6250000000000000000 : ℝ)^32 ≤ (1461713184091249/1250000000000000 : ℝ)^129 := by
      have hnat : (11743894107388605783 : ℕ)^32*1250000000000000^129 ≤ 1461713184091249^129*6250000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11743894107388605783 6250000000000000000 1461713184091249 1250000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1461713184091249/1250000000000000 : ℝ)) (X := (11743894107388605783/6250000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (8618894107388605783/3125000000000000000 : ℝ) ≤ (3215411128888889/2500000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (8618894107388605783/3125000000000000000 : ℝ)^32 ≤ (3215411128888889/2500000000000000 : ℝ)^129 := by
      have hnat : (8618894107388605783 : ℕ)^32*2500000000000000^129 ≤ 3215411128888889^129*3125000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8618894107388605783 3125000000000000000 3215411128888889 2500000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3215411128888889/2500000000000000 : ℝ)) (X := (8618894107388605783/3125000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(211713184091249/1210650000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(97328253568797/807100000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (24213/25000 : ℝ)) (alpha := (211713184091249/1210650000000000 : ℝ)) (beta := (97328253568797/807100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (24213/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(211713184091249/1210650000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(97328253568797/807100000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_1 : ((6632125251/10000000000 : ℝ)*X 1 0+(3150101441/10000000000 : ℝ)*X 1 1+(75419663/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((3115802983/5000000000 : ℝ)*X 2 0+(-435357407/1250000000 : ℝ)*X 2 1+(-796230481/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((912630839/2500000000 : ℝ)*X 0 0+(-590489889/2500000000 : ℝ)*X 0 1+(3358543533/5000000000 : ℝ)*X 0 2+(912630839/2500000000 : ℝ)*X 1 0+(-590489889/2500000000 : ℝ)*X 1 1+(3358543533/5000000000 : ℝ)*X 1 2+(912630839/2500000000 : ℝ)*X 2 0+(-590489889/2500000000 : ℝ)*X 2 1+(3358543533/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((39452709/2500000000 : ℝ)*X 0 0+(-8542309709/10000000000 : ℝ)*X 0 1+(2797258139/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((406618901/1250000000 : ℝ)*X 1 0+(7154097619/10000000000 : ℝ)*X 1 1+(2188597519/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((299237537/312500000 : ℝ)*X 2 0+(-13465909/2000000000 : ℝ)*X 2 1+(-223356673/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((943820233/2500000000 : ℝ)*X 0 0+(-1433916679/10000000000 : ℝ)*X 0 1+(902635847/1250000000 : ℝ)*X 0 2+(943820233/2500000000 : ℝ)*X 1 0+(-1433916679/10000000000 : ℝ)*X 1 1+(902635847/1250000000 : ℝ)*X 1 2+(943820233/2500000000 : ℝ)*X 2 0+(-1433916679/10000000000 : ℝ)*X 2 1+(902635847/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((1/5000000000 : ℝ)*X 0 0+(-3755929829/10000000000 : ℝ)*X 0 1+(7865146063/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((4304604389/5000000000 : ℝ)*X 1 0+(157890409/625000000 : ℝ)*X 1 1+(31456269/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((7766339279/10000000000 : ℝ)*X 2 0+(-1017457247/5000000000 : ℝ)*X 2 1+(-2558105193/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((471823601/2000000000 : ℝ)*X 0 0+(-164786979/1250000000 : ℝ)*X 0 1+(1041262811/1250000000 : ℝ)*X 0 2+(471823601/2000000000 : ℝ)*X 1 0+(-164786979/1250000000 : ℝ)*X 1 1+(1041262811/1250000000 : ℝ)*X 1 2+(471823601/2000000000 : ℝ)*X 2 0+(-164786979/1250000000 : ℝ)*X 2 1+(1041262811/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((7839629/2500000000 : ℝ)*X 0 0+(-4405781957/5000000000 : ℝ)*X 0 1+(1220517733/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((4417274339/5000000000 : ℝ)*X 1 0+(1340066999/10000000000 : ℝ)*X 1 1+(759252621/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((3728186843/10000000000 : ℝ)*X 2 0+(-694096993/2500000000 : ℝ)*X 2 1+(-3173562933/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((3847625397/5000000000 : ℝ)*X 0 0+(-111181081/1250000000 : ℝ)*X 0 1+(1775330771/5000000000 : ℝ)*X 0 2+(3847625397/5000000000 : ℝ)*X 1 0+(-111181081/1250000000 : ℝ)*X 1 1+(1775330771/5000000000 : ℝ)*X 1 2+(3847625397/5000000000 : ℝ)*X 2 0+(-111181081/1250000000 : ℝ)*X 2 1+(1775330771/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301086_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((89341/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(89341/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (969470644528328225287319427131/140053211112150000000000000000000000 : ℝ) := by norm_num
    linear_combination (16951356321/500000000000 : ℝ)*(base1) + (556001997299/1000000000000 : ℝ)*(base7) + (240049432001/1000000000000 : ℝ)*(base43) + (181881612163/200000000000 : ℝ)*(base54) + (1277717/500000000000 : ℝ)*(base60) + (406369699349/250000000000 : ℝ)*(major_s1_0) + (346357341349/250000000000 : ℝ)*(major_s1_1) + (358035368291/500000000000 : ℝ)*(major_s1_2) + (16958677/1000000000000 : ℝ)*(sp_s1_6) + (1603483933243/1000000000000 : ℝ)*(sp_s1_7) + (904815326301/500000000000 : ℝ)*(sp_s1_8) + (330064869861/500000000000 : ℝ)*(sp_s1_9) + (142307005949/200000000000 : ℝ)*(sp_s1_13) + (8684013/200000000000 : ℝ)*(sp_s1_16) + (1098860764579/1000000000000 : ℝ)*(f.failure) + (904815326301/500000000000 : ℝ)*(f.sum) + (3289672615789612741/9843492487500000000000000000000 : ℝ)*base63 + (298365651259257/403550000000000000000000000 : ℝ)*base64 + (1140070745062937/1626150000000000000000000000 : ℝ)*base67 + (75826113240499/605325000000000000000000000 : ℝ)*base69 + (2351466569125322707/9689134612500000000000000000000 : ℝ)*base71 + (640890283254553/1200487500000000000000000000 : ℝ)*base73 + (9695287311209/195138000000000000000000000 : ℝ)*base74 + (2038409346697379/4801950000000000000000000000 : ℝ)*base76 + (13209687123413011013/52057939950000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (4001/25000000000000000 : ℝ)*base86 + (29001/25000000000000000 : ℝ)*base88 + (29001/25000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-94073/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-94073/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (634220174215695500218770776263/46684403704050000000000000000000000 : ℝ) := by norm_num
    linear_combination (923844857961/1000000000000 : ℝ)*(base7) + (6670647797/12500000000 : ℝ)*(base33) + (728793/1000000000000 : ℝ)*(base40) + (1055273382607/1000000000000 : ℝ)*(major_s1_0) + (1588925206367/1000000000000 : ℝ)*(major_s1_1) + (1588925206367/1000000000000 : ℝ)*(major_s1_2) + (44744521/1000000000000 : ℝ)*(sp_s1_1) + (4193859/62500000000 : ℝ)*(sp_s1_2) + (13520221/500000000000 : ℝ)*(sp_s1_13) + (1534663179389/1000000000000 : ℝ)*(sp_s1_14) + (500469318867/500000000000 : ℝ)*(sp_s1_15) + (200188850777/200000000000 : ℝ)*(sp_s1_16) + (499491880079/250000000000 : ℝ)*(sp_s1_20) + (223787/8000000000 : ℝ)*(sp_s1_22) + (537074851399/500000000000 : ℝ)*(f.failure) + (1534663179389/1000000000000 : ℝ)*(f.sum) + (24154949335601370025337/78747939900000000000000000000000 : ℝ)*base62 + (318663985897689/807100000000000000000000000 : ℝ)*base64 + (2247439347535403/3252300000000000000000000000 : ℝ)*base67 + (224938368331711/605325000000000000000000000 : ℝ)*base68 + (1341425046000034907/77513076900000000000000000000000 : ℝ)*base70 + (1372788836743409/4801950000000000000000000000 : ℝ)*base73 + (710513783029421/1951380000000000000000000000 : ℝ)*base75 + (582572588429293/4801950000000000000000000000 : ℝ)*base76 + (15019545940883994437/104115879900000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (1081/12500000000000000 : ℝ)*base86 + (1081/12500000000000000 : ℝ)*base88 + (1081/12500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(46653/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(46653/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (166646478072876768242333378721/15561467901350000000000000000000000 : ℝ) := by norm_num
    linear_combination (328709997277/500000000000 : ℝ)*(base7) + (920399/250000000000 : ℝ)*(base15) + (17240226037/125000000000 : ℝ)*(base33) + (21211872979/20000000000 : ℝ)*(base43) + (147113/1000000000000 : ℝ)*(base50) + (8081/1000000000000 : ℝ)*(base60) + (1484877530191/1000000000000 : ℝ)*(major_s1_0) + (562205689537/1000000000000 : ℝ)*(major_s1_1) + (1622799338487/1000000000000 : ℝ)*(major_s1_2) + (10184991/500000000000 : ℝ)*(sp_s1_16) + (341510398863/500000000000 : ℝ)*(sp_s1_21) + (100355559799/62500000000 : ℝ)*(sp_s1_22) + (545078619447/1000000000000 : ℝ)*(sp_s1_23) + (1754469383759/1000000000000 : ℝ)*(sp_s1_27) + (219409877841/200000000000 : ℝ)*(f.failure) + (1743614446677/1000000000000 : ℝ)*(f.sum) + (80743264570076590507/78747939900000000000000000000000 : ℝ)*base62 + (98340249858979/807100000000000000000000000 : ℝ)*base64 + (131689990695977/3252300000000000000000000000 : ℝ)*base66 + (142303033486869/403550000000000000000000000 : ℝ)*base68 + (1994096338394809861/77513076900000000000000000000000 : ℝ)*base71 + (2676743515065043/4801950000000000000000000000 : ℝ)*base72 + (99669132505441/390276000000000000000000000 : ℝ)*base74 + (399641338832231/4801950000000000000000000000 : ℝ)*base77 + (13587713746044584527/104115879900000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (1/500000000000 : ℝ)*base84 + (3021/5000000000000000 : ℝ)*base87 + (3021/5000000000000000 : ℝ)*base89 + (3021/5000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((96039/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(96039/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-97569/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-97569/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(24213/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(24213/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((89341/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(89341/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-94073/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-94073/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(46653/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(46653/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301086_s1 p hpa hpb X hX hprev0

#print axioms solution
