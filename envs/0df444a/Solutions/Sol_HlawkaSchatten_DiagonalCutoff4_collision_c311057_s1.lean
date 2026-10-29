-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c311057_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:00:27.625779+00:00
-- url     : https://prove2.me/submissions/e3325bab-ee03-42f8-acbd-87fde1fbf30a

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
theorem collision_support_c311057_s1_s1_0 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-390406043/1250000000 : ℝ)*x 0 + (311195989/1000000000 : ℝ)*x 1 + (788600269/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (390406043/1250000000 : ℝ)^9 ≤ (22397955670759/100000000000000 : ℝ)^7 := by
    have hnat : (390406043 : ℕ)^9*100000000000000^7 ≤ 22397955670759^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      390406043 1250000000 22397955670759 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (311195989/1000000000 : ℝ)^9 ≤ (22293926219527/100000000000000 : ℝ)^7 := by
    have hnat : (311195989 : ℕ)^9*100000000000000^7 ≤ 22293926219527^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      311195989 1000000000 22293926219527 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (788600269/1250000000 : ℝ)^9 ≤ (55308118102883/100000000000000 : ℝ)^7 := by
    have hnat : (788600269 : ℕ)^9*100000000000000^7 ≤ 55308118102883^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      788600269 1250000000 55308118102883 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-390406043/1250000000 : ℝ), (311195989/1000000000 : ℝ), (788600269/1250000000 : ℝ)] ![(22397955670759/100000000000000 : ℝ), (22293926219527/100000000000000 : ℝ), (55308118102883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-390406043/1250000000 : ℝ)|^9 ≤ (22397955670759/100000000000000 : ℝ)^7
        have hw : |(-390406043/1250000000 : ℝ)|=(390406043/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(311195989/1000000000 : ℝ)|^9 ≤ (22293926219527/100000000000000 : ℝ)^7
        have hw : |(311195989/1000000000 : ℝ)|=(311195989/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(788600269/1250000000 : ℝ)|^9 ≤ (55308118102883/100000000000000 : ℝ)^7
        have hw : |(788600269/1250000000 : ℝ)|=(788600269/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311057_s1_s1_1 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1557982213/5000000000 : ℝ)*x 0 + (-1552351149/5000000000 : ℝ)*x 1 + (6320683989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1557982213/5000000000 : ℝ)^9 ≤ (697838060987/3125000000000 : ℝ)^7 := by
    have hnat : (1557982213 : ℕ)^9*3125000000000^7 ≤ 697838060987^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1557982213 5000000000 697838060987 3125000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1552351149/5000000000 : ℝ)^9 ≤ (2222710032339/10000000000000 : ℝ)^7 := by
    have hnat : (1552351149 : ℕ)^9*10000000000000^7 ≤ 2222710032339^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1552351149 5000000000 2222710032339 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6320683989/10000000000 : ℝ)^9 ≤ (55442081704097/100000000000000 : ℝ)^7 := by
    have hnat : (6320683989 : ℕ)^9*100000000000000^7 ≤ 55442081704097^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6320683989 10000000000 55442081704097 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1557982213/5000000000 : ℝ), (-1552351149/5000000000 : ℝ), (6320683989/10000000000 : ℝ)] ![(697838060987/3125000000000 : ℝ), (2222710032339/10000000000000 : ℝ), (55442081704097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1557982213/5000000000 : ℝ)|^9 ≤ (697838060987/3125000000000 : ℝ)^7
        have hw : |(1557982213/5000000000 : ℝ)|=(1557982213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1552351149/5000000000 : ℝ)|^9 ≤ (2222710032339/10000000000000 : ℝ)^7
        have hw : |(-1552351149/5000000000 : ℝ)|=(1552351149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6320683989/10000000000 : ℝ)|^9 ≤ (55442081704097/100000000000000 : ℝ)^7
        have hw : |(6320683989/10000000000 : ℝ)|=(6320683989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311057_s1_s1_6 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2383713069/5000000000 : ℝ)*x 0 + (4781112973/10000000000 : ℝ)*x 1 + (25245089/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2383713069/5000000000 : ℝ)^9 ≤ (19290128148403/50000000000000 : ℝ)^7 := by
    have hnat : (2383713069 : ℕ)^9*50000000000000^7 ≤ 19290128148403^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2383713069 5000000000 19290128148403 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4781112973/10000000000 : ℝ)^9 ≤ (38722720776153/100000000000000 : ℝ)^7 := by
    have hnat : (4781112973 : ℕ)^9*100000000000000^7 ≤ 38722720776153^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4781112973 10000000000 38722720776153 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (25245089/80000000 : ℝ)^9 ≤ (22697022909409/100000000000000 : ℝ)^7 := by
    have hnat : (25245089 : ℕ)^9*100000000000000^7 ≤ 22697022909409^7*80000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25245089 80000000 22697022909409 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2383713069/5000000000 : ℝ), (4781112973/10000000000 : ℝ), (25245089/80000000 : ℝ)] ![(19290128148403/50000000000000 : ℝ), (38722720776153/100000000000000 : ℝ), (22697022909409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2383713069/5000000000 : ℝ)|^9 ≤ (19290128148403/50000000000000 : ℝ)^7
        have hw : |(2383713069/5000000000 : ℝ)|=(2383713069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4781112973/10000000000 : ℝ)|^9 ≤ (38722720776153/100000000000000 : ℝ)^7
        have hw : |(4781112973/10000000000 : ℝ)|=(4781112973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(25245089/80000000 : ℝ)|^9 ≤ (22697022909409/100000000000000 : ℝ)^7
        have hw : |(25245089/80000000 : ℝ)|=(25245089/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311057_s1_s1_7 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-308539867/1250000000 : ℝ)*x 0 + (1893301951/10000000000 : ℝ)*x 1 + (385930809/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (308539867/1250000000 : ℝ)^9 ≤ (16550138756207/100000000000000 : ℝ)^7 := by
    have hnat : (308539867 : ℕ)^9*100000000000000^7 ≤ 16550138756207^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      308539867 1250000000 16550138756207 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1893301951/10000000000 : ℝ)^9 ≤ (1471029189267/12500000000000 : ℝ)^7 := by
    have hnat : (1893301951 : ℕ)^9*12500000000000^7 ≤ 1471029189267^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1893301951 10000000000 1471029189267 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (385930809/500000000 : ℝ)^9 ≤ (71681627711217/100000000000000 : ℝ)^7 := by
    have hnat : (385930809 : ℕ)^9*100000000000000^7 ≤ 71681627711217^7*500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385930809 500000000 71681627711217 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-308539867/1250000000 : ℝ), (1893301951/10000000000 : ℝ), (385930809/500000000 : ℝ)] ![(16550138756207/100000000000000 : ℝ), (1471029189267/12500000000000 : ℝ), (71681627711217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-308539867/1250000000 : ℝ)|^9 ≤ (16550138756207/100000000000000 : ℝ)^7
        have hw : |(-308539867/1250000000 : ℝ)|=(308539867/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1893301951/10000000000 : ℝ)|^9 ≤ (1471029189267/12500000000000 : ℝ)^7
        have hw : |(1893301951/10000000000 : ℝ)|=(1893301951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(385930809/500000000 : ℝ)|^9 ≤ (71681627711217/100000000000000 : ℝ)^7
        have hw : |(385930809/500000000 : ℝ)|=(385930809/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311057_s1_s1_8 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2456744439/10000000000 : ℝ)*x 0 + (-471105959/2500000000 : ℝ)*x 1 + (7732901653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2456744439/10000000000 : ℝ)^9 ≤ (4112606219477/25000000000000 : ℝ)^7 := by
    have hnat : (2456744439 : ℕ)^9*25000000000000^7 ≤ 4112606219477^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2456744439 10000000000 4112606219477 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (471105959/2500000000 : ℝ)^9 ≤ (11697330405207/100000000000000 : ℝ)^7 := by
    have hnat : (471105959 : ℕ)^9*100000000000000^7 ≤ 11697330405207^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471105959 2500000000 11697330405207 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7732901653/10000000000 : ℝ)^9 ≤ (71852244697991/100000000000000 : ℝ)^7 := by
    have hnat : (7732901653 : ℕ)^9*100000000000000^7 ≤ 71852244697991^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7732901653 10000000000 71852244697991 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2456744439/10000000000 : ℝ), (-471105959/2500000000 : ℝ), (7732901653/10000000000 : ℝ)] ![(4112606219477/25000000000000 : ℝ), (11697330405207/100000000000000 : ℝ), (71852244697991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2456744439/10000000000 : ℝ)|^9 ≤ (4112606219477/25000000000000 : ℝ)^7
        have hw : |(2456744439/10000000000 : ℝ)|=(2456744439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-471105959/2500000000 : ℝ)|^9 ≤ (11697330405207/100000000000000 : ℝ)^7
        have hw : |(-471105959/2500000000 : ℝ)|=(471105959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7732901653/10000000000 : ℝ)|^9 ≤ (71852244697991/100000000000000 : ℝ)^7
        have hw : |(7732901653/10000000000 : ℝ)|=(7732901653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311057_s1_s1_9 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (985591331/2500000000 : ℝ)*x 0 + (7559086817/10000000000 : ℝ)*x 1 + (-55903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (985591331/2500000000 : ℝ)^9 ≤ (30217520680423/100000000000000 : ℝ)^7 := by
    have hnat : (985591331 : ℕ)^9*100000000000000^7 ≤ 30217520680423^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      985591331 2500000000 30217520680423 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7559086817/10000000000 : ℝ)^9 ≤ (34891230831759/50000000000000 : ℝ)^7 := by
    have hnat : (7559086817 : ℕ)^9*50000000000000^7 ≤ 34891230831759^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7559086817 10000000000 34891230831759 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (55903/10000000000 : ℝ)^9 ≤ (17648277/100000000000000 : ℝ)^7 := by
    have hnat : (55903 : ℕ)^9*100000000000000^7 ≤ 17648277^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55903 10000000000 17648277 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(985591331/2500000000 : ℝ), (7559086817/10000000000 : ℝ), (-55903/10000000000 : ℝ)] ![(30217520680423/100000000000000 : ℝ), (34891230831759/50000000000000 : ℝ), (17648277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(985591331/2500000000 : ℝ)|^9 ≤ (30217520680423/100000000000000 : ℝ)^7
        have hw : |(985591331/2500000000 : ℝ)|=(985591331/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7559086817/10000000000 : ℝ)|^9 ≤ (34891230831759/50000000000000 : ℝ)^7
        have hw : |(7559086817/10000000000 : ℝ)|=(7559086817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-55903/10000000000 : ℝ)|^9 ≤ (17648277/100000000000000 : ℝ)^7
        have hw : |(-55903/10000000000 : ℝ)|=(55903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311057_s1_s1_12 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (718306231/2000000000 : ℝ)*x 0 + (3443198889/5000000000 : ℝ)*x 1 + (1833567369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (718306231/2000000000 : ℝ)^9 ≤ (5361010690079/20000000000000 : ℝ)^7 := by
    have hnat : (718306231 : ℕ)^9*20000000000000^7 ≤ 5361010690079^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      718306231 2000000000 5361010690079 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3443198889/5000000000 : ℝ)^9 ≤ (61901922220257/100000000000000 : ℝ)^7 := by
    have hnat : (3443198889 : ℕ)^9*100000000000000^7 ≤ 61901922220257^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3443198889 5000000000 61901922220257 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1833567369/10000000000 : ℝ)^9 ≤ (5646512158501/50000000000000 : ℝ)^7 := by
    have hnat : (1833567369 : ℕ)^9*50000000000000^7 ≤ 5646512158501^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1833567369 10000000000 5646512158501 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(718306231/2000000000 : ℝ), (3443198889/5000000000 : ℝ), (1833567369/10000000000 : ℝ)] ![(5361010690079/20000000000000 : ℝ), (61901922220257/100000000000000 : ℝ), (5646512158501/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(718306231/2000000000 : ℝ)|^9 ≤ (5361010690079/20000000000000 : ℝ)^7
        have hw : |(718306231/2000000000 : ℝ)|=(718306231/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3443198889/5000000000 : ℝ)|^9 ≤ (61901922220257/100000000000000 : ℝ)^7
        have hw : |(3443198889/5000000000 : ℝ)|=(3443198889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1833567369/10000000000 : ℝ)|^9 ≤ (5646512158501/50000000000000 : ℝ)^7
        have hw : |(1833567369/10000000000 : ℝ)|=(1833567369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311057_s1_s1_13 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-190519547/1000000000 : ℝ)*x 0 + (1228010563/5000000000 : ℝ)*x 1 + (1543904249/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (190519547/1000000000 : ℝ)^9 ≤ (11863367396639/100000000000000 : ℝ)^7 := by
    have hnat : (190519547 : ℕ)^9*100000000000000^7 ≤ 11863367396639^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190519547 1000000000 11863367396639 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1228010563/5000000000 : ℝ)^9 ≤ (8222099005311/50000000000000 : ℝ)^7 := by
    have hnat : (1228010563 : ℕ)^9*50000000000000^7 ≤ 8222099005311^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1228010563 5000000000 8222099005311 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1543904249/2000000000 : ℝ)^9 ≤ (35846217290613/50000000000000 : ℝ)^7 := by
    have hnat : (1543904249 : ℕ)^9*50000000000000^7 ≤ 35846217290613^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1543904249 2000000000 35846217290613 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-190519547/1000000000 : ℝ), (1228010563/5000000000 : ℝ), (1543904249/2000000000 : ℝ)] ![(11863367396639/100000000000000 : ℝ), (8222099005311/50000000000000 : ℝ), (35846217290613/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-190519547/1000000000 : ℝ)|^9 ≤ (11863367396639/100000000000000 : ℝ)^7
        have hw : |(-190519547/1000000000 : ℝ)|=(190519547/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1228010563/5000000000 : ℝ)|^9 ≤ (8222099005311/50000000000000 : ℝ)^7
        have hw : |(1228010563/5000000000 : ℝ)|=(1228010563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1543904249/2000000000 : ℝ)|^9 ≤ (35846217290613/50000000000000 : ℝ)^7
        have hw : |(1543904249/2000000000 : ℝ)|=(1543904249/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311057_s1_s1_14 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1896256803/10000000000 : ℝ)*x 0 + (-611124533/2500000000 : ℝ)*x 1 + (309352337/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1896256803/10000000000 : ℝ)^9 ≤ (2947963221981/25000000000000 : ℝ)^7 := by
    have hnat : (1896256803 : ℕ)^9*25000000000000^7 ≤ 2947963221981^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1896256803 10000000000 2947963221981 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (611124533/2500000000 : ℝ)^9 ≤ (3269013885613/20000000000000 : ℝ)^7 := by
    have hnat : (611124533 : ℕ)^9*20000000000000^7 ≤ 3269013885613^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      611124533 2500000000 3269013885613 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (309352337/400000000 : ℝ)^9 ≤ (71863077671943/100000000000000 : ℝ)^7 := by
    have hnat : (309352337 : ℕ)^9*100000000000000^7 ≤ 71863077671943^7*400000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      309352337 400000000 71863077671943 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1896256803/10000000000 : ℝ), (-611124533/2500000000 : ℝ), (309352337/400000000 : ℝ)] ![(2947963221981/25000000000000 : ℝ), (3269013885613/20000000000000 : ℝ), (71863077671943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1896256803/10000000000 : ℝ)|^9 ≤ (2947963221981/25000000000000 : ℝ)^7
        have hw : |(1896256803/10000000000 : ℝ)|=(1896256803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-611124533/2500000000 : ℝ)|^9 ≤ (3269013885613/20000000000000 : ℝ)^7
        have hw : |(-611124533/2500000000 : ℝ)|=(611124533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(309352337/400000000 : ℝ)|^9 ≤ (71863077671943/100000000000000 : ℝ)^7
        have hw : |(309352337/400000000 : ℝ)|=(309352337/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311057_s1_s1_15 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (7545359013/10000000000 : ℝ)*x 0 + (3958885067/10000000000 : ℝ)*x 1 + (-28129/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7545359013/10000000000 : ℝ)^9 ≤ (34809782956351/50000000000000 : ℝ)^7 := by
    have hnat : (7545359013 : ℕ)^9*50000000000000^7 ≤ 34809782956351^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7545359013 10000000000 34809782956351 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3958885067/10000000000 : ℝ)^9 ≤ (15190208140833/50000000000000 : ℝ)^7 := by
    have hnat : (3958885067 : ℕ)^9*50000000000000^7 ≤ 15190208140833^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3958885067 10000000000 15190208140833 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (28129/5000000000 : ℝ)^9 ≤ (17792499/100000000000000 : ℝ)^7 := by
    have hnat : (28129 : ℕ)^9*100000000000000^7 ≤ 17792499^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28129 5000000000 17792499 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7545359013/10000000000 : ℝ), (3958885067/10000000000 : ℝ), (-28129/5000000000 : ℝ)] ![(34809782956351/50000000000000 : ℝ), (15190208140833/50000000000000 : ℝ), (17792499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7545359013/10000000000 : ℝ)|^9 ≤ (34809782956351/50000000000000 : ℝ)^7
        have hw : |(7545359013/10000000000 : ℝ)|=(7545359013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3958885067/10000000000 : ℝ)|^9 ≤ (15190208140833/50000000000000 : ℝ)^7
        have hw : |(3958885067/10000000000 : ℝ)|=(3958885067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-28129/5000000000 : ℝ)|^9 ≤ (17792499/100000000000000 : ℝ)^7
        have hw : |(-28129/5000000000 : ℝ)|=(28129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311057_s1_s1_18 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (6874101417/10000000000 : ℝ)*x 0 + (901672717/2500000000 : ℝ)*x 1 + (1833127789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6874101417/10000000000 : ℝ)^9 ≤ (15439961429187/25000000000000 : ℝ)^7 := by
    have hnat : (6874101417 : ℕ)^9*25000000000000^7 ≤ 15439961429187^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6874101417 10000000000 15439961429187 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (901672717/2500000000 : ℝ)^9 ≤ (26950610761419/100000000000000 : ℝ)^7 := by
    have hnat : (901672717 : ℕ)^9*100000000000000^7 ≤ 26950610761419^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901672717 2500000000 26950610761419 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1833127789/10000000000 : ℝ)^9 ≤ (45158174009/400000000000 : ℝ)^7 := by
    have hnat : (1833127789 : ℕ)^9*400000000000^7 ≤ 45158174009^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1833127789 10000000000 45158174009 400000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6874101417/10000000000 : ℝ), (901672717/2500000000 : ℝ), (1833127789/10000000000 : ℝ)] ![(15439961429187/25000000000000 : ℝ), (26950610761419/100000000000000 : ℝ), (45158174009/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6874101417/10000000000 : ℝ)|^9 ≤ (15439961429187/25000000000000 : ℝ)^7
        have hw : |(6874101417/10000000000 : ℝ)|=(6874101417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(901672717/2500000000 : ℝ)|^9 ≤ (26950610761419/100000000000000 : ℝ)^7
        have hw : |(901672717/2500000000 : ℝ)|=(901672717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1833127789/10000000000 : ℝ)|^9 ≤ (45158174009/400000000000 : ℝ)^7
        have hw : |(1833127789/10000000000 : ℝ)|=(1833127789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311057_s1_s1_19 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-4486557389/10000000000 : ℝ)*x 0 + (1998391417/10000000000 : ℝ)*x 1 + (374158421/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4486557389/10000000000 : ℝ)^9 ≤ (1784143853141/5000000000000 : ℝ)^7 := by
    have hnat : (4486557389 : ℕ)^9*5000000000000^7 ≤ 1784143853141^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486557389 10000000000 1784143853141 5000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1998391417/10000000000 : ℝ)^9 ≤ (12614644044531/100000000000000 : ℝ)^7 := by
    have hnat : (1998391417 : ℕ)^9*100000000000000^7 ≤ 12614644044531^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1998391417 10000000000 12614644044531 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (374158421/625000000 : ℝ)^9 ≤ (12925619719287/25000000000000 : ℝ)^7 := by
    have hnat : (374158421 : ℕ)^9*25000000000000^7 ≤ 12925619719287^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      374158421 625000000 12925619719287 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4486557389/10000000000 : ℝ), (1998391417/10000000000 : ℝ), (374158421/625000000 : ℝ)] ![(1784143853141/5000000000000 : ℝ), (12614644044531/100000000000000 : ℝ), (12925619719287/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4486557389/10000000000 : ℝ)|^9 ≤ (1784143853141/5000000000000 : ℝ)^7
        have hw : |(-4486557389/10000000000 : ℝ)|=(4486557389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1998391417/10000000000 : ℝ)|^9 ≤ (12614644044531/100000000000000 : ℝ)^7
        have hw : |(1998391417/10000000000 : ℝ)|=(1998391417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(374158421/625000000 : ℝ)|^9 ≤ (12925619719287/25000000000000 : ℝ)^7
        have hw : |(374158421/625000000 : ℝ)|=(374158421/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311057_s1_s1_20 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2003977639/10000000000 : ℝ)*x 0 + (-558585581/1250000000 : ℝ)*x 1 + (2999448027/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2003977639/10000000000 : ℝ)^9 ≤ (12659999589/100000000000 : ℝ)^7 := by
    have hnat : (2003977639 : ℕ)^9*100000000000^7 ≤ 12659999589^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2003977639 10000000000 12659999589 100000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (558585581/1250000000 : ℝ)^9 ≤ (4437527587241/12500000000000 : ℝ)^7 := by
    have hnat : (558585581 : ℕ)^9*12500000000000^7 ≤ 4437527587241^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      558585581 1250000000 4437527587241 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2999448027/5000000000 : ℝ)^9 ≤ (51839779697937/100000000000000 : ℝ)^7 := by
    have hnat : (2999448027 : ℕ)^9*100000000000000^7 ≤ 51839779697937^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2999448027 5000000000 51839779697937 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2003977639/10000000000 : ℝ), (-558585581/1250000000 : ℝ), (2999448027/5000000000 : ℝ)] ![(12659999589/100000000000 : ℝ), (4437527587241/12500000000000 : ℝ), (51839779697937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2003977639/10000000000 : ℝ)|^9 ≤ (12659999589/100000000000 : ℝ)^7
        have hw : |(2003977639/10000000000 : ℝ)|=(2003977639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-558585581/1250000000 : ℝ)|^9 ≤ (4437527587241/12500000000000 : ℝ)^7
        have hw : |(-558585581/1250000000 : ℝ)|=(558585581/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2999448027/5000000000 : ℝ)|^9 ≤ (51839779697937/100000000000000 : ℝ)^7
        have hw : |(2999448027/5000000000 : ℝ)|=(2999448027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311057_s1_s1_21 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (6121087877/10000000000 : ℝ)*x 0 + (2769105757/5000000000 : ℝ)*x 1 + (6673551/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6121087877/10000000000 : ℝ)^9 ≤ (53201331811787/100000000000000 : ℝ)^7 := by
    have hnat : (6121087877 : ℕ)^9*100000000000000^7 ≤ 53201331811787^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6121087877 10000000000 53201331811787 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2769105757/5000000000 : ℝ)^9 ≤ (5847315966991/12500000000000 : ℝ)^7 := by
    have hnat : (2769105757 : ℕ)^9*12500000000000^7 ≤ 5847315966991^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2769105757 5000000000 5847315966991 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6673551/5000000000 : ℝ)^9 ≤ (10070220449/50000000000000 : ℝ)^7 := by
    have hnat : (6673551 : ℕ)^9*50000000000000^7 ≤ 10070220449^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6673551 5000000000 10070220449 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6121087877/10000000000 : ℝ), (2769105757/5000000000 : ℝ), (6673551/5000000000 : ℝ)] ![(53201331811787/100000000000000 : ℝ), (5847315966991/12500000000000 : ℝ), (10070220449/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6121087877/10000000000 : ℝ)|^9 ≤ (53201331811787/100000000000000 : ℝ)^7
        have hw : |(6121087877/10000000000 : ℝ)|=(6121087877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2769105757/5000000000 : ℝ)|^9 ≤ (5847315966991/12500000000000 : ℝ)^7
        have hw : |(2769105757/5000000000 : ℝ)|=(2769105757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6673551/5000000000 : ℝ)|^9 ≤ (10070220449/50000000000000 : ℝ)^7
        have hw : |(6673551/5000000000 : ℝ)|=(6673551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311057_s1_s1_25 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (382079963/1000000000 : ℝ)*x 0 + (2769105757/5000000000 : ℝ)*x 1 + (3316640023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (382079963/1000000000 : ℝ)^9 ≤ (7256208870989/25000000000000 : ℝ)^7 := by
    have hnat : (382079963 : ℕ)^9*25000000000000^7 ≤ 7256208870989^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      382079963 1000000000 7256208870989 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2769105757/5000000000 : ℝ)^9 ≤ (5847315966991/12500000000000 : ℝ)^7 := by
    have hnat : (2769105757 : ℕ)^9*12500000000000^7 ≤ 5847315966991^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2769105757 5000000000 5847315966991 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3316640023/10000000000 : ℝ)^9 ≤ (12098318382229/50000000000000 : ℝ)^7 := by
    have hnat : (3316640023 : ℕ)^9*50000000000000^7 ≤ 12098318382229^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3316640023 10000000000 12098318382229 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(382079963/1000000000 : ℝ), (2769105757/5000000000 : ℝ), (3316640023/10000000000 : ℝ)] ![(7256208870989/25000000000000 : ℝ), (5847315966991/12500000000000 : ℝ), (12098318382229/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(382079963/1000000000 : ℝ)|^9 ≤ (7256208870989/25000000000000 : ℝ)^7
        have hw : |(382079963/1000000000 : ℝ)|=(382079963/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2769105757/5000000000 : ℝ)|^9 ≤ (5847315966991/12500000000000 : ℝ)^7
        have hw : |(2769105757/5000000000 : ℝ)|=(2769105757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3316640023/10000000000 : ℝ)|^9 ≤ (12098318382229/50000000000000 : ℝ)^7
        have hw : |(3316640023/10000000000 : ℝ)|=(3316640023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c311057_s1 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((4357/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4357/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21571/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(21571/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(46901/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(46901/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2178/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2178/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6957/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(6957/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(18923/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(18923/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (19517/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (19517/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (19517/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (19517/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (19517/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (19517/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (89829/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
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
  have s1_pow0 : (4357/5000 : ℝ) ^ (71/16 : ℝ) ≤ (678618064187534937/1250000000000000000 : ℝ) := by
    have hpowers : (4357/5000 : ℝ)^71 ≤ (678618064187534937/1250000000000000000 : ℝ)^16 := by
      have hnat : (4357 : ℕ)^71*1250000000000000000^16 ≤ 678618064187534937^16*5000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4357 5000 678618064187534937 1250000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4357/5000 : ℝ)) (X := (678618064187534937/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (1928618064187534937/1250000000000000000 : ℝ) ≤ (11026608734324609/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (1928618064187534937/1250000000000000000 : ℝ)^16 ≤ (11026608734324609/10000000000000000 : ℝ)^71 := by
      have hnat : (1928618064187534937 : ℕ)^16*10000000000000000^71 ≤ 11026608734324609^71*1250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1928618064187534937 1250000000000000000 11026608734324609 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11026608734324609/10000000000000000 : ℝ)) (X := (1928618064187534937/1250000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (1303618064187534937/625000000000000000 : ℝ) ≤ (5900899971257529/5000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (1303618064187534937/625000000000000000 : ℝ)^16 ≤ (5900899971257529/5000000000000000 : ℝ)^71 := by
      have hnat : (1303618064187534937 : ℕ)^16*5000000000000000^71 ≤ 5900899971257529^71*625000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1303618064187534937 625000000000000000 5900899971257529 5000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5900899971257529/5000000000000000 : ℝ)) (X := (1303618064187534937/625000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1026608734324609/8714000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(775191208190449/8714000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (4357/5000 : ℝ)) (alpha := (1026608734324609/8714000000000000 : ℝ)) (beta := (775191208190449/8714000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (4357/5000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1026608734324609/8714000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(775191208190449/8714000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (21571/25000 : ℝ) ^ (71/16 : ℝ) ≤ (51962564166583181233/100000000000000000000 : ℝ) := by
    have hpowers : (21571/25000 : ℝ)^71 ≤ (51962564166583181233/100000000000000000000 : ℝ)^16 := by
      have hnat : (21571 : ℕ)^71*100000000000000000000^16 ≤ 51962564166583181233^16*25000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21571 25000 51962564166583181233 100000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21571/25000 : ℝ)) (X := (51962564166583181233/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (151962564166583181233/100000000000000000000 : ℝ) ≤ (10988912864682877/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (151962564166583181233/100000000000000000000 : ℝ)^16 ≤ (10988912864682877/10000000000000000 : ℝ)^71 := by
      have hnat : (151962564166583181233 : ℕ)^16*10000000000000000^71 ≤ 10988912864682877^71*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        151962564166583181233 100000000000000000000 10988912864682877 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10988912864682877/10000000000000000 : ℝ)) (X := (151962564166583181233/100000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (101962564166583181233/50000000000000000000 : ℝ) ≤ (11741940789083019/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (101962564166583181233/50000000000000000000 : ℝ)^16 ≤ (11741940789083019/10000000000000000 : ℝ)^71 := by
      have hnat : (101962564166583181233 : ℕ)^16*10000000000000000^71 ≤ 11741940789083019^71*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101962564166583181233 50000000000000000000 11741940789083019 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11741940789083019/10000000000000000 : ℝ)) (X := (101962564166583181233/50000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(988912864682877/8628400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(376513962200071/4314200000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (21571/25000 : ℝ)) (alpha := (988912864682877/8628400000000000 : ℝ)) (beta := (376513962200071/4314200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (21571/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(988912864682877/8628400000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(376513962200071/4314200000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (46901/100000 : ℝ) ^ (71/16 : ℝ) ≤ (108572691008098979/3125000000000000000 : ℝ) := by
    have hpowers : (46901/100000 : ℝ)^71 ≤ (108572691008098979/3125000000000000000 : ℝ)^16 := by
      have hnat : (46901 : ℕ)^71*3125000000000000000^16 ≤ 108572691008098979^16*100000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        46901 100000 108572691008098979 3125000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (46901/100000 : ℝ)) (X := (108572691008098979/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (3233572691008098979/3125000000000000000 : ℝ) ≤ (5038631107546039/5000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (3233572691008098979/3125000000000000000 : ℝ)^16 ≤ (5038631107546039/5000000000000000 : ℝ)^71 := by
      have hnat : (3233572691008098979 : ℕ)^16*5000000000000000^71 ≤ 5038631107546039^71*3125000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3233572691008098979 3125000000000000000 5038631107546039 5000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5038631107546039/5000000000000000 : ℝ)) (X := (3233572691008098979/3125000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (1671072691008098979/1562500000000000000 : ℝ) ≤ (5076270115013003/5000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (1671072691008098979/1562500000000000000 : ℝ)^16 ≤ (5076270115013003/5000000000000000 : ℝ)^71 := by
      have hnat : (1671072691008098979 : ℕ)^16*5000000000000000^71 ≤ 5076270115013003^71*1562500000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1671072691008098979 1562500000000000000 5076270115013003 5000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5076270115013003/5000000000000000 : ℝ)) (X := (1671072691008098979/1562500000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(38631107546039/2345050000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(9409751866741/586262500000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (46901/100000 : ℝ)) (alpha := (38631107546039/2345050000000000 : ℝ)) (beta := (9409751866741/586262500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (46901/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(38631107546039/2345050000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(9409751866741/586262500000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-390406043/1250000000 : ℝ)*X 0 0+(311195989/1000000000 : ℝ)*X 0 1+(788600269/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311057_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1557982213/5000000000 : ℝ)*X 1 0+(-1552351149/5000000000 : ℝ)*X 1 1+(6320683989/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311057_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((2383713069/5000000000 : ℝ)*X 0 0+(4781112973/10000000000 : ℝ)*X 0 1+(25245089/80000000 : ℝ)*X 0 2+(2383713069/5000000000 : ℝ)*X 1 0+(4781112973/10000000000 : ℝ)*X 1 1+(25245089/80000000 : ℝ)*X 1 2+(2383713069/5000000000 : ℝ)*X 2 0+(4781112973/10000000000 : ℝ)*X 2 1+(25245089/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311057_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-308539867/1250000000 : ℝ)*X 0 0+(1893301951/10000000000 : ℝ)*X 0 1+(385930809/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311057_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((2456744439/10000000000 : ℝ)*X 1 0+(-471105959/2500000000 : ℝ)*X 1 1+(7732901653/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311057_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((985591331/2500000000 : ℝ)*X 2 0+(7559086817/10000000000 : ℝ)*X 2 1+(-55903/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311057_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_12 : ((718306231/2000000000 : ℝ)*X 0 0+(3443198889/5000000000 : ℝ)*X 0 1+(1833567369/10000000000 : ℝ)*X 0 2+(718306231/2000000000 : ℝ)*X 1 0+(3443198889/5000000000 : ℝ)*X 1 1+(1833567369/10000000000 : ℝ)*X 1 2+(718306231/2000000000 : ℝ)*X 2 0+(3443198889/5000000000 : ℝ)*X 2 1+(1833567369/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311057_s1_s1_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((-190519547/1000000000 : ℝ)*X 0 0+(1228010563/5000000000 : ℝ)*X 0 1+(1543904249/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311057_s1_s1_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((1896256803/10000000000 : ℝ)*X 1 0+(-611124533/2500000000 : ℝ)*X 1 1+(309352337/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311057_s1_s1_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((7545359013/10000000000 : ℝ)*X 2 0+(3958885067/10000000000 : ℝ)*X 2 1+(-28129/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311057_s1_s1_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_18 : ((6874101417/10000000000 : ℝ)*X 0 0+(901672717/2500000000 : ℝ)*X 0 1+(1833127789/10000000000 : ℝ)*X 0 2+(6874101417/10000000000 : ℝ)*X 1 0+(901672717/2500000000 : ℝ)*X 1 1+(1833127789/10000000000 : ℝ)*X 1 2+(6874101417/10000000000 : ℝ)*X 2 0+(901672717/2500000000 : ℝ)*X 2 1+(1833127789/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311057_s1_s1_18 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_19 : ((-4486557389/10000000000 : ℝ)*X 0 0+(1998391417/10000000000 : ℝ)*X 0 1+(374158421/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311057_s1_s1_19 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((2003977639/10000000000 : ℝ)*X 1 0+(-558585581/1250000000 : ℝ)*X 1 1+(2999448027/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311057_s1_s1_20 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((6121087877/10000000000 : ℝ)*X 2 0+(2769105757/5000000000 : ℝ)*X 2 1+(6673551/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311057_s1_s1_21 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_25 : ((382079963/1000000000 : ℝ)*X 0 0+(2769105757/5000000000 : ℝ)*X 0 1+(3316640023/10000000000 : ℝ)*X 0 2+(382079963/1000000000 : ℝ)*X 1 0+(2769105757/5000000000 : ℝ)*X 1 1+(3316640023/10000000000 : ℝ)*X 1 2+(382079963/1000000000 : ℝ)*X 2 0+(2769105757/5000000000 : ℝ)*X 2 1+(3316640023/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311057_s1_s1_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((2178/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2178/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (38614091816120574641121/2345050000000000000000000000 : ℝ) := by norm_num
    linear_combination (202104784953/250000000000 : ℝ)*(base7) + (81850762223/250000000000 : ℝ)*(base59) + (12682479247/125000000000 : ℝ)*(base60) + (286502285483/125000000000 : ℝ)*(major_s1_0) + (286502285483/125000000000 : ℝ)*(major_s1_1) + (286502285483/125000000000 : ℝ)*(major_s1_2) + (996271/100000000000 : ℝ)*(sp_s1_0) + (5199241/500000000000 : ℝ)*(sp_s1_1) + (1352639203143/500000000000 : ℝ)*(sp_s1_7) + (541033798787/200000000000 : ℝ)*(sp_s1_8) + (676322092249/250000000000 : ℝ)*(sp_s1_9) + (1101507864701/500000000000 : ℝ)*(sp_s1_12) + (108976579/1000000000000 : ℝ)*(sp_s1_14) + (3246867/200000000000 : ℝ)*(sp_s1_25) + (55784512957/40000000000 : ℝ)*(f.failure) + (676322092249/250000000000 : ℝ)*(f.sum) + (1100054236896732311/10117014710000000000000000000000 : ℝ)*base63 + (62208554035993/293131250000000000000000000 : ℝ)*base65 + (239059753901179/1078550000000000000000000000 : ℝ)*base66 + (145285282706583/1172525000000000000000000000 : ℝ)*base68 + (21347961707149624737/51086914250000000000000000000000 : ℝ)*base71 + (47090097177327/272312500000000000000000000 : ℝ)*base72 + (106536839178129/1078550000000000000000000000 : ℝ)*base74 + (45938581975003/1089250000000000000000000000 : ℝ)*base76 + (11529885031187221/11748105875000000000000000000000 : ℝ)*base79 + (259/1000000000000000 : ℝ)*base87 + (259/1000000000000000 : ℝ)*base89 + (259/1000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6957/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(6957/10000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (61147275536490706670716133433/3443736960271093750000000000000000 : ℝ) := by norm_num
    linear_combination (161622120971/200000000000 : ℝ)*(base7) + (1311147/1000000000000 : ℝ)*(base40) + (325939082829/1000000000000 : ℝ)*(base59) + (226337093007/1000000000000 : ℝ)*(base60) + (7155138717/3125000000 : ℝ)*(major_s1_0) + (7155138717/3125000000 : ℝ)*(major_s1_1) + (7155138717/3125000000 : ℝ)*(major_s1_2) + (9637563/1000000000000 : ℝ)*(sp_s1_1) + (1889951/250000000000 : ℝ)*(sp_s1_6) + (12702731/100000000000 : ℝ)*(sp_s1_8) + (540433870203/200000000000 : ℝ)*(sp_s1_13) + (1351016343071/500000000000 : ℝ)*(sp_s1_14) + (540433870203/200000000000 : ℝ)*(sp_s1_15) + (550317859347/250000000000 : ℝ)*(sp_s1_18) + (696584196169/500000000000 : ℝ)*(f.failure) + (540433870203/200000000000 : ℝ)*(f.sum) + (126794103678705179/5058507355000000000000000000000 : ℝ)*base62 + (366220782574801/234505000000000000000000000 : ℝ)*base65 + (35157818058443/43142000000000000000000000 : ℝ)*base67 + (128355812283933/234505000000000000000000000 : ℝ)*base69 + (4480988413957887137/5108691425000000000000000000000 : ℝ)*base71 + (202361046885549/217850000000000000000000000 : ℝ)*base73 + (227906096256019/215710000000000000000000000 : ℝ)*base75 + (150047065673639/217850000000000000000000000 : ℝ)*base77 + (813394712297763397/2349621175000000000000000000000 : ℝ)*base79 + (4297/12500000000000000 : ℝ)*base86 + (4297/12500000000000000 : ℝ)*base88 + (4297/12500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(18923/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(18923/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (78742666898422024603390510773/14891835503875000000000000000000000 : ℝ) := by norm_num
    linear_combination (253008440843/1000000000000 : ℝ)*(base5) + (89857157169/1000000000000 : ℝ)*(base7) + (7819039/1000000000000 : ℝ)*(base8) + (2013673/250000000000 : ℝ)*(base16) + (20821/200000000000 : ℝ)*(base50) + (412609975647/500000000000 : ℝ)*(base59) + (981479719707/500000000000 : ℝ)*(major_s1_0) + (981479719707/500000000000 : ℝ)*(major_s1_1) + (981479719707/500000000000 : ℝ)*(major_s1_2) + (688289/500000000000 : ℝ)*(sp_s1_6) + (20919573393/7812500000 : ℝ)*(sp_s1_19) + (2677705158651/1000000000000 : ℝ)*(sp_s1_20) + (1465360827093/500000000000 : ℝ)*(sp_s1_21) + (515619692769/500000000000 : ℝ)*(sp_s1_25) + (1194392045789/1000000000000 : ℝ)*(f.failure) + (2677713213343/1000000000000 : ℝ)*(f.sum) + (481746388671113381/1093731320000000000000000000000 : ℝ)*base62 + (504845779180283/1172525000000000000000000000 : ℝ)*base64 + (19035465927241/58300000000000000000000000 : ℝ)*base67 + (13987144948111/2345050000000000000000000000 : ℝ)*base68 + (127437848301484575777/204347657000000000000000000000000 : ℝ)*base70 + (79751905496157/4357000000000000000000000000 : ℝ)*base72 + (45858025664213/116600000000000000000000000 : ℝ)*base74 + (686403268151437/4357000000000000000000000000 : ℝ)*base76 + (502196823818335839/2540131000000000000000000000000 : ℝ)*base79 + (17357/25000000000000000 : ℝ)*base86 + (17357/25000000000000000 : ℝ)*base88 + (17357/25000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((4357/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4357/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21571/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(21571/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(46901/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(46901/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2178/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2178/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6957/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(6957/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(18923/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(18923/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c311057_s1 p hpa hpb X hX hprev0

#print axioms solution
