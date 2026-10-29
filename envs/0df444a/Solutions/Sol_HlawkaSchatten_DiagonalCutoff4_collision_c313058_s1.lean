-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c313058_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:34:09.768823+00:00
-- url     : https://prove2.me/submissions/594ab955-ddb2-432d-91c5-c4c6429762de

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
theorem collision_support_c313058_s1_s1_0 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-3332518953/10000000000 : ℝ)*x 0 + (3261843483/10000000000 : ℝ)*x 1 + (-5939358537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3332518953/10000000000 : ℝ)^37 ≤ (24610684777783/100000000000000 : ℝ)^29 := by
    have hnat : (3332518953 : ℕ)^37*100000000000000^29 ≤ 24610684777783^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3332518953 10000000000 24610684777783 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3261843483/10000000000 : ℝ)^37 ≤ (5986680149153/25000000000000 : ℝ)^29 := by
    have hnat : (3261843483 : ℕ)^37*25000000000000^29 ≤ 5986680149153^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3261843483 10000000000 5986680149153 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5939358537/10000000000 : ℝ)^37 ≤ (51442594608697/100000000000000 : ℝ)^29 := by
    have hnat : (5939358537 : ℕ)^37*100000000000000^29 ≤ 51442594608697^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5939358537 10000000000 51442594608697 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3332518953/10000000000 : ℝ), (3261843483/10000000000 : ℝ), (-5939358537/10000000000 : ℝ)] ![(24610684777783/100000000000000 : ℝ), (5986680149153/25000000000000 : ℝ), (51442594608697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3332518953/10000000000 : ℝ)|^37 ≤ (24610684777783/100000000000000 : ℝ)^29
        have hw : |(-3332518953/10000000000 : ℝ)|=(3332518953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3261843483/10000000000 : ℝ)|^37 ≤ (5986680149153/25000000000000 : ℝ)^29
        have hw : |(3261843483/10000000000 : ℝ)|=(3261843483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5939358537/10000000000 : ℝ)|^37 ≤ (51442594608697/100000000000000 : ℝ)^29
        have hw : |(-5939358537/10000000000 : ℝ)|=(5939358537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313058_s1_s1_2 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1125170421/2000000000 : ℝ)*x 0 + (5222581491/10000000000 : ℝ)*x 1 + (285365703/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1125170421/2000000000 : ℝ)^37 ≤ (750057862113/1562500000000 : ℝ)^29 := by
    have hnat : (1125170421 : ℕ)^37*1562500000000^29 ≤ 750057862113^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125170421 2000000000 750057862113 1562500000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5222581491/10000000000 : ℝ)^37 ≤ (10914415138079/25000000000000 : ℝ)^29 := by
    have hnat : (5222581491 : ℕ)^37*25000000000000^29 ≤ 10914415138079^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5222581491 10000000000 10914415138079 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (285365703/2000000000 : ℝ)^37 ≤ (333545450309/4000000000000 : ℝ)^29 := by
    have hnat : (285365703 : ℕ)^37*4000000000000^29 ≤ 333545450309^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285365703 2000000000 333545450309 4000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1125170421/2000000000 : ℝ), (5222581491/10000000000 : ℝ), (285365703/2000000000 : ℝ)] ![(750057862113/1562500000000 : ℝ), (10914415138079/25000000000000 : ℝ), (333545450309/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1125170421/2000000000 : ℝ)|^37 ≤ (750057862113/1562500000000 : ℝ)^29
        have hw : |(1125170421/2000000000 : ℝ)|=(1125170421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5222581491/10000000000 : ℝ)|^37 ≤ (10914415138079/25000000000000 : ℝ)^29
        have hw : |(5222581491/10000000000 : ℝ)|=(5222581491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(285365703/2000000000 : ℝ)|^37 ≤ (333545450309/4000000000000 : ℝ)^29
        have hw : |(285365703/2000000000 : ℝ)|=(285365703/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313058_s1_s1_6 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2115810293/5000000000 : ℝ)*x 0 + (854584313/1250000000 : ℝ)*x 1 + (-482501183/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2115810293/5000000000 : ℝ)^37 ≤ (1043095601953/3125000000000 : ℝ)^29 := by
    have hnat : (2115810293 : ℕ)^37*3125000000000^29 ≤ 1043095601953^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115810293 5000000000 1043095601953 3125000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (854584313/1250000000 : ℝ)^37 ≤ (12311610647521/20000000000000 : ℝ)^29 := by
    have hnat : (854584313 : ℕ)^37*20000000000000^29 ≤ 12311610647521^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      854584313 1250000000 12311610647521 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (482501183/5000000000 : ℝ)^37 ≤ (2531443740257/50000000000000 : ℝ)^29 := by
    have hnat : (482501183 : ℕ)^37*50000000000000^29 ≤ 2531443740257^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482501183 5000000000 2531443740257 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2115810293/5000000000 : ℝ), (854584313/1250000000 : ℝ), (-482501183/5000000000 : ℝ)] ![(1043095601953/3125000000000 : ℝ), (12311610647521/20000000000000 : ℝ), (2531443740257/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2115810293/5000000000 : ℝ)|^37 ≤ (1043095601953/3125000000000 : ℝ)^29
        have hw : |(2115810293/5000000000 : ℝ)|=(2115810293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(854584313/1250000000 : ℝ)|^37 ≤ (12311610647521/20000000000000 : ℝ)^29
        have hw : |(854584313/1250000000 : ℝ)|=(854584313/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-482501183/5000000000 : ℝ)|^37 ≤ (2531443740257/50000000000000 : ℝ)^29
        have hw : |(-482501183/5000000000 : ℝ)|=(482501183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313058_s1_s1_7 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-755166543/2500000000 : ℝ)*x 0 + (2790575401/10000000000 : ℝ)*x 1 + (-6583547067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (755166543/2500000000 : ℝ)^37 ≤ (5427787101991/25000000000000 : ℝ)^29 := by
    have hnat : (755166543 : ℕ)^37*25000000000000^29 ≤ 5427787101991^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      755166543 2500000000 5427787101991 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2790575401/10000000000 : ℝ)^37 ≤ (19623736144347/100000000000000 : ℝ)^29 := by
    have hnat : (2790575401 : ℕ)^37*100000000000000^29 ≤ 19623736144347^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2790575401 10000000000 19623736144347 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6583547067/10000000000 : ℝ)^37 ≤ (58665115429417/100000000000000 : ℝ)^29 := by
    have hnat : (6583547067 : ℕ)^37*100000000000000^29 ≤ 58665115429417^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6583547067 10000000000 58665115429417 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-755166543/2500000000 : ℝ), (2790575401/10000000000 : ℝ), (-6583547067/10000000000 : ℝ)] ![(5427787101991/25000000000000 : ℝ), (19623736144347/100000000000000 : ℝ), (58665115429417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-755166543/2500000000 : ℝ)|^37 ≤ (5427787101991/25000000000000 : ℝ)^29
        have hw : |(-755166543/2500000000 : ℝ)|=(755166543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2790575401/10000000000 : ℝ)|^37 ≤ (19623736144347/100000000000000 : ℝ)^29
        have hw : |(2790575401/10000000000 : ℝ)|=(2790575401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6583547067/10000000000 : ℝ)|^37 ≤ (58665115429417/100000000000000 : ℝ)^29
        have hw : |(-6583547067/10000000000 : ℝ)|=(6583547067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313058_s1_s1_8 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3109129127/10000000000 : ℝ)*x 0 + (-2811503191/10000000000 : ℝ)*x 1 + (-6495209763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3109129127/10000000000 : ℝ)^37 ≤ (22525634748847/100000000000000 : ℝ)^29 := by
    have hnat : (3109129127 : ℕ)^37*100000000000000^29 ≤ 22525634748847^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3109129127 10000000000 22525634748847 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2811503191/10000000000 : ℝ)^37 ≤ (3962339037423/20000000000000 : ℝ)^29 := by
    have hnat : (2811503191 : ℕ)^37*20000000000000^29 ≤ 3962339037423^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2811503191 10000000000 3962339037423 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6495209763/10000000000 : ℝ)^37 ≤ (57662670055343/100000000000000 : ℝ)^29 := by
    have hnat : (6495209763 : ℕ)^37*100000000000000^29 ≤ 57662670055343^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6495209763 10000000000 57662670055343 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3109129127/10000000000 : ℝ), (-2811503191/10000000000 : ℝ), (-6495209763/10000000000 : ℝ)] ![(22525634748847/100000000000000 : ℝ), (3962339037423/20000000000000 : ℝ), (57662670055343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3109129127/10000000000 : ℝ)|^37 ≤ (22525634748847/100000000000000 : ℝ)^29
        have hw : |(3109129127/10000000000 : ℝ)|=(3109129127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2811503191/10000000000 : ℝ)|^37 ≤ (3962339037423/20000000000000 : ℝ)^29
        have hw : |(-2811503191/10000000000 : ℝ)|=(2811503191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6495209763/10000000000 : ℝ)|^37 ≤ (57662670055343/100000000000000 : ℝ)^29
        have hw : |(-6495209763/10000000000 : ℝ)|=(6495209763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313058_s1_s1_9 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1123884121/2000000000 : ℝ)*x 0 + (1366041823/2500000000 : ℝ)*x 1 + (1075768239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1123884121/2000000000 : ℝ)^37 ≤ (23966848695473/50000000000000 : ℝ)^29 := by
    have hnat : (1123884121 : ℕ)^37*50000000000000^29 ≤ 23966848695473^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123884121 2000000000 23966848695473 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1366041823/2500000000 : ℝ)^37 ≤ (9250108078427/20000000000000 : ℝ)^29 := by
    have hnat : (1366041823 : ℕ)^37*20000000000000^29 ≤ 9250108078427^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366041823 2500000000 9250108078427 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1075768239/10000000000 : ℝ)^37 ≤ (5815762197721/100000000000000 : ℝ)^29 := by
    have hnat : (1075768239 : ℕ)^37*100000000000000^29 ≤ 5815762197721^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075768239 10000000000 5815762197721 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1123884121/2000000000 : ℝ), (1366041823/2500000000 : ℝ), (1075768239/10000000000 : ℝ)] ![(23966848695473/50000000000000 : ℝ), (9250108078427/20000000000000 : ℝ), (5815762197721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1123884121/2000000000 : ℝ)|^37 ≤ (23966848695473/50000000000000 : ℝ)^29
        have hw : |(1123884121/2000000000 : ℝ)|=(1123884121/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1366041823/2500000000 : ℝ)|^37 ≤ (9250108078427/20000000000000 : ℝ)^29
        have hw : |(1366041823/2500000000 : ℝ)|=(1366041823/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1075768239/10000000000 : ℝ)|^37 ≤ (5815762197721/100000000000000 : ℝ)^29
        have hw : |(1075768239/10000000000 : ℝ)|=(1075768239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313058_s1_s1_13 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (800768341/2000000000 : ℝ)*x 0 + (3725974387/5000000000 : ℝ)*x 1 + (-71767049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (800768341/2000000000 : ℝ)^37 ≤ (31103936303013/100000000000000 : ℝ)^29 := by
    have hnat : (800768341 : ℕ)^37*100000000000000^29 ≤ 31103936303013^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      800768341 2000000000 31103936303013 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3725974387/5000000000 : ℝ)^37 ≤ (34356108426731/50000000000000 : ℝ)^29 := by
    have hnat : (3725974387 : ℕ)^37*50000000000000^29 ≤ 34356108426731^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3725974387 5000000000 34356108426731 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (71767049/10000000000 : ℝ)^37 ≤ (91923415393/50000000000000 : ℝ)^29 := by
    have hnat : (71767049 : ℕ)^37*50000000000000^29 ≤ 91923415393^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71767049 10000000000 91923415393 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(800768341/2000000000 : ℝ), (3725974387/5000000000 : ℝ), (-71767049/10000000000 : ℝ)] ![(31103936303013/100000000000000 : ℝ), (34356108426731/50000000000000 : ℝ), (91923415393/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(800768341/2000000000 : ℝ)|^37 ≤ (31103936303013/100000000000000 : ℝ)^29
        have hw : |(800768341/2000000000 : ℝ)|=(800768341/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3725974387/5000000000 : ℝ)|^37 ≤ (34356108426731/50000000000000 : ℝ)^29
        have hw : |(3725974387/5000000000 : ℝ)|=(3725974387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-71767049/10000000000 : ℝ)|^37 ≤ (91923415393/50000000000000 : ℝ)^29
        have hw : |(-71767049/10000000000 : ℝ)|=(71767049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313058_s1_s1_14 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-565137693/2000000000 : ℝ)*x 0 + (296412241/1000000000 : ℝ)*x 1 + (-6601272633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (565137693/2000000000 : ℝ)^37 ≤ (9969658700661/50000000000000 : ℝ)^29 := by
    have hnat : (565137693 : ℕ)^37*50000000000000^29 ≤ 9969658700661^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565137693 2000000000 9969658700661 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (296412241/1000000000 : ℝ)^37 ≤ (5298492435319/25000000000000 : ℝ)^29 := by
    have hnat : (296412241 : ℕ)^37*25000000000000^29 ≤ 5298492435319^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      296412241 1000000000 5298492435319 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6601272633/10000000000 : ℝ)^37 ≤ (29433356424801/50000000000000 : ℝ)^29 := by
    have hnat : (6601272633 : ℕ)^37*50000000000000^29 ≤ 29433356424801^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6601272633 10000000000 29433356424801 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-565137693/2000000000 : ℝ), (296412241/1000000000 : ℝ), (-6601272633/10000000000 : ℝ)] ![(9969658700661/50000000000000 : ℝ), (5298492435319/25000000000000 : ℝ), (29433356424801/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-565137693/2000000000 : ℝ)|^37 ≤ (9969658700661/50000000000000 : ℝ)^29
        have hw : |(-565137693/2000000000 : ℝ)|=(565137693/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(296412241/1000000000 : ℝ)|^37 ≤ (5298492435319/25000000000000 : ℝ)^29
        have hw : |(296412241/1000000000 : ℝ)|=(296412241/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6601272633/10000000000 : ℝ)|^37 ≤ (29433356424801/50000000000000 : ℝ)^29
        have hw : |(-6601272633/10000000000 : ℝ)|=(6601272633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313058_s1_s1_15 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (89334169/312500000 : ℝ)*x 0 + (-1520595277/5000000000 : ℝ)*x 1 + (-3256467753/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (89334169/312500000 : ℝ)^37 ≤ (20236939983961/100000000000000 : ℝ)^29 := by
    have hnat : (89334169 : ℕ)^37*100000000000000^29 ≤ 20236939983961^29*312500000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89334169 312500000 20236939983961 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1520595277/5000000000 : ℝ)^37 ≤ (2737442420051/12500000000000 : ℝ)^29 := by
    have hnat : (1520595277 : ℕ)^37*12500000000000^29 ≤ 2737442420051^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1520595277 5000000000 2737442420051 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3256467753/5000000000 : ℝ)^37 ≤ (28931760315493/50000000000000 : ℝ)^29 := by
    have hnat : (3256467753 : ℕ)^37*50000000000000^29 ≤ 28931760315493^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3256467753 5000000000 28931760315493 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(89334169/312500000 : ℝ), (-1520595277/5000000000 : ℝ), (-3256467753/5000000000 : ℝ)] ![(20236939983961/100000000000000 : ℝ), (2737442420051/12500000000000 : ℝ), (28931760315493/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(89334169/312500000 : ℝ)|^37 ≤ (20236939983961/100000000000000 : ℝ)^29
        have hw : |(89334169/312500000 : ℝ)|=(89334169/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1520595277/5000000000 : ℝ)|^37 ≤ (2737442420051/12500000000000 : ℝ)^29
        have hw : |(-1520595277/5000000000 : ℝ)|=(1520595277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3256467753/5000000000 : ℝ)|^37 ≤ (28931760315493/50000000000000 : ℝ)^29
        have hw : |(-3256467753/5000000000 : ℝ)|=(3256467753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313058_s1_s1_16 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1529491787/2500000000 : ℝ)*x 0 + (512180511/1000000000 : ℝ)*x 1 + (800664763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1529491787/2500000000 : ℝ)^37 ≤ (13356115116093/25000000000000 : ℝ)^29 := by
    have hnat : (1529491787 : ℕ)^37*25000000000000^29 ≤ 13356115116093^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1529491787 2500000000 13356115116093 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (512180511/1000000000 : ℝ)^37 ≤ (8517141958963/20000000000000 : ℝ)^29 := by
    have hnat : (512180511 : ℕ)^37*20000000000000^29 ≤ 8517141958963^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512180511 1000000000 8517141958963 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (800664763/10000000000 : ℝ)^37 ≤ (3989829724187/100000000000000 : ℝ)^29 := by
    have hnat : (800664763 : ℕ)^37*100000000000000^29 ≤ 3989829724187^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      800664763 10000000000 3989829724187 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1529491787/2500000000 : ℝ), (512180511/1000000000 : ℝ), (800664763/10000000000 : ℝ)] ![(13356115116093/25000000000000 : ℝ), (8517141958963/20000000000000 : ℝ), (3989829724187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1529491787/2500000000 : ℝ)|^37 ≤ (13356115116093/25000000000000 : ℝ)^29
        have hw : |(1529491787/2500000000 : ℝ)|=(1529491787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(512180511/1000000000 : ℝ)|^37 ≤ (8517141958963/20000000000000 : ℝ)^29
        have hw : |(512180511/1000000000 : ℝ)|=(512180511/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(800664763/10000000000 : ℝ)|^37 ≤ (3989829724187/100000000000000 : ℝ)^29
        have hw : |(800664763/10000000000 : ℝ)|=(800664763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313058_s1_s1_20 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1071013299/2500000000 : ℝ)*x 0 + (1798926081/2500000000 : ℝ)*x 1 + (-126857997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071013299/2500000000 : ℝ)^37 ≤ (6781528155321/20000000000000 : ℝ)^29 := by
    have hnat : (1071013299 : ℕ)^37*20000000000000^29 ≤ 6781528155321^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071013299 2500000000 6781528155321 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1798926081/2500000000 : ℝ)^37 ≤ (32856043241899/50000000000000 : ℝ)^29 := by
    have hnat : (1798926081 : ℕ)^37*50000000000000^29 ≤ 32856043241899^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1798926081 2500000000 32856043241899 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (126857997/10000000000 : ℝ)^37 ≤ (380272734619/100000000000000 : ℝ)^29 := by
    have hnat : (126857997 : ℕ)^37*100000000000000^29 ≤ 380272734619^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126857997 10000000000 380272734619 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071013299/2500000000 : ℝ), (1798926081/2500000000 : ℝ), (-126857997/10000000000 : ℝ)] ![(6781528155321/20000000000000 : ℝ), (32856043241899/50000000000000 : ℝ), (380272734619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071013299/2500000000 : ℝ)|^37 ≤ (6781528155321/20000000000000 : ℝ)^29
        have hw : |(1071013299/2500000000 : ℝ)|=(1071013299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1798926081/2500000000 : ℝ)|^37 ≤ (32856043241899/50000000000000 : ℝ)^29
        have hw : |(1798926081/2500000000 : ℝ)|=(1798926081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-126857997/10000000000 : ℝ)|^37 ≤ (380272734619/100000000000000 : ℝ)^29
        have hw : |(-126857997/10000000000 : ℝ)|=(126857997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313058_s1_s1_21 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-164015859/500000000 : ℝ)*x 0 + (3221550701/10000000000 : ℝ)*x 1 + (-3008861923/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (164015859/500000000 : ℝ)^37 ≤ (24119893181703/100000000000000 : ℝ)^29 := by
    have hnat : (164015859 : ℕ)^37*100000000000000^29 ≤ 24119893181703^29*500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164015859 500000000 24119893181703 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3221550701/10000000000 : ℝ)^37 ≤ (11784977563713/50000000000000 : ℝ)^29 := by
    have hnat : (3221550701 : ℕ)^37*50000000000000^29 ≤ 11784977563713^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3221550701 10000000000 11784977563713 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3008861923/5000000000 : ℝ)^37 ≤ (13077537919131/25000000000000 : ℝ)^29 := by
    have hnat : (3008861923 : ℕ)^37*25000000000000^29 ≤ 13077537919131^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3008861923 5000000000 13077537919131 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-164015859/500000000 : ℝ), (3221550701/10000000000 : ℝ), (-3008861923/5000000000 : ℝ)] ![(24119893181703/100000000000000 : ℝ), (11784977563713/50000000000000 : ℝ), (13077537919131/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-164015859/500000000 : ℝ)|^37 ≤ (24119893181703/100000000000000 : ℝ)^29
        have hw : |(-164015859/500000000 : ℝ)|=(164015859/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3221550701/10000000000 : ℝ)|^37 ≤ (11784977563713/50000000000000 : ℝ)^29
        have hw : |(3221550701/10000000000 : ℝ)|=(3221550701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3008861923/5000000000 : ℝ)|^37 ≤ (13077537919131/25000000000000 : ℝ)^29
        have hw : |(-3008861923/5000000000 : ℝ)|=(3008861923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313058_s1_s1_22 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3229431089/10000000000 : ℝ)*x 0 + (-98133519/312500000 : ℝ)*x 1 + (-1532140953/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3229431089/10000000000 : ℝ)^37 ≤ (2955442563321/12500000000000 : ℝ)^29 := by
    have hnat : (3229431089 : ℕ)^37*12500000000000^29 ≤ 2955442563321^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3229431089 10000000000 2955442563321 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (98133519/312500000 : ℝ)^37 ≤ (22813909983053/100000000000000 : ℝ)^29 := by
    have hnat : (98133519 : ℕ)^37*100000000000000^29 ≤ 22813909983053^29*312500000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98133519 312500000 22813909983053 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1532140953/2500000000 : ℝ)^37 ≤ (13385637376191/25000000000000 : ℝ)^29 := by
    have hnat : (1532140953 : ℕ)^37*25000000000000^29 ≤ 13385637376191^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1532140953 2500000000 13385637376191 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3229431089/10000000000 : ℝ), (-98133519/312500000 : ℝ), (-1532140953/2500000000 : ℝ)] ![(2955442563321/12500000000000 : ℝ), (22813909983053/100000000000000 : ℝ), (13385637376191/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3229431089/10000000000 : ℝ)|^37 ≤ (2955442563321/12500000000000 : ℝ)^29
        have hw : |(3229431089/10000000000 : ℝ)|=(3229431089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-98133519/312500000 : ℝ)|^37 ≤ (22813909983053/100000000000000 : ℝ)^29
        have hw : |(-98133519/312500000 : ℝ)|=(98133519/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1532140953/2500000000 : ℝ)|^37 ≤ (13385637376191/25000000000000 : ℝ)^29
        have hw : |(-1532140953/2500000000 : ℝ)|=(1532140953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313058_s1_s1_23 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6501540481/10000000000 : ℝ)*x 0 + (4335555783/10000000000 : ℝ)*x 1 + (679553649/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6501540481/10000000000 : ℝ)^37 ≤ (28867193074839/50000000000000 : ℝ)^29 := by
    have hnat : (6501540481 : ℕ)^37*50000000000000^29 ≤ 28867193074839^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6501540481 10000000000 28867193074839 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4335555783/10000000000 : ℝ)^37 ≤ (6885717416591/20000000000000 : ℝ)^29 := by
    have hnat : (4335555783 : ℕ)^37*20000000000000^29 ≤ 6885717416591^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4335555783 10000000000 6885717416591 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (679553649/5000000000 : ℝ)^37 ≤ (7837026751113/100000000000000 : ℝ)^29 := by
    have hnat : (679553649 : ℕ)^37*100000000000000^29 ≤ 7837026751113^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679553649 5000000000 7837026751113 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6501540481/10000000000 : ℝ), (4335555783/10000000000 : ℝ), (679553649/5000000000 : ℝ)] ![(28867193074839/50000000000000 : ℝ), (6885717416591/20000000000000 : ℝ), (7837026751113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6501540481/10000000000 : ℝ)|^37 ≤ (28867193074839/50000000000000 : ℝ)^29
        have hw : |(6501540481/10000000000 : ℝ)|=(6501540481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4335555783/10000000000 : ℝ)|^37 ≤ (6885717416591/20000000000000 : ℝ)^29
        have hw : |(4335555783/10000000000 : ℝ)|=(4335555783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(679553649/5000000000 : ℝ)|^37 ≤ (7837026751113/100000000000000 : ℝ)^29
        have hw : |(679553649/5000000000 : ℝ)|=(679553649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313058_s1_s1_27 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (140189949/500000000 : ℝ)*x 0 + (260420159/312500000 : ℝ)*x 1 + (-2131951/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (140189949/500000000 : ℝ)^37 ≤ (19742456206763/100000000000000 : ℝ)^29 := by
    have hnat : (140189949 : ℕ)^37*100000000000000^29 ≤ 19742456206763^29*500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140189949 500000000 19742456206763 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260420159/312500000 : ℝ)^37 ≤ (15849409193903/20000000000000 : ℝ)^29 := by
    have hnat : (260420159 : ℕ)^37*20000000000000^29 ≤ 15849409193903^29*312500000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260420159 312500000 15849409193903 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2131951/78125000 : ℝ)^37 ≤ (1010497814041/100000000000000 : ℝ)^29 := by
    have hnat : (2131951 : ℕ)^37*100000000000000^29 ≤ 1010497814041^29*78125000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2131951 78125000 1010497814041 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(140189949/500000000 : ℝ), (260420159/312500000 : ℝ), (-2131951/78125000 : ℝ)] ![(19742456206763/100000000000000 : ℝ), (15849409193903/20000000000000 : ℝ), (1010497814041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(140189949/500000000 : ℝ)|^37 ≤ (19742456206763/100000000000000 : ℝ)^29
        have hw : |(140189949/500000000 : ℝ)|=(140189949/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(260420159/312500000 : ℝ)|^37 ≤ (15849409193903/20000000000000 : ℝ)^29
        have hw : |(260420159/312500000 : ℝ)|=(260420159/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2131951/78125000 : ℝ)|^37 ≤ (1010497814041/100000000000000 : ℝ)^29
        have hw : |(-2131951/78125000 : ℝ)|=(2131951/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c313058_s1 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((84479/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(84479/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15679/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(15679/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-69423/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-69423/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((12503/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12503/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8639/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8639/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-18089/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-18089/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (78599/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (78599/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (78599/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (78599/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78599/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78599/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base18 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s1_pow0 : (84479/100000 : ℝ) ^ (73/16 : ℝ) ≤ (23161209864274516541/50000000000000000000 : ℝ) := by
    have hpowers : (84479/100000 : ℝ)^73 ≤ (23161209864274516541/50000000000000000000 : ℝ)^16 := by
      have hnat : (84479 : ℕ)^73*50000000000000000000^16 ≤ 23161209864274516541^16*100000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        84479 100000 23161209864274516541 50000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (84479/100000 : ℝ)) (X := (23161209864274516541/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (73161209864274516541/50000000000000000000 : ℝ) ≤ (339689827979329/312500000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (73161209864274516541/50000000000000000000 : ℝ)^16 ≤ (339689827979329/312500000000000 : ℝ)^73 := by
      have hnat : (73161209864274516541 : ℕ)^16*312500000000000^73 ≤ 339689827979329^73*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        73161209864274516541 50000000000000000000 339689827979329 312500000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (339689827979329/312500000000000 : ℝ)) (X := (73161209864274516541/50000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (48161209864274516541/25000000000000000000 : ℝ) ≤ (1443186937585853/1250000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (48161209864274516541/25000000000000000000 : ℝ)^16 ≤ (1443186937585853/1250000000000000 : ℝ)^73 := by
      have hnat : (48161209864274516541 : ℕ)^16*1250000000000000^73 ≤ 1443186937585853^73*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        48161209864274516541 25000000000000000000 1443186937585853 1250000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1443186937585853/1250000000000000 : ℝ)) (X := (48161209864274516541/25000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(27189827979329/263996875000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(84427625668537/1055987500000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (84479/100000 : ℝ)) (alpha := (27189827979329/263996875000000 : ℝ)) (beta := (84427625668537/1055987500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (84479/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(27189827979329/263996875000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(84427625668537/1055987500000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (15679/20000 : ℝ) ^ (73/16 : ℝ) ≤ (32937502293602273221/100000000000000000000 : ℝ) := by
    have hpowers : (15679/20000 : ℝ)^73 ≤ (32937502293602273221/100000000000000000000 : ℝ)^16 := by
      have hnat : (15679 : ℕ)^73*100000000000000000000^16 ≤ 32937502293602273221^16*20000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15679 20000 32937502293602273221 100000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15679/20000 : ℝ)) (X := (32937502293602273221/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (132937502293602273221/100000000000000000000 : ℝ) ≤ (5321950483667819/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (132937502293602273221/100000000000000000000 : ℝ)^16 ≤ (5321950483667819/5000000000000000 : ℝ)^73 := by
      have hnat : (132937502293602273221 : ℕ)^16*5000000000000000^73 ≤ 5321950483667819^73*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        132937502293602273221 100000000000000000000 5321950483667819 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5321950483667819/5000000000000000 : ℝ)) (X := (132937502293602273221/100000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (82937502293602273221/50000000000000000000 : ℝ) ≤ (698314699471721/625000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (82937502293602273221/50000000000000000000 : ℝ)^16 ≤ (698314699471721/625000000000000 : ℝ)^73 := by
      have hnat : (82937502293602273221 : ℕ)^16*625000000000000^73 ≤ 698314699471721^73*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        82937502293602273221 50000000000000000000 698314699471721 625000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (698314699471721/625000000000000 : ℝ)) (X := (82937502293602273221/50000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(321950483667819/3919750000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(264567112105949/3919750000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (15679/20000 : ℝ)) (alpha := (321950483667819/3919750000000000 : ℝ)) (beta := (264567112105949/3919750000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (15679/20000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(321950483667819/3919750000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(264567112105949/3919750000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (69423/100000 : ℝ) ^ (73/16 : ℝ) ≤ (1891730029047773103/10000000000000000000 : ℝ) := by
    have hpowers : (69423/100000 : ℝ)^73 ≤ (1891730029047773103/10000000000000000000 : ℝ)^16 := by
      have hnat : (69423 : ℕ)^73*10000000000000000000^16 ≤ 1891730029047773103^16*100000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        69423 100000 1891730029047773103 10000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (69423/100000 : ℝ)) (X := (1891730029047773103/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (11891730029047773103/10000000000000000000 : ℝ) ≤ (10387046212069869/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (11891730029047773103/10000000000000000000 : ℝ)^16 ≤ (10387046212069869/10000000000000000 : ℝ)^73 := by
      have hnat : (11891730029047773103 : ℕ)^16*10000000000000000^73 ≤ 10387046212069869^73*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11891730029047773103 10000000000000000000 10387046212069869 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10387046212069869/10000000000000000 : ℝ)) (X := (11891730029047773103/10000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (6891730029047773103/5000000000000000000 : ℝ) ≤ (10728630159659103/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (6891730029047773103/5000000000000000000 : ℝ)^16 ≤ (10728630159659103/10000000000000000 : ℝ)^73 := by
      have hnat : (6891730029047773103 : ℕ)^16*10000000000000000^73 ≤ 10728630159659103^73*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6891730029047773103 5000000000000000000 10728630159659103 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10728630159659103/10000000000000000 : ℝ)) (X := (6891730029047773103/5000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(387046212069869/6942300000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(56930657931539/1157050000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (69423/100000 : ℝ)) (alpha := (387046212069869/6942300000000000 : ℝ)) (beta := (56930657931539/1157050000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (69423/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(387046212069869/6942300000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(56930657931539/1157050000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3332518953/10000000000 : ℝ)*X 0 0+(3261843483/10000000000 : ℝ)*X 0 1+(-5939358537/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313058_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1125170421/2000000000 : ℝ)*X 2 0+(5222581491/10000000000 : ℝ)*X 2 1+(285365703/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313058_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((2115810293/5000000000 : ℝ)*X 0 0+(854584313/1250000000 : ℝ)*X 0 1+(-482501183/5000000000 : ℝ)*X 0 2+(2115810293/5000000000 : ℝ)*X 1 0+(854584313/1250000000 : ℝ)*X 1 1+(-482501183/5000000000 : ℝ)*X 1 2+(2115810293/5000000000 : ℝ)*X 2 0+(854584313/1250000000 : ℝ)*X 2 1+(-482501183/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313058_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-755166543/2500000000 : ℝ)*X 0 0+(2790575401/10000000000 : ℝ)*X 0 1+(-6583547067/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313058_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((3109129127/10000000000 : ℝ)*X 1 0+(-2811503191/10000000000 : ℝ)*X 1 1+(-6495209763/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313058_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((1123884121/2000000000 : ℝ)*X 2 0+(1366041823/2500000000 : ℝ)*X 2 1+(1075768239/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313058_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((800768341/2000000000 : ℝ)*X 0 0+(3725974387/5000000000 : ℝ)*X 0 1+(-71767049/10000000000 : ℝ)*X 0 2+(800768341/2000000000 : ℝ)*X 1 0+(3725974387/5000000000 : ℝ)*X 1 1+(-71767049/10000000000 : ℝ)*X 1 2+(800768341/2000000000 : ℝ)*X 2 0+(3725974387/5000000000 : ℝ)*X 2 1+(-71767049/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313058_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-565137693/2000000000 : ℝ)*X 0 0+(296412241/1000000000 : ℝ)*X 0 1+(-6601272633/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313058_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((89334169/312500000 : ℝ)*X 1 0+(-1520595277/5000000000 : ℝ)*X 1 1+(-3256467753/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313058_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((1529491787/2500000000 : ℝ)*X 2 0+(512180511/1000000000 : ℝ)*X 2 1+(800664763/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313058_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((1071013299/2500000000 : ℝ)*X 0 0+(1798926081/2500000000 : ℝ)*X 0 1+(-126857997/10000000000 : ℝ)*X 0 2+(1071013299/2500000000 : ℝ)*X 1 0+(1798926081/2500000000 : ℝ)*X 1 1+(-126857997/10000000000 : ℝ)*X 1 2+(1071013299/2500000000 : ℝ)*X 2 0+(1798926081/2500000000 : ℝ)*X 2 1+(-126857997/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313058_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-164015859/500000000 : ℝ)*X 0 0+(3221550701/10000000000 : ℝ)*X 0 1+(-3008861923/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313058_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((3229431089/10000000000 : ℝ)*X 1 0+(-98133519/312500000 : ℝ)*X 1 1+(-1532140953/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313058_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((6501540481/10000000000 : ℝ)*X 2 0+(4335555783/10000000000 : ℝ)*X 2 1+(679553649/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313058_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((140189949/500000000 : ℝ)*X 0 0+(260420159/312500000 : ℝ)*X 0 1+(-2131951/78125000 : ℝ)*X 0 2+(140189949/500000000 : ℝ)*X 1 0+(260420159/312500000 : ℝ)*X 1 1+(-2131951/78125000 : ℝ)*X 1 2+(140189949/500000000 : ℝ)*X 2 0+(260420159/312500000 : ℝ)*X 2 1+(-2131951/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313058_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((12503/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12503/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1614967377018013918359002151/90706934750000000000000000000000 : ℝ) := by norm_num
    linear_combination (17653493/500000000000 : ℝ)*(base5) + (4407097/1000000000000 : ℝ)*(base59) + (1008480979587/500000000000 : ℝ)*(base60) + (9335106134109/1000000000000 : ℝ)*(major_s1_0) + (9335106134109/1000000000000 : ℝ)*(major_s1_1) + (9335106134109/1000000000000 : ℝ)*(major_s1_2) + (6917267/500000000000 : ℝ)*(sp_s1_6) + (13162149438633/1000000000000 : ℝ)*(sp_s1_7) + (6581126291577/500000000000 : ℝ)*(sp_s1_8) + (329059549037/25000000000 : ℝ)*(sp_s1_9) + (2753852589913/500000000000 : ℝ)*(sp_s1_13) + (197215861/1000000000000 : ℝ)*(sp_s1_14) + (4703567/50000000000 : ℝ)*(sp_s1_15) + (1646213/15625000000 : ℝ)*(sp_s1_27) + (2753929839489/500000000000 : ℝ)*(f.failure) + (6581173327247/500000000000 : ℝ)*(f.sum) + (61685926035315163193/181413869500000000000000000000000 : ℝ)*base62 + (1247042520101/4519726562500000000000000 : ℝ)*base65 + (625731319000509/3919750000000000000000000000 : ℝ)*base66 + (438491113251627/2314100000000000000000000000 : ℝ)*base68 + (2646421811293960851/19549285390000000000000000000000 : ℝ)*base71 + (21180430869039/131998437500000000000000000 : ℝ)*base72 + (28422499174379/3919750000000000000000000000 : ℝ)*base74 + (27682655917361/1055987500000000000000000000 : ℝ)*base76 + (5826249658113285729/331136560250000000000000000000000 : ℝ)*base79 + (22143/50000000000000000 : ℝ)*base87 + (22143/50000000000000000 : ℝ)*base89 + (22143/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8639/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8639/20000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (805623082254912560567184221/48873213475000000000000000000000 : ℝ) := by norm_num
    linear_combination (121709626303/31250000000 : ℝ)*(base5) + (2924207/250000000000 : ℝ)*(base18) + (2085013/500000000000 : ℝ)*(base49) + (259174039847/62500000000 : ℝ)*(base60) + (4296421458509/500000000000 : ℝ)*(major_s1_0) + (4296421458509/500000000000 : ℝ)*(major_s1_1) + (4296421458509/500000000000 : ℝ)*(major_s1_2) + (6795529/500000000000 : ℝ)*(sp_s1_2) + (164593113/1000000000000 : ℝ)*(sp_s1_8) + (484630706067/40000000000 : ℝ)*(sp_s1_14) + (12115591361733/1000000000000 : ℝ)*(sp_s1_15) + (8005226235759/500000000000 : ℝ)*(sp_s1_16) + (1175204646013/1000000000000 : ℝ)*(sp_s1_20) + (1926159/200000000000 : ℝ)*(sp_s1_23) + (506991268771/100000000000 : ℝ)*(f.failure) + (484630706067/40000000000 : ℝ)*(f.sum) + (38209514869861042523/136060402125000000000000000000000 : ℝ)*base63 + (25681530364377/289262500000000000000000000 : ℝ)*base64 + (74259591248091/1959875000000000000000000000 : ℝ)*base67 + (350162692593967/1735575000000000000000000000 : ℝ)*base69 + (3212375895147631/781971415600000000000000000000 : ℝ)*base70 + (394755152526263/2111975000000000000000000000 : ℝ)*base72 + (542242228487833/3919750000000000000000000000 : ℝ)*base74 + (622587081326473/4223950000000000000000000000 : ℝ)*base76 + (148027635386727102767/331136560250000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (10477/10000000000000000 : ℝ)*base87 + (10477/10000000000000000 : ℝ)*base89 + (10477/10000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-18089/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-18089/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (24690019339750266486752547/9774642695000000000000000000000 : ℝ) := by norm_num
    linear_combination (683661/500000000000 : ℝ)*(base15) + (63771605397/500000000000 : ℝ)*(base49) + (234532342203/500000000000 : ℝ)*(base60) + (2217539321/488281250 : ℝ)*(major_s1_0) + (2217539321/488281250 : ℝ)*(major_s1_1) + (2217539321/488281250 : ℝ)*(major_s1_2) + (176034949/1000000000000 : ℝ)*(sp_s1_0) + (21783769/1000000000000 : ℝ)*(sp_s1_2) + (20447709/1000000000000 : ℝ)*(sp_s1_13) + (692831/100000000000 : ℝ)*(sp_s1_16) + (6403295525051/1000000000000 : ℝ)*(sp_s1_21) + (6403470192679/1000000000000 : ℝ)*(sp_s1_22) + (3201721423961/500000000000 : ℝ)*(sp_s1_23) + (669887052281/250000000000 : ℝ)*(sp_s1_27) + (1339784328417/500000000000 : ℝ)*(f.failure) + (6403471560001/1000000000000 : ℝ)*(f.sum) + (26147047699423864781/68030201062500000000000000000000 : ℝ)*base62 + (214605893650683/289262500000000000000000000 : ℝ)*base65 + (663130769499277/979937500000000000000000000 : ℝ)*base66 + (51909891195671/867787500000000000000000000 : ℝ)*base69 + (2785914788780867827/9774642695000000000000000000000 : ℝ)*base71 + (735579749526021/4223950000000000000000000000 : ℝ)*base72 + (100414998748997/244984375000000000000000000 : ℝ)*base75 + (3179401361767927/4223950000000000000000000000 : ℝ)*base77 + (8585564155077053737/82784140062500000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (12079/50000000000000000 : ℝ)*base87 + (12079/50000000000000000 : ℝ)*base89 + (12079/50000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((84479/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(84479/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15679/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(15679/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-69423/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-69423/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((12503/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12503/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8639/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8639/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-18089/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-18089/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c313058_s1 p hpa hpb X hX hprev0

#print axioms solution
