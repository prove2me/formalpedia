-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c313063_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:34:57.594985+00:00
-- url     : https://prove2.me/submissions/760cd959-7f20-47d8-afb4-d2707dc4f065

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
theorem collision_support_c313063_s3_s3_0 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1537010473/10000000000 : ℝ)*x 0 + (5375399373/10000000000 : ℝ)*x 1 + (5397997733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1537010473/10000000000 : ℝ)^37 ≤ (916878551519/10000000000000 : ℝ)^29 := by
    have hnat : (1537010473 : ℕ)^37*10000000000000^29 ≤ 916878551519^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1537010473 10000000000 916878551519 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5375399373/10000000000 : ℝ)^37 ≤ (5661757932967/12500000000000 : ℝ)^29 := by
    have hnat : (5375399373 : ℕ)^37*12500000000000^29 ≤ 5661757932967^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375399373 10000000000 5661757932967 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5397997733/10000000000 : ℝ)^37 ≤ (22768575502781/50000000000000 : ℝ)^29 := by
    have hnat : (5397997733 : ℕ)^37*50000000000000^29 ≤ 22768575502781^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397997733 10000000000 22768575502781 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1537010473/10000000000 : ℝ), (5375399373/10000000000 : ℝ), (5397997733/10000000000 : ℝ)] ![(916878551519/10000000000000 : ℝ), (5661757932967/12500000000000 : ℝ), (22768575502781/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1537010473/10000000000 : ℝ)|^37 ≤ (916878551519/10000000000000 : ℝ)^29
        have hw : |(-1537010473/10000000000 : ℝ)|=(1537010473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5375399373/10000000000 : ℝ)|^37 ≤ (5661757932967/12500000000000 : ℝ)^29
        have hw : |(5375399373/10000000000 : ℝ)|=(5375399373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5397997733/10000000000 : ℝ)|^37 ≤ (22768575502781/50000000000000 : ℝ)^29
        have hw : |(5397997733/10000000000 : ℝ)|=(5397997733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313063_s3_s3_1 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5376320119/10000000000 : ℝ)*x 0 + (-1544729019/10000000000 : ℝ)*x 1 + (2695807583/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376320119/10000000000 : ℝ)^37 ≤ (22651981152671/50000000000000 : ℝ)^29 := by
    have hnat : (5376320119 : ℕ)^37*50000000000000^29 ≤ 22651981152671^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376320119 10000000000 22651981152671 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1544729019/10000000000 : ℝ)^37 ≤ (9227571603223/100000000000000 : ℝ)^29 := by
    have hnat : (1544729019 : ℕ)^37*100000000000000^29 ≤ 9227571603223^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1544729019 10000000000 9227571603223 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695807583/5000000000 : ℝ)^37 ≤ (22734233041577/50000000000000 : ℝ)^29 := by
    have hnat : (2695807583 : ℕ)^37*50000000000000^29 ≤ 22734233041577^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695807583 5000000000 22734233041577 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376320119/10000000000 : ℝ), (-1544729019/10000000000 : ℝ), (2695807583/5000000000 : ℝ)] ![(22651981152671/50000000000000 : ℝ), (9227571603223/100000000000000 : ℝ), (22734233041577/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376320119/10000000000 : ℝ)|^37 ≤ (22651981152671/50000000000000 : ℝ)^29
        have hw : |(5376320119/10000000000 : ℝ)|=(5376320119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1544729019/10000000000 : ℝ)|^37 ≤ (9227571603223/100000000000000 : ℝ)^29
        have hw : |(-1544729019/10000000000 : ℝ)|=(1544729019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695807583/5000000000 : ℝ)|^37 ≤ (22734233041577/50000000000000 : ℝ)^29
        have hw : |(2695807583/5000000000 : ℝ)|=(2695807583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313063_s3_s3_2 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1078720407/2000000000 : ℝ)*x 0 + (269411977/500000000 : ℝ)*x 1 + (-762535083/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078720407/2000000000 : ℝ)^37 ≤ (4548984503697/10000000000000 : ℝ)^29 := by
    have hnat : (1078720407 : ℕ)^37*10000000000000^29 ≤ 4548984503697^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078720407 2000000000 4548984503697 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269411977/500000000 : ℝ)^37 ≤ (22716074458427/50000000000000 : ℝ)^29 := by
    have hnat : (269411977 : ℕ)^37*50000000000000^29 ≤ 22716074458427^29*500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269411977 500000000 22716074458427 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (762535083/5000000000 : ℝ)^37 ≤ (9078006028143/100000000000000 : ℝ)^29 := by
    have hnat : (762535083 : ℕ)^37*100000000000000^29 ≤ 9078006028143^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      762535083 5000000000 9078006028143 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1078720407/2000000000 : ℝ), (269411977/500000000 : ℝ), (-762535083/5000000000 : ℝ)] ![(4548984503697/10000000000000 : ℝ), (22716074458427/50000000000000 : ℝ), (9078006028143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1078720407/2000000000 : ℝ)|^37 ≤ (4548984503697/10000000000000 : ℝ)^29
        have hw : |(1078720407/2000000000 : ℝ)|=(1078720407/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269411977/500000000 : ℝ)|^37 ≤ (22716074458427/50000000000000 : ℝ)^29
        have hw : |(269411977/500000000 : ℝ)|=(269411977/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-762535083/5000000000 : ℝ)|^37 ≤ (9078006028143/100000000000000 : ℝ)^29
        have hw : |(-762535083/5000000000 : ℝ)|=(762535083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313063_s3_s3_6 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4234453337/10000000000 : ℝ)*x 0 + (4230992033/10000000000 : ℝ)*x 1 + (2107888697/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4234453337/10000000000 : ℝ)^37 ≤ (33407570731297/100000000000000 : ℝ)^29 := by
    have hnat : (4234453337 : ℕ)^37*100000000000000^29 ≤ 33407570731297^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4234453337 10000000000 33407570731297 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4230992033/10000000000 : ℝ)^37 ≤ (1042897925871/3125000000000 : ℝ)^29 := by
    have hnat : (4230992033 : ℕ)^37*3125000000000^29 ≤ 1042897925871^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230992033 10000000000 1042897925871 3125000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2107888697/5000000000 : ℝ)^37 ≤ (33219695620559/100000000000000 : ℝ)^29 := by
    have hnat : (2107888697 : ℕ)^37*100000000000000^29 ≤ 33219695620559^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107888697 5000000000 33219695620559 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4234453337/10000000000 : ℝ), (4230992033/10000000000 : ℝ), (2107888697/5000000000 : ℝ)] ![(33407570731297/100000000000000 : ℝ), (1042897925871/3125000000000 : ℝ), (33219695620559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4234453337/10000000000 : ℝ)|^37 ≤ (33407570731297/100000000000000 : ℝ)^29
        have hw : |(4234453337/10000000000 : ℝ)|=(4234453337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4230992033/10000000000 : ℝ)|^37 ≤ (1042897925871/3125000000000 : ℝ)^29
        have hw : |(4230992033/10000000000 : ℝ)|=(4230992033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2107888697/5000000000 : ℝ)|^37 ≤ (33219695620559/100000000000000 : ℝ)^29
        have hw : |(2107888697/5000000000 : ℝ)|=(2107888697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313063_s3_s3_7 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-356372267/2500000000 : ℝ)*x 0 + (922239597/2000000000 : ℝ)*x 1 + (6207675237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (356372267/2500000000 : ℝ)^37 ≤ (520540634357/6250000000000 : ℝ)^29 := by
    have hnat : (356372267 : ℕ)^37*6250000000000^29 ≤ 520540634357^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      356372267 2500000000 520540634357 6250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (922239597/2000000000 : ℝ)^37 ≤ (9311352089061/25000000000000 : ℝ)^29 := by
    have hnat : (922239597 : ℕ)^37*25000000000000^29 ≤ 9311352089061^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      922239597 2000000000 9311352089061 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6207675237/10000000000 : ℝ)^37 ≤ (27212970741023/50000000000000 : ℝ)^29 := by
    have hnat : (6207675237 : ℕ)^37*50000000000000^29 ≤ 27212970741023^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6207675237 10000000000 27212970741023 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-356372267/2500000000 : ℝ), (922239597/2000000000 : ℝ), (6207675237/10000000000 : ℝ)] ![(520540634357/6250000000000 : ℝ), (9311352089061/25000000000000 : ℝ), (27212970741023/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-356372267/2500000000 : ℝ)|^37 ≤ (520540634357/6250000000000 : ℝ)^29
        have hw : |(-356372267/2500000000 : ℝ)|=(356372267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(922239597/2000000000 : ℝ)|^37 ≤ (9311352089061/25000000000000 : ℝ)^29
        have hw : |(922239597/2000000000 : ℝ)|=(922239597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6207675237/10000000000 : ℝ)|^37 ≤ (27212970741023/50000000000000 : ℝ)^29
        have hw : |(6207675237/10000000000 : ℝ)|=(6207675237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313063_s3_s3_8 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1006232381/2000000000 : ℝ)*x 0 + (-805336603/10000000000 : ℝ)*x 1 + (6201238029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1006232381/2000000000 : ℝ)^37 ≤ (41626499522289/100000000000000 : ℝ)^29 := by
    have hnat : (1006232381 : ℕ)^37*100000000000000^29 ≤ 41626499522289^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006232381 2000000000 41626499522289 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (805336603/10000000000 : ℝ)^37 ≤ (1004889063787/25000000000000 : ℝ)^29 := by
    have hnat : (805336603 : ℕ)^37*25000000000000^29 ≤ 1004889063787^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      805336603 10000000000 1004889063787 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6201238029/10000000000 : ℝ)^37 ≤ (10870788840287/20000000000000 : ℝ)^29 := by
    have hnat : (6201238029 : ℕ)^37*20000000000000^29 ≤ 10870788840287^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6201238029 10000000000 10870788840287 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1006232381/2000000000 : ℝ), (-805336603/10000000000 : ℝ), (6201238029/10000000000 : ℝ)] ![(41626499522289/100000000000000 : ℝ), (1004889063787/25000000000000 : ℝ), (10870788840287/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1006232381/2000000000 : ℝ)|^37 ≤ (41626499522289/100000000000000 : ℝ)^29
        have hw : |(1006232381/2000000000 : ℝ)|=(1006232381/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-805336603/10000000000 : ℝ)|^37 ≤ (1004889063787/25000000000000 : ℝ)^29
        have hw : |(-805336603/10000000000 : ℝ)|=(805336603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6201238029/10000000000 : ℝ)|^37 ≤ (10870788840287/20000000000000 : ℝ)^29
        have hw : |(6201238029/10000000000 : ℝ)|=(6201238029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313063_s3_s3_9 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4821483503/10000000000 : ℝ)*x 0 + (801785459/1250000000 : ℝ)*x 1 + (-774847067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4821483503/10000000000 : ℝ)^37 ≤ (39425957865853/100000000000000 : ℝ)^29 := by
    have hnat : (4821483503 : ℕ)^37*100000000000000^29 ≤ 39425957865853^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4821483503 10000000000 39425957865853 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (801785459/1250000000 : ℝ)^37 ≤ (28373810259587/50000000000000 : ℝ)^29 := by
    have hnat : (801785459 : ℕ)^37*50000000000000^29 ≤ 28373810259587^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      801785459 1250000000 28373810259587 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (774847067/10000000000 : ℝ)^37 ≤ (765284319637/20000000000000 : ℝ)^29 := by
    have hnat : (774847067 : ℕ)^37*20000000000000^29 ≤ 765284319637^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      774847067 10000000000 765284319637 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4821483503/10000000000 : ℝ), (801785459/1250000000 : ℝ), (-774847067/10000000000 : ℝ)] ![(39425957865853/100000000000000 : ℝ), (28373810259587/50000000000000 : ℝ), (765284319637/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4821483503/10000000000 : ℝ)|^37 ≤ (39425957865853/100000000000000 : ℝ)^29
        have hw : |(4821483503/10000000000 : ℝ)|=(4821483503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(801785459/1250000000 : ℝ)|^37 ≤ (28373810259587/50000000000000 : ℝ)^29
        have hw : |(801785459/1250000000 : ℝ)|=(801785459/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-774847067/10000000000 : ℝ)|^37 ≤ (765284319637/20000000000000 : ℝ)^29
        have hw : |(-774847067/10000000000 : ℝ)|=(774847067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313063_s3_s3_13 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4479135463/10000000000 : ℝ)*x 0 + (5624821721/10000000000 : ℝ)*x 1 + (1195819911/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4479135463/10000000000 : ℝ)^37 ≤ (35889871764867/100000000000000 : ℝ)^29 := by
    have hnat : (4479135463 : ℕ)^37*100000000000000^29 ≤ 35889871764867^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4479135463 10000000000 35889871764867 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5624821721/10000000000 : ℝ)^37 ≤ (47992486134649/100000000000000 : ℝ)^29 := by
    have hnat : (5624821721 : ℕ)^37*100000000000000^29 ≤ 47992486134649^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5624821721 10000000000 47992486134649 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1195819911/5000000000 : ℝ)^37 ≤ (1007352630141/6250000000000 : ℝ)^29 := by
    have hnat : (1195819911 : ℕ)^37*6250000000000^29 ≤ 1007352630141^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1195819911 5000000000 1007352630141 6250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4479135463/10000000000 : ℝ), (5624821721/10000000000 : ℝ), (1195819911/5000000000 : ℝ)] ![(35889871764867/100000000000000 : ℝ), (47992486134649/100000000000000 : ℝ), (1007352630141/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4479135463/10000000000 : ℝ)|^37 ≤ (35889871764867/100000000000000 : ℝ)^29
        have hw : |(4479135463/10000000000 : ℝ)|=(4479135463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5624821721/10000000000 : ℝ)|^37 ≤ (47992486134649/100000000000000 : ℝ)^29
        have hw : |(5624821721/10000000000 : ℝ)|=(5624821721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1195819911/5000000000 : ℝ)|^37 ≤ (1007352630141/6250000000000 : ℝ)^29
        have hw : |(1195819911/5000000000 : ℝ)|=(1195819911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313063_s3_s3_14 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-159773879/2000000000 : ℝ)*x 0 + (5040265783/10000000000 : ℝ)*x 1 + (6196320343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (159773879/2000000000 : ℝ)^37 ≤ (1989209326221/50000000000000 : ℝ)^29 := by
    have hnat : (159773879 : ℕ)^37*50000000000000^29 ≤ 1989209326221^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      159773879 2000000000 1989209326221 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5040265783/10000000000 : ℝ)^37 ≤ (20861312674343/50000000000000 : ℝ)^29 := by
    have hnat : (5040265783 : ℕ)^37*50000000000000^29 ≤ 20861312674343^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5040265783 10000000000 20861312674343 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6196320343/10000000000 : ℝ)^37 ≤ (13574738995147/25000000000000 : ℝ)^29 := by
    have hnat : (6196320343 : ℕ)^37*25000000000000^29 ≤ 13574738995147^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6196320343 10000000000 13574738995147 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-159773879/2000000000 : ℝ), (5040265783/10000000000 : ℝ), (6196320343/10000000000 : ℝ)] ![(1989209326221/50000000000000 : ℝ), (20861312674343/50000000000000 : ℝ), (13574738995147/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-159773879/2000000000 : ℝ)|^37 ≤ (1989209326221/50000000000000 : ℝ)^29
        have hw : |(-159773879/2000000000 : ℝ)|=(159773879/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5040265783/10000000000 : ℝ)|^37 ≤ (20861312674343/50000000000000 : ℝ)^29
        have hw : |(5040265783/10000000000 : ℝ)|=(5040265783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6196320343/10000000000 : ℝ)|^37 ≤ (13574738995147/25000000000000 : ℝ)^29
        have hw : |(6196320343/10000000000 : ℝ)|=(6196320343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313063_s3_s3_15 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (926427429/2000000000 : ℝ)*x 0 + (-177901489/1250000000 : ℝ)*x 1 + (3094941443/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (926427429/2000000000 : ℝ)^37 ≤ (37461328710587/100000000000000 : ℝ)^29 := by
    have hnat : (926427429 : ℕ)^37*100000000000000^29 ≤ 37461328710587^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      926427429 2000000000 37461328710587 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (177901489/1250000000 : ℝ)^37 ≤ (4155839495421/50000000000000 : ℝ)^29 := by
    have hnat : (177901489 : ℕ)^37*50000000000000^29 ≤ 4155839495421^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177901489 1250000000 4155839495421 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3094941443/5000000000 : ℝ)^37 ≤ (677837403619/1250000000000 : ℝ)^29 := by
    have hnat : (3094941443 : ℕ)^37*1250000000000^29 ≤ 677837403619^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3094941443 5000000000 677837403619 1250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(926427429/2000000000 : ℝ), (-177901489/1250000000 : ℝ), (3094941443/5000000000 : ℝ)] ![(37461328710587/100000000000000 : ℝ), (4155839495421/50000000000000 : ℝ), (677837403619/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(926427429/2000000000 : ℝ)|^37 ≤ (37461328710587/100000000000000 : ℝ)^29
        have hw : |(926427429/2000000000 : ℝ)|=(926427429/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-177901489/1250000000 : ℝ)|^37 ≤ (4155839495421/50000000000000 : ℝ)^29
        have hw : |(-177901489/1250000000 : ℝ)|=(177901489/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3094941443/5000000000 : ℝ)|^37 ≤ (677837403619/1250000000000 : ℝ)^29
        have hw : |(3094941443/5000000000 : ℝ)|=(3094941443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313063_s3_s3_16 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1238252661/2000000000 : ℝ)*x 0 + (5053217871/10000000000 : ℝ)*x 1 + (-157240507/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1238252661/2000000000 : ℝ)^37 ≤ (54242422117959/100000000000000 : ℝ)^29 := by
    have hnat : (1238252661 : ℕ)^37*100000000000000^29 ≤ 54242422117959^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1238252661 2000000000 54242422117959 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5053217871/10000000000 : ℝ)^37 ≤ (20929733059961/50000000000000 : ℝ)^29 := by
    have hnat : (5053217871 : ℕ)^37*50000000000000^29 ≤ 20929733059961^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5053217871 10000000000 20929733059961 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (157240507/2000000000 : ℝ)^37 ≤ (974527937673/25000000000000 : ℝ)^29 := by
    have hnat : (157240507 : ℕ)^37*25000000000000^29 ≤ 974527937673^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157240507 2000000000 974527937673 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1238252661/2000000000 : ℝ), (5053217871/10000000000 : ℝ), (-157240507/2000000000 : ℝ)] ![(54242422117959/100000000000000 : ℝ), (20929733059961/50000000000000 : ℝ), (974527937673/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1238252661/2000000000 : ℝ)|^37 ≤ (54242422117959/100000000000000 : ℝ)^29
        have hw : |(1238252661/2000000000 : ℝ)|=(1238252661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5053217871/10000000000 : ℝ)|^37 ≤ (20929733059961/50000000000000 : ℝ)^29
        have hw : |(5053217871/10000000000 : ℝ)|=(5053217871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-157240507/2000000000 : ℝ)|^37 ≤ (974527937673/25000000000000 : ℝ)^29
        have hw : |(-157240507/2000000000 : ℝ)|=(157240507/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313063_s3_s3_20 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1530798233/2500000000 : ℝ)*x 0 + (195444817/500000000 : ℝ)*x 1 + (60469417/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1530798233/2500000000 : ℝ)^37 ≤ (26741344732659/50000000000000 : ℝ)^29 := by
    have hnat : (1530798233 : ℕ)^37*50000000000000^29 ≤ 26741344732659^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1530798233 2500000000 26741344732659 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (195444817/500000000 : ℝ)^37 ≤ (37707468881/125000000000 : ℝ)^29 := by
    have hnat : (195444817 : ℕ)^37*125000000000^29 ≤ 37707468881^29*500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195444817 500000000 37707468881 125000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (60469417/250000000 : ℝ)^37 ≤ (16351335417829/100000000000000 : ℝ)^29 := by
    have hnat : (60469417 : ℕ)^37*100000000000000^29 ≤ 16351335417829^29*250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60469417 250000000 16351335417829 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1530798233/2500000000 : ℝ), (195444817/500000000 : ℝ), (60469417/250000000 : ℝ)] ![(26741344732659/50000000000000 : ℝ), (37707468881/125000000000 : ℝ), (16351335417829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1530798233/2500000000 : ℝ)|^37 ≤ (26741344732659/50000000000000 : ℝ)^29
        have hw : |(1530798233/2500000000 : ℝ)|=(1530798233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(195444817/500000000 : ℝ)|^37 ≤ (37707468881/125000000000 : ℝ)^29
        have hw : |(195444817/500000000 : ℝ)|=(195444817/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(60469417/250000000 : ℝ)|^37 ≤ (16351335417829/100000000000000 : ℝ)^29
        have hw : |(60469417/250000000 : ℝ)|=(60469417/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313063_s3_s3_21 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-148367513/2000000000 : ℝ)*x 0 + (1466280059/2500000000 : ℝ)*x 1 + (1354596113/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (148367513/2000000000 : ℝ)^37 ≤ (904919369129/25000000000000 : ℝ)^29 := by
    have hnat : (148367513 : ℕ)^37*25000000000000^29 ≤ 904919369129^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      148367513 2000000000 904919369129 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1466280059/2500000000 : ℝ)^37 ≤ (10124726652329/20000000000000 : ℝ)^29 := by
    have hnat : (1466280059 : ℕ)^37*20000000000000^29 ≤ 10124726652329^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1466280059 2500000000 10124726652329 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1354596113/2500000000 : ℝ)^37 ≤ (5719586156563/12500000000000 : ℝ)^29 := by
    have hnat : (1354596113 : ℕ)^37*12500000000000^29 ≤ 5719586156563^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354596113 2500000000 5719586156563 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-148367513/2000000000 : ℝ), (1466280059/2500000000 : ℝ), (1354596113/2500000000 : ℝ)] ![(904919369129/25000000000000 : ℝ), (10124726652329/20000000000000 : ℝ), (5719586156563/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-148367513/2000000000 : ℝ)|^37 ≤ (904919369129/25000000000000 : ℝ)^29
        have hw : |(-148367513/2000000000 : ℝ)|=(148367513/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1466280059/2500000000 : ℝ)|^37 ≤ (10124726652329/20000000000000 : ℝ)^29
        have hw : |(1466280059/2500000000 : ℝ)|=(1466280059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1354596113/2500000000 : ℝ)|^37 ≤ (5719586156563/12500000000000 : ℝ)^29
        have hw : |(1354596113/2500000000 : ℝ)|=(1354596113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313063_s3_s3_22 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1557715963/2500000000 : ℝ)*x 0 + (-185190597/2500000000 : ℝ)*x 1 + (1259567499/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1557715963/2500000000 : ℝ)^37 ≤ (54685466365383/100000000000000 : ℝ)^29 := by
    have hnat : (1557715963 : ℕ)^37*100000000000000^29 ≤ 54685466365383^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1557715963 2500000000 54685466365383 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (185190597/2500000000 : ℝ)^37 ≤ (1806492723197/50000000000000 : ℝ)^29 := by
    have hnat : (185190597 : ℕ)^37*50000000000000^29 ≤ 1806492723197^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      185190597 2500000000 1806492723197 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1259567499/2500000000 : ℝ)^37 ≤ (20850774087291/50000000000000 : ℝ)^29 := by
    have hnat : (1259567499 : ℕ)^37*50000000000000^29 ≤ 20850774087291^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1259567499 2500000000 20850774087291 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1557715963/2500000000 : ℝ), (-185190597/2500000000 : ℝ), (1259567499/2500000000 : ℝ)] ![(54685466365383/100000000000000 : ℝ), (1806492723197/50000000000000 : ℝ), (20850774087291/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1557715963/2500000000 : ℝ)|^37 ≤ (54685466365383/100000000000000 : ℝ)^29
        have hw : |(1557715963/2500000000 : ℝ)|=(1557715963/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-185190597/2500000000 : ℝ)|^37 ≤ (1806492723197/50000000000000 : ℝ)^29
        have hw : |(-185190597/2500000000 : ℝ)|=(185190597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1259567499/2500000000 : ℝ)|^37 ≤ (20850774087291/50000000000000 : ℝ)^29
        have hw : |(1259567499/2500000000 : ℝ)|=(1259567499/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313063_s3_s3_23 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4579062779/10000000000 : ℝ)*x 0 + (6251748269/10000000000 : ℝ)*x 1 + (-350906053/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4579062779/10000000000 : ℝ)^37 ≤ (36914562712467/100000000000000 : ℝ)^29 := by
    have hnat : (4579062779 : ℕ)^37*100000000000000^29 ≤ 36914562712467^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4579062779 10000000000 36914562712467 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6251748269/10000000000 : ℝ)^37 ≤ (27459715525993/50000000000000 : ℝ)^29 := by
    have hnat : (6251748269 : ℕ)^37*50000000000000^29 ≤ 27459715525993^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6251748269 10000000000 27459715525993 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (350906053/2500000000 : ℝ)^37 ≤ (8166006221821/100000000000000 : ℝ)^29 := by
    have hnat : (350906053 : ℕ)^37*100000000000000^29 ≤ 8166006221821^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      350906053 2500000000 8166006221821 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4579062779/10000000000 : ℝ), (6251748269/10000000000 : ℝ), (-350906053/2500000000 : ℝ)] ![(36914562712467/100000000000000 : ℝ), (27459715525993/50000000000000 : ℝ), (8166006221821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4579062779/10000000000 : ℝ)|^37 ≤ (36914562712467/100000000000000 : ℝ)^29
        have hw : |(4579062779/10000000000 : ℝ)|=(4579062779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6251748269/10000000000 : ℝ)|^37 ≤ (27459715525993/50000000000000 : ℝ)^29
        have hw : |(6251748269/10000000000 : ℝ)|=(6251748269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-350906053/2500000000 : ℝ)|^37 ≤ (8166006221821/100000000000000 : ℝ)^29
        have hw : |(-350906053/2500000000 : ℝ)|=(350906053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313063_s3_s3_27 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6291684949/10000000000 : ℝ)*x 0 + (1585504911/5000000000 : ℝ)*x 1 + (3001262161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6291684949/10000000000 : ℝ)^37 ≤ (11073487061311/20000000000000 : ℝ)^29 := by
    have hnat : (6291684949 : ℕ)^37*20000000000000^29 ≤ 11073487061311^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6291684949 10000000000 11073487061311 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1585504911/5000000000 : ℝ)^37 ≤ (4619839813909/20000000000000 : ℝ)^29 := by
    have hnat : (1585504911 : ℕ)^37*20000000000000^29 ≤ 4619839813909^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1585504911 5000000000 4619839813909 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3001262161/10000000000 : ℝ)^37 ≤ (21533365611639/100000000000000 : ℝ)^29 := by
    have hnat : (3001262161 : ℕ)^37*100000000000000^29 ≤ 21533365611639^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3001262161 10000000000 21533365611639 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6291684949/10000000000 : ℝ), (1585504911/5000000000 : ℝ), (3001262161/10000000000 : ℝ)] ![(11073487061311/20000000000000 : ℝ), (4619839813909/20000000000000 : ℝ), (21533365611639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6291684949/10000000000 : ℝ)|^37 ≤ (11073487061311/20000000000000 : ℝ)^29
        have hw : |(6291684949/10000000000 : ℝ)|=(6291684949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1585504911/5000000000 : ℝ)|^37 ≤ (4619839813909/20000000000000 : ℝ)^29
        have hw : |(1585504911/5000000000 : ℝ)|=(1585504911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3001262161/10000000000 : ℝ)|^37 ≤ (21533365611639/100000000000000 : ℝ)^29
        have hw : |(3001262161/10000000000 : ℝ)|=(3001262161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c313063_s3 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((48059/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(48059/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(48877/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(48877/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(46727/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(46727/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((33017/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(33017/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8369/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8369/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32003/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(32003/100000 : ℝ)*X 1 2) := by
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
  have main2 : (78599/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78599/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
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
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (48059/100000 : ℝ) ^ (73/16 : ℝ) ≤ (3532622290973129567/100000000000000000000 : ℝ) := by
    have hpowers : (48059/100000 : ℝ)^73 ≤ (3532622290973129567/100000000000000000000 : ℝ)^16 := by
      have hnat : (48059 : ℕ)^73*100000000000000000000^16 ≤ 3532622290973129567^16*100000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        48059 100000 3532622290973129567 100000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (48059/100000 : ℝ)) (X := (3532622290973129567/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s3_corner0a : (103532622290973129567/100000000000000000000 : ℝ) ≤ (10076381337041583/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (103532622290973129567/100000000000000000000 : ℝ)^16 ≤ (10076381337041583/10000000000000000 : ℝ)^73 := by
      have hnat : (103532622290973129567 : ℕ)^16*10000000000000000^73 ≤ 10076381337041583^73*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        103532622290973129567 100000000000000000000 10076381337041583 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10076381337041583/10000000000000000 : ℝ)) (X := (103532622290973129567/100000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s3_corner0b : (53532622290973129567/50000000000000000000 : ℝ) ≤ (5075377016248229/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (53532622290973129567/50000000000000000000 : ℝ)^16 ≤ (5075377016248229/5000000000000000 : ℝ)^73 := by
      have hnat : (53532622290973129567 : ℕ)^16*5000000000000000^73 ≤ 5075377016248229^73*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53532622290973129567 50000000000000000000 5075377016248229 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5075377016248229/5000000000000000 : ℝ)) (X := (53532622290973129567/50000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(76381337041583/4805900000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(594981563639/38447200000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (48059/100000 : ℝ)) (alpha := (76381337041583/4805900000000000 : ℝ)) (beta := (594981563639/38447200000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (48059/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(76381337041583/4805900000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(594981563639/38447200000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (48877/100000 : ℝ) ^ (73/16 : ℝ) ≤ (1907697347086553629/50000000000000000000 : ℝ) := by
    have hpowers : (48877/100000 : ℝ)^73 ≤ (1907697347086553629/50000000000000000000 : ℝ)^16 := by
      have hnat : (48877 : ℕ)^73*50000000000000000000^16 ≤ 1907697347086553629^16*100000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        48877 100000 1907697347086553629 50000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (48877/100000 : ℝ)) (X := (1907697347086553629/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s3_corner1a : (51907697347086553629/50000000000000000000 : ℝ) ≤ (2520601729543639/2500000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (51907697347086553629/50000000000000000000 : ℝ)^16 ≤ (2520601729543639/2500000000000000 : ℝ)^73 := by
      have hnat : (51907697347086553629 : ℕ)^16*2500000000000000^73 ≤ 2520601729543639^73*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51907697347086553629 50000000000000000000 2520601729543639 2500000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2520601729543639/2500000000000000 : ℝ)) (X := (51907697347086553629/50000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s3_corner1b : (26907697347086553629/25000000000000000000 : ℝ) ≤ (5081240965364333/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (26907697347086553629/25000000000000000000 : ℝ)^16 ≤ (5081240965364333/5000000000000000 : ℝ)^73 := by
      have hnat : (26907697347086553629 : ℕ)^16*5000000000000000^73 ≤ 5081240965364333^73*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26907697347086553629 25000000000000000000 5081240965364333 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5081240965364333/5000000000000000 : ℝ)) (X := (26907697347086553629/25000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(20601729543639/1221925000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(8007501255411/488770000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (48877/100000 : ℝ)) (alpha := (20601729543639/1221925000000000 : ℝ)) (beta := (8007501255411/488770000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (48877/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(20601729543639/1221925000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(8007501255411/488770000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (46727/100000 : ℝ) ^ (73/16 : ℝ) ≤ (3107445634937625699/100000000000000000000 : ℝ) := by
    have hpowers : (46727/100000 : ℝ)^73 ≤ (3107445634937625699/100000000000000000000 : ℝ)^16 := by
      have hnat : (46727 : ℕ)^73*100000000000000000000^16 ≤ 3107445634937625699^16*100000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        46727 100000 3107445634937625699 100000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (46727/100000 : ℝ)) (X := (3107445634937625699/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s3_corner2a : (103107445634937625699/100000000000000000000 : ℝ) ≤ (5033648519642843/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (103107445634937625699/100000000000000000000 : ℝ)^16 ≤ (5033648519642843/5000000000000000 : ℝ)^73 := by
      have hnat : (103107445634937625699 : ℕ)^16*5000000000000000^73 ≤ 5033648519642843^73*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        103107445634937625699 100000000000000000000 5033648519642843 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5033648519642843/5000000000000000 : ℝ)) (X := (103107445634937625699/100000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s3_corner2b : (53107445634937625699/50000000000000000000 : ℝ) ≤ (2026605716580069/2000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (53107445634937625699/50000000000000000000 : ℝ)^16 ≤ (2026605716580069/2000000000000000 : ℝ)^73 := by
      have hnat : (53107445634937625699 : ℕ)^16*2000000000000000^73 ≤ 2026605716580069^73*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53107445634937625699 50000000000000000000 2026605716580069 2000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2026605716580069/2000000000000000 : ℝ)) (X := (53107445634937625699/50000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(33648519642843/2336350000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(65731543614659/4672700000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (46727/100000 : ℝ)) (alpha := (33648519642843/2336350000000000 : ℝ)) (beta := (65731543614659/4672700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (46727/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(33648519642843/2336350000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(65731543614659/4672700000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-1537010473/10000000000 : ℝ)*X 0 0+(5375399373/10000000000 : ℝ)*X 0 1+(5397997733/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313063_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_1 : ((5376320119/10000000000 : ℝ)*X 1 0+(-1544729019/10000000000 : ℝ)*X 1 1+(2695807583/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313063_s3_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((1078720407/2000000000 : ℝ)*X 2 0+(269411977/500000000 : ℝ)*X 2 1+(-762535083/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313063_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_6 : ((4234453337/10000000000 : ℝ)*X 0 0+(4230992033/10000000000 : ℝ)*X 0 1+(2107888697/5000000000 : ℝ)*X 0 2+(4234453337/10000000000 : ℝ)*X 1 0+(4230992033/10000000000 : ℝ)*X 1 1+(2107888697/5000000000 : ℝ)*X 1 2+(4234453337/10000000000 : ℝ)*X 2 0+(4230992033/10000000000 : ℝ)*X 2 1+(2107888697/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313063_s3_s3_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-356372267/2500000000 : ℝ)*X 0 0+(922239597/2000000000 : ℝ)*X 0 1+(6207675237/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313063_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((1006232381/2000000000 : ℝ)*X 1 0+(-805336603/10000000000 : ℝ)*X 1 1+(6201238029/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313063_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((4821483503/10000000000 : ℝ)*X 2 0+(801785459/1250000000 : ℝ)*X 2 1+(-774847067/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313063_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((4479135463/10000000000 : ℝ)*X 0 0+(5624821721/10000000000 : ℝ)*X 0 1+(1195819911/5000000000 : ℝ)*X 0 2+(4479135463/10000000000 : ℝ)*X 1 0+(5624821721/10000000000 : ℝ)*X 1 1+(1195819911/5000000000 : ℝ)*X 1 2+(4479135463/10000000000 : ℝ)*X 2 0+(5624821721/10000000000 : ℝ)*X 2 1+(1195819911/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313063_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-159773879/2000000000 : ℝ)*X 0 0+(5040265783/10000000000 : ℝ)*X 0 1+(6196320343/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313063_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((926427429/2000000000 : ℝ)*X 1 0+(-177901489/1250000000 : ℝ)*X 1 1+(3094941443/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313063_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((1238252661/2000000000 : ℝ)*X 2 0+(5053217871/10000000000 : ℝ)*X 2 1+(-157240507/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313063_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((1530798233/2500000000 : ℝ)*X 0 0+(195444817/500000000 : ℝ)*X 0 1+(60469417/250000000 : ℝ)*X 0 2+(1530798233/2500000000 : ℝ)*X 1 0+(195444817/500000000 : ℝ)*X 1 1+(60469417/250000000 : ℝ)*X 1 2+(1530798233/2500000000 : ℝ)*X 2 0+(195444817/500000000 : ℝ)*X 2 1+(60469417/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313063_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-148367513/2000000000 : ℝ)*X 0 0+(1466280059/2500000000 : ℝ)*X 0 1+(1354596113/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313063_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((1557715963/2500000000 : ℝ)*X 1 0+(-185190597/2500000000 : ℝ)*X 1 1+(1259567499/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313063_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((4579062779/10000000000 : ℝ)*X 2 0+(6251748269/10000000000 : ℝ)*X 2 1+(-350906053/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313063_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((6291684949/10000000000 : ℝ)*X 0 0+(1585504911/5000000000 : ℝ)*X 0 1+(3001262161/10000000000 : ℝ)*X 0 2+(6291684949/10000000000 : ℝ)*X 1 0+(1585504911/5000000000 : ℝ)*X 1 1+(3001262161/10000000000 : ℝ)*X 1 2+(6291684949/10000000000 : ℝ)*X 2 0+(1585504911/5000000000 : ℝ)*X 2 1+(3001262161/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313063_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((33017/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(33017/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (11363576291381292355826331/892138898046875000000000000000 : ℝ) := by norm_num
    linear_combination (337463/200000000000 : ℝ)*(base50) + (145303207377/1000000000000 : ℝ)*(base60) + (2268780901943/500000000000 : ℝ)*(major_s3_0) + (2268780901943/500000000000 : ℝ)*(major_s3_1) + (2268780901943/500000000000 : ℝ)*(major_s3_2) + (3833393/200000000000 : ℝ)*(sp_s3_0) + (14400197/1000000000000 : ℝ)*(sp_s3_6) + (639782584743/100000000000 : ℝ)*(sp_s3_7) + (3198905304383/500000000000 : ℝ)*(sp_s3_8) + (6397809135147/1000000000000 : ℝ)*(sp_s3_9) + (535443709243/200000000000 : ℝ)*(sp_s3_13) + (20700571/500000000000 : ℝ)*(sp_s3_14) + (75806771/1000000000000 : ℝ)*(sp_s3_15) + (7728039/100000000000 : ℝ)*(sp_s3_23) + (2677232946413/1000000000000 : ℝ)*(f.failure) + (6397886415537/1000000000000 : ℝ)*(f.sum) + (33871352922968723843/114193778950000000000000000000000 : ℝ)*base62 + (79270647518171/1168175000000000000000000000 : ℝ)*base65 + (84104206383153/488770000000000000000000000 : ℝ)*base67 + (697467765163067/2336350000000000000000000000 : ℝ)*base68 + (12247526226007694289/28070661162500000000000000000000 : ℝ)*base71 + (96864340115987/480590000000000000000000000 : ℝ)*base72 + (1255819221846417/2443850000000000000000000000 : ℝ)*base74 + (281239970611181/2402950000000000000000000000 : ℝ)*base76 + (7032945484248360911/11744898715000000000000000000000 : ℝ)*base79 + (100131/100000000000000000 : ℝ)*base87 + (100131/100000000000000000 : ℝ)*base89 + (100131/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8369/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8369/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (67913120501531063816902141839/4154457852050000000000000000000000 : ℝ) := by norm_num
    linear_combination (5047309/1000000000000 : ℝ)*(base60) + (1150090257777/250000000000 : ℝ)*(major_s3_0) + (1150090257777/250000000000 : ℝ)*(major_s3_1) + (1150090257777/250000000000 : ℝ)*(major_s3_2) + (50332793/1000000000000 : ℝ)*(sp_s3_0) + (2523103/50000000000 : ℝ)*(sp_s3_1) + (4157353/40000000000 : ℝ)*(sp_s3_2) + (7821471/125000000000 : ℝ)*(sp_s3_7) + (28610167/500000000000 : ℝ)*(sp_s3_8) + (6486318228859/1000000000000 : ℝ)*(sp_s3_14) + (3243161725513/500000000000 : ℝ)*(sp_s3_15) + (1621581799899/250000000000 : ℝ)*(sp_s3_16) + (271416588603/100000000000 : ℝ)*(sp_s3_20) + (59796873/500000000000 : ℝ)*(sp_s3_27) + (84821421243/31250000000 : ℝ)*(f.failure) + (324321556671/50000000000 : ℝ)*(f.sum) + (8087901382156349/21611237500000000000000000000 : ℝ)*base63 + (121124596069861/584087500000000000000000000 : ℝ)*base64 + (9984839699/46250000000000000000000 : ℝ)*base67 + (764871323656677/1168175000000000000000000000 : ℝ)*base69 + (25393150507638915241/56141322325000000000000000000000 : ℝ)*base70 + (50132192670029/240295000000000000000000000 : ℝ)*base73 + (650888542321/1850000000000000000000000 : ℝ)*base74 + (374997675013139/1201475000000000000000000000 : ℝ)*base76 + (732431940326217/8890915000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (159/3125000000000000 : ℝ)*base86 + (159/3125000000000000 : ℝ)*base88 + (159/3125000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32003/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(32003/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (12715229751839750480339210919/1071882582530869140625000000000000 : ℝ) := by norm_num
    linear_combination (1676537/250000000000 : ℝ)*(base15) + (223863981577/1000000000000 : ℝ)*(base40) + (2124425481119/500000000000 : ℝ)*(major_s3_0) + (2124425481119/500000000000 : ℝ)*(major_s3_1) + (2124425481119/500000000000 : ℝ)*(major_s3_2) + (13011637/200000000000 : ℝ)*(sp_s3_0) + (28329741/500000000000 : ℝ)*(sp_s3_1) + (29045199/1000000000000 : ℝ)*(sp_s3_2) + (2023991/50000000000 : ℝ)*(sp_s3_9) + (33138983/500000000000 : ℝ)*(sp_s3_20) + (2995371955229/500000000000 : ℝ)*(sp_s3_21) + (5990745603013/1000000000000 : ℝ)*(sp_s3_22) + (748842430453/125000000000 : ℝ)*(sp_s3_23) + (2506822723691/1000000000000 : ℝ)*(sp_s3_27) + (2506889001657/1000000000000 : ℝ)*(f.failure) + (5990808968643/1000000000000 : ℝ)*(f.sum) + (5336283218988241587/57096889475000000000000000000000 : ℝ)*base62 + (24910155286019/146021875000000000000000000 : ℝ)*base64 + (51580460849843/244385000000000000000000000 : ℝ)*base66 + (612612047568041/2336350000000000000000000000 : ℝ)*base68 + (16474138047673629341/56141322325000000000000000000000 : ℝ)*base70 + (75780087177/3754609375000000000000000 : ℝ)*base73 + (171641695330689/610962500000000000000000000 : ℝ)*base74 + (898536711229033/2402950000000000000000000000 : ℝ)*base76 + (114303650066220913/587244935750000000000000000000 : ℝ)*base79 + (39959/100000000000000000 : ℝ)*base87 + (39959/100000000000000000 : ℝ)*base89 + (39959/100000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((48059/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(48059/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(48877/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(48877/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(46727/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(46727/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((33017/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(33017/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8369/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8369/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32003/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(32003/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c313063_s3 p hpa hpb X hX hprev2

#print axioms solution
