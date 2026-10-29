-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c329055_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:28:37.790546+00:00
-- url     : https://prove2.me/submissions/aaf21074-0b5a-49f1-9ce5-ea12627ce269

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
theorem collision_support_c329055_s1_s1_0 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-825358321/5000000000 : ℝ)*x 0 + (2725731269/5000000000 : ℝ)*x 1 + (2349619103/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (825358321/5000000000 : ℝ)^95 ≤ (2865276042153/25000000000000 : ℝ)^79 := by
    have hnat : (825358321 : ℕ)^95*25000000000000^79 ≤ 2865276042153^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      825358321 5000000000 2865276042153 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2725731269/5000000000 : ℝ)^95 ≤ (48211271198111/100000000000000 : ℝ)^79 := by
    have hnat : (2725731269 : ℕ)^95*100000000000000^79 ≤ 48211271198111^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725731269 5000000000 48211271198111 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2349619103/5000000000 : ℝ)^95 ≤ (1260238269347/3125000000000 : ℝ)^79 := by
    have hnat : (2349619103 : ℕ)^95*3125000000000^79 ≤ 1260238269347^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2349619103 5000000000 1260238269347 3125000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-825358321/5000000000 : ℝ), (2725731269/5000000000 : ℝ), (2349619103/5000000000 : ℝ)] ![(2865276042153/25000000000000 : ℝ), (48211271198111/100000000000000 : ℝ), (1260238269347/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-825358321/5000000000 : ℝ)|^95 ≤ (2865276042153/25000000000000 : ℝ)^79
        have hw : |(-825358321/5000000000 : ℝ)|=(825358321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2725731269/5000000000 : ℝ)|^95 ≤ (48211271198111/100000000000000 : ℝ)^79
        have hw : |(2725731269/5000000000 : ℝ)|=(2725731269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2349619103/5000000000 : ℝ)|^95 ≤ (1260238269347/3125000000000 : ℝ)^79
        have hw : |(2349619103/5000000000 : ℝ)|=(2349619103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329055_s1_s1_1 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1174829659/2500000000 : ℝ)*x 0 + (-877656711/10000000000 : ℝ)*x 1 + (3009536523/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1174829659/2500000000 : ℝ)^95 ≤ (806569092857/2000000000000 : ℝ)^79 := by
    have hnat : (1174829659 : ℕ)^95*2000000000000^79 ≤ 806569092857^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1174829659 2500000000 806569092857 2000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (877656711/10000000000 : ℝ)^95 ≤ (41889436339/781250000000 : ℝ)^79 := by
    have hnat : (877656711 : ℕ)^95*781250000000^79 ≤ 41889436339^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      877656711 10000000000 41889436339 781250000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3009536523/5000000000 : ℝ)^95 ≤ (5430969749033/10000000000000 : ℝ)^79 := by
    have hnat : (3009536523 : ℕ)^95*10000000000000^79 ≤ 5430969749033^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3009536523 5000000000 5430969749033 10000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1174829659/2500000000 : ℝ), (-877656711/10000000000 : ℝ), (3009536523/5000000000 : ℝ)] ![(806569092857/2000000000000 : ℝ), (41889436339/781250000000 : ℝ), (5430969749033/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1174829659/2500000000 : ℝ)|^95 ≤ (806569092857/2000000000000 : ℝ)^79
        have hw : |(1174829659/2500000000 : ℝ)|=(1174829659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-877656711/10000000000 : ℝ)|^95 ≤ (41889436339/781250000000 : ℝ)^79
        have hw : |(-877656711/10000000000 : ℝ)|=(877656711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3009536523/5000000000 : ℝ)|^95 ≤ (5430969749033/10000000000000 : ℝ)^79
        have hw : |(3009536523/5000000000 : ℝ)|=(3009536523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329055_s1_s1_6 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6299708317/10000000000 : ℝ)*x 0 + (3688327847/10000000000 : ℝ)*x 1 + (1773542119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6299708317/10000000000 : ℝ)^95 ≤ (57368894414233/100000000000000 : ℝ)^79 := by
    have hnat : (6299708317 : ℕ)^95*100000000000000^79 ≤ 57368894414233^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6299708317 10000000000 57368894414233 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3688327847/10000000000 : ℝ)^95 ≤ (15068457281859/50000000000000 : ℝ)^79 := by
    have hnat : (3688327847 : ℕ)^95*50000000000000^79 ≤ 15068457281859^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3688327847 10000000000 15068457281859 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1773542119/10000000000 : ℝ)^95 ≤ (12494191008649/100000000000000 : ℝ)^79 := by
    have hnat : (1773542119 : ℕ)^95*100000000000000^79 ≤ 12494191008649^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1773542119 10000000000 12494191008649 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6299708317/10000000000 : ℝ), (3688327847/10000000000 : ℝ), (1773542119/10000000000 : ℝ)] ![(57368894414233/100000000000000 : ℝ), (15068457281859/50000000000000 : ℝ), (12494191008649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6299708317/10000000000 : ℝ)|^95 ≤ (57368894414233/100000000000000 : ℝ)^79
        have hw : |(6299708317/10000000000 : ℝ)|=(6299708317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3688327847/10000000000 : ℝ)|^95 ≤ (15068457281859/50000000000000 : ℝ)^79
        have hw : |(3688327847/10000000000 : ℝ)|=(3688327847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1773542119/10000000000 : ℝ)|^95 ≤ (12494191008649/100000000000000 : ℝ)^79
        have hw : |(1773542119/10000000000 : ℝ)|=(1773542119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329055_s1_s1_7 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-718620141/5000000000 : ℝ)*x 0 + (5050374063/10000000000 : ℝ)*x 1 + (527292571/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (718620141/5000000000 : ℝ)^95 ≤ (4851459657109/50000000000000 : ℝ)^79 := by
    have hnat : (718620141 : ℕ)^95*50000000000000^79 ≤ 4851459657109^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      718620141 5000000000 4851459657109 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5050374063/10000000000 : ℝ)^95 ≤ (43978172203587/100000000000000 : ℝ)^79 := by
    have hnat : (5050374063 : ℕ)^95*100000000000000^79 ≤ 43978172203587^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5050374063 10000000000 43978172203587 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (527292571/1000000000 : ℝ)^95 ≤ (5789863558553/12500000000000 : ℝ)^79 := by
    have hnat : (527292571 : ℕ)^95*12500000000000^79 ≤ 5789863558553^79*1000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527292571 1000000000 5789863558553 12500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-718620141/5000000000 : ℝ), (5050374063/10000000000 : ℝ), (527292571/1000000000 : ℝ)] ![(4851459657109/50000000000000 : ℝ), (43978172203587/100000000000000 : ℝ), (5789863558553/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-718620141/5000000000 : ℝ)|^95 ≤ (4851459657109/50000000000000 : ℝ)^79
        have hw : |(-718620141/5000000000 : ℝ)|=(718620141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5050374063/10000000000 : ℝ)|^95 ≤ (43978172203587/100000000000000 : ℝ)^79
        have hw : |(5050374063/10000000000 : ℝ)|=(5050374063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(527292571/1000000000 : ℝ)|^95 ≤ (5789863558553/12500000000000 : ℝ)^79
        have hw : |(527292571/1000000000 : ℝ)|=(527292571/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329055_s1_s1_8 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (9404289/20000000 : ℝ)*x 0 + (-240834787/5000000000 : ℝ)*x 1 + (6269335213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9404289/20000000 : ℝ)^95 ≤ (20178809449339/50000000000000 : ℝ)^79 := by
    have hnat : (9404289 : ℕ)^95*50000000000000^79 ≤ 20178809449339^79*20000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9404289 20000000 20178809449339 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (240834787/5000000000 : ℝ)^95 ≤ (2605938993371/100000000000000 : ℝ)^79 := by
    have hnat : (240834787 : ℕ)^95*100000000000000^79 ≤ 2605938993371^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240834787 5000000000 2605938993371 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6269335213/10000000000 : ℝ)^95 ≤ (11407288419051/20000000000000 : ℝ)^79 := by
    have hnat : (6269335213 : ℕ)^95*20000000000000^79 ≤ 11407288419051^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6269335213 10000000000 11407288419051 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9404289/20000000 : ℝ), (-240834787/5000000000 : ℝ), (6269335213/10000000000 : ℝ)] ![(20178809449339/50000000000000 : ℝ), (2605938993371/100000000000000 : ℝ), (11407288419051/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9404289/20000000 : ℝ)|^95 ≤ (20178809449339/50000000000000 : ℝ)^79
        have hw : |(9404289/20000000 : ℝ)|=(9404289/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-240834787/5000000000 : ℝ)|^95 ≤ (2605938993371/100000000000000 : ℝ)^79
        have hw : |(-240834787/5000000000 : ℝ)|=(240834787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6269335213/10000000000 : ℝ)|^95 ≤ (11407288419051/20000000000000 : ℝ)^79
        have hw : |(6269335213/10000000000 : ℝ)|=(6269335213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329055_s1_s1_9 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2348097407/5000000000 : ℝ)*x 0 + (5883041347/10000000000 : ℝ)*x 1 + (-26952747/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2348097407/5000000000 : ℝ)^95 ≤ (2518513715779/6250000000000 : ℝ)^79 := by
    have hnat : (2348097407 : ℕ)^95*6250000000000^79 ≤ 2518513715779^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2348097407 5000000000 2518513715779 6250000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5883041347/10000000000 : ℝ)^95 ≤ (26418551305049/50000000000000 : ℝ)^79 := by
    have hnat : (5883041347 : ℕ)^95*50000000000000^79 ≤ 26418551305049^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5883041347 10000000000 26418551305049 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26952747/250000000 : ℝ)^95 ≤ (171666947789/2500000000000 : ℝ)^79 := by
    have hnat : (26952747 : ℕ)^95*2500000000000^79 ≤ 171666947789^79*250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26952747 250000000 171666947789 2500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2348097407/5000000000 : ℝ), (5883041347/10000000000 : ℝ), (-26952747/250000000 : ℝ)] ![(2518513715779/6250000000000 : ℝ), (26418551305049/50000000000000 : ℝ), (171666947789/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2348097407/5000000000 : ℝ)|^95 ≤ (2518513715779/6250000000000 : ℝ)^79
        have hw : |(2348097407/5000000000 : ℝ)|=(2348097407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5883041347/10000000000 : ℝ)|^95 ≤ (26418551305049/50000000000000 : ℝ)^79
        have hw : |(5883041347/10000000000 : ℝ)|=(5883041347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-26952747/250000000 : ℝ)|^95 ≤ (171666947789/2500000000000 : ℝ)^79
        have hw : |(-26952747/250000000 : ℝ)|=(26952747/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329055_s1_s1_13 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (43346561/78125000 : ℝ)*x 0 + (2561013011/5000000000 : ℝ)*x 1 + (483635673/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43346561/78125000 : ℝ)^95 ≤ (6155450865101/12500000000000 : ℝ)^79 := by
    have hnat : (43346561 : ℕ)^95*12500000000000^79 ≤ 6155450865101^79*78125000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43346561 78125000 6155450865101 12500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2561013011/5000000000 : ℝ)^95 ≤ (44729551773479/100000000000000 : ℝ)^79 := by
    have hnat : (2561013011 : ℕ)^95*100000000000000^79 ≤ 44729551773479^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2561013011 5000000000 44729551773479 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (483635673/5000000000 : ℝ)^95 ≤ (3013420645603/50000000000000 : ℝ)^79 := by
    have hnat : (483635673 : ℕ)^95*50000000000000^79 ≤ 3013420645603^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      483635673 5000000000 3013420645603 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(43346561/78125000 : ℝ), (2561013011/5000000000 : ℝ), (483635673/5000000000 : ℝ)] ![(6155450865101/12500000000000 : ℝ), (44729551773479/100000000000000 : ℝ), (3013420645603/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(43346561/78125000 : ℝ)|^95 ≤ (6155450865101/12500000000000 : ℝ)^79
        have hw : |(43346561/78125000 : ℝ)|=(43346561/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2561013011/5000000000 : ℝ)|^95 ≤ (44729551773479/100000000000000 : ℝ)^79
        have hw : |(2561013011/5000000000 : ℝ)|=(2561013011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(483635673/5000000000 : ℝ)|^95 ≤ (3013420645603/50000000000000 : ℝ)^79
        have hw : |(483635673/5000000000 : ℝ)|=(483635673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329055_s1_s1_14 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-126892109/1250000000 : ℝ)*x 0 + (1321347753/2500000000 : ℝ)*x 1 + (5352628849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (126892109/1250000000 : ℝ)^95 ≤ (6387257067361/100000000000000 : ℝ)^79 := by
    have hnat : (126892109 : ℕ)^95*100000000000000^79 ≤ 6387257067361^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126892109 1250000000 6387257067361 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1321347753/2500000000 : ℝ)^95 ≤ (11612653944057/25000000000000 : ℝ)^79 := by
    have hnat : (1321347753 : ℕ)^95*25000000000000^79 ≤ 11612653944057^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321347753 2500000000 11612653944057 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5352628849/10000000000 : ℝ)^95 ≤ (47162127142013/100000000000000 : ℝ)^79 := by
    have hnat : (5352628849 : ℕ)^95*100000000000000^79 ≤ 47162127142013^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352628849 10000000000 47162127142013 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-126892109/1250000000 : ℝ), (1321347753/2500000000 : ℝ), (5352628849/10000000000 : ℝ)] ![(6387257067361/100000000000000 : ℝ), (11612653944057/25000000000000 : ℝ), (47162127142013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-126892109/1250000000 : ℝ)|^95 ≤ (6387257067361/100000000000000 : ℝ)^79
        have hw : |(-126892109/1250000000 : ℝ)|=(126892109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1321347753/2500000000 : ℝ)|^95 ≤ (11612653944057/25000000000000 : ℝ)^79
        have hw : |(1321347753/2500000000 : ℝ)|=(1321347753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5352628849/10000000000 : ℝ)|^95 ≤ (47162127142013/100000000000000 : ℝ)^79
        have hw : |(5352628849/10000000000 : ℝ)|=(5352628849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329055_s1_s1_15 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4481948871/10000000000 : ℝ)*x 0 + (-40525769/500000000 : ℝ)*x 1 + (97951503/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4481948871/10000000000 : ℝ)^95 ≤ (38095871678763/100000000000000 : ℝ)^79 := by
    have hnat : (4481948871 : ℕ)^95*100000000000000^79 ≤ 38095871678763^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481948871 10000000000 38095871678763 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40525769/500000000 : ℝ)^95 ≤ (2436244585509/50000000000000 : ℝ)^79 := by
    have hnat : (40525769 : ℕ)^95*50000000000000^79 ≤ 2436244585509^79*500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40525769 500000000 2436244585509 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (97951503/156250000 : ℝ)^95 ≤ (28515819563789/50000000000000 : ℝ)^79 := by
    have hnat : (97951503 : ℕ)^95*50000000000000^79 ≤ 28515819563789^79*156250000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97951503 156250000 28515819563789 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4481948871/10000000000 : ℝ), (-40525769/500000000 : ℝ), (97951503/156250000 : ℝ)] ![(38095871678763/100000000000000 : ℝ), (2436244585509/50000000000000 : ℝ), (28515819563789/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4481948871/10000000000 : ℝ)|^95 ≤ (38095871678763/100000000000000 : ℝ)^79
        have hw : |(4481948871/10000000000 : ℝ)|=(4481948871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-40525769/500000000 : ℝ)|^95 ≤ (2436244585509/50000000000000 : ℝ)^79
        have hw : |(-40525769/500000000 : ℝ)|=(40525769/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(97951503/156250000 : ℝ)|^95 ≤ (28515819563789/50000000000000 : ℝ)^79
        have hw : |(97951503/156250000 : ℝ)|=(97951503/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329055_s1_s1_16 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (10692421/20000000 : ℝ)*x 0 + (662972151/1250000000 : ℝ)*x 1 + (-998405357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10692421/20000000 : ℝ)^95 ≤ (23547064790059/50000000000000 : ℝ)^79 := by
    have hnat : (10692421 : ℕ)^95*50000000000000^79 ≤ 23547064790059^79*20000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10692421 20000000 23547064790059 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (662972151/1250000000 : ℝ)^95 ≤ (46644997565171/100000000000000 : ℝ)^79 := by
    have hnat : (662972151 : ℕ)^95*100000000000000^79 ≤ 46644997565171^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662972151 1250000000 46644997565171 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (998405357/10000000000 : ℝ)^95 ≤ (6260872834333/100000000000000 : ℝ)^79 := by
    have hnat : (998405357 : ℕ)^95*100000000000000^79 ≤ 6260872834333^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998405357 10000000000 6260872834333 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10692421/20000000 : ℝ), (662972151/1250000000 : ℝ), (-998405357/10000000000 : ℝ)] ![(23547064790059/50000000000000 : ℝ), (46644997565171/100000000000000 : ℝ), (6260872834333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10692421/20000000 : ℝ)|^95 ≤ (23547064790059/50000000000000 : ℝ)^79
        have hw : |(10692421/20000000 : ℝ)|=(10692421/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(662972151/1250000000 : ℝ)|^95 ≤ (46644997565171/100000000000000 : ℝ)^79
        have hw : |(662972151/1250000000 : ℝ)|=(662972151/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-998405357/10000000000 : ℝ)|^95 ≤ (6260872834333/100000000000000 : ℝ)^79
        have hw : |(-998405357/10000000000 : ℝ)|=(998405357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329055_s1_s1_20 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7093048603/10000000000 : ℝ)*x 0 + (3448659163/10000000000 : ℝ)*x 1 + (968789539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7093048603/10000000000 : ℝ)^95 ≤ (66164020074411/100000000000000 : ℝ)^79 := by
    have hnat : (7093048603 : ℕ)^95*100000000000000^79 ≤ 66164020074411^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7093048603 10000000000 66164020074411 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3448659163/10000000000 : ℝ)^95 ≤ (13898880725139/50000000000000 : ℝ)^79 := by
    have hnat : (3448659163 : ℕ)^95*50000000000000^79 ≤ 13898880725139^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3448659163 10000000000 13898880725139 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (968789539/10000000000 : ℝ)^95 ≤ (6038218452757/100000000000000 : ℝ)^79 := by
    have hnat : (968789539 : ℕ)^95*100000000000000^79 ≤ 6038218452757^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      968789539 10000000000 6038218452757 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7093048603/10000000000 : ℝ), (3448659163/10000000000 : ℝ), (968789539/10000000000 : ℝ)] ![(66164020074411/100000000000000 : ℝ), (13898880725139/50000000000000 : ℝ), (6038218452757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7093048603/10000000000 : ℝ)|^95 ≤ (66164020074411/100000000000000 : ℝ)^79
        have hw : |(7093048603/10000000000 : ℝ)|=(7093048603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3448659163/10000000000 : ℝ)|^95 ≤ (13898880725139/50000000000000 : ℝ)^79
        have hw : |(3448659163/10000000000 : ℝ)|=(3448659163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(968789539/10000000000 : ℝ)|^95 ≤ (6038218452757/100000000000000 : ℝ)^79
        have hw : |(968789539/10000000000 : ℝ)|=(968789539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329055_s1_s1_21 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-4403191/39062500 : ℝ)*x 0 + (1178390927/2000000000 : ℝ)*x 1 + (2325100541/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4403191/39062500 : ℝ)^95 ≤ (7244509842147/100000000000000 : ℝ)^79 := by
    have hnat : (4403191 : ℕ)^95*100000000000000^79 ≤ 7244509842147^79*39062500^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4403191 39062500 7244509842147 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1178390927/2000000000 : ℝ)^95 ≤ (26466691534027/50000000000000 : ℝ)^79 := by
    have hnat : (1178390927 : ℕ)^95*50000000000000^79 ≤ 26466691534027^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1178390927 2000000000 26466691534027 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2325100541/5000000000 : ℝ)^95 ≤ (39822107071249/100000000000000 : ℝ)^79 := by
    have hnat : (2325100541 : ℕ)^95*100000000000000^79 ≤ 39822107071249^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2325100541 5000000000 39822107071249 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4403191/39062500 : ℝ), (1178390927/2000000000 : ℝ), (2325100541/5000000000 : ℝ)] ![(7244509842147/100000000000000 : ℝ), (26466691534027/50000000000000 : ℝ), (39822107071249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4403191/39062500 : ℝ)|^95 ≤ (7244509842147/100000000000000 : ℝ)^79
        have hw : |(-4403191/39062500 : ℝ)|=(4403191/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1178390927/2000000000 : ℝ)|^95 ≤ (26466691534027/50000000000000 : ℝ)^79
        have hw : |(1178390927/2000000000 : ℝ)|=(1178390927/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2325100541/5000000000 : ℝ)|^95 ≤ (39822107071249/100000000000000 : ℝ)^79
        have hw : |(2325100541/5000000000 : ℝ)|=(2325100541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329055_s1_s1_22 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1310020819/2500000000 : ℝ)*x 0 + (-227186903/5000000000 : ℝ)*x 1 + (576812177/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1310020819/2500000000 : ℝ)^95 ≤ (45972200320839/100000000000000 : ℝ)^79 := by
    have hnat : (1310020819 : ℕ)^95*100000000000000^79 ≤ 45972200320839^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310020819 2500000000 45972200320839 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (227186903/5000000000 : ℝ)^95 ≤ (2429388608087/100000000000000 : ℝ)^79 := by
    have hnat : (227186903 : ℕ)^95*100000000000000^79 ≤ 2429388608087^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227186903 5000000000 2429388608087 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (576812177/1000000000 : ℝ)^95 ≤ (51598411060041/100000000000000 : ℝ)^79 := by
    have hnat : (576812177 : ℕ)^95*100000000000000^79 ≤ 51598411060041^79*1000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      576812177 1000000000 51598411060041 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1310020819/2500000000 : ℝ), (-227186903/5000000000 : ℝ), (576812177/1000000000 : ℝ)] ![(45972200320839/100000000000000 : ℝ), (2429388608087/100000000000000 : ℝ), (51598411060041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1310020819/2500000000 : ℝ)|^95 ≤ (45972200320839/100000000000000 : ℝ)^79
        have hw : |(1310020819/2500000000 : ℝ)|=(1310020819/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-227186903/5000000000 : ℝ)|^95 ≤ (2429388608087/100000000000000 : ℝ)^79
        have hw : |(-227186903/5000000000 : ℝ)|=(227186903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(576812177/1000000000 : ℝ)|^95 ≤ (51598411060041/100000000000000 : ℝ)^79
        have hw : |(576812177/1000000000 : ℝ)|=(576812177/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329055_s1_s1_23 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4370307341/10000000000 : ℝ)*x 0 + (5910338381/10000000000 : ℝ)*x 1 + (-1462739291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4370307341/10000000000 : ℝ)^95 ≤ (4619705517713/12500000000000 : ℝ)^79 := by
    have hnat : (4370307341 : ℕ)^95*12500000000000^79 ≤ 4619705517713^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370307341 10000000000 4619705517713 12500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5910338381/10000000000 : ℝ)^95 ≤ (53132055618991/100000000000000 : ℝ)^79 := by
    have hnat : (5910338381 : ℕ)^95*100000000000000^79 ≤ 53132055618991^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5910338381 10000000000 53132055618991 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1462739291/10000000000 : ℝ)^95 ≤ (9910300223457/100000000000000 : ℝ)^79 := by
    have hnat : (1462739291 : ℕ)^95*100000000000000^79 ≤ 9910300223457^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1462739291 10000000000 9910300223457 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4370307341/10000000000 : ℝ), (5910338381/10000000000 : ℝ), (-1462739291/10000000000 : ℝ)] ![(4619705517713/12500000000000 : ℝ), (53132055618991/100000000000000 : ℝ), (9910300223457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4370307341/10000000000 : ℝ)|^95 ≤ (4619705517713/12500000000000 : ℝ)^79
        have hw : |(4370307341/10000000000 : ℝ)|=(4370307341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5910338381/10000000000 : ℝ)|^95 ≤ (53132055618991/100000000000000 : ℝ)^79
        have hw : |(5910338381/10000000000 : ℝ)|=(5910338381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1462739291/10000000000 : ℝ)|^95 ≤ (9910300223457/100000000000000 : ℝ)^79
        have hw : |(-1462739291/10000000000 : ℝ)|=(1462739291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329055_s1_s1_27 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1864344903/2500000000 : ℝ)*x 0 + (1110497411/5000000000 : ℝ)*x 1 + (234284721/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1864344903/2500000000 : ℝ)^95 ≤ (14054355364983/20000000000000 : ℝ)^79 := by
    have hnat : (1864344903 : ℕ)^95*20000000000000^79 ≤ 14054355364983^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1864344903 2500000000 14054355364983 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1110497411/5000000000 : ℝ)^95 ≤ (1637580828239/10000000000000 : ℝ)^79 := by
    have hnat : (1110497411 : ℕ)^95*10000000000000^79 ≤ 1637580828239^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1110497411 5000000000 1637580828239 10000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (234284721/1250000000 : ℝ)^95 ≤ (6676207436167/50000000000000 : ℝ)^79 := by
    have hnat : (234284721 : ℕ)^95*50000000000000^79 ≤ 6676207436167^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234284721 1250000000 6676207436167 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1864344903/2500000000 : ℝ), (1110497411/5000000000 : ℝ), (234284721/1250000000 : ℝ)] ![(14054355364983/20000000000000 : ℝ), (1637580828239/10000000000000 : ℝ), (6676207436167/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1864344903/2500000000 : ℝ)|^95 ≤ (14054355364983/20000000000000 : ℝ)^79
        have hw : |(1864344903/2500000000 : ℝ)|=(1864344903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1110497411/5000000000 : ℝ)|^95 ≤ (1637580828239/10000000000000 : ℝ)^79
        have hw : |(1110497411/5000000000 : ℝ)|=(1110497411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(234284721/1250000000 : ℝ)|^95 ≤ (6676207436167/50000000000000 : ℝ)^79
        have hw : |(234284721/1250000000 : ℝ)|=(234284721/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c329055_s1 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((61467/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(61467/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1831/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1831/3125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(59459/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(59459/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2799/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2799/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14389/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14389/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27563/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(27563/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (10347/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (10347/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (10347/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (10347/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (10347/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (10347/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (61467/100000 : ℝ) ^ (93/16 : ℝ) ≤ (1181712203379280193/20000000000000000000 : ℝ) := by
    have hpowers : (61467/100000 : ℝ)^93 ≤ (1181712203379280193/20000000000000000000 : ℝ)^16 := by
      have hnat : (61467 : ℕ)^93*20000000000000000000^16 ≤ 1181712203379280193^16*100000^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61467 100000 1181712203379280193 20000000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (61467/100000 : ℝ)) (X := (1181712203379280193/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (21181712203379280193/20000000000000000000 : ℝ) ≤ (10099252159991001/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (21181712203379280193/20000000000000000000 : ℝ)^16 ≤ (10099252159991001/10000000000000000 : ℝ)^93 := by
      have hnat : (21181712203379280193 : ℕ)^16*10000000000000000^93 ≤ 10099252159991001^93*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21181712203379280193 20000000000000000000 10099252159991001 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10099252159991001/10000000000000000 : ℝ)) (X := (21181712203379280193/20000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (11181712203379280193/10000000000000000000 : ℝ) ≤ (10194020807696433/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (11181712203379280193/10000000000000000000 : ℝ)^16 ≤ (10194020807696433/10000000000000000 : ℝ)^93 := by
      have hnat : (11181712203379280193 : ℕ)^16*10000000000000000^93 ≤ 10194020807696433^93*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11181712203379280193 10000000000000000000 10194020807696433 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10194020807696433/10000000000000000 : ℝ)) (X := (11181712203379280193/10000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(99252159991001/6146700000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(3948693654393/256112500000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (61467/100000 : ℝ)) (alpha := (99252159991001/6146700000000000 : ℝ)) (beta := (3948693654393/256112500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (61467/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(99252159991001/6146700000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(3948693654393/256112500000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (1831/3125 : ℝ) ^ (93/16 : ℝ) ≤ (8735550712370769/195312500000000000 : ℝ) := by
    have hpowers : (1831/3125 : ℝ)^93 ≤ (8735550712370769/195312500000000000 : ℝ)^16 := by
      have hnat : (1831 : ℕ)^93*195312500000000000^16 ≤ 8735550712370769^16*3125^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1831 3125 8735550712370769 195312500000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1831/3125 : ℝ)) (X := (8735550712370769/195312500000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (204048050712370769/195312500000000000 : ℝ) ≤ (314861277880637/312500000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (204048050712370769/195312500000000000 : ℝ)^16 ≤ (314861277880637/312500000000000 : ℝ)^93 := by
      have hnat : (204048050712370769 : ℕ)^16*312500000000000^93 ≤ 314861277880637^93*195312500000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        204048050712370769 195312500000000000 314861277880637 312500000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (314861277880637/312500000000000 : ℝ)) (X := (204048050712370769/195312500000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (106391800712370769/97656250000000000 : ℝ) ≤ (10148489257174171/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (106391800712370769/97656250000000000 : ℝ)^16 ≤ (10148489257174171/10000000000000000 : ℝ)^93 := by
      have hnat : (106391800712370769 : ℕ)^16*10000000000000000^93 ≤ 10148489257174171^93*97656250000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        106391800712370769 97656250000000000 10148489257174171 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10148489257174171/10000000000000000 : ℝ)) (X := (106391800712370769/97656250000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(2361277880637/183100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(72928364993787/5859200000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1831/3125 : ℝ)) (alpha := (2361277880637/183100000000000 : ℝ)) (beta := (72928364993787/5859200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1831/3125 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(2361277880637/183100000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(72928364993787/5859200000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (59459/100000 : ℝ) ^ (93/16 : ℝ) ≤ (2435621556690451143/50000000000000000000 : ℝ) := by
    have hpowers : (59459/100000 : ℝ)^93 ≤ (2435621556690451143/50000000000000000000 : ℝ)^16 := by
      have hnat : (59459 : ℕ)^93*50000000000000000000^16 ≤ 2435621556690451143^16*100000^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59459 100000 2435621556690451143 50000000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (59459/100000 : ℝ)) (X := (2435621556690451143/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (52435621556690451143/50000000000000000000 : ℝ) ≤ (5041082400005887/5000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (52435621556690451143/50000000000000000000 : ℝ)^16 ≤ (5041082400005887/5000000000000000 : ℝ)^93 := by
      have hnat : (52435621556690451143 : ℕ)^16*5000000000000000^93 ≤ 5041082400005887^93*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52435621556690451143 50000000000000000000 5041082400005887 5000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5041082400005887/5000000000000000 : ℝ)) (X := (52435621556690451143/50000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (27435621556690451143/25000000000000000000 : ℝ) ≤ (1270153514647539/1250000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (27435621556690451143/25000000000000000000 : ℝ)^16 ≤ (1270153514647539/1250000000000000 : ℝ)^93 := by
      have hnat : (27435621556690451143 : ℕ)^16*1250000000000000^93 ≤ 1270153514647539^93*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27435621556690451143 25000000000000000000 1270153514647539 1250000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1270153514647539/1250000000000000 : ℝ)) (X := (27435621556690451143/25000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(41082400005887/2972950000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(39531658584269/2972950000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (59459/100000 : ℝ)) (alpha := (41082400005887/2972950000000000 : ℝ)) (beta := (39531658584269/2972950000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (59459/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(41082400005887/2972950000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(39531658584269/2972950000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-825358321/5000000000 : ℝ)*X 0 0+(2725731269/5000000000 : ℝ)*X 0 1+(2349619103/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329055_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1174829659/2500000000 : ℝ)*X 1 0+(-877656711/10000000000 : ℝ)*X 1 1+(3009536523/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329055_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((6299708317/10000000000 : ℝ)*X 0 0+(3688327847/10000000000 : ℝ)*X 0 1+(1773542119/10000000000 : ℝ)*X 0 2+(6299708317/10000000000 : ℝ)*X 1 0+(3688327847/10000000000 : ℝ)*X 1 1+(1773542119/10000000000 : ℝ)*X 1 2+(6299708317/10000000000 : ℝ)*X 2 0+(3688327847/10000000000 : ℝ)*X 2 1+(1773542119/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329055_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-718620141/5000000000 : ℝ)*X 0 0+(5050374063/10000000000 : ℝ)*X 0 1+(527292571/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329055_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((9404289/20000000 : ℝ)*X 1 0+(-240834787/5000000000 : ℝ)*X 1 1+(6269335213/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329055_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((2348097407/5000000000 : ℝ)*X 2 0+(5883041347/10000000000 : ℝ)*X 2 1+(-26952747/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329055_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((43346561/78125000 : ℝ)*X 0 0+(2561013011/5000000000 : ℝ)*X 0 1+(483635673/5000000000 : ℝ)*X 0 2+(43346561/78125000 : ℝ)*X 1 0+(2561013011/5000000000 : ℝ)*X 1 1+(483635673/5000000000 : ℝ)*X 1 2+(43346561/78125000 : ℝ)*X 2 0+(2561013011/5000000000 : ℝ)*X 2 1+(483635673/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329055_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-126892109/1250000000 : ℝ)*X 0 0+(1321347753/2500000000 : ℝ)*X 0 1+(5352628849/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329055_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((4481948871/10000000000 : ℝ)*X 1 0+(-40525769/500000000 : ℝ)*X 1 1+(97951503/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329055_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((10692421/20000000 : ℝ)*X 2 0+(662972151/1250000000 : ℝ)*X 2 1+(-998405357/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329055_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((7093048603/10000000000 : ℝ)*X 0 0+(3448659163/10000000000 : ℝ)*X 0 1+(968789539/10000000000 : ℝ)*X 0 2+(7093048603/10000000000 : ℝ)*X 1 0+(3448659163/10000000000 : ℝ)*X 1 1+(968789539/10000000000 : ℝ)*X 1 2+(7093048603/10000000000 : ℝ)*X 2 0+(3448659163/10000000000 : ℝ)*X 2 1+(968789539/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329055_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-4403191/39062500 : ℝ)*X 0 0+(1178390927/2000000000 : ℝ)*X 0 1+(2325100541/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329055_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((1310020819/2500000000 : ℝ)*X 1 0+(-227186903/5000000000 : ℝ)*X 1 1+(576812177/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329055_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((4370307341/10000000000 : ℝ)*X 2 0+(5910338381/10000000000 : ℝ)*X 2 1+(-1462739291/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329055_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((1864344903/2500000000 : ℝ)*X 0 0+(1110497411/5000000000 : ℝ)*X 0 1+(234284721/1250000000 : ℝ)*X 0 2+(1864344903/2500000000 : ℝ)*X 1 0+(1110497411/5000000000 : ℝ)*X 1 1+(234284721/1250000000 : ℝ)*X 1 2+(1864344903/2500000000 : ℝ)*X 2 0+(1110497411/5000000000 : ℝ)*X 2 1+(234284721/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329055_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((2799/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2799/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1288248905306123238879/183100000000000000000000000 : ℝ) := by norm_num
    linear_combination (200588199357/200000000000 : ℝ)*(base49) + (495107047631/62500000000 : ℝ)*(major_s1_0) + (495107047631/62500000000 : ℝ)*(major_s1_1) + (495107047631/62500000000 : ℝ)*(major_s1_2) + (107910993/1000000000000 : ℝ)*(sp_s1_0) + (48997/40000000000 : ℝ)*(sp_s1_1) + (5585723/200000000000 : ℝ)*(sp_s1_6) + (3070172002383/250000000000 : ℝ)*(sp_s1_7) + (6140336783207/500000000000 : ℝ)*(sp_s1_8) + (6140325721587/500000000000 : ℝ)*(sp_s1_9) + (3562598113451/1000000000000 : ℝ)*(sp_s1_13) + (12234553/100000000000 : ℝ)*(sp_s1_15) + (152043/125000000000 : ℝ)*(sp_s1_21) + (29138739/200000000000 : ℝ)*(sp_s1_23) + (1781313021033/500000000000 : ℝ)*(f.failure) + (12280797136869/1000000000000 : ℝ)*(f.sum) + (610560565840472609/5443471450000000000000000000000 : ℝ)*base62 + (184607395248809/2972950000000000000000000000 : ℝ)*base65 + (73056911525137/366200000000000000000000000 : ℝ)*base66 + (182041780301717/2972950000000000000000000000 : ℝ)*base69 + (22439152254320567/261054739500000000000000000000 : ℝ)*base70 + (20589967318311/146350000000000000000000000 : ℝ)*base73 + (2547232328753/45775000000000000000000000 : ℝ)*base75 + (1732696538429/27440625000000000000000000 : ℝ)*base77 + (14445264157420699/42874696000000000000000000000 : ℝ)*base78 + (3437/12500000000000000 : ℝ)*base87 + (3437/12500000000000000 : ℝ)*base89 + (3437/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14389/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14389/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (426565164935624148296103757219/28552009353996800000000000000000000 : ℝ) := by norm_num
    linear_combination (3082963/1000000000000 : ℝ)*(base39) + (846372612591/1000000000000 : ℝ)*(base49) + (1415077/500000000000 : ℝ)*(base60) + (7412547484997/1000000000000 : ℝ)*(major_s1_0) + (7412547484997/1000000000000 : ℝ)*(major_s1_1) + (7412547484997/1000000000000 : ℝ)*(major_s1_2) + (18017997/500000000000 : ℝ)*(sp_s1_1) + (4310363/100000000000 : ℝ)*(sp_s1_7) + (67958893/500000000000 : ℝ)*(sp_s1_8) + (71821296057/6250000000 : ℝ)*(sp_s1_14) + (11491278518969/1000000000000 : ℝ)*(sp_s1_15) + (45965801891/4000000000 : ℝ)*(sp_s1_16) + (41669640157/12500000000 : ℝ)*(sp_s1_20) + (68304699/1000000000000 : ℝ)*(sp_s1_27) + (3333639517259/1000000000000 : ℝ)*(f.failure) + (45965801891/4000000000 : ℝ)*(f.sum) + (3071590798043716451/10886942900000000000000000000000 : ℝ)*base62 + (1645645114349733/2972950000000000000000000000 : ℝ)*base65 + (3529842802962521/5859200000000000000000000000 : ℝ)*base67 + (350467458931647/1486475000000000000000000000 : ℝ)*base69 + (29050302012620532337/73095327060000000000000000000000 : ℝ)*base71 + (149255708762347/512225000000000000000000000 : ℝ)*base73 + (37888914984009/183100000000000000000000000 : ℝ)*base75 + (531585642335137/6146700000000000000000000000 : ℝ)*base77 + (519971675315544777/4801965952000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (14449/25000000000000000 : ℝ)*base86 + (14449/25000000000000000 : ℝ)*base88 + (14449/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27563/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(27563/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5351497388667953375230676047717/1784500584624800000000000000000000000 : ℝ) := by norm_num
    linear_combination (1114491/1000000000000 : ℝ)*(base15) + (243233/250000000000 : ℝ)*(base40) + (543039139363/500000000000 : ℝ)*(base49) + (410543/200000000000 : ℝ)*(base59) + (3733680569071/500000000000 : ℝ)*(major_s1_0) + (3733680569071/500000000000 : ℝ)*(major_s1_1) + (3733680569071/500000000000 : ℝ)*(major_s1_2) + (663609/500000000000 : ℝ)*(sp_s1_1) + (29866573/1000000000000 : ℝ)*(sp_s1_9) + (1319399/62500000000 : ℝ)*(sp_s1_20) + (11576430455559/1000000000000 : ℝ)*(sp_s1_21) + (11576428013849/1000000000000 : ℝ)*(sp_s1_22) + (5788200294493/500000000000 : ℝ)*(sp_s1_23) + (1679134855353/500000000000 : ℝ)*(sp_s1_27) + (3358290821089/1000000000000 : ℝ)*(f.failure) + (11576430455559/1000000000000 : ℝ)*(f.sum) + (1773130138591543233/5443471450000000000000000000000 : ℝ)*base62 + (289181311282943/2972950000000000000000000000 : ℝ)*base65 + (505063681073003/2929600000000000000000000000 : ℝ)*base67 + (473145762684567/1486475000000000000000000000 : ℝ)*base69 + (1432326692871449503/7309532706000000000000000000000 : ℝ)*base71 + (107805517726517/512225000000000000000000000 : ℝ)*base73 + (28578468301933/91550000000000000000000000 : ℝ)*base74 + (8135198603009/768337500000000000000000000 : ℝ)*base77 + (527825802816492967/12004914880000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (33579/25000000000000000 : ℝ)*base86 + (33579/25000000000000000 : ℝ)*base88 + (33579/25000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((61467/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(61467/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1831/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1831/3125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(59459/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(59459/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2799/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2799/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14389/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14389/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27563/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(27563/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c329055_s1 p hpa hpb X hX hprev0

#print axioms solution
