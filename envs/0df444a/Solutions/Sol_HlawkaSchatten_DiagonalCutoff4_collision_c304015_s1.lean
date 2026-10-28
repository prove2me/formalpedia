-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304015_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:36:47.029591+00:00
-- url     : https://prove2.me/submissions/33104d24-a175-48d7-8809-527bcec17a8e

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
theorem collision_support_c304015_s1_s1_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-610007797/2000000000 : ℝ)*x 0 + (-5998702093/10000000000 : ℝ)*x 1 + (1866973433/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (610007797/2000000000 : ℝ)^17 ≤ (21165577662407/100000000000000 : ℝ)^13 := by
    have hnat : (610007797 : ℕ)^17*100000000000000^13 ≤ 21165577662407^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      610007797 2000000000 21165577662407 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5998702093/10000000000 : ℝ)^17 ≤ (25629328977311/50000000000000 : ℝ)^13 := by
    have hnat : (5998702093 : ℕ)^17*50000000000000^13 ≤ 25629328977311^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5998702093 10000000000 25629328977311 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1866973433/5000000000 : ℝ)^17 ≤ (5515152873327/20000000000000 : ℝ)^13 := by
    have hnat : (1866973433 : ℕ)^17*20000000000000^13 ≤ 5515152873327^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1866973433 5000000000 5515152873327 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-610007797/2000000000 : ℝ), (-5998702093/10000000000 : ℝ), (1866973433/5000000000 : ℝ)] ![(21165577662407/100000000000000 : ℝ), (25629328977311/50000000000000 : ℝ), (5515152873327/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-610007797/2000000000 : ℝ)|^17 ≤ (21165577662407/100000000000000 : ℝ)^13
        have hw : |(-610007797/2000000000 : ℝ)|=(610007797/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5998702093/10000000000 : ℝ)|^17 ≤ (25629328977311/50000000000000 : ℝ)^13
        have hw : |(-5998702093/10000000000 : ℝ)|=(5998702093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1866973433/5000000000 : ℝ)|^17 ≤ (5515152873327/20000000000000 : ℝ)^13
        have hw : |(1866973433/5000000000 : ℝ)|=(1866973433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304015_s1_s1_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6023239107/10000000000 : ℝ)*x 0 + (3289975209/10000000000 : ℝ)*x 1 + (3474584893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6023239107/10000000000 : ℝ)^17 ≤ (25766505621683/50000000000000 : ℝ)^13 := by
    have hnat : (6023239107 : ℕ)^17*50000000000000^13 ≤ 25766505621683^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6023239107 10000000000 25766505621683 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3289975209/10000000000 : ℝ)^17 ≤ (23368805297041/100000000000000 : ℝ)^13 := by
    have hnat : (3289975209 : ℕ)^17*100000000000000^13 ≤ 23368805297041^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3289975209 10000000000 23368805297041 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3474584893/10000000000 : ℝ)^17 ≤ (25098183443313/100000000000000 : ℝ)^13 := by
    have hnat : (3474584893 : ℕ)^17*100000000000000^13 ≤ 25098183443313^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3474584893 10000000000 25098183443313 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6023239107/10000000000 : ℝ), (3289975209/10000000000 : ℝ), (3474584893/10000000000 : ℝ)] ![(25766505621683/50000000000000 : ℝ), (23368805297041/100000000000000 : ℝ), (25098183443313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6023239107/10000000000 : ℝ)|^17 ≤ (25766505621683/50000000000000 : ℝ)^13
        have hw : |(6023239107/10000000000 : ℝ)|=(6023239107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3289975209/10000000000 : ℝ)|^17 ≤ (23368805297041/100000000000000 : ℝ)^13
        have hw : |(3289975209/10000000000 : ℝ)|=(3289975209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3474584893/10000000000 : ℝ)|^17 ≤ (25098183443313/100000000000000 : ℝ)^13
        have hw : |(3474584893/10000000000 : ℝ)|=(3474584893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304015_s1_s1_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1757126561/5000000000 : ℝ)*x 0 + (-4446520817/10000000000 : ℝ)*x 1 + (-495056997/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1757126561/5000000000 : ℝ)^17 ≤ (25473543345761/100000000000000 : ℝ)^13 := by
    have hnat : (1757126561 : ℕ)^17*100000000000000^13 ≤ 25473543345761^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1757126561 5000000000 25473543345761 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4446520817/10000000000 : ℝ)^17 ≤ (34651248966533/100000000000000 : ℝ)^13 := by
    have hnat : (4446520817 : ℕ)^17*100000000000000^13 ≤ 34651248966533^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4446520817 10000000000 34651248966533 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (495056997/1000000000 : ℝ)^17 ≤ (7975041534209/20000000000000 : ℝ)^13 := by
    have hnat : (495056997 : ℕ)^17*20000000000000^13 ≤ 7975041534209^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      495056997 1000000000 7975041534209 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1757126561/5000000000 : ℝ), (-4446520817/10000000000 : ℝ), (-495056997/1000000000 : ℝ)] ![(25473543345761/100000000000000 : ℝ), (34651248966533/100000000000000 : ℝ), (7975041534209/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1757126561/5000000000 : ℝ)|^17 ≤ (25473543345761/100000000000000 : ℝ)^13
        have hw : |(1757126561/5000000000 : ℝ)|=(1757126561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4446520817/10000000000 : ℝ)|^17 ≤ (34651248966533/100000000000000 : ℝ)^13
        have hw : |(-4446520817/10000000000 : ℝ)|=(4446520817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-495056997/1000000000 : ℝ)|^17 ≤ (7975041534209/20000000000000 : ℝ)^13
        have hw : |(-495056997/1000000000 : ℝ)|=(495056997/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304015_s1_s1_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1344750631/5000000000 : ℝ)*x 0 + (-6787806073/10000000000 : ℝ)*x 1 + (1559602383/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344750631/5000000000 : ℝ)^17 ≤ (448875752747/2500000000000 : ℝ)^13 := by
    have hnat : (1344750631 : ℕ)^17*2500000000000^13 ≤ 448875752747^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344750631 5000000000 448875752747 2500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6787806073/10000000000 : ℝ)^17 ≤ (60249557951727/100000000000000 : ℝ)^13 := by
    have hnat : (6787806073 : ℕ)^17*100000000000000^13 ≤ 60249557951727^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6787806073 10000000000 60249557951727 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1559602383/5000000000 : ℝ)^17 ≤ (10897705961233/50000000000000 : ℝ)^13 := by
    have hnat : (1559602383 : ℕ)^17*50000000000000^13 ≤ 10897705961233^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1559602383 5000000000 10897705961233 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1344750631/5000000000 : ℝ), (-6787806073/10000000000 : ℝ), (1559602383/5000000000 : ℝ)] ![(448875752747/2500000000000 : ℝ), (60249557951727/100000000000000 : ℝ), (10897705961233/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1344750631/5000000000 : ℝ)|^17 ≤ (448875752747/2500000000000 : ℝ)^13
        have hw : |(-1344750631/5000000000 : ℝ)|=(1344750631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6787806073/10000000000 : ℝ)|^17 ≤ (60249557951727/100000000000000 : ℝ)^13
        have hw : |(-6787806073/10000000000 : ℝ)|=(6787806073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1559602383/5000000000 : ℝ)|^17 ≤ (10897705961233/50000000000000 : ℝ)^13
        have hw : |(1559602383/5000000000 : ℝ)|=(1559602383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304015_s1_s1_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6215319991/10000000000 : ℝ)*x 0 + (640809041/2000000000 : ℝ)*x 1 + (3329178551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6215319991/10000000000 : ℝ)^17 ≤ (53692521334181/100000000000000 : ℝ)^13 := by
    have hnat : (6215319991 : ℕ)^17*100000000000000^13 ≤ 53692521334181^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6215319991 10000000000 53692521334181 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (640809041/2000000000 : ℝ)^17 ≤ (1128693207293/5000000000000 : ℝ)^13 := by
    have hnat : (640809041 : ℕ)^17*5000000000000^13 ≤ 1128693207293^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      640809041 2000000000 1128693207293 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3329178551/10000000000 : ℝ)^17 ≤ (23733614515229/100000000000000 : ℝ)^13 := by
    have hnat : (3329178551 : ℕ)^17*100000000000000^13 ≤ 23733614515229^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3329178551 10000000000 23733614515229 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6215319991/10000000000 : ℝ), (640809041/2000000000 : ℝ), (3329178551/10000000000 : ℝ)] ![(53692521334181/100000000000000 : ℝ), (1128693207293/5000000000000 : ℝ), (23733614515229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6215319991/10000000000 : ℝ)|^17 ≤ (53692521334181/100000000000000 : ℝ)^13
        have hw : |(6215319991/10000000000 : ℝ)|=(6215319991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(640809041/2000000000 : ℝ)|^17 ≤ (1128693207293/5000000000000 : ℝ)^13
        have hw : |(640809041/2000000000 : ℝ)|=(640809041/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3329178551/10000000000 : ℝ)|^17 ≤ (23733614515229/100000000000000 : ℝ)^13
        have hw : |(3329178551/10000000000 : ℝ)|=(3329178551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304015_s1_s1_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3532258911/10000000000 : ℝ)*x 0 + (-4363249591/10000000000 : ℝ)*x 1 + (-1253639539/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3532258911/10000000000 : ℝ)^17 ≤ (5128870869609/20000000000000 : ℝ)^13 := by
    have hnat : (3532258911 : ℕ)^17*20000000000000^13 ≤ 5128870869609^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3532258911 10000000000 5128870869609 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4363249591/10000000000 : ℝ)^17 ≤ (16902556102407/50000000000000 : ℝ)^13 := by
    have hnat : (4363249591 : ℕ)^17*50000000000000^13 ≤ 16902556102407^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363249591 10000000000 16902556102407 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1253639539/2500000000 : ℝ)^17 ≤ (40550533427619/100000000000000 : ℝ)^13 := by
    have hnat : (1253639539 : ℕ)^17*100000000000000^13 ≤ 40550533427619^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1253639539 2500000000 40550533427619 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3532258911/10000000000 : ℝ), (-4363249591/10000000000 : ℝ), (-1253639539/2500000000 : ℝ)] ![(5128870869609/20000000000000 : ℝ), (16902556102407/50000000000000 : ℝ), (40550533427619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3532258911/10000000000 : ℝ)|^17 ≤ (5128870869609/20000000000000 : ℝ)^13
        have hw : |(3532258911/10000000000 : ℝ)|=(3532258911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4363249591/10000000000 : ℝ)|^17 ≤ (16902556102407/50000000000000 : ℝ)^13
        have hw : |(-4363249591/10000000000 : ℝ)|=(4363249591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1253639539/2500000000 : ℝ)|^17 ≤ (40550533427619/100000000000000 : ℝ)^13
        have hw : |(-1253639539/2500000000 : ℝ)|=(1253639539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304015_s1_s1_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (196543231/1000000000 : ℝ)*x 0 + (-153469/1000000000 : ℝ)*x 1 + (17725391/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (196543231/1000000000 : ℝ)^17 ≤ (5957040944379/50000000000000 : ℝ)^13 := by
    have hnat : (196543231 : ℕ)^17*50000000000000^13 ≤ 5957040944379^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196543231 1000000000 5957040944379 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (153469/1000000000 : ℝ)^17 ≤ (1029173417/100000000000000 : ℝ)^13 := by
    have hnat : (153469 : ℕ)^17*100000000000000^13 ≤ 1029173417^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153469 1000000000 1029173417 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17725391/19531250 : ℝ)^17 ≤ (22021222232947/25000000000000 : ℝ)^13 := by
    have hnat : (17725391 : ℕ)^17*25000000000000^13 ≤ 22021222232947^13*19531250^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17725391 19531250 22021222232947 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(196543231/1000000000 : ℝ), (-153469/1000000000 : ℝ), (17725391/19531250 : ℝ)] ![(5957040944379/50000000000000 : ℝ), (1029173417/100000000000000 : ℝ), (22021222232947/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(196543231/1000000000 : ℝ)|^17 ≤ (5957040944379/50000000000000 : ℝ)^13
        have hw : |(196543231/1000000000 : ℝ)|=(196543231/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-153469/1000000000 : ℝ)|^17 ≤ (1029173417/100000000000000 : ℝ)^13
        have hw : |(-153469/1000000000 : ℝ)|=(153469/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(17725391/19531250 : ℝ)|^17 ≤ (22021222232947/25000000000000 : ℝ)^13
        have hw : |(17725391/19531250 : ℝ)|=(17725391/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304015_s1_s1_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-152288947/500000000 : ℝ)*x 0 + (-392358789/625000000 : ℝ)*x 1 + (53255359/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (152288947/500000000 : ℝ)^17 ≤ (21126927517183/100000000000000 : ℝ)^13 := by
    have hnat : (152288947 : ℕ)^17*100000000000000^13 ≤ 21126927517183^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      152288947 500000000 21126927517183 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (392358789/625000000 : ℝ)^17 ≤ (3399922653287/6250000000000 : ℝ)^13 := by
    have hnat : (392358789 : ℕ)^17*6250000000000^13 ≤ 3399922653287^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      392358789 625000000 3399922653287 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53255359/156250000 : ℝ)^17 ≤ (24474310018713/100000000000000 : ℝ)^13 := by
    have hnat : (53255359 : ℕ)^17*100000000000000^13 ≤ 24474310018713^13*156250000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53255359 156250000 24474310018713 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-152288947/500000000 : ℝ), (-392358789/625000000 : ℝ), (53255359/156250000 : ℝ)] ![(21126927517183/100000000000000 : ℝ), (3399922653287/6250000000000 : ℝ), (24474310018713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-152288947/500000000 : ℝ)|^17 ≤ (21126927517183/100000000000000 : ℝ)^13
        have hw : |(-152288947/500000000 : ℝ)|=(152288947/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-392358789/625000000 : ℝ)|^17 ≤ (3399922653287/6250000000000 : ℝ)^13
        have hw : |(-392358789/625000000 : ℝ)|=(392358789/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(53255359/156250000 : ℝ)|^17 ≤ (24474310018713/100000000000000 : ℝ)^13
        have hw : |(53255359/156250000 : ℝ)|=(53255359/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304015_s1_s1_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6967281083/10000000000 : ℝ)*x 0 + (2778149557/10000000000 : ℝ)*x 1 + (87500821/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6967281083/10000000000 : ℝ)^17 ≤ (389632471671/625000000000 : ℝ)^13 := by
    have hnat : (6967281083 : ℕ)^17*625000000000^13 ≤ 389632471671^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6967281083 10000000000 389632471671 625000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2778149557/10000000000 : ℝ)^17 ≤ (4683208720343/25000000000000 : ℝ)^13 := by
    have hnat : (2778149557 : ℕ)^17*25000000000000^13 ≤ 4683208720343^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2778149557 10000000000 4683208720343 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (87500821/312500000 : ℝ)^17 ≤ (9462984816797/50000000000000 : ℝ)^13 := by
    have hnat : (87500821 : ℕ)^17*50000000000000^13 ≤ 9462984816797^13*312500000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87500821 312500000 9462984816797 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6967281083/10000000000 : ℝ), (2778149557/10000000000 : ℝ), (87500821/312500000 : ℝ)] ![(389632471671/625000000000 : ℝ), (4683208720343/25000000000000 : ℝ), (9462984816797/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6967281083/10000000000 : ℝ)|^17 ≤ (389632471671/625000000000 : ℝ)^13
        have hw : |(6967281083/10000000000 : ℝ)|=(6967281083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2778149557/10000000000 : ℝ)|^17 ≤ (4683208720343/25000000000000 : ℝ)^13
        have hw : |(2778149557/10000000000 : ℝ)|=(2778149557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(87500821/312500000 : ℝ)|^17 ≤ (9462984816797/50000000000000 : ℝ)^13
        have hw : |(87500821/312500000 : ℝ)|=(87500821/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304015_s1_s1_16 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3560203199/10000000000 : ℝ)*x 0 + (-115430921/250000000 : ℝ)*x 1 + (-4741630309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3560203199/10000000000 : ℝ)^17 ≤ (25909977029367/100000000000000 : ℝ)^13 := by
    have hnat : (3560203199 : ℕ)^17*100000000000000^13 ≤ 25909977029367^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3560203199 10000000000 25909977029367 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (115430921/250000000 : ℝ)^17 ≤ (36401151489079/100000000000000 : ℝ)^13 := by
    have hnat : (115430921 : ℕ)^17*100000000000000^13 ≤ 36401151489079^13*250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      115430921 250000000 36401151489079 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4741630309/10000000000 : ℝ)^17 ≤ (301510971787/800000000000 : ℝ)^13 := by
    have hnat : (4741630309 : ℕ)^17*800000000000^13 ≤ 301510971787^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4741630309 10000000000 301510971787 800000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3560203199/10000000000 : ℝ), (-115430921/250000000 : ℝ), (-4741630309/10000000000 : ℝ)] ![(25909977029367/100000000000000 : ℝ), (36401151489079/100000000000000 : ℝ), (301510971787/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3560203199/10000000000 : ℝ)|^17 ≤ (25909977029367/100000000000000 : ℝ)^13
        have hw : |(3560203199/10000000000 : ℝ)|=(3560203199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-115430921/250000000 : ℝ)|^17 ≤ (36401151489079/100000000000000 : ℝ)^13
        have hw : |(-115430921/250000000 : ℝ)|=(115430921/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4741630309/10000000000 : ℝ)|^17 ≤ (301510971787/800000000000 : ℝ)^13
        have hw : |(-4741630309/10000000000 : ℝ)|=(4741630309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304015_s1_s1_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (377152123/2000000000 : ℝ)*x 0 + (-2201163/2000000000 : ℝ)*x 1 + (9123821097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (377152123/2000000000 : ℝ)^17 ≤ (1410812705147/12500000000000 : ℝ)^13 := by
    have hnat : (377152123 : ℕ)^17*12500000000000^13 ≤ 1410812705147^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      377152123 2000000000 1410812705147 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2201163/2000000000 : ℝ)^17 ≤ (13531692453/100000000000000 : ℝ)^13 := by
    have hnat : (2201163 : ℕ)^17*100000000000000^13 ≤ 13531692453^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2201163 2000000000 13531692453 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9123821097/10000000000 : ℝ)^17 ≤ (11087495831513/12500000000000 : ℝ)^13 := by
    have hnat : (9123821097 : ℕ)^17*12500000000000^13 ≤ 11087495831513^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9123821097 10000000000 11087495831513 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(377152123/2000000000 : ℝ), (-2201163/2000000000 : ℝ), (9123821097/10000000000 : ℝ)] ![(1410812705147/12500000000000 : ℝ), (13531692453/100000000000000 : ℝ), (11087495831513/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(377152123/2000000000 : ℝ)|^17 ≤ (1410812705147/12500000000000 : ℝ)^13
        have hw : |(377152123/2000000000 : ℝ)|=(377152123/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2201163/2000000000 : ℝ)|^17 ≤ (13531692453/100000000000000 : ℝ)^13
        have hw : |(-2201163/2000000000 : ℝ)|=(2201163/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9123821097/10000000000 : ℝ)|^17 ≤ (11087495831513/12500000000000 : ℝ)^13
        have hw : |(9123821097/10000000000 : ℝ)|=(9123821097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304015_s1_s1_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2575312717/10000000000 : ℝ)*x 0 + (-1696924501/2500000000 : ℝ)*x 1 + (322714987/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2575312717/10000000000 : ℝ)^17 ≤ (424118186451/2500000000000 : ℝ)^13 := by
    have hnat : (2575312717 : ℕ)^17*2500000000000^13 ≤ 424118186451^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2575312717 10000000000 424118186451 2500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1696924501/2500000000 : ℝ)^17 ≤ (30124151784483/50000000000000 : ℝ)^13 := by
    have hnat : (1696924501 : ℕ)^17*50000000000000^13 ≤ 30124151784483^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1696924501 2500000000 30124151784483 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (322714987/1000000000 : ℝ)^17 ≤ (11393484479213/50000000000000 : ℝ)^13 := by
    have hnat : (322714987 : ℕ)^17*50000000000000^13 ≤ 11393484479213^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      322714987 1000000000 11393484479213 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2575312717/10000000000 : ℝ), (-1696924501/2500000000 : ℝ), (322714987/1000000000 : ℝ)] ![(424118186451/2500000000000 : ℝ), (30124151784483/50000000000000 : ℝ), (11393484479213/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2575312717/10000000000 : ℝ)|^17 ≤ (424118186451/2500000000000 : ℝ)^13
        have hw : |(-2575312717/10000000000 : ℝ)|=(2575312717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1696924501/2500000000 : ℝ)|^17 ≤ (30124151784483/50000000000000 : ℝ)^13
        have hw : |(-1696924501/2500000000 : ℝ)|=(1696924501/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(322714987/1000000000 : ℝ)|^17 ≤ (11393484479213/50000000000000 : ℝ)^13
        have hw : |(322714987/1000000000 : ℝ)|=(322714987/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304015_s1_s1_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3310023967/5000000000 : ℝ)*x 0 + (726046001/2500000000 : ℝ)*x 1 + (780976201/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3310023967/5000000000 : ℝ)^17 ≤ (58309790761413/100000000000000 : ℝ)^13 := by
    have hnat : (3310023967 : ℕ)^17*100000000000000^13 ≤ 58309790761413^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3310023967 5000000000 58309790761413 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (726046001/2500000000 : ℝ)^17 ≤ (9925920408429/50000000000000 : ℝ)^13 := by
    have hnat : (726046001 : ℕ)^17*50000000000000^13 ≤ 9925920408429^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      726046001 2500000000 9925920408429 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (780976201/2500000000 : ℝ)^17 ≤ (2183836841011/10000000000000 : ℝ)^13 := by
    have hnat : (780976201 : ℕ)^17*10000000000000^13 ≤ 2183836841011^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      780976201 2500000000 2183836841011 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3310023967/5000000000 : ℝ), (726046001/2500000000 : ℝ), (780976201/2500000000 : ℝ)] ![(58309790761413/100000000000000 : ℝ), (9925920408429/50000000000000 : ℝ), (2183836841011/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3310023967/5000000000 : ℝ)|^17 ≤ (58309790761413/100000000000000 : ℝ)^13
        have hw : |(3310023967/5000000000 : ℝ)|=(3310023967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(726046001/2500000000 : ℝ)|^17 ≤ (9925920408429/50000000000000 : ℝ)^13
        have hw : |(726046001/2500000000 : ℝ)|=(726046001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(780976201/2500000000 : ℝ)|^17 ≤ (2183836841011/10000000000000 : ℝ)^13
        have hw : |(780976201/2500000000 : ℝ)|=(780976201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304015_s1_s1_23 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3137942413/10000000000 : ℝ)*x 0 + (-4219666109/10000000000 : ℝ)*x 1 + (-5492337037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3137942413/10000000000 : ℝ)^17 ≤ (21966784940557/100000000000000 : ℝ)^13 := by
    have hnat : (3137942413 : ℕ)^17*100000000000000^13 ≤ 21966784940557^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3137942413 10000000000 21966784940557 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4219666109/10000000000 : ℝ)^17 ≤ (32357803835037/100000000000000 : ℝ)^13 := by
    have hnat : (4219666109 : ℕ)^17*100000000000000^13 ≤ 32357803835037^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4219666109 10000000000 32357803835037 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5492337037/10000000000 : ℝ)^17 ≤ (5709426401343/12500000000000 : ℝ)^13 := by
    have hnat : (5492337037 : ℕ)^17*12500000000000^13 ≤ 5709426401343^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5492337037 10000000000 5709426401343 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3137942413/10000000000 : ℝ), (-4219666109/10000000000 : ℝ), (-5492337037/10000000000 : ℝ)] ![(21966784940557/100000000000000 : ℝ), (32357803835037/100000000000000 : ℝ), (5709426401343/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3137942413/10000000000 : ℝ)|^17 ≤ (21966784940557/100000000000000 : ℝ)^13
        have hw : |(3137942413/10000000000 : ℝ)|=(3137942413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4219666109/10000000000 : ℝ)|^17 ≤ (32357803835037/100000000000000 : ℝ)^13
        have hw : |(-4219666109/10000000000 : ℝ)|=(4219666109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5492337037/10000000000 : ℝ)|^17 ≤ (5709426401343/12500000000000 : ℝ)^13
        have hw : |(-5492337037/10000000000 : ℝ)|=(5492337037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304015_s1_s1_27 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (125486597/625000000 : ℝ)*x 0 + (-4075023/10000000000 : ℝ)*x 1 + (45243197/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (125486597/625000000 : ℝ)^17 ≤ (12250922972759/100000000000000 : ℝ)^13 := by
    have hnat : (125486597 : ℕ)^17*100000000000000^13 ≤ 12250922972759^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125486597 625000000 12250922972759 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4075023/10000000000 : ℝ)^17 ≤ (3690567569/100000000000000 : ℝ)^13 := by
    have hnat : (4075023 : ℕ)^17*100000000000000^13 ≤ 3690567569^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4075023 10000000000 3690567569 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (45243197/50000000 : ℝ)^17 ≤ (685510831591/781250000000 : ℝ)^13 := by
    have hnat : (45243197 : ℕ)^17*781250000000^13 ≤ 685510831591^13*50000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45243197 50000000 685510831591 781250000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(125486597/625000000 : ℝ), (-4075023/10000000000 : ℝ), (45243197/50000000 : ℝ)] ![(12250922972759/100000000000000 : ℝ), (3690567569/100000000000000 : ℝ), (685510831591/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(125486597/625000000 : ℝ)|^17 ≤ (12250922972759/100000000000000 : ℝ)^13
        have hw : |(125486597/625000000 : ℝ)|=(125486597/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4075023/10000000000 : ℝ)|^17 ≤ (3690567569/100000000000000 : ℝ)^13
        have hw : |(-4075023/10000000000 : ℝ)|=(4075023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(45243197/50000000 : ℝ)|^17 ≤ (685510831591/781250000000 : ℝ)^13
        have hw : |(45243197/50000000 : ℝ)|=(45243197/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304015_s1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((85129/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(85129/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-16137/20000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(-16137/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(82389/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(82389/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((49243/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(49243/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-37161/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(-37161/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4733/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(4733/12500 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76617/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76617/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (85129/100000 : ℝ) ^ (33/8 : ℝ) ≤ (25735927418744161303/50000000000000000000 : ℝ) := by
    have hpowers : (85129/100000 : ℝ)^33 ≤ (25735927418744161303/50000000000000000000 : ℝ)^8 := by
      have hnat : (85129 : ℕ)^33*50000000000000000000^8 ≤ 25735927418744161303^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        85129 100000 25735927418744161303 50000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (85129/100000 : ℝ)) (X := (25735927418744161303/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (75735927418744161303/50000000000000000000 : ℝ) ≤ (5529512436051663/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (75735927418744161303/50000000000000000000 : ℝ)^8 ≤ (5529512436051663/5000000000000000 : ℝ)^33 := by
      have hnat : (75735927418744161303 : ℕ)^8*5000000000000000^33 ≤ 5529512436051663^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        75735927418744161303 50000000000000000000 5529512436051663 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5529512436051663/5000000000000000 : ℝ)) (X := (75735927418744161303/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (50735927418744161303/25000000000000000000 : ℝ) ≤ (1483970640279259/1250000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (50735927418744161303/25000000000000000000 : ℝ)^8 ≤ (1483970640279259/1250000000000000 : ℝ)^33 := by
      have hnat : (50735927418744161303 : ℕ)^8*1250000000000000^33 ≤ 1483970640279259^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50735927418744161303 25000000000000000000 1483970640279259 1250000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1483970640279259/1250000000000000 : ℝ)) (X := (50735927418744161303/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(529512436051663/4256450000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(406370125065373/4256450000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (85129/100000 : ℝ)) (alpha := (529512436051663/4256450000000000 : ℝ)) (beta := (406370125065373/4256450000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (85129/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(529512436051663/4256450000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(406370125065373/4256450000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (16137/20000 : ℝ) ^ (33/8 : ℝ) ≤ (41259153529520265473/100000000000000000000 : ℝ) := by
    have hpowers : (16137/20000 : ℝ)^33 ≤ (41259153529520265473/100000000000000000000 : ℝ)^8 := by
      have hnat : (16137 : ℕ)^33*100000000000000000000^8 ≤ 41259153529520265473^8*20000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16137 20000 41259153529520265473 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16137/20000 : ℝ)) (X := (41259153529520265473/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (141259153529520265473/100000000000000000000 : ℝ) ≤ (2174691495767693/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (141259153529520265473/100000000000000000000 : ℝ)^8 ≤ (2174691495767693/2000000000000000 : ℝ)^33 := by
      have hnat : (141259153529520265473 : ℕ)^8*2000000000000000^33 ≤ 2174691495767693^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        141259153529520265473 100000000000000000000 2174691495767693 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2174691495767693/2000000000000000 : ℝ)) (X := (141259153529520265473/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (91259153529520265473/50000000000000000000 : ℝ) ≤ (144629547284247/125000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (91259153529520265473/50000000000000000000 : ℝ)^8 ≤ (144629547284247/125000000000000 : ℝ)^33 := by
      have hnat : (91259153529520265473 : ℕ)^8*125000000000000^33 ≤ 144629547284247^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        91259153529520265473 50000000000000000000 144629547284247 125000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (144629547284247/125000000000000 : ℝ)) (X := (91259153529520265473/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(58230498589231/537900000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(139381260780259/1613700000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (16137/20000 : ℝ)) (alpha := (58230498589231/537900000000000 : ℝ)) (beta := (139381260780259/1613700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (16137/20000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(58230498589231/537900000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(139381260780259/1613700000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (82389/100000 : ℝ) ^ (33/8 : ℝ) ≤ (22486951581358286799/50000000000000000000 : ℝ) := by
    have hpowers : (82389/100000 : ℝ)^33 ≤ (22486951581358286799/50000000000000000000 : ℝ)^8 := by
      have hnat : (82389 : ℕ)^33*50000000000000000000^8 ≤ 22486951581358286799^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        82389 100000 22486951581358286799 50000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (82389/100000 : ℝ)) (X := (22486951581358286799/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (72486951581358286799/50000000000000000000 : ℝ) ≤ (683881070122163/625000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (72486951581358286799/50000000000000000000 : ℝ)^8 ≤ (683881070122163/625000000000000 : ℝ)^33 := by
      have hnat : (72486951581358286799 : ℕ)^8*625000000000000^33 ≤ 683881070122163^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        72486951581358286799 50000000000000000000 683881070122163 625000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (683881070122163/625000000000000 : ℝ)) (X := (72486951581358286799/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (47486951581358286799/25000000000000000000 : ℝ) ≤ (1460352565033987/1250000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (47486951581358286799/25000000000000000000 : ℝ)^8 ≤ (1460352565033987/1250000000000000 : ℝ)^33 := by
      have hnat : (47486951581358286799 : ℕ)^8*1250000000000000^33 ≤ 1460352565033987^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        47486951581358286799 25000000000000000000 1460352565033987 1250000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1460352565033987/1250000000000000 : ℝ)) (X := (47486951581358286799/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(58881070122163/514931250000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1064257756203/11837500000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (82389/100000 : ℝ)) (alpha := (58881070122163/514931250000000 : ℝ)) (beta := (1064257756203/11837500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (82389/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(58881070122163/514931250000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1064257756203/11837500000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-610007797/2000000000 : ℝ)*X 0 0+(-5998702093/10000000000 : ℝ)*X 0 1+(1866973433/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304015_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((6023239107/10000000000 : ℝ)*X 1 0+(3289975209/10000000000 : ℝ)*X 1 1+(3474584893/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304015_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1757126561/5000000000 : ℝ)*X 2 0+(-4446520817/10000000000 : ℝ)*X 2 1+(-495056997/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304015_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-1344750631/5000000000 : ℝ)*X 0 0+(-6787806073/10000000000 : ℝ)*X 0 1+(1559602383/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304015_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((6215319991/10000000000 : ℝ)*X 1 0+(640809041/2000000000 : ℝ)*X 1 1+(3329178551/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304015_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((3532258911/10000000000 : ℝ)*X 2 0+(-4363249591/10000000000 : ℝ)*X 2 1+(-1253639539/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304015_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((196543231/1000000000 : ℝ)*X 0 0+(-153469/1000000000 : ℝ)*X 0 1+(17725391/19531250 : ℝ)*X 0 2+(196543231/1000000000 : ℝ)*X 1 0+(-153469/1000000000 : ℝ)*X 1 1+(17725391/19531250 : ℝ)*X 1 2+(196543231/1000000000 : ℝ)*X 2 0+(-153469/1000000000 : ℝ)*X 2 1+(17725391/19531250 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304015_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-152288947/500000000 : ℝ)*X 0 0+(-392358789/625000000 : ℝ)*X 0 1+(53255359/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304015_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((6967281083/10000000000 : ℝ)*X 1 0+(2778149557/10000000000 : ℝ)*X 1 1+(87500821/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304015_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((3560203199/10000000000 : ℝ)*X 2 0+(-115430921/250000000 : ℝ)*X 2 1+(-4741630309/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304015_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((377152123/2000000000 : ℝ)*X 0 0+(-2201163/2000000000 : ℝ)*X 0 1+(9123821097/10000000000 : ℝ)*X 0 2+(377152123/2000000000 : ℝ)*X 1 0+(-2201163/2000000000 : ℝ)*X 1 1+(9123821097/10000000000 : ℝ)*X 1 2+(377152123/2000000000 : ℝ)*X 2 0+(-2201163/2000000000 : ℝ)*X 2 1+(9123821097/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304015_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-2575312717/10000000000 : ℝ)*X 0 0+(-1696924501/2500000000 : ℝ)*X 0 1+(322714987/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304015_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((3310023967/5000000000 : ℝ)*X 1 0+(726046001/2500000000 : ℝ)*X 1 1+(780976201/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304015_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((3137942413/10000000000 : ℝ)*X 2 0+(-4219666109/10000000000 : ℝ)*X 2 1+(-5492337037/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304015_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((125486597/625000000 : ℝ)*X 0 0+(-4075023/10000000000 : ℝ)*X 0 1+(45243197/50000000 : ℝ)*X 0 2+(125486597/625000000 : ℝ)*X 1 0+(-4075023/10000000000 : ℝ)*X 1 1+(45243197/50000000 : ℝ)*X 1 2+(125486597/625000000 : ℝ)*X 2 0+(-4075023/10000000000 : ℝ)*X 2 1+(45243197/50000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304015_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((49243/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(49243/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (15034820215951789451901/4256450000000000000000000000 : ℝ) := by norm_num
    linear_combination (2248745748573/1000000000000 : ℝ)*(base3) + (1777588713171/1000000000000 : ℝ)*(base40) + (2708372921269/1000000000000 : ℝ)*(base50) + (9559474804423/1000000000000 : ℝ)*(major_s1_0) + (9559474804423/1000000000000 : ℝ)*(major_s1_1) + (9559474804423/1000000000000 : ℝ)*(major_s1_2) + (46596041/1000000000000 : ℝ)*(sp_s1_1) + (644956943/1000000000000 : ℝ)*(sp_s1_2) + (3204054911337/250000000000 : ℝ)*(sp_s1_7) + (15064918797879/1000000000000 : ℝ)*(sp_s1_8) + (2563114937681/200000000000 : ℝ)*(sp_s1_9) + (810332230887/200000000000 : ℝ)*(sp_s1_13) + (149429097/500000000000 : ℝ)*(sp_s1_20) + (1011512439/500000000000 : ℝ)*(sp_s1_27) + (39392054913/6250000000 : ℝ)*(f.failure) + (3204054911337/250000000000 : ℝ)*(f.sum) + (907467863155804993/14772347700000000000000000000000 : ℝ)*base63 + (10143401693053/23675000000000000000000000 : ℝ)*base65 + (73808476859663/1613700000000000000000000000 : ℝ)*base66 + (59565008529337/1029862500000000000000000000 : ℝ)*base68 + (110687130405929043/4030858150000000000000000000000 : ℝ)*base70 + (1268819300310179/4256450000000000000000000000 : ℝ)*base73 + (189198981725143/537900000000000000000000000 : ℝ)*base74 + (1273434587585249/4256450000000000000000000000 : ℝ)*base77 + (6080018722239012569/12488424300000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (161/625000000000000 : ℝ)*base87 + (161/625000000000000 : ℝ)*base89 + (161/625000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-37161/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(-37161/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6934942131072039290003/1119117250000000000000000000 : ℝ) := by norm_num
    linear_combination (301403416643/500000000000 : ℝ)*(base3) + (2754633/1000000000000 : ℝ)*(base21) + (1030422584313/1000000000000 : ℝ)*(base40) + (702666611/1000000000 : ℝ)*(base50) + (1095471561891/200000000000 : ℝ)*(major_s1_0) + (1095471561891/200000000000 : ℝ)*(major_s1_1) + (1095471561891/200000000000 : ℝ)*(major_s1_2) + (23886551/500000000000 : ℝ)*(sp_s1_0) + (340235027/500000000000 : ℝ)*(sp_s1_13) + (3671674031033/500000000000 : ℝ)*(sp_s1_14) + (7946154963703/1000000000000 : ℝ)*(sp_s1_15) + (1468678616107/200000000000 : ℝ)*(sp_s1_16) + (1503915207399/500000000000 : ℝ)*(sp_s1_20) + (47704751/1000000000000 : ℝ)*(sp_s1_22) + (3611317718139/1000000000000 : ℝ)*(f.failure) + (229481119849/31250000000 : ℝ)*(f.sum) + (273043517371781273/984823180000000000000000000000 : ℝ)*base62 + (178080580537/591875000000000000000000 : ℝ)*base65 + (27816318065753/107580000000000000000000000 : ℝ)*base66 + (48621032409371/274630000000000000000000000 : ℝ)*base68 + (646863914813069/12596431718750000000000000000 : ℝ)*base70 + (172994964719917/851290000000000000000000000 : ℝ)*base73 + (29432047710957/35860000000000000000000000 : ℝ)*base74 + (81847666685603/851290000000000000000000000 : ℝ)*base77 + (96596681933104807/832561620000000000000000000000 : ℝ)*base78 + (9801/12500000000000000 : ℝ)*base87 + (9801/12500000000000000 : ℝ)*base89 + (9801/12500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4733/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(4733/12500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (9731108112682759356263809409/476346661876250000000000000000000 : ℝ) := by norm_num
    linear_combination (387881460381/100000000000 : ℝ)*(base3) + (1294192846833/500000000000 : ℝ)*(base40) + (3608428046539/1000000000000 : ℝ)*(base50) + (4808579/1000000000000 : ℝ)*(base59) + (8355151846621/1000000000000 : ℝ)*(major_s1_0) + (8355151846621/1000000000000 : ℝ)*(major_s1_1) + (8355151846621/1000000000000 : ℝ)*(major_s1_2) + (190476307/1000000000000 : ℝ)*(sp_s1_7) + (19898643/500000000000 : ℝ)*(sp_s1_8) + (26702309/40000000000 : ℝ)*(sp_s1_20) + (11201408792391/1000000000000 : ℝ)*(sp_s1_21) + (7540187037611/500000000000 : ℝ)*(sp_s1_22) + (5600799634349/500000000000 : ℝ)*(sp_s1_23) + (203651931683/125000000000 : ℝ)*(sp_s1_27) + (5508697614999/1000000000000 : ℝ)*(f.failure) + (5600799634349/500000000000 : ℝ)*(f.sum) + (3389721395988123329/14772347700000000000000000000000 : ℝ)*base62 + (8062421834039/23675000000000000000000000 : ℝ)*base64 + (372181352697251/1613700000000000000000000000 : ℝ)*base66 + (123877593651481/4119450000000000000000000000 : ℝ)*base68 + (173397579332462761/251928634375000000000000000000 : ℝ)*base70 + (633850068627639/2128225000000000000000000000 : ℝ)*base73 + (78573124628281/537900000000000000000000000 : ℝ)*base74 + (471830502667143/1064112500000000000000000000 : ℝ)*base76 + (1159912314087751673/12488424300000000000000000000000 : ℝ)*base79 + (3541/12500000000000000 : ℝ)*base87 + (3541/12500000000000000 : ℝ)*base89 + (3541/12500000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((85129/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(85129/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-16137/20000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(-16137/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(82389/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(82389/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((49243/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(49243/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-37161/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(-37161/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4733/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(4733/12500 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304015_s1 p hpa hpb X hX hprev0

#print axioms solution
