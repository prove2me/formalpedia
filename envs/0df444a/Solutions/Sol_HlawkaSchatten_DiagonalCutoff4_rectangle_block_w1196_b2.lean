-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1196_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:01:17.485308+00:00
-- url     : https://prove2.me/submissions/ffd3c3ae-09fd-4f91-bc33-20326b35a664

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_majorant
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
theorem frame_box_of_interval_base {p k A d ell u v w rho lo : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      -u ≤ X 0 0 ∧ X 0 0 ≤ -ell ∧ v ≤ X 0 1 ∧ X 0 1 ≤ w)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
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
    · intro i j hij
      rw [pair_relabel]
      exact hlower (e i) (e j) (e.injective.ne hij)
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

theorem frame_interval_of_base {p k A d rho lo R L : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      L*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ R*pair X 0 0)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → L*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ R*pair X i i := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      L*pair X (e 0) (e 0) ≤ pair X (e 0) (e 1) ∧
        pair X (e 0) (e 1) ≤ R*pair X (e 0) (e 0) := by
    have hh := base (relabel e X) (frame_relabel hX e)
      (fun i j hij => by rw [pair_relabel];exact hsign (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hratio (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hlower (e i) (e j) (e.injective.ne hij))
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


theorem rectangle_pair_majorant {p a lo hi c alpha : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hlo : 0 ≤ lo) (hlohi : lo < hi) (hhi : hi ≤ 1) (halpha : 0 ≤ alpha)
    (hc : 1 ≤ c+2*alpha*lo)
    (hcorner00 : 1+2*lo^a ≤ (c+2*alpha*lo)^a)
    (hcorner10 : 1+hi^a+lo^a ≤ (c+alpha*(hi+lo))^a)
    (hcorner11 : 1+2*hi^a ≤ (c+2*alpha*hi)^a)
    (X : Fin 3 → Fin 3 → ℝ)
    (hmain : ∀ i, 0 ≤ pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h)
    (hupper : ∀ i h, i ≠ h → |pair X i h| ≤ hi*pair X i i)
    (i j l : Fin 3) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    lpNorm p (pair X i) ≤ c*pair X i i+alpha*(pair X i j+pair X i l) := by
  have hh := rectangle_majorant hp ha hap hlo hlohi hhi halpha hc hcorner00 hcorner10 hcorner11
    (hmain i) (hlower i j hij) ((le_abs_self _).trans (hupper i j hij))
    (hlower i l hil) ((le_abs_self _).trans (hupper i l hil))
  have he : lpNorm p (pair X i) =
      (|pair X i i|^p+|pair X i j|^p+|pair X i l|^p)^(1/p) := by
    simp only [lpNorm,Real.norm_eq_abs]
    congr 1
    fin_cases i <;> fin_cases j <;> fin_cases l <;> try contradiction
    all_goals simp [Fin.sum_univ_three] <;> ring
  rw [he]
  exact hh

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
theorem support_rectangle_w1196_s6_0 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2141304501/10000000000 : ℝ)*x 0 + (5392303459/10000000000 : ℝ)*x 1 + (1053266221/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2141304501/10000000000 : ℝ)^8389 ≤ (16270940991/125000000000 : ℝ)^6341 := by
    have hnat : (2141304501 : ℕ)^8389*125000000000^6341 ≤ 16270940991^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141304501 10000000000 16270940991 125000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392303459/10000000000 : ℝ)^8389 ≤ (4417163557827/10000000000000 : ℝ)^6341 := by
    have hnat : (5392303459 : ℕ)^8389*10000000000000^6341 ≤ 4417163557827^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392303459 10000000000 4417163557827 10000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053266221/2000000000 : ℝ)^8389 ≤ (5351451452671/12500000000000 : ℝ)^6341 := by
    have hnat : (1053266221 : ℕ)^8389*12500000000000^6341 ≤ 5351451452671^6341*2000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053266221 2000000000 5351451452671 12500000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2141304501/10000000000 : ℝ), (5392303459/10000000000 : ℝ), (1053266221/2000000000 : ℝ)] ![(16270940991/125000000000 : ℝ), (4417163557827/10000000000000 : ℝ), (5351451452671/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2141304501/10000000000 : ℝ)|^8389 ≤ (16270940991/125000000000 : ℝ)^6341
        have hw : |(-2141304501/10000000000 : ℝ)|=(2141304501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392303459/10000000000 : ℝ)|^8389 ≤ (4417163557827/10000000000000 : ℝ)^6341
        have hw : |(5392303459/10000000000 : ℝ)|=(5392303459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053266221/2000000000 : ℝ)|^8389 ≤ (5351451452671/12500000000000 : ℝ)^6341
        have hw : |(1053266221/2000000000 : ℝ)|=(1053266221/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s6_1 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672299737/5000000000 : ℝ)*x 0 + (-275648773/1250000000 : ℝ)*x 1 + (2633165571/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672299737/5000000000 : ℝ)^8389 ≤ (8731078529419/20000000000000 : ℝ)^6341 := by
    have hnat : (2672299737 : ℕ)^8389*20000000000000^6341 ≤ 8731078529419^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672299737 5000000000 8731078529419 20000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (275648773/1250000000 : ℝ)^8389 ≤ (13532995311493/100000000000000 : ℝ)^6341 := by
    have hnat : (275648773 : ℕ)^8389*100000000000000^6341 ≤ 13532995311493^6341*1250000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275648773 1250000000 13532995311493 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633165571/5000000000 : ℝ)^8389 ≤ (42811612019299/100000000000000 : ℝ)^6341 := by
    have hnat : (2633165571 : ℕ)^8389*100000000000000^6341 ≤ 42811612019299^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633165571 5000000000 42811612019299 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672299737/5000000000 : ℝ), (-275648773/1250000000 : ℝ), (2633165571/5000000000 : ℝ)] ![(8731078529419/20000000000000 : ℝ), (13532995311493/100000000000000 : ℝ), (42811612019299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672299737/5000000000 : ℝ)|^8389 ≤ (8731078529419/20000000000000 : ℝ)^6341
        have hw : |(2672299737/5000000000 : ℝ)|=(2672299737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-275648773/1250000000 : ℝ)|^8389 ≤ (13532995311493/100000000000000 : ℝ)^6341
        have hw : |(-275648773/1250000000 : ℝ)|=(275648773/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633165571/5000000000 : ℝ)|^8389 ≤ (42811612019299/100000000000000 : ℝ)^6341
        have hw : |(2633165571/5000000000 : ℝ)|=(2633165571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s6_2 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (267229977/500000000 : ℝ)*x 0 + (5266331017/10000000000 : ℝ)*x 1 + (-2205190263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267229977/500000000 : ℝ)^8389 ≤ (10913848340077/25000000000000 : ℝ)^6341 := by
    have hnat : (267229977 : ℕ)^8389*25000000000000^6341 ≤ 10913848340077^6341*500000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267229977 500000000 10913848340077 25000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266331017/10000000000 : ℝ)^8389 ≤ (21405805337469/50000000000000 : ℝ)^6341 := by
    have hnat : (5266331017 : ℕ)^8389*50000000000000^6341 ≤ 21405805337469^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266331017 10000000000 21405805337469 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2205190263/10000000000 : ℝ)^8389 ≤ (13532995952891/100000000000000 : ℝ)^6341 := by
    have hnat : (2205190263 : ℕ)^8389*100000000000000^6341 ≤ 13532995952891^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205190263 10000000000 13532995952891 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267229977/500000000 : ℝ), (5266331017/10000000000 : ℝ), (-2205190263/10000000000 : ℝ)] ![(10913848340077/25000000000000 : ℝ), (21405805337469/50000000000000 : ℝ), (13532995952891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267229977/500000000 : ℝ)|^8389 ≤ (10913848340077/25000000000000 : ℝ)^6341
        have hw : |(267229977/500000000 : ℝ)|=(267229977/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266331017/10000000000 : ℝ)|^8389 ≤ (21405805337469/50000000000000 : ℝ)^6341
        have hw : |(5266331017/10000000000 : ℝ)|=(5266331017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2205190263/10000000000 : ℝ)|^8389 ≤ (13532995952891/100000000000000 : ℝ)^6341
        have hw : |(-2205190263/10000000000 : ℝ)|=(2205190263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s6_3 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (87142169/200000000 : ℝ)*x 0 + (4232278471/10000000000 : ℝ)*x 1 + (1121388709/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (87142169/200000000 : ℝ)^8389 ≤ (1332685189361/4000000000000 : ℝ)^6341 := by
    have hnat : (87142169 : ℕ)^8389*4000000000000^6341 ≤ 1332685189361^6341*200000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87142169 200000000 1332685189361 4000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4232278471/10000000000 : ℝ)^8389 ≤ (32060193155991/100000000000000 : ℝ)^6341 := by
    have hnat : (4232278471 : ℕ)^8389*100000000000000^6341 ≤ 32060193155991^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232278471 10000000000 32060193155991 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1121388709/2500000000 : ℝ)^8389 ≤ (6924535420117/20000000000000 : ℝ)^6341 := by
    have hnat : (1121388709 : ℕ)^8389*20000000000000^6341 ≤ 6924535420117^6341*2500000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121388709 2500000000 6924535420117 20000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(87142169/200000000 : ℝ), (4232278471/10000000000 : ℝ), (1121388709/2500000000 : ℝ)] ![(1332685189361/4000000000000 : ℝ), (32060193155991/100000000000000 : ℝ), (6924535420117/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(87142169/200000000 : ℝ)|^8389 ≤ (1332685189361/4000000000000 : ℝ)^6341
        have hw : |(87142169/200000000 : ℝ)|=(87142169/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4232278471/10000000000 : ℝ)|^8389 ≤ (32060193155991/100000000000000 : ℝ)^6341
        have hw : |(4232278471/10000000000 : ℝ)|=(4232278471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1121388709/2500000000 : ℝ)|^8389 ≤ (6924535420117/20000000000000 : ℝ)^6341
        have hw : |(1121388709/2500000000 : ℝ)|=(1121388709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s6_4 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-428261897/2000000000 : ℝ)*x 0 + (210665973/400000000 : ℝ)*x 1 + (2695991977/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (428261897/2000000000 : ℝ)^8389 ≤ (6508396437653/50000000000000 : ℝ)^6341 := by
    have hnat : (428261897 : ℕ)^8389*50000000000000^6341 ≤ 6508396437653^6341*2000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428261897 2000000000 6508396437653 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210665973/400000000 : ℝ)^8389 ≤ (42815034074951/100000000000000 : ℝ)^6341 := by
    have hnat : (210665973 : ℕ)^8389*100000000000000^6341 ≤ 42815034074951^6341*400000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210665973 400000000 42815034074951 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695991977/5000000000 : ℝ)^8389 ≤ (44168173035869/100000000000000 : ℝ)^6341 := by
    have hnat : (2695991977 : ℕ)^8389*100000000000000^6341 ≤ 44168173035869^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695991977 5000000000 44168173035869 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-428261897/2000000000 : ℝ), (210665973/400000000 : ℝ), (2695991977/5000000000 : ℝ)] ![(6508396437653/50000000000000 : ℝ), (42815034074951/100000000000000 : ℝ), (44168173035869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-428261897/2000000000 : ℝ)|^8389 ≤ (6508396437653/50000000000000 : ℝ)^6341
        have hw : |(-428261897/2000000000 : ℝ)|=(428261897/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210665973/400000000 : ℝ)|^8389 ≤ (42815034074951/100000000000000 : ℝ)^6341
        have hw : |(210665973/400000000 : ℝ)|=(210665973/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695991977/5000000000 : ℝ)|^8389 ≤ (44168173035869/100000000000000 : ℝ)^6341
        have hw : |(2695991977/5000000000 : ℝ)|=(2695991977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s6_5 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062511831/2000000000 : ℝ)*x 0 + (-64985537/312500000 : ℝ)*x 1 + (5391983921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062511831/2000000000 : ℝ)^8389 ≤ (4330949246693/10000000000000 : ℝ)^6341 := by
    have hnat : (1062511831 : ℕ)^8389*10000000000000^6341 ≤ 4330949246693^6341*2000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062511831 2000000000 4330949246693 10000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (64985537/312500000 : ℝ)^8389 ≤ (12522334837599/100000000000000 : ℝ)^6341 := by
    have hnat : (64985537 : ℕ)^8389*100000000000000^6341 ≤ 12522334837599^6341*312500000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64985537 312500000 12522334837599 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391983921/10000000000 : ℝ)^8389 ≤ (8833634535649/20000000000000 : ℝ)^6341 := by
    have hnat : (5391983921 : ℕ)^8389*20000000000000^6341 ≤ 8833634535649^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391983921 10000000000 8833634535649 20000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062511831/2000000000 : ℝ), (-64985537/312500000 : ℝ), (5391983921/10000000000 : ℝ)] ![(4330949246693/10000000000000 : ℝ), (12522334837599/100000000000000 : ℝ), (8833634535649/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062511831/2000000000 : ℝ)|^8389 ≤ (4330949246693/10000000000000 : ℝ)^6341
        have hw : |(1062511831/2000000000 : ℝ)|=(1062511831/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-64985537/312500000 : ℝ)|^8389 ≤ (12522334837599/100000000000000 : ℝ)^6341
        have hw : |(-64985537/312500000 : ℝ)|=(64985537/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391983921/10000000000 : ℝ)|^8389 ≤ (8833634535649/20000000000000 : ℝ)^6341
        have hw : |(5391983921/10000000000 : ℝ)|=(5391983921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s6_6 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656279587/5000000000 : ℝ)*x 0 + (1347995969/2500000000 : ℝ)*x 1 + (-103976861/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656279587/5000000000 : ℝ)^8389 ≤ (866189853437/2000000000000 : ℝ)^6341 := by
    have hnat : (2656279587 : ℕ)^8389*2000000000000^6341 ≤ 866189853437^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656279587 5000000000 866189853437 2000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347995969/2500000000 : ℝ)^8389 ≤ (1766726887623/4000000000000 : ℝ)^6341 := by
    have hnat : (1347995969 : ℕ)^8389*4000000000000^6341 ≤ 1766726887623^6341*2500000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347995969 2500000000 1766726887623 4000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (103976861/500000000 : ℝ)^8389 ≤ (2504467024879/20000000000000 : ℝ)^6341 := by
    have hnat : (103976861 : ℕ)^8389*20000000000000^6341 ≤ 2504467024879^6341*500000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103976861 500000000 2504467024879 20000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656279587/5000000000 : ℝ), (1347995969/2500000000 : ℝ), (-103976861/500000000 : ℝ)] ![(866189853437/2000000000000 : ℝ), (1766726887623/4000000000000 : ℝ), (2504467024879/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656279587/5000000000 : ℝ)|^8389 ≤ (866189853437/2000000000000 : ℝ)^6341
        have hw : |(2656279587/5000000000 : ℝ)|=(2656279587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347995969/2500000000 : ℝ)|^8389 ≤ (1766726887623/4000000000000 : ℝ)^6341
        have hw : |(1347995969/2500000000 : ℝ)|=(1347995969/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-103976861/500000000 : ℝ)|^8389 ≤ (2504467024879/20000000000000 : ℝ)^6341
        have hw : |(-103976861/500000000 : ℝ)|=(103976861/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s6_7 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4357118051/10000000000 : ℝ)*x 0 + (280307167/625000000 : ℝ)*x 1 + (4232921043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357118051/10000000000 : ℝ)^8389 ≤ (6663445372129/20000000000000 : ℝ)^6341 := by
    have hnat : (4357118051 : ℕ)^8389*20000000000000^6341 ≤ 6663445372129^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357118051 10000000000 6663445372129 20000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (280307167/625000000 : ℝ)^8389 ≤ (17308070052781/50000000000000 : ℝ)^6341 := by
    have hnat : (280307167 : ℕ)^8389*50000000000000^6341 ≤ 17308070052781^6341*625000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280307167 625000000 17308070052781 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4232921043/10000000000 : ℝ)^8389 ≤ (801665825533/2500000000000 : ℝ)^6341 := by
    have hnat : (4232921043 : ℕ)^8389*2500000000000^6341 ≤ 801665825533^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232921043 10000000000 801665825533 2500000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357118051/10000000000 : ℝ), (280307167/625000000 : ℝ), (4232921043/10000000000 : ℝ)] ![(6663445372129/20000000000000 : ℝ), (17308070052781/50000000000000 : ℝ), (801665825533/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357118051/10000000000 : ℝ)|^8389 ≤ (6663445372129/20000000000000 : ℝ)^6341
        have hw : |(4357118051/10000000000 : ℝ)|=(4357118051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(280307167/625000000 : ℝ)|^8389 ≤ (17308070052781/50000000000000 : ℝ)^6341
        have hw : |(280307167/625000000 : ℝ)|=(280307167/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4232921043/10000000000 : ℝ)|^8389 ≤ (801665825533/2500000000000 : ℝ)^6341
        have hw : |(4232921043/10000000000 : ℝ)|=(4232921043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1196_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150528399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14111/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (356/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (11417/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2817/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14111/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (356/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14111/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (356/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14111/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (356/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14111/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (356/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14111/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (356/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14111/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (356/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (356/3125 : ℝ) ^ (2097/512 : ℝ) ≤ (6840432773896093/50000000000000000000 : ℝ) := by
    have hpowers : (356/3125 : ℝ)^2097 ≤ (6840432773896093/50000000000000000000 : ℝ)^512 := by
      have hnat : (356 : ℕ)^2097*50000000000000000000^512 ≤ 6840432773896093^512*3125^2097 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        356 3125 6840432773896093 50000000000000000000 2097 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (356/3125 : ℝ)) (X := (6840432773896093/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14111/100000 : ℝ) ^ (2097/512 : ℝ) ≤ (16436570044771073/50000000000000000000 : ℝ) := by
    have hpowers : (14111/100000 : ℝ)^2097 ≤ (16436570044771073/50000000000000000000 : ℝ)^512 := by
      have hnat : (14111 : ℕ)^2097*50000000000000000000^512 ≤ 16436570044771073^512*100000^2097 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14111 100000 16436570044771073 50000000000000000000 2097 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14111/100000 : ℝ)) (X := (16436570044771073/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006840432773896093/25000000000000000000 : ℝ) ≤ (125008349879543/125000000000000 : ℝ) ^ (2097/512 : ℝ) := by
    have hpowers : (25006840432773896093/25000000000000000000 : ℝ)^512 ≤ (125008349879543/125000000000000 : ℝ)^2097 := by
      have hnat : (25006840432773896093 : ℕ)^512*125000000000000^2097 ≤ 125008349879543^2097*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006840432773896093 25000000000000000000 125008349879543 125000000000000 512 2097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125008349879543/125000000000000 : ℝ)) (X := (25006840432773896093/25000000000000000000 : ℝ)) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011638501409333583/25000000000000000000 : ℝ) ≤ (200022729097233/200000000000000 : ℝ) ^ (2097/512 : ℝ) := by
    have hpowers : (25011638501409333583/25000000000000000000 : ℝ)^512 ≤ (200022729097233/200000000000000 : ℝ)^2097 := by
      have hnat : (25011638501409333583 : ℕ)^512*200000000000000^2097 ≤ 200022729097233^2097*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011638501409333583 25000000000000000000 200022729097233 200000000000000 512 2097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200022729097233/200000000000000 : ℝ)) (X := (25011638501409333583/25000000000000000000 : ℝ)) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016436570044771073/25000000000000000000 : ℝ) ≤ (500080245967993/500000000000000 : ℝ) ^ (2097/512 : ℝ) := by
    have hpowers : (25016436570044771073/25000000000000000000 : ℝ)^512 ≤ (500080245967993/500000000000000 : ℝ)^2097 := by
      have hnat : (25016436570044771073 : ℕ)^512*500000000000000^2097 ≤ 500080245967993^2097*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016436570044771073 25000000000000000000 500080245967993 500000000000000 512 2097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500080245967993/500000000000000 : ℝ)) (X := (25016436570044771073/25000000000000000000 : ℝ)) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6840432773896093/50000000000000000000 : ℝ) ≤ ((339764284633387209/339875000000000000 : ℝ)+2*(46846449821/27190000000000 : ℝ)*(356/3125 : ℝ))^(2097/512 : ℝ) := by
    rw [show (339764284633387209/339875000000000000 : ℝ)+2*(46846449821/27190000000000 : ℝ)*(356/3125 : ℝ)=(125008349879543/125000000000000 : ℝ) by norm_num, show 1+2*(6840432773896093/50000000000000000000 : ℝ)=(25006840432773896093/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16436570044771073/50000000000000000000 : ℝ)+(6840432773896093/50000000000000000000 : ℝ) ≤ ((339764284633387209/339875000000000000 : ℝ)+(46846449821/27190000000000 : ℝ)*((14111/100000 : ℝ)+(356/3125 : ℝ)))^(2097/512 : ℝ) := by
    rw [show (339764284633387209/339875000000000000 : ℝ)+(46846449821/27190000000000 : ℝ)*((14111/100000 : ℝ)+(356/3125 : ℝ))=(200022729097233/200000000000000 : ℝ) by norm_num, show 1+(16436570044771073/50000000000000000000 : ℝ)+(6840432773896093/50000000000000000000 : ℝ)=(25011638501409333583/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16436570044771073/50000000000000000000 : ℝ) ≤ ((339764284633387209/339875000000000000 : ℝ)+2*(46846449821/27190000000000 : ℝ)*(14111/100000 : ℝ))^(2097/512 : ℝ) := by
    rw [show (339764284633387209/339875000000000000 : ℝ)+2*(46846449821/27190000000000 : ℝ)*(14111/100000 : ℝ)=(500080245967993/500000000000000 : ℝ) by norm_num, show 1+2*(16436570044771073/50000000000000000000 : ℝ)=(25016436570044771073/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (339764284633387209/339875000000000000 : ℝ)*(X 1 0+X 2 0)+(46846449821/27190000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2097/512 : ℝ)) (lo := (356/3125 : ℝ)) (hi := (14111/100000 : ℝ)) (c := (339764284633387209/339875000000000000 : ℝ)) (alpha := (46846449821/27190000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (339764284633387209/339875000000000000 : ℝ)*(X 0 1+X 2 1)+(46846449821/27190000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2097/512 : ℝ)) (lo := (356/3125 : ℝ)) (hi := (14111/100000 : ℝ)) (c := (339764284633387209/339875000000000000 : ℝ)) (alpha := (46846449821/27190000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (339764284633387209/339875000000000000 : ℝ)*(X 0 2+X 1 2)+(46846449821/27190000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2097/512 : ℝ)) (lo := (356/3125 : ℝ)) (hi := (14111/100000 : ℝ)) (c := (339764284633387209/339875000000000000 : ℝ)) (alpha := (46846449821/27190000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2141304501/10000000000 : ℝ)*X 0 0+(5392303459/10000000000 : ℝ)*X 0 1+(1053266221/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672299737/5000000000 : ℝ)*X 1 0+(-275648773/1250000000 : ℝ)*X 1 1+(2633165571/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267229977/500000000 : ℝ)*X 2 0+(5266331017/10000000000 : ℝ)*X 2 1+(-2205190263/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((87142169/200000000 : ℝ)*X 0 0+(4232278471/10000000000 : ℝ)*X 0 1+(1121388709/2500000000 : ℝ)*X 0 2+(87142169/200000000 : ℝ)*X 1 0+(4232278471/10000000000 : ℝ)*X 1 1+(1121388709/2500000000 : ℝ)*X 1 2+(87142169/200000000 : ℝ)*X 2 0+(4232278471/10000000000 : ℝ)*X 2 1+(1121388709/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-428261897/2000000000 : ℝ)*X 0 0+(210665973/400000000 : ℝ)*X 0 1+(2695991977/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062511831/2000000000 : ℝ)*X 1 0+(-64985537/312500000 : ℝ)*X 1 1+(5391983921/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656279587/5000000000 : ℝ)*X 2 0+(1347995969/2500000000 : ℝ)*X 2 1+(-103976861/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4357118051/10000000000 : ℝ)*X 0 0+(280307167/625000000 : ℝ)*X 0 1+(4232921043/10000000000 : ℝ)*X 0 2+(4357118051/10000000000 : ℝ)*X 1 0+(280307167/625000000 : ℝ)*X 1 1+(4232921043/10000000000 : ℝ)*X 1 2+(4357118051/10000000000 : ℝ)*X 2 0+(280307167/625000000 : ℝ)*X 2 1+(4232921043/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7487970799533771395509227/1699375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (730376097/100000000000000 : ℝ)*(base19) + (141862937/20000000000000 : ℝ)*(base23) + (91902563/100000000000000 : ℝ)*(lower2) + (49279973/25000000000000 : ℝ)*(upper3) + (14126703/50000000000000 : ℝ)*(lower4) + (594328246979983/10000000000000 : ℝ)*(major0) + (594328246979983/10000000000000 : ℝ)*(major1) + (594328246979983/10000000000000 : ℝ)*(major2) + (7938270762045559/100000000000000 : ℝ)*(sp0) + (1587656839339647/20000000000000 : ℝ)*(sp1) + (7938284217759647/100000000000000 : ℝ)*(sp2) + (3948265477293147/100000000000000 : ℝ)*(sp3) + (14165028773/100000000000000 : ℝ)*(sp4) + (2877671043/20000000000000 : ℝ)*(sp7) + (1974139932824181/50000000000000 : ℝ)*(f.failure) + (1984571231768583/25000000000000 : ℝ)*(f.sum) + (28775278644709/2719000000000000000000000000 : ℝ)*base66 + (60213379982978697/3398750000000000000000000000000 : ℝ)*base67 + (41842287391767447/3398750000000000000000000000000 : ℝ)*base69 + (26891569415406197/3398750000000000000000000000000 : ℝ)*base71 + (991456950897/2719000000000000000000000000 : ℝ)*base73 + (90091577166108697/3398750000000000000000000000000 : ℝ)*base75 + (27336690141893697/3398750000000000000000000000000 : ℝ)*base77 + (54742227919519947/3398750000000000000000000000000 : ℝ)*base79 + (155381871779/679750000000000000000000000 : ℝ)*base81 + (14416219/5000000000000000000000 : ℝ)*base89 + (14416219/5000000000000000000000 : ℝ)*base91 + (14416219/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4375574321246972372814357/2124218750000000000000000000000 : ℝ) := by norm_num
    linear_combination (1126232371/100000000000000 : ℝ)*(base19) + (1264154663/100000000000000 : ℝ)*(base23) + (61219/97656250000 : ℝ)*(upper2) + (2878859/4000000000000 : ℝ)*(upper3) + (13560339/10000000000000 : ℝ)*(upper5) + (746687181946759/12500000000000 : ℝ)*(major0) + (746687181946759/12500000000000 : ℝ)*(major1) + (746687181946759/12500000000000 : ℝ)*(major2) + (33478661943/100000000000000 : ℝ)*(sp1) + (320505263/1000000000000 : ℝ)*(sp2) + (1994660590496503/25000000000000 : ℝ)*(sp4) + (7978607757091697/100000000000000 : ℝ)*(sp5) + (997326130913131/12500000000000 : ℝ)*(sp6) + (1984176240250211/50000000000000 : ℝ)*(sp7) + (1984176240250211/50000000000000 : ℝ)*(f.failure) + (1994660590496503/25000000000000 : ℝ)*(f.sum) + (3346439403243/1359500000000000000000000000 : ℝ)*base65 + (34622089960411881/4248437500000000000000000000000 : ℝ)*base67 + (8414956724052189/1062109375000000000000000000000 : ℝ)*base69 + (17318907177754363/8496875000000000000000000000000 : ℝ)*base72 + (1011146157971/339875000000000000000000000 : ℝ)*base73 + (22588171560723113/8496875000000000000000000000000 : ℝ)*base76 + (3902388357471407/531054687500000000000000000000 : ℝ)*base77 + (38129552173986881/4248437500000000000000000000000 : ℝ)*base79 + (293390757299/271900000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (21242189/5000000000000000000000 : ℝ)*base89 + (21242189/5000000000000000000000 : ℝ)*base91 + (21242189/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1196_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150528399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14111/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (356/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11417/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2817/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1196_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1196_s7_0 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-66916419/312500000 : ℝ)*x 0 + (1078410957/2000000000 : ℝ)*x 1 + (5266566047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66916419/312500000 : ℝ)^8389 ≤ (13016920932037/100000000000000 : ℝ)^6341 := by
    have hnat : (66916419 : ℕ)^8389*100000000000000^6341 ≤ 13016920932037^6341*312500000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66916419 312500000 13016920932037 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078410957/2000000000 : ℝ)^8389 ≤ (4416894064049/10000000000000 : ℝ)^6341 := by
    have hnat : (1078410957 : ℕ)^8389*10000000000000^6341 ≤ 4416894064049^6341*2000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078410957 2000000000 4416894064049 10000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266566047/10000000000 : ℝ)^8389 ≤ (42814138414267/100000000000000 : ℝ)^6341 := by
    have hnat : (5266566047 : ℕ)^8389*100000000000000^6341 ≤ 42814138414267^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266566047 10000000000 42814138414267 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-66916419/312500000 : ℝ), (1078410957/2000000000 : ℝ), (5266566047/10000000000 : ℝ)] ![(13016920932037/100000000000000 : ℝ), (4416894064049/10000000000000 : ℝ), (42814138414267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-66916419/312500000 : ℝ)|^8389 ≤ (13016920932037/100000000000000 : ℝ)^6341
        have hw : |(-66916419/312500000 : ℝ)|=(66916419/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078410957/2000000000 : ℝ)|^8389 ≤ (4416894064049/10000000000000 : ℝ)^6341
        have hw : |(1078410957/2000000000 : ℝ)|=(1078410957/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266566047/10000000000 : ℝ)|^8389 ≤ (42814138414267/100000000000000 : ℝ)^6341
        have hw : |(5266566047/10000000000 : ℝ)|=(5266566047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s7_1 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344536867/10000000000 : ℝ)*x 0 + (-1102481169/5000000000 : ℝ)*x 1 + (5266566047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344536867/10000000000 : ℝ)^8389 ≤ (1746188644049/4000000000000 : ℝ)^6341 := by
    have hnat : (5344536867 : ℕ)^8389*4000000000000^6341 ≤ 1746188644049^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344536867 10000000000 1746188644049 4000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1102481169/5000000000 : ℝ)^8389 ≤ (676557273507/5000000000000 : ℝ)^6341 := by
    have hnat : (1102481169 : ℕ)^8389*5000000000000^6341 ≤ 676557273507^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102481169 5000000000 676557273507 5000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266566047/10000000000 : ℝ)^8389 ≤ (42814138414267/100000000000000 : ℝ)^6341 := by
    have hnat : (5266566047 : ℕ)^8389*100000000000000^6341 ≤ 42814138414267^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266566047 10000000000 42814138414267 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344536867/10000000000 : ℝ), (-1102481169/5000000000 : ℝ), (5266566047/10000000000 : ℝ)] ![(1746188644049/4000000000000 : ℝ), (676557273507/5000000000000 : ℝ), (42814138414267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344536867/10000000000 : ℝ)|^8389 ≤ (1746188644049/4000000000000 : ℝ)^6341
        have hw : |(5344536867/10000000000 : ℝ)|=(5344536867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1102481169/5000000000 : ℝ)|^8389 ≤ (676557273507/5000000000000 : ℝ)^6341
        have hw : |(-1102481169/5000000000 : ℝ)|=(1102481169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266566047/10000000000 : ℝ)|^8389 ≤ (42814138414267/100000000000000 : ℝ)^6341
        have hw : |(5266566047/10000000000 : ℝ)|=(5266566047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s7_2 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344536867/10000000000 : ℝ)*x 0 + (5266566047/10000000000 : ℝ)*x 1 + (-1102481169/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344536867/10000000000 : ℝ)^8389 ≤ (1746188644049/4000000000000 : ℝ)^6341 := by
    have hnat : (5344536867 : ℕ)^8389*4000000000000^6341 ≤ 1746188644049^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344536867 10000000000 1746188644049 4000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266566047/10000000000 : ℝ)^8389 ≤ (42814138414267/100000000000000 : ℝ)^6341 := by
    have hnat : (5266566047 : ℕ)^8389*100000000000000^6341 ≤ 42814138414267^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266566047 10000000000 42814138414267 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1102481169/5000000000 : ℝ)^8389 ≤ (676557273507/5000000000000 : ℝ)^6341 := by
    have hnat : (1102481169 : ℕ)^8389*5000000000000^6341 ≤ 676557273507^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102481169 5000000000 676557273507 5000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344536867/10000000000 : ℝ), (5266566047/10000000000 : ℝ), (-1102481169/5000000000 : ℝ)] ![(1746188644049/4000000000000 : ℝ), (42814138414267/100000000000000 : ℝ), (676557273507/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344536867/10000000000 : ℝ)|^8389 ≤ (1746188644049/4000000000000 : ℝ)^6341
        have hw : |(5344536867/10000000000 : ℝ)|=(5344536867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266566047/10000000000 : ℝ)|^8389 ≤ (42814138414267/100000000000000 : ℝ)^6341
        have hw : |(5266566047/10000000000 : ℝ)|=(5266566047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1102481169/5000000000 : ℝ)|^8389 ≤ (676557273507/5000000000000 : ℝ)^6341
        have hw : |(-1102481169/5000000000 : ℝ)|=(1102481169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s7_3 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2178560293/5000000000 : ℝ)*x 0 + (2116381661/5000000000 : ℝ)*x 1 + (4485066961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178560293/5000000000 : ℝ)^8389 ≤ (33317252505483/100000000000000 : ℝ)^6341 := by
    have hnat : (2178560293 : ℕ)^8389*100000000000000^6341 ≤ 33317252505483^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178560293 5000000000 33317252505483 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2116381661/5000000000 : ℝ)^8389 ≤ (32065052310071/100000000000000 : ℝ)^6341 := by
    have hnat : (2116381661 : ℕ)^8389*100000000000000^6341 ≤ 32065052310071^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116381661 5000000000 32065052310071 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4485066961/10000000000 : ℝ)^8389 ≤ (34617695167933/100000000000000 : ℝ)^6341 := by
    have hnat : (4485066961 : ℕ)^8389*100000000000000^6341 ≤ 34617695167933^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4485066961 10000000000 34617695167933 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178560293/5000000000 : ℝ), (2116381661/5000000000 : ℝ), (4485066961/10000000000 : ℝ)] ![(33317252505483/100000000000000 : ℝ), (32065052310071/100000000000000 : ℝ), (34617695167933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178560293/5000000000 : ℝ)|^8389 ≤ (33317252505483/100000000000000 : ℝ)^6341
        have hw : |(2178560293/5000000000 : ℝ)|=(2178560293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2116381661/5000000000 : ℝ)|^8389 ≤ (32065052310071/100000000000000 : ℝ)^6341
        have hw : |(2116381661/5000000000 : ℝ)|=(2116381661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4485066961/10000000000 : ℝ)|^8389 ≤ (34617695167933/100000000000000 : ℝ)^6341
        have hw : |(4485066961/10000000000 : ℝ)|=(4485066961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s7_4 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-267666379/1250000000 : ℝ)*x 0 + (2633441061/5000000000 : ℝ)*x 1 + (215669477/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267666379/1250000000 : ℝ)^8389 ≤ (13016966161719/100000000000000 : ℝ)^6341 := by
    have hnat : (267666379 : ℕ)^8389*100000000000000^6341 ≤ 13016966161719^6341*1250000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267666379 1250000000 13016966161719 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633441061/5000000000 : ℝ)^8389 ≤ (42817537847147/100000000000000 : ℝ)^6341 := by
    have hnat : (2633441061 : ℕ)^8389*100000000000000^6341 ≤ 42817537847147^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633441061 5000000000 42817537847147 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215669477/400000000 : ℝ)^8389 ≤ (22082747988219/50000000000000 : ℝ)^6341 := by
    have hnat : (215669477 : ℕ)^8389*50000000000000^6341 ≤ 22082747988219^6341*400000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215669477 400000000 22082747988219 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-267666379/1250000000 : ℝ), (2633441061/5000000000 : ℝ), (215669477/400000000 : ℝ)] ![(13016966161719/100000000000000 : ℝ), (42817537847147/100000000000000 : ℝ), (22082747988219/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-267666379/1250000000 : ℝ)|^8389 ≤ (13016966161719/100000000000000 : ℝ)^6341
        have hw : |(-267666379/1250000000 : ℝ)|=(267666379/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633441061/5000000000 : ℝ)|^8389 ≤ (42817537847147/100000000000000 : ℝ)^6341
        have hw : |(2633441061/5000000000 : ℝ)|=(2633441061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215669477/400000000 : ℝ)|^8389 ≤ (22082747988219/50000000000000 : ℝ)^6341
        have hw : |(215669477/400000000 : ℝ)|=(215669477/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s7_5 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312619593/10000000000 : ℝ)*x 0 + (-2079790303/10000000000 : ℝ)*x 1 + (2695868847/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312619593/10000000000 : ℝ)^8389 ≤ (43310144309379/100000000000000 : ℝ)^6341 := by
    have hnat : (5312619593 : ℕ)^8389*100000000000000^6341 ≤ 43310144309379^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312619593 10000000000 43310144309379 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2079790303/10000000000 : ℝ)^8389 ≤ (12524351366011/100000000000000 : ℝ)^6341 := by
    have hnat : (2079790303 : ℕ)^8389*100000000000000^6341 ≤ 12524351366011^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079790303 10000000000 12524351366011 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695868847/5000000000 : ℝ)^8389 ≤ (1380172009689/3125000000000 : ℝ)^6341 := by
    have hnat : (2695868847 : ℕ)^8389*3125000000000^6341 ≤ 1380172009689^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695868847 5000000000 1380172009689 3125000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312619593/10000000000 : ℝ), (-2079790303/10000000000 : ℝ), (2695868847/5000000000 : ℝ)] ![(43310144309379/100000000000000 : ℝ), (12524351366011/100000000000000 : ℝ), (1380172009689/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312619593/10000000000 : ℝ)|^8389 ≤ (43310144309379/100000000000000 : ℝ)^6341
        have hw : |(5312619593/10000000000 : ℝ)|=(5312619593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2079790303/10000000000 : ℝ)|^8389 ≤ (12524351366011/100000000000000 : ℝ)^6341
        have hw : |(-2079790303/10000000000 : ℝ)|=(2079790303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695868847/5000000000 : ℝ)|^8389 ≤ (1380172009689/3125000000000 : ℝ)^6341
        have hw : |(2695868847/5000000000 : ℝ)|=(2695868847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s7_6 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (166019331/312500000 : ℝ)*x 0 + (5391738433/10000000000 : ℝ)*x 1 + (-2079790653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166019331/312500000 : ℝ)^8389 ≤ (21655066756633/50000000000000 : ℝ)^6341 := by
    have hnat : (166019331 : ℕ)^8389*50000000000000^6341 ≤ 21655066756633^6341*312500000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166019331 312500000 21655066756633 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391738433/10000000000 : ℝ)^8389 ≤ (44165512318551/100000000000000 : ℝ)^6341 := by
    have hnat : (5391738433 : ℕ)^8389*100000000000000^6341 ≤ 44165512318551^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391738433 10000000000 44165512318551 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2079790653/10000000000 : ℝ)^8389 ≤ (6262177077209/50000000000000 : ℝ)^6341 := by
    have hnat : (2079790653 : ℕ)^8389*50000000000000^6341 ≤ 6262177077209^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079790653 10000000000 6262177077209 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(166019331/312500000 : ℝ), (5391738433/10000000000 : ℝ), (-2079790653/10000000000 : ℝ)] ![(21655066756633/50000000000000 : ℝ), (44165512318551/100000000000000 : ℝ), (6262177077209/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(166019331/312500000 : ℝ)|^8389 ≤ (21655066756633/50000000000000 : ℝ)^6341
        have hw : |(166019331/312500000 : ℝ)|=(166019331/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391738433/10000000000 : ℝ)|^8389 ≤ (44165512318551/100000000000000 : ℝ)^6341
        have hw : |(5391738433/10000000000 : ℝ)|=(5391738433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2079790653/10000000000 : ℝ)|^8389 ≤ (6262177077209/50000000000000 : ℝ)^6341
        have hw : |(-2079790653/10000000000 : ℝ)|=(2079790653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s7_7 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4357130903/10000000000 : ℝ)*x 0 + (4484431199/10000000000 : ℝ)*x 1 + (4233400641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357130903/10000000000 : ℝ)^8389 ≤ (2082334804717/6250000000000 : ℝ)^6341 := by
    have hnat : (4357130903 : ℕ)^8389*6250000000000^6341 ≤ 2082334804717^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357130903 10000000000 2082334804717 6250000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4484431199/10000000000 : ℝ)^8389 ≤ (17305601675357/50000000000000 : ℝ)^6341 := by
    have hnat : (4484431199 : ℕ)^8389*50000000000000^6341 ≤ 17305601675357^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484431199 10000000000 17305601675357 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4233400641/10000000000 : ℝ)^8389 ≤ (16035719882393/50000000000000 : ℝ)^6341 := by
    have hnat : (4233400641 : ℕ)^8389*50000000000000^6341 ≤ 16035719882393^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4233400641 10000000000 16035719882393 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357130903/10000000000 : ℝ), (4484431199/10000000000 : ℝ), (4233400641/10000000000 : ℝ)] ![(2082334804717/6250000000000 : ℝ), (17305601675357/50000000000000 : ℝ), (16035719882393/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357130903/10000000000 : ℝ)|^8389 ≤ (2082334804717/6250000000000 : ℝ)^6341
        have hw : |(4357130903/10000000000 : ℝ)|=(4357130903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4484431199/10000000000 : ℝ)|^8389 ≤ (17305601675357/50000000000000 : ℝ)^6341
        have hw : |(4484431199/10000000000 : ℝ)|=(4484431199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4233400641/10000000000 : ℝ)|^8389 ≤ (16035719882393/50000000000000 : ℝ)^6341
        have hw : |(4233400641/10000000000 : ℝ)|=(4233400641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1196_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150528399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2817/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11417/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5711/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (88/625 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2817/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11417/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2817/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11417/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2817/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11417/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2817/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11417/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2817/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11417/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2817/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11417/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (11417/100000 : ℝ) ^ (2097/512 : ℝ) ≤ (6902124517607773/50000000000000000000 : ℝ) := by
    have hpowers : (11417/100000 : ℝ)^2097 ≤ (6902124517607773/50000000000000000000 : ℝ)^512 := by
      have hnat : (11417 : ℕ)^2097*50000000000000000000^512 ≤ 6902124517607773^512*100000^2097 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11417 100000 6902124517607773 50000000000000000000 2097 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11417/100000 : ℝ)) (X := (6902124517607773/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2817/20000 : ℝ) ^ (2097/512 : ℝ) ≤ (32625770419421511/100000000000000000000 : ℝ) := by
    have hpowers : (2817/20000 : ℝ)^2097 ≤ (32625770419421511/100000000000000000000 : ℝ)^512 := by
      have hnat : (2817 : ℕ)^2097*100000000000000000000^512 ≤ 32625770419421511^512*20000^2097 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2817 20000 32625770419421511 100000000000000000000 2097 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2817/20000 : ℝ)) (X := (32625770419421511/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006902124517607773/25000000000000000000 : ℝ) ≤ (2500168503533279/2500000000000000 : ℝ) ^ (2097/512 : ℝ) := by
    have hpowers : (25006902124517607773/25000000000000000000 : ℝ)^512 ≤ (2500168503533279/2500000000000000 : ℝ)^2097 := by
      have hnat : (25006902124517607773 : ℕ)^512*2500000000000000^2097 ≤ 2500168503533279^2097*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006902124517607773 25000000000000000000 2500168503533279 2500000000000000 512 2097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500168503533279/2500000000000000 : ℝ)) (X := (25006902124517607773/25000000000000000000 : ℝ)) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046430019454637057/100000000000000000000 : ℝ) ≤ (10001133428699177/10000000000000000 : ℝ) ^ (2097/512 : ℝ) := by
    have hpowers : (100046430019454637057/100000000000000000000 : ℝ)^512 ≤ (10001133428699177/10000000000000000 : ℝ)^2097 := by
      have hnat : (100046430019454637057 : ℕ)^512*10000000000000000^2097 ≤ 10001133428699177^2097*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046430019454637057 100000000000000000000 10001133428699177 10000000000000000 512 2097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001133428699177/10000000000000000 : ℝ)) (X := (100046430019454637057/100000000000000000000 : ℝ)) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032625770419421511/50000000000000000000 : ℝ) ≤ (5000796421632619/5000000000000000 : ℝ) ^ (2097/512 : ℝ) := by
    have hpowers : (50032625770419421511/50000000000000000000 : ℝ)^512 ≤ (5000796421632619/5000000000000000 : ℝ)^2097 := by
      have hnat : (50032625770419421511 : ℕ)^512*5000000000000000^2097 ≤ 5000796421632619^2097*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032625770419421511 50000000000000000000 5000796421632619 5000000000000000 512 2097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000796421632619/5000000000000000 : ℝ)) (X := (50032625770419421511/50000000000000000000 : ℝ)) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6902124517607773/50000000000000000000 : ℝ) ≤ ((13335653998752858307/13340000000000000000 : ℝ)+2*(459414566061/266800000000000 : ℝ)*(11417/100000 : ℝ))^(2097/512 : ℝ) := by
    rw [show (13335653998752858307/13340000000000000000 : ℝ)+2*(459414566061/266800000000000 : ℝ)*(11417/100000 : ℝ)=(2500168503533279/2500000000000000 : ℝ) by norm_num, show 1+2*(6902124517607773/50000000000000000000 : ℝ)=(25006902124517607773/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32625770419421511/100000000000000000000 : ℝ)+(6902124517607773/50000000000000000000 : ℝ) ≤ ((13335653998752858307/13340000000000000000 : ℝ)+(459414566061/266800000000000 : ℝ)*((2817/20000 : ℝ)+(11417/100000 : ℝ)))^(2097/512 : ℝ) := by
    rw [show (13335653998752858307/13340000000000000000 : ℝ)+(459414566061/266800000000000 : ℝ)*((2817/20000 : ℝ)+(11417/100000 : ℝ))=(10001133428699177/10000000000000000 : ℝ) by norm_num, show 1+(32625770419421511/100000000000000000000 : ℝ)+(6902124517607773/50000000000000000000 : ℝ)=(100046430019454637057/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32625770419421511/100000000000000000000 : ℝ) ≤ ((13335653998752858307/13340000000000000000 : ℝ)+2*(459414566061/266800000000000 : ℝ)*(2817/20000 : ℝ))^(2097/512 : ℝ) := by
    rw [show (13335653998752858307/13340000000000000000 : ℝ)+2*(459414566061/266800000000000 : ℝ)*(2817/20000 : ℝ)=(5000796421632619/5000000000000000 : ℝ) by norm_num, show 1+2*(32625770419421511/100000000000000000000 : ℝ)=(50032625770419421511/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13335653998752858307/13340000000000000000 : ℝ)*(X 1 0+X 2 0)+(459414566061/266800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2097/512 : ℝ)) (lo := (11417/100000 : ℝ)) (hi := (2817/20000 : ℝ)) (c := (13335653998752858307/13340000000000000000 : ℝ)) (alpha := (459414566061/266800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13335653998752858307/13340000000000000000 : ℝ)*(X 0 1+X 2 1)+(459414566061/266800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2097/512 : ℝ)) (lo := (11417/100000 : ℝ)) (hi := (2817/20000 : ℝ)) (c := (13335653998752858307/13340000000000000000 : ℝ)) (alpha := (459414566061/266800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13335653998752858307/13340000000000000000 : ℝ)*(X 0 2+X 1 2)+(459414566061/266800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2097/512 : ℝ)) (lo := (11417/100000 : ℝ)) (hi := (2817/20000 : ℝ)) (c := (13335653998752858307/13340000000000000000 : ℝ)) (alpha := (459414566061/266800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-66916419/312500000 : ℝ)*X 0 0+(1078410957/2000000000 : ℝ)*X 0 1+(5266566047/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344536867/10000000000 : ℝ)*X 1 0+(-1102481169/5000000000 : ℝ)*X 1 1+(5266566047/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344536867/10000000000 : ℝ)*X 2 0+(5266566047/10000000000 : ℝ)*X 2 1+(-1102481169/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2178560293/5000000000 : ℝ)*X 0 0+(2116381661/5000000000 : ℝ)*X 0 1+(4485066961/10000000000 : ℝ)*X 0 2+(2178560293/5000000000 : ℝ)*X 1 0+(2116381661/5000000000 : ℝ)*X 1 1+(4485066961/10000000000 : ℝ)*X 1 2+(2178560293/5000000000 : ℝ)*X 2 0+(2116381661/5000000000 : ℝ)*X 2 1+(4485066961/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-267666379/1250000000 : ℝ)*X 0 0+(2633441061/5000000000 : ℝ)*X 0 1+(215669477/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312619593/10000000000 : ℝ)*X 1 0+(-2079790303/10000000000 : ℝ)*X 1 1+(2695868847/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((166019331/312500000 : ℝ)*X 2 0+(5391738433/10000000000 : ℝ)*X 2 1+(-2079790653/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4357130903/10000000000 : ℝ)*X 0 0+(4484431199/10000000000 : ℝ)*X 0 1+(4233400641/10000000000 : ℝ)*X 0 2+(4357130903/10000000000 : ℝ)*X 1 0+(4484431199/10000000000 : ℝ)*X 1 1+(4233400641/10000000000 : ℝ)*X 1 2+(4357130903/10000000000 : ℝ)*X 2 0+(4484431199/10000000000 : ℝ)*X 2 1+(4233400641/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (705086697114294177040469859/166750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (828321603/100000000000000 : ℝ)*(base19) + (77056981/10000000000000 : ℝ)*(base23) + (30865659/100000000000000 : ℝ)*(lower2) + (3334819/3125000000000 : ℝ)*(upper3) + (64176173/100000000000000 : ℝ)*(upper5) + (1491548879129179/25000000000000 : ℝ)*(major0) + (1491548879129179/25000000000000 : ℝ)*(major1) + (1491548879129179/25000000000000 : ℝ)*(major2) + (7968866484844463/100000000000000 : ℝ)*(sp0) + (1593777690933091/20000000000000 : ℝ)*(sp1) + (7968888512417249/100000000000000 : ℝ)*(sp2) + (1981744668270899/50000000000000 : ℝ)*(sp3) + (4559628519/20000000000000 : ℝ)*(sp4) + (6136278851/50000000000000 : ℝ)*(sp7) + (7927003218199/200000000000 : ℝ)*(f.failure) + (3984444641493529/50000000000000 : ℝ)*(f.sum) + (8302409763731/3335000000000000000000000000 : ℝ)*base66 + (2300276548415689953/333500000000000000000000000000000 : ℝ)*base67 + (162427954133810047/333500000000000000000000000000000 : ℝ)*base70 + (1519525171304310047/333500000000000000000000000000000 : ℝ)*base72 + (16908024907479/3335000000000000000000000000 : ℝ)*base73 + (1752449589824689953/333500000000000000000000000000000 : ℝ)*base75 + (2242683035537310047/333500000000000000000000000000000 : ℝ)*base78 + (6493602413027310047/333500000000000000000000000000000 : ℝ)*base80 + (8341040776089/3335000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (66599/20000000000000000000 : ℝ)*base90 + (66599/20000000000000000000 : ℝ)*base92 + (66599/20000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (109462382540022677742988509/66700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (514464359/20000000000000 : ℝ)*(base19) + (455372033/25000000000000 : ℝ)*(base23) + (382145259/100000000000000 : ℝ)*(upper2) + (773035591/100000000000000 : ℝ)*(upper3) + (74928671/25000000000000 : ℝ)*(upper5) + (599641468200171/10000000000000 : ℝ)*(major0) + (599641468200171/10000000000000 : ℝ)*(major1) + (599641468200171/10000000000000 : ℝ)*(major2) + (82148736767/100000000000000 : ℝ)*(sp1) + (44314382019/50000000000000 : ℝ)*(sp2) + (4004626154327761/50000000000000 : ℝ)*(sp4) + (8009167587596961/100000000000000 : ℝ)*(sp5) + (8009161858403351/100000000000000 : ℝ)*(sp6) + (3983577000644051/100000000000000 : ℝ)*(sp7) + (3983577000644051/100000000000000 : ℝ)*(f.failure) + (4004626154327761/50000000000000 : ℝ)*(f.sum) + (200664087027/266800000000000000000000000 : ℝ)*base66 + (623128970175520497/133400000000000000000000000000000 : ℝ)*base67 + (259845858328320497/133400000000000000000000000000000 : ℝ)*base69 + (600527130636720497/133400000000000000000000000000000 : ℝ)*base71 + (7976170571951/1334000000000000000000000000 : ℝ)*base73 + (734484142613879503/133400000000000000000000000000000 : ℝ)*base76 + (1376015364178320497/133400000000000000000000000000000 : ℝ)*base77 + (314636889763479503/133400000000000000000000000000000 : ℝ)*base80 + (911768340133/266800000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (34095651/10000000000000000000000 : ℝ)*base90 + (34095651/10000000000000000000000 : ℝ)*base92 + (34095651/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1196_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150528399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2817/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11417/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5711/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (88/625 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1196_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1196_s8_0 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-85653153/400000000 : ℝ)*x 0 + (134800169/250000000 : ℝ)*x 1 + (5266611883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85653153/400000000 : ℝ)^8389 ≤ (6508474206221/50000000000000 : ℝ)^6341 := by
    have hnat : (85653153 : ℕ)^8389*50000000000000^6341 ≤ 6508474206221^6341*400000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85653153 400000000 6508474206221 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134800169/250000000 : ℝ)^8389 ≤ (44168420187057/100000000000000 : ℝ)^6341 := by
    have hnat : (134800169 : ℕ)^8389*100000000000000^6341 ≤ 44168420187057^6341*250000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134800169 250000000 44168420187057 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266611883/10000000000 : ℝ)^8389 ≤ (4281463138307/10000000000000 : ℝ)^6341 := by
    have hnat : (5266611883 : ℕ)^8389*10000000000000^6341 ≤ 4281463138307^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266611883 10000000000 4281463138307 10000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-85653153/400000000 : ℝ), (134800169/250000000 : ℝ), (5266611883/10000000000 : ℝ)] ![(6508474206221/50000000000000 : ℝ), (44168420187057/100000000000000 : ℝ), (4281463138307/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-85653153/400000000 : ℝ)|^8389 ≤ (6508474206221/50000000000000 : ℝ)^6341
        have hw : |(-85653153/400000000 : ℝ)|=(85653153/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(134800169/250000000 : ℝ)|^8389 ≤ (44168420187057/100000000000000 : ℝ)^6341
        have hw : |(134800169/250000000 : ℝ)|=(134800169/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266611883/10000000000 : ℝ)|^8389 ≤ (4281463138307/10000000000000 : ℝ)^6341
        have hw : |(5266611883/10000000000 : ℝ)|=(5266611883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s8_1 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344524949/10000000000 : ℝ)*x 0 + (-1102458767/5000000000 : ℝ)*x 1 + (5266611843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344524949/10000000000 : ℝ)^8389 ≤ (21827293656411/50000000000000 : ℝ)^6341 := by
    have hnat : (5344524949 : ℕ)^8389*50000000000000^6341 ≤ 21827293656411^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344524949 10000000000 21827293656411 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1102458767/5000000000 : ℝ)^8389 ≤ (1691347715207/12500000000000 : ℝ)^6341 := by
    have hnat : (1102458767 : ℕ)^8389*12500000000000^6341 ≤ 1691347715207^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102458767 5000000000 1691347715207 12500000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266611843/10000000000 : ℝ)^8389 ≤ (42814630952867/100000000000000 : ℝ)^6341 := by
    have hnat : (5266611843 : ℕ)^8389*100000000000000^6341 ≤ 42814630952867^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266611843 10000000000 42814630952867 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344524949/10000000000 : ℝ), (-1102458767/5000000000 : ℝ), (5266611843/10000000000 : ℝ)] ![(21827293656411/50000000000000 : ℝ), (1691347715207/12500000000000 : ℝ), (42814630952867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344524949/10000000000 : ℝ)|^8389 ≤ (21827293656411/50000000000000 : ℝ)^6341
        have hw : |(5344524949/10000000000 : ℝ)|=(5344524949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1102458767/5000000000 : ℝ)|^8389 ≤ (1691347715207/12500000000000 : ℝ)^6341
        have hw : |(-1102458767/5000000000 : ℝ)|=(1102458767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266611843/10000000000 : ℝ)|^8389 ≤ (42814630952867/100000000000000 : ℝ)^6341
        have hw : |(5266611843/10000000000 : ℝ)|=(5266611843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s8_2 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344524943/10000000000 : ℝ)*x 0 + (5266611849/10000000000 : ℝ)*x 1 + (-1102458767/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344524943/10000000000 : ℝ)^8389 ≤ (8730917449597/20000000000000 : ℝ)^6341 := by
    have hnat : (5344524943 : ℕ)^8389*20000000000000^6341 ≤ 8730917449597^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344524943 10000000000 8730917449597 20000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266611849/10000000000 : ℝ)^8389 ≤ (21407315508699/50000000000000 : ℝ)^6341 := by
    have hnat : (5266611849 : ℕ)^8389*50000000000000^6341 ≤ 21407315508699^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266611849 10000000000 21407315508699 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1102458767/5000000000 : ℝ)^8389 ≤ (1691347715207/12500000000000 : ℝ)^6341 := by
    have hnat : (1102458767 : ℕ)^8389*12500000000000^6341 ≤ 1691347715207^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102458767 5000000000 1691347715207 12500000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344524943/10000000000 : ℝ), (5266611849/10000000000 : ℝ), (-1102458767/5000000000 : ℝ)] ![(8730917449597/20000000000000 : ℝ), (21407315508699/50000000000000 : ℝ), (1691347715207/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344524943/10000000000 : ℝ)|^8389 ≤ (8730917449597/20000000000000 : ℝ)^6341
        have hw : |(5344524943/10000000000 : ℝ)|=(5344524943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266611849/10000000000 : ℝ)|^8389 ≤ (21407315508699/50000000000000 : ℝ)^6341
        have hw : |(5266611849/10000000000 : ℝ)|=(5266611849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1102458767/5000000000 : ℝ)|^8389 ≤ (1691347715207/12500000000000 : ℝ)^6341
        have hw : |(-1102458767/5000000000 : ℝ)|=(1102458767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s8_3 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4357122979/10000000000 : ℝ)*x 0 + (4232857327/10000000000 : ℝ)*x 1 + (4484972327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357122979/10000000000 : ℝ)^8389 ≤ (3331727671381/10000000000000 : ℝ)^6341 := by
    have hnat : (4357122979 : ℕ)^8389*10000000000000^6341 ≤ 3331727671381^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357122979 10000000000 3331727671381 10000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4232857327/10000000000 : ℝ)^8389 ≤ (16032997222299/50000000000000 : ℝ)^6341 := by
    have hnat : (4232857327 : ℕ)^8389*50000000000000^6341 ≤ 16032997222299^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232857327 10000000000 16032997222299 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4484972327/10000000000 : ℝ)^8389 ≤ (17308364416837/50000000000000 : ℝ)^6341 := by
    have hnat : (4484972327 : ℕ)^8389*50000000000000^6341 ≤ 17308364416837^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484972327 10000000000 17308364416837 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357122979/10000000000 : ℝ), (4232857327/10000000000 : ℝ), (4484972327/10000000000 : ℝ)] ![(3331727671381/10000000000000 : ℝ), (16032997222299/50000000000000 : ℝ), (17308364416837/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357122979/10000000000 : ℝ)|^8389 ≤ (3331727671381/10000000000000 : ℝ)^6341
        have hw : |(4357122979/10000000000 : ℝ)|=(4357122979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4232857327/10000000000 : ℝ)|^8389 ≤ (16032997222299/50000000000000 : ℝ)^6341
        have hw : |(4232857327/10000000000 : ℝ)|=(4232857327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4484972327/10000000000 : ℝ)|^8389 ≤ (17308364416837/50000000000000 : ℝ)^6341
        have hw : |(4484972327/10000000000 : ℝ)|=(4484972327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s8_4 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-16729169/78125000 : ℝ)*x 0 + (1316731829/2500000000 : ℝ)*x 1 + (2695845071/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16729169/78125000 : ℝ)^8389 ≤ (13016987071613/100000000000000 : ℝ)^6341 := by
    have hnat : (16729169 : ℕ)^8389*100000000000000^6341 ≤ 13016987071613^6341*78125000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16729169 78125000 13016987071613 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316731829/2500000000 : ℝ)^8389 ≤ (8563604784123/20000000000000 : ℝ)^6341 := by
    have hnat : (1316731829 : ℕ)^8389*20000000000000^6341 ≤ 8563604784123^6341*2500000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316731829 2500000000 8563604784123 20000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695845071/5000000000 : ℝ)^8389 ≤ (22082494496181/50000000000000 : ℝ)^6341 := by
    have hnat : (2695845071 : ℕ)^8389*50000000000000^6341 ≤ 22082494496181^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695845071 5000000000 22082494496181 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-16729169/78125000 : ℝ), (1316731829/2500000000 : ℝ), (2695845071/5000000000 : ℝ)] ![(13016987071613/100000000000000 : ℝ), (8563604784123/20000000000000 : ℝ), (22082494496181/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-16729169/78125000 : ℝ)|^8389 ≤ (13016987071613/100000000000000 : ℝ)^6341
        have hw : |(-16729169/78125000 : ℝ)|=(16729169/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316731829/2500000000 : ℝ)|^8389 ≤ (8563604784123/20000000000000 : ℝ)^6341
        have hw : |(1316731829/2500000000 : ℝ)|=(1316731829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695845071/5000000000 : ℝ)|^8389 ≤ (22082494496181/50000000000000 : ℝ)^6341
        have hw : |(2695845071/5000000000 : ℝ)|=(2695845071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s8_5 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312631219/10000000000 : ℝ)*x 0 + (-2079839249/10000000000 : ℝ)*x 1 + (269584507/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312631219/10000000000 : ℝ)^8389 ≤ (8662053939929/20000000000000 : ℝ)^6341 := by
    have hnat : (5312631219 : ℕ)^8389*20000000000000^6341 ≤ 8662053939929^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312631219 10000000000 8662053939929 20000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2079839249/10000000000 : ℝ)^8389 ≤ (3131185328569/25000000000000 : ℝ)^6341 := by
    have hnat : (2079839249 : ℕ)^8389*25000000000000^6341 ≤ 3131185328569^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079839249 10000000000 3131185328569 25000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269584507/500000000 : ℝ)^8389 ≤ (690077952667/1562500000000 : ℝ)^6341 := by
    have hnat : (269584507 : ℕ)^8389*1562500000000^6341 ≤ 690077952667^6341*500000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269584507 500000000 690077952667 1562500000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312631219/10000000000 : ℝ), (-2079839249/10000000000 : ℝ), (269584507/500000000 : ℝ)] ![(8662053939929/20000000000000 : ℝ), (3131185328569/25000000000000 : ℝ), (690077952667/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312631219/10000000000 : ℝ)|^8389 ≤ (8662053939929/20000000000000 : ℝ)^6341
        have hw : |(5312631219/10000000000 : ℝ)|=(5312631219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2079839249/10000000000 : ℝ)|^8389 ≤ (3131185328569/25000000000000 : ℝ)^6341
        have hw : |(-2079839249/10000000000 : ℝ)|=(2079839249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269584507/500000000 : ℝ)|^8389 ≤ (690077952667/1562500000000 : ℝ)^6341
        have hw : |(269584507/500000000 : ℝ)|=(269584507/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s8_6 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312631221/10000000000 : ℝ)*x 0 + (1347922539/2500000000 : ℝ)*x 1 + (-1039919613/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312631221/10000000000 : ℝ)^8389 ≤ (338361482197/781250000000 : ℝ)^6341 := by
    have hnat : (5312631221 : ℕ)^8389*781250000000^6341 ≤ 338361482197^6341*10000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312631221 10000000000 338361482197 781250000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347922539/2500000000 : ℝ)^8389 ≤ (44164989144079/100000000000000 : ℝ)^6341 := by
    have hnat : (1347922539 : ℕ)^8389*100000000000000^6341 ≤ 44164989144079^6341*2500000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347922539 2500000000 44164989144079 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1039919613/5000000000 : ℝ)^8389 ≤ (3131185282759/25000000000000 : ℝ)^6341 := by
    have hnat : (1039919613 : ℕ)^8389*25000000000000^6341 ≤ 3131185282759^6341*5000000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039919613 5000000000 3131185282759 25000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312631221/10000000000 : ℝ), (1347922539/2500000000 : ℝ), (-1039919613/5000000000 : ℝ)] ![(338361482197/781250000000 : ℝ), (44164989144079/100000000000000 : ℝ), (3131185282759/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312631221/10000000000 : ℝ)|^8389 ≤ (338361482197/781250000000 : ℝ)^6341
        have hw : |(5312631221/10000000000 : ℝ)|=(5312631221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347922539/2500000000 : ℝ)|^8389 ≤ (44164989144079/100000000000000 : ℝ)^6341
        have hw : |(1347922539/2500000000 : ℝ)|=(1347922539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1039919613/5000000000 : ℝ)|^8389 ≤ (3131185282759/25000000000000 : ℝ)^6341
        have hw : |(-1039919613/5000000000 : ℝ)|=(1039919613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1196_s8_7 (p : ℝ) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1089283121/2500000000 : ℝ)*x 0 + (1121084523/2500000000 : ℝ)*x 1 + (42334939/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089283121/2500000000 : ℝ)^8389 ≤ (4164671608671/12500000000000 : ℝ)^6341 := by
    have hnat : (1089283121 : ℕ)^8389*12500000000000^6341 ≤ 4164671608671^6341*2500000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089283121 2500000000 4164671608671 12500000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1121084523/2500000000 : ℝ)^8389 ≤ (34610252652557/100000000000000 : ℝ)^6341 := by
    have hnat : (1121084523 : ℕ)^8389*100000000000000^6341 ≤ 34610252652557^6341*2500000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121084523 2500000000 34610252652557 100000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42334939/100000000 : ℝ)^8389 ≤ (16036187234097/50000000000000 : ℝ)^6341 := by
    have hnat : (42334939 : ℕ)^8389*50000000000000^6341 ≤ 16036187234097^6341*100000000^8389 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42334939 100000000 16036187234097 50000000000000 8389 6341 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8389/2048 : ℝ)) 8389 6341 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089283121/2500000000 : ℝ), (1121084523/2500000000 : ℝ), (42334939/100000000 : ℝ)] ![(4164671608671/12500000000000 : ℝ), (34610252652557/100000000000000 : ℝ), (16036187234097/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089283121/2500000000 : ℝ)|^8389 ≤ (4164671608671/12500000000000 : ℝ)^6341
        have hw : |(1089283121/2500000000 : ℝ)|=(1089283121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1121084523/2500000000 : ℝ)|^8389 ≤ (34610252652557/100000000000000 : ℝ)^6341
        have hw : |(1121084523/2500000000 : ℝ)|=(1121084523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42334939/100000000 : ℝ)|^8389 ≤ (16036187234097/50000000000000 : ℝ)^6341
        have hw : |(42334939/100000000 : ℝ)|=(42334939/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1196_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150528399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (88/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5711/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11423/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14079/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (88/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5711/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (88/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5711/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (88/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5711/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (88/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5711/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (88/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5711/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (88/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5711/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (5711/50000 : ℝ) ^ (2097/512 : ℝ) ≤ (13829026316113977/100000000000000000000 : ℝ) := by
    have hpowers : (5711/50000 : ℝ)^2097 ≤ (13829026316113977/100000000000000000000 : ℝ)^512 := by
      have hnat : (5711 : ℕ)^2097*100000000000000000000^512 ≤ 13829026316113977^512*50000^2097 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5711 50000 13829026316113977 100000000000000000000 2097 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5711/50000 : ℝ)) (X := (13829026316113977/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have hpowhi : (88/625 : ℝ) ^ (2097/512 : ℝ) ≤ (32578361095623589/100000000000000000000 : ℝ) := by
    have hpowers : (88/625 : ℝ)^2097 ≤ (32578361095623589/100000000000000000000 : ℝ)^512 := by
      have hnat : (88 : ℕ)^2097*100000000000000000000^512 ≤ 32578361095623589^512*625^2097 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        88 625 32578361095623589 100000000000000000000 2097 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (88/625 : ℝ)) (X := (32578361095623589/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013829026316113977/50000000000000000000 : ℝ) ≤ (2500168805949083/2500000000000000 : ℝ) ^ (2097/512 : ℝ) := by
    have hpowers : (50013829026316113977/50000000000000000000 : ℝ)^512 ≤ (2500168805949083/2500000000000000 : ℝ)^2097 := by
      have hnat : (50013829026316113977 : ℕ)^512*2500000000000000^2097 ≤ 2500168805949083^2097*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013829026316113977 50000000000000000000 2500168805949083 2500000000000000 512 2097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500168805949083/2500000000000000 : ℝ)) (X := (50013829026316113977/50000000000000000000 : ℝ)) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023203693705868783/50000000000000000000 : ℝ) ≤ (10001132876312811/10000000000000000 : ℝ) ^ (2097/512 : ℝ) := by
    have hpowers : (50023203693705868783/50000000000000000000 : ℝ)^512 ≤ (10001132876312811/10000000000000000 : ℝ)^2097 := by
      have hnat : (50023203693705868783 : ℕ)^512*10000000000000000^2097 ≤ 10001132876312811^2097*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023203693705868783 50000000000000000000 10001132876312811 10000000000000000 512 2097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001132876312811/10000000000000000 : ℝ)) (X := (50023203693705868783/50000000000000000000 : ℝ)) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032578361095623589/50000000000000000000 : ℝ) ≤ (1000159052882929/1000000000000000 : ℝ) ^ (2097/512 : ℝ) := by
    have hpowers : (50032578361095623589/50000000000000000000 : ℝ)^512 ≤ (1000159052882929/1000000000000000 : ℝ)^2097 := by
      have hnat : (50032578361095623589 : ℕ)^512*1000000000000000^2097 ≤ 1000159052882929^2097*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032578361095623589 50000000000000000000 1000159052882929 1000000000000000 512 2097 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000159052882929/1000000000000000 : ℝ)) (X := (50032578361095623589/50000000000000000000 : ℝ)) (by norm_num) 2097 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13829026316113977/100000000000000000000 : ℝ) ≤ ((1328567006538210209/1329000000000000000 : ℝ)+2*(457652516479/265800000000000 : ℝ)*(5711/50000 : ℝ))^(2097/512 : ℝ) := by
    rw [show (1328567006538210209/1329000000000000000 : ℝ)+2*(457652516479/265800000000000 : ℝ)*(5711/50000 : ℝ)=(2500168805949083/2500000000000000 : ℝ) by norm_num, show 1+2*(13829026316113977/100000000000000000000 : ℝ)=(50013829026316113977/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32578361095623589/100000000000000000000 : ℝ)+(13829026316113977/100000000000000000000 : ℝ) ≤ ((1328567006538210209/1329000000000000000 : ℝ)+(457652516479/265800000000000 : ℝ)*((88/625 : ℝ)+(5711/50000 : ℝ)))^(2097/512 : ℝ) := by
    rw [show (1328567006538210209/1329000000000000000 : ℝ)+(457652516479/265800000000000 : ℝ)*((88/625 : ℝ)+(5711/50000 : ℝ))=(10001132876312811/10000000000000000 : ℝ) by norm_num, show 1+(32578361095623589/100000000000000000000 : ℝ)+(13829026316113977/100000000000000000000 : ℝ)=(50023203693705868783/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32578361095623589/100000000000000000000 : ℝ) ≤ ((1328567006538210209/1329000000000000000 : ℝ)+2*(457652516479/265800000000000 : ℝ)*(88/625 : ℝ))^(2097/512 : ℝ) := by
    rw [show (1328567006538210209/1329000000000000000 : ℝ)+2*(457652516479/265800000000000 : ℝ)*(88/625 : ℝ)=(1000159052882929/1000000000000000 : ℝ) by norm_num, show 1+2*(32578361095623589/100000000000000000000 : ℝ)=(50032578361095623589/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1328567006538210209/1329000000000000000 : ℝ)*(X 1 0+X 2 0)+(457652516479/265800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2097/512 : ℝ)) (lo := (5711/50000 : ℝ)) (hi := (88/625 : ℝ)) (c := (1328567006538210209/1329000000000000000 : ℝ)) (alpha := (457652516479/265800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1328567006538210209/1329000000000000000 : ℝ)*(X 0 1+X 2 1)+(457652516479/265800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2097/512 : ℝ)) (lo := (5711/50000 : ℝ)) (hi := (88/625 : ℝ)) (c := (1328567006538210209/1329000000000000000 : ℝ)) (alpha := (457652516479/265800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1328567006538210209/1329000000000000000 : ℝ)*(X 0 2+X 1 2)+(457652516479/265800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2097/512 : ℝ)) (lo := (5711/50000 : ℝ)) (hi := (88/625 : ℝ)) (c := (1328567006538210209/1329000000000000000 : ℝ)) (alpha := (457652516479/265800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-85653153/400000000 : ℝ)*X 0 0+(134800169/250000000 : ℝ)*X 0 1+(5266611883/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344524949/10000000000 : ℝ)*X 1 0+(-1102458767/5000000000 : ℝ)*X 1 1+(5266611843/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344524943/10000000000 : ℝ)*X 2 0+(5266611849/10000000000 : ℝ)*X 2 1+(-1102458767/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4357122979/10000000000 : ℝ)*X 0 0+(4232857327/10000000000 : ℝ)*X 0 1+(4484972327/10000000000 : ℝ)*X 0 2+(4357122979/10000000000 : ℝ)*X 1 0+(4232857327/10000000000 : ℝ)*X 1 1+(4484972327/10000000000 : ℝ)*X 1 2+(4357122979/10000000000 : ℝ)*X 2 0+(4232857327/10000000000 : ℝ)*X 2 1+(4484972327/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-16729169/78125000 : ℝ)*X 0 0+(1316731829/2500000000 : ℝ)*X 0 1+(2695845071/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312631219/10000000000 : ℝ)*X 1 0+(-2079839249/10000000000 : ℝ)*X 1 1+(269584507/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312631221/10000000000 : ℝ)*X 2 0+(1347922539/2500000000 : ℝ)*X 2 1+(-1039919613/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1089283121/2500000000 : ℝ)*X 0 0+(1121084523/2500000000 : ℝ)*X 0 1+(42334939/100000000 : ℝ)*X 0 2+(1089283121/2500000000 : ℝ)*X 1 0+(1121084523/2500000000 : ℝ)*X 1 1+(42334939/100000000 : ℝ)*X 1 2+(1089283121/2500000000 : ℝ)*X 2 0+(1121084523/2500000000 : ℝ)*X 2 1+(42334939/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1196_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22157963793522146125739817/5537500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (810520297/100000000000000 : ℝ)*(base19) + (17456433/2500000000000 : ℝ)*(base23) + (55214319/100000000000000 : ℝ)*(lower2) + (114078261/100000000000000 : ℝ)*(upper3) + (9082881/25000000000000 : ℝ)*(upper5) + (2985328249893087/50000000000000 : ℝ)*(major0) + (2985328249893087/50000000000000 : ℝ)*(major1) + (2985328249893087/50000000000000 : ℝ)*(major2) + (7974828705873121/100000000000000 : ℝ)*(sp0) + (3987423448650719/50000000000000 : ℝ)*(sp1) + (1594969401912883/20000000000000 : ℝ)*(sp2) + (3966453441038901/100000000000000 : ℝ)*(sp3) + (3800389723/20000000000000 : ℝ)*(sp4) + (5858665217/50000000000000 : ℝ)*(sp7) + (793293031673867/20000000000000 : ℝ)*(f.failure) + (1594969541564347/20000000000000 : ℝ)*(f.sum) + (6428744733559/2215000000000000000000000000 : ℝ)*base66 + (74503847290180061/22150000000000000000000000000000 : ℝ)*base67 + (130435686218430061/22150000000000000000000000000000 : ℝ)*base69 + (176817666674880061/22150000000000000000000000000000 : ℝ)*base71 + (2212971216673/1107500000000000000000000000 : ℝ)*base73 + (111015007867280061/22150000000000000000000000000000 : ℝ)*base75 + (30686339353569939/22150000000000000000000000000000 : ℝ)*base78 + (369949672314930061/22150000000000000000000000000000 : ℝ)*base79 + (549669520059/553750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (9648933/2000000000000000000000 : ℝ)*base89 + (9648933/2000000000000000000000 : ℝ)*base91 + (9648933/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (64875400476428318861146903/11075000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (230428957/20000000000000 : ℝ)*(base19) + (1180091721/100000000000000 : ℝ)*(base23) + (392724333/100000000000000 : ℝ)*(lower1) + (136616639/100000000000000 : ℝ)*(upper3) + (1223219/25000000000000 : ℝ)*(lower4) + (29466367/25000000000000 : ℝ)*(upper5) + (6000849454125667/100000000000000 : ℝ)*(major0) + (6000849454125667/100000000000000 : ℝ)*(major1) + (6000849454125667/100000000000000 : ℝ)*(major2) + (2618465971/100000000000000 : ℝ)*(sp2) + (8015175575834397/100000000000000 : ℝ)*(sp4) + (2003793605922403/25000000000000 : ℝ)*(sp5) + (4007585888638353/50000000000000 : ℝ)*(sp6) + (3986523137156111/100000000000000 : ℝ)*(sp7) + (3986523137156111/100000000000000 : ℝ)*(f.failure) + (8015175575834397/100000000000000 : ℝ)*(f.sum) + (48970467541307/13290000000000000000000000000 : ℝ)*base66 + (4125799909535199403/132900000000000000000000000000000 : ℝ)*base67 + (2329321688733800597/132900000000000000000000000000000 : ℝ)*base70 + (4007605412360000597/132900000000000000000000000000000 : ℝ)*base72 + (59842073004467/13290000000000000000000000000 : ℝ)*base74 + (15846768251301200597/132900000000000000000000000000000 : ℝ)*base76 + (709114548377900597/132900000000000000000000000000000 : ℝ)*base78 + (4412826812037500597/132900000000000000000000000000000 : ℝ)*base80 + (64552301594207/13290000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (101896289/10000000000000000000000 : ℝ)*base89 + (101896289/10000000000000000000000 : ℝ)*base91 + (101896289/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1196_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150528399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (88/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5711/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11423/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14079/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1196_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1196_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150528399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14111/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (356/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11423/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14079/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1196_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1196_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1196_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2097/512 : ℝ) ≤ p) (hpb : p ≤ (8389/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150528399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14111/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (356/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11423/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14079/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1196_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
