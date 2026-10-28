-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1033_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:41:36.694971+00:00
-- url     : https://prove2.me/submissions/74b0f628-9857-42e1-98fc-dbf8f68a70e6

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
theorem support_rectangle_w1033_s9_0 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1110062377/5000000000 : ℝ)*x 0 + (2697451823/5000000000 : ℝ)*x 1 + (13159631/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1110062377/5000000000 : ℝ)^4113 ≤ (13480382675283/100000000000000 : ℝ)^3089 := by
    have hnat : (1110062377 : ℕ)^4113*100000000000000^3089 ≤ 13480382675283^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1110062377 5000000000 13480382675283 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697451823/5000000000 : ℝ)^4113 ≤ (43967987770777/100000000000000 : ℝ)^3089 := by
    have hnat : (2697451823 : ℕ)^4113*100000000000000^3089 ≤ 43967987770777^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697451823 5000000000 43967987770777 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13159631/25000000 : ℝ)^4113 ≤ (42551629545479/100000000000000 : ℝ)^3089 := by
    have hnat : (13159631 : ℕ)^4113*100000000000000^3089 ≤ 42551629545479^3089*25000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13159631 25000000 42551629545479 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1110062377/5000000000 : ℝ), (2697451823/5000000000 : ℝ), (13159631/25000000 : ℝ)] ![(13480382675283/100000000000000 : ℝ), (43967987770777/100000000000000 : ℝ), (42551629545479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1110062377/5000000000 : ℝ)|^4113 ≤ (13480382675283/100000000000000 : ℝ)^3089
        have hw : |(-1110062377/5000000000 : ℝ)|=(1110062377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697451823/5000000000 : ℝ)|^4113 ≤ (43967987770777/100000000000000 : ℝ)^3089
        have hw : |(2697451823/5000000000 : ℝ)|=(2697451823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(13159631/25000000 : ℝ)|^4113 ≤ (42551629545479/100000000000000 : ℝ)^3089
        have hw : |(13159631/25000000 : ℝ)|=(13159631/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s9_1 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672519223/5000000000 : ℝ)*x 0 + (-45732499/200000000 : ℝ)*x 1 + (5263852257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672519223/5000000000 : ℝ)^4113 ≤ (43427701382723/100000000000000 : ℝ)^3089 := by
    have hnat : (2672519223 : ℕ)^4113*100000000000000^3089 ≤ 43427701382723^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672519223 5000000000 43427701382723 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (45732499/200000000 : ℝ)^4113 ≤ (14020670590377/100000000000000 : ℝ)^3089 := by
    have hnat : (45732499 : ℕ)^4113*100000000000000^3089 ≤ 14020670590377^3089*200000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45732499 200000000 14020670590377 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263852257/10000000000 : ℝ)^4113 ≤ (42551628006299/100000000000000 : ℝ)^3089 := by
    have hnat : (5263852257 : ℕ)^4113*100000000000000^3089 ≤ 42551628006299^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263852257 10000000000 42551628006299 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672519223/5000000000 : ℝ), (-45732499/200000000 : ℝ), (5263852257/10000000000 : ℝ)] ![(43427701382723/100000000000000 : ℝ), (14020670590377/100000000000000 : ℝ), (42551628006299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672519223/5000000000 : ℝ)|^4113 ≤ (43427701382723/100000000000000 : ℝ)^3089
        have hw : |(2672519223/5000000000 : ℝ)|=(2672519223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-45732499/200000000 : ℝ)|^4113 ≤ (14020670590377/100000000000000 : ℝ)^3089
        have hw : |(-45732499/200000000 : ℝ)|=(45732499/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263852257/10000000000 : ℝ)|^4113 ≤ (42551628006299/100000000000000 : ℝ)^3089
        have hw : |(5263852257/10000000000 : ℝ)|=(5263852257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s9_2 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345038357/10000000000 : ℝ)*x 0 + (1052770467/2000000000 : ℝ)*x 1 + (-1143312483/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345038357/10000000000 : ℝ)^4113 ≤ (434277004199/1000000000000 : ℝ)^3089 := by
    have hnat : (5345038357 : ℕ)^4113*1000000000000^3089 ≤ 434277004199^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345038357 10000000000 434277004199 1000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052770467/2000000000 : ℝ)^4113 ≤ (10637907211463/25000000000000 : ℝ)^3089 := by
    have hnat : (1052770467 : ℕ)^4113*25000000000000^3089 ≤ 10637907211463^3089*2000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052770467 2000000000 10637907211463 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1143312483/5000000000 : ℝ)^4113 ≤ (3505167680251/25000000000000 : ℝ)^3089 := by
    have hnat : (1143312483 : ℕ)^4113*25000000000000^3089 ≤ 3505167680251^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1143312483 5000000000 3505167680251 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345038357/10000000000 : ℝ), (1052770467/2000000000 : ℝ), (-1143312483/5000000000 : ℝ)] ![(434277004199/1000000000000 : ℝ), (10637907211463/25000000000000 : ℝ), (3505167680251/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345038357/10000000000 : ℝ)|^4113 ≤ (434277004199/1000000000000 : ℝ)^3089
        have hw : |(5345038357/10000000000 : ℝ)|=(5345038357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052770467/2000000000 : ℝ)|^4113 ≤ (10637907211463/25000000000000 : ℝ)^3089
        have hw : |(1052770467/2000000000 : ℝ)|=(1052770467/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1143312483/5000000000 : ℝ)|^4113 ≤ (3505167680251/25000000000000 : ℝ)^3089
        have hw : |(-1143312483/5000000000 : ℝ)|=(1143312483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s9_3 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2190130397/5000000000 : ℝ)*x 0 + (425457741/1000000000 : ℝ)*x 1 + (2254869361/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2190130397/5000000000 : ℝ)^4113 ≤ (16658182610167/50000000000000 : ℝ)^3089 := by
    have hnat : (2190130397 : ℕ)^4113*50000000000000^3089 ≤ 16658182610167^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190130397 5000000000 16658182610167 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (425457741/1000000000 : ℝ)^4113 ≤ (32049610571763/100000000000000 : ℝ)^3089 := by
    have hnat : (425457741 : ℕ)^4113*100000000000000^3089 ≤ 32049610571763^3089*1000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425457741 1000000000 32049610571763 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2254869361/5000000000 : ℝ)^4113 ≤ (6926804836771/20000000000000 : ℝ)^3089 := by
    have hnat : (2254869361 : ℕ)^4113*20000000000000^3089 ≤ 6926804836771^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254869361 5000000000 6926804836771 20000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2190130397/5000000000 : ℝ), (425457741/1000000000 : ℝ), (2254869361/5000000000 : ℝ)] ![(16658182610167/50000000000000 : ℝ), (32049610571763/100000000000000 : ℝ), (6926804836771/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2190130397/5000000000 : ℝ)|^4113 ≤ (16658182610167/50000000000000 : ℝ)^3089
        have hw : |(2190130397/5000000000 : ℝ)|=(2190130397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(425457741/1000000000 : ℝ)|^4113 ≤ (32049610571763/100000000000000 : ℝ)^3089
        have hw : |(425457741/1000000000 : ℝ)|=(425457741/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2254869361/5000000000 : ℝ)|^4113 ≤ (6926804836771/20000000000000 : ℝ)^3089
        have hw : |(2254869361/5000000000 : ℝ)|=(2254869361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s9_4 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2220130047/10000000000 : ℝ)*x 0 + (5264180009/10000000000 : ℝ)*x 1 + (2697287373/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2220130047/10000000000 : ℝ)^4113 ≤ (13480425467787/100000000000000 : ℝ)^3089 := by
    have hnat : (2220130047 : ℕ)^4113*100000000000000^3089 ≤ 13480425467787^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2220130047 10000000000 13480425467787 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264180009/10000000000 : ℝ)^4113 ≤ (21277577899767/50000000000000 : ℝ)^3089 := by
    have hnat : (5264180009 : ℕ)^4113*50000000000000^3089 ≤ 21277577899767^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264180009 10000000000 21277577899767 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697287373/5000000000 : ℝ)^4113 ≤ (10991104679061/25000000000000 : ℝ)^3089 := by
    have hnat : (2697287373 : ℕ)^4113*25000000000000^3089 ≤ 10991104679061^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697287373 5000000000 10991104679061 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2220130047/10000000000 : ℝ), (5264180009/10000000000 : ℝ), (2697287373/5000000000 : ℝ)] ![(13480425467787/100000000000000 : ℝ), (21277577899767/50000000000000 : ℝ), (10991104679061/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2220130047/10000000000 : ℝ)|^4113 ≤ (13480425467787/100000000000000 : ℝ)^3089
        have hw : |(-2220130047/10000000000 : ℝ)|=(2220130047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264180009/10000000000 : ℝ)|^4113 ≤ (21277577899767/50000000000000 : ℝ)^3089
        have hw : |(5264180009/10000000000 : ℝ)|=(5264180009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697287373/5000000000 : ℝ)|^4113 ≤ (10991104679061/25000000000000 : ℝ)^3089
        have hw : |(2697287373/5000000000 : ℝ)|=(2697287373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s9_5 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4380270887/10000000000 : ℝ)*x 0 + (2254550203/5000000000 : ℝ)*x 1 + (1063804487/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4380270887/10000000000 : ℝ)^4113 ≤ (6663293487267/20000000000000 : ℝ)^3089 := by
    have hnat : (4380270887 : ℕ)^4113*20000000000000^3089 ≤ 6663293487267^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4380270887 10000000000 6663293487267 20000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2254550203/5000000000 : ℝ)^4113 ≤ (34627497119161/100000000000000 : ℝ)^3089 := by
    have hnat : (2254550203 : ℕ)^4113*100000000000000^3089 ≤ 34627497119161^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254550203 5000000000 34627497119161 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1063804487/2500000000 : ℝ)^4113 ≤ (32056035419867/100000000000000 : ℝ)^3089 := by
    have hnat : (1063804487 : ℕ)^4113*100000000000000^3089 ≤ 32056035419867^3089*2500000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063804487 2500000000 32056035419867 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4380270887/10000000000 : ℝ), (2254550203/5000000000 : ℝ), (1063804487/2500000000 : ℝ)] ![(6663293487267/20000000000000 : ℝ), (34627497119161/100000000000000 : ℝ), (32056035419867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4380270887/10000000000 : ℝ)|^4113 ≤ (6663293487267/20000000000000 : ℝ)^3089
        have hw : |(4380270887/10000000000 : ℝ)|=(4380270887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2254550203/5000000000 : ℝ)|^4113 ≤ (34627497119161/100000000000000 : ℝ)^3089
        have hw : |(2254550203/5000000000 : ℝ)|=(2254550203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1063804487/2500000000 : ℝ)|^4113 ≤ (32056035419867/100000000000000 : ℝ)^3089
        have hw : |(1063804487/2500000000 : ℝ)|=(1063804487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1033_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18418937/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6991/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2241/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5603/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6991/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6991/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2241/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6991/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2241/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6991/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2241/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6991/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2241/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6991/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2241/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6991/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2241/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2241/20000 : ℝ) ^ (8225/2048 : ℝ) ≤ (152170458593891/1000000000000000000 : ℝ) := by
    have hpowers : (2241/20000 : ℝ)^8225 ≤ (152170458593891/1000000000000000000 : ℝ)^2048 := by
      have hnat : (2241 : ℕ)^8225*1000000000000000000^2048 ≤ 152170458593891^2048*20000^8225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2241 20000 152170458593891 1000000000000000000 8225 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2241/20000 : ℝ)) (X := (152170458593891/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (6991/50000 : ℝ) ^ (8225/2048 : ℝ) ≤ (37026231227375029/100000000000000000000 : ℝ) := by
    have hpowers : (6991/50000 : ℝ)^8225 ≤ (37026231227375029/100000000000000000000 : ℝ)^2048 := by
      have hnat : (6991 : ℕ)^8225*100000000000000000000^2048 ≤ 37026231227375029^2048*50000^8225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6991 50000 37026231227375029 100000000000000000000 8225 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6991/50000 : ℝ)) (X := (37026231227375029/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (500152170458593891/500000000000000000 : ℝ) ≤ (10000757713046991/10000000000000000 : ℝ) ^ (8225/2048 : ℝ) := by
    have hpowers : (500152170458593891/500000000000000000 : ℝ)^2048 ≤ (10000757713046991/10000000000000000 : ℝ)^8225 := by
      have hnat : (500152170458593891 : ℕ)^2048*10000000000000000^8225 ≤ 10000757713046991^8225*500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500152170458593891 500000000000000000 10000757713046991 10000000000000000 2048 8225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000757713046991/10000000000000000 : ℝ)) (X := (500152170458593891/500000000000000000 : ℝ)) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052243277086764129/100000000000000000000 : ℝ) ≤ (10001300586606119/10000000000000000 : ℝ) ^ (8225/2048 : ℝ) := by
    have hpowers : (100052243277086764129/100000000000000000000 : ℝ)^2048 ≤ (10001300586606119/10000000000000000 : ℝ)^8225 := by
      have hnat : (100052243277086764129 : ℕ)^2048*10000000000000000^8225 ≤ 10001300586606119^8225*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052243277086764129 100000000000000000000 10001300586606119 10000000000000000 2048 8225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001300586606119/10000000000000000 : ℝ)) (X := (100052243277086764129/100000000000000000000 : ℝ)) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50037026231227375029/50000000000000000000 : ℝ) ≤ (10001843460165247/10000000000000000 : ℝ) ^ (8225/2048 : ℝ) := by
    have hpowers : (50037026231227375029/50000000000000000000 : ℝ)^2048 ≤ (10001843460165247/10000000000000000 : ℝ)^8225 := by
      have hnat : (50037026231227375029 : ℕ)^2048*10000000000000000^8225 ≤ 10001843460165247^8225*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037026231227375029 50000000000000000000 10001843460165247 10000000000000000 2048 8225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001843460165247/10000000000000000 : ℝ)) (X := (50037026231227375029/50000000000000000000 : ℝ)) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(152170458593891/1000000000000000000 : ℝ) ≤ ((27759938372671435527/27770000000000000000 : ℝ)+2*(67859194891/34712500000000 : ℝ)*(2241/20000 : ℝ))^(8225/2048 : ℝ) := by
    rw [show (27759938372671435527/27770000000000000000 : ℝ)+2*(67859194891/34712500000000 : ℝ)*(2241/20000 : ℝ)=(10000757713046991/10000000000000000 : ℝ) by norm_num, show 1+2*(152170458593891/1000000000000000000 : ℝ)=(500152170458593891/500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37026231227375029/100000000000000000000 : ℝ)+(152170458593891/1000000000000000000 : ℝ) ≤ ((27759938372671435527/27770000000000000000 : ℝ)+(67859194891/34712500000000 : ℝ)*((6991/50000 : ℝ)+(2241/20000 : ℝ)))^(8225/2048 : ℝ) := by
    rw [show (27759938372671435527/27770000000000000000 : ℝ)+(67859194891/34712500000000 : ℝ)*((6991/50000 : ℝ)+(2241/20000 : ℝ))=(10001300586606119/10000000000000000 : ℝ) by norm_num, show 1+(37026231227375029/100000000000000000000 : ℝ)+(152170458593891/1000000000000000000 : ℝ)=(100052243277086764129/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37026231227375029/100000000000000000000 : ℝ) ≤ ((27759938372671435527/27770000000000000000 : ℝ)+2*(67859194891/34712500000000 : ℝ)*(6991/50000 : ℝ))^(8225/2048 : ℝ) := by
    rw [show (27759938372671435527/27770000000000000000 : ℝ)+2*(67859194891/34712500000000 : ℝ)*(6991/50000 : ℝ)=(10001843460165247/10000000000000000 : ℝ) by norm_num, show 1+2*(37026231227375029/100000000000000000000 : ℝ)=(50037026231227375029/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27759938372671435527/27770000000000000000 : ℝ)*(X 1 0+X 2 0)+(67859194891/34712500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8225/2048 : ℝ)) (lo := (2241/20000 : ℝ)) (hi := (6991/50000 : ℝ)) (c := (27759938372671435527/27770000000000000000 : ℝ)) (alpha := (67859194891/34712500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27759938372671435527/27770000000000000000 : ℝ)*(X 0 1+X 2 1)+(67859194891/34712500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8225/2048 : ℝ)) (lo := (2241/20000 : ℝ)) (hi := (6991/50000 : ℝ)) (c := (27759938372671435527/27770000000000000000 : ℝ)) (alpha := (67859194891/34712500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27759938372671435527/27770000000000000000 : ℝ)*(X 0 2+X 1 2)+(67859194891/34712500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8225/2048 : ℝ)) (lo := (2241/20000 : ℝ)) (hi := (6991/50000 : ℝ)) (c := (27759938372671435527/27770000000000000000 : ℝ)) (alpha := (67859194891/34712500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1110062377/5000000000 : ℝ)*X 0 0+(2697451823/5000000000 : ℝ)*X 0 1+(13159631/25000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672519223/5000000000 : ℝ)*X 1 0+(-45732499/200000000 : ℝ)*X 1 1+(5263852257/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345038357/10000000000 : ℝ)*X 2 0+(1052770467/2000000000 : ℝ)*X 2 1+(-1143312483/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2190130397/5000000000 : ℝ)*X 0 0+(425457741/1000000000 : ℝ)*X 0 1+(2254869361/5000000000 : ℝ)*X 0 2+(2190130397/5000000000 : ℝ)*X 1 0+(425457741/1000000000 : ℝ)*X 1 1+(2254869361/5000000000 : ℝ)*X 1 2+(2190130397/5000000000 : ℝ)*X 2 0+(425457741/1000000000 : ℝ)*X 2 1+(2254869361/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2220130047/10000000000 : ℝ)*X 0 0+(5264180009/10000000000 : ℝ)*X 0 1+(2697287373/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4380270887/10000000000 : ℝ)*X 0 0+(2254550203/5000000000 : ℝ)*X 0 1+(1063804487/2500000000 : ℝ)*X 0 2+(4380270887/10000000000 : ℝ)*X 1 0+(2254550203/5000000000 : ℝ)*X 1 1+(1063804487/2500000000 : ℝ)*X 1 2+(4380270887/10000000000 : ℝ)*X 2 0+(2254550203/5000000000 : ℝ)*X 2 1+(1063804487/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (324120133119823721604894843/86781250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (53705379/12500000000000 : ℝ)*(base19) + (4438891/1250000000000 : ℝ)*(base23) + (41778633/100000000000000 : ℝ)*(lower2) + (9507227/100000000000000 : ℝ)*(upper3) + (8731703/12500000000000 : ℝ)*(lower4) + (721857832688353/12500000000000 : ℝ)*(major0) + (721857832688353/12500000000000 : ℝ)*(major1) + (721857832688353/12500000000000 : ℝ)*(major2) + (1526122359405193/20000000000000 : ℝ)*(sp0) + (7630617859021261/100000000000000 : ℝ)*(sp1) + (7630617933553013/100000000000000 : ℝ)*(sp2) + (3919098534261373/100000000000000 : ℝ)*(sp3) + (811454791/12500000000000 : ℝ)*(sp4) + (2093897747/25000000000000 : ℝ)*(sp5) + (97977672746309/2500000000000 : ℝ)*(f.failure) + (7630618288664293/100000000000000 : ℝ)*(f.sum) + (10805780421737/3471250000000000000000000000 : ℝ)*base66 + (950589435358282969/347125000000000000000000000000000 : ℝ)*base68 + (2522194477281532969/347125000000000000000000000000000 : ℝ)*base70 + (1997066660501782969/347125000000000000000000000000000 : ℝ)*base72 + (3879462058723/3471250000000000000000000000 : ℝ)*base73 + (2315240422938157969/347125000000000000000000000000000 : ℝ)*base76 + (154580975048842031/347125000000000000000000000000000 : ℝ)*base77 + (907331416620907969/347125000000000000000000000000000 : ℝ)*base80 + (330968887313/3471250000000000000000000000 : ℝ)*base81 + (46467/31250000000000000000 : ℝ)*base90 + (46467/31250000000000000000 : ℝ)*base92 + (46467/31250000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1033_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18418937/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6991/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2241/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5603/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6991/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1033_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1033_s10_0 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345038631/10000000000 : ℝ)*x 0 + (5263858251/10000000000 : ℝ)*x 1 + (-2286616803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345038631/10000000000 : ℝ)^4113 ≤ (43427703384099/100000000000000 : ℝ)^3089 := by
    have hnat : (5345038631 : ℕ)^4113*100000000000000^3089 ≤ 43427703384099^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345038631 10000000000 43427703384099 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263858251/10000000000 : ℝ)^4113 ≤ (42551692522697/100000000000000 : ℝ)^3089 := by
    have hnat : (5263858251 : ℕ)^4113*100000000000000^3089 ≤ 42551692522697^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263858251 10000000000 42551692522697 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2286616803/10000000000 : ℝ)^4113 ≤ (14020604076523/100000000000000 : ℝ)^3089 := by
    have hnat : (2286616803 : ℕ)^4113*100000000000000^3089 ≤ 14020604076523^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2286616803 10000000000 14020604076523 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345038631/10000000000 : ℝ), (5263858251/10000000000 : ℝ), (-2286616803/10000000000 : ℝ)] ![(43427703384099/100000000000000 : ℝ), (42551692522697/100000000000000 : ℝ), (14020604076523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345038631/10000000000 : ℝ)|^4113 ≤ (43427703384099/100000000000000 : ℝ)^3089
        have hw : |(5345038631/10000000000 : ℝ)|=(5345038631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263858251/10000000000 : ℝ)|^4113 ≤ (42551692522697/100000000000000 : ℝ)^3089
        have hw : |(5263858251/10000000000 : ℝ)|=(5263858251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2286616803/10000000000 : ℝ)|^4113 ≤ (14020604076523/100000000000000 : ℝ)^3089
        have hw : |(-2286616803/10000000000 : ℝ)|=(2286616803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s10_1 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2220126921/10000000000 : ℝ)*x 0 + (5264186079/10000000000 : ℝ)*x 1 + (2697285527/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2220126921/10000000000 : ℝ)^4113 ≤ (134804001949/1000000000000 : ℝ)^3089 := by
    have hnat : (2220126921 : ℕ)^4113*1000000000000^3089 ≤ 134804001949^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2220126921 10000000000 134804001949 1000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264186079/10000000000 : ℝ)^4113 ≤ (21277610567653/50000000000000 : ℝ)^3089 := by
    have hnat : (5264186079 : ℕ)^4113*50000000000000^3089 ≤ 21277610567653^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264186079 10000000000 21277610567653 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697285527/5000000000 : ℝ)^4113 ≤ (21982189326479/50000000000000 : ℝ)^3089 := by
    have hnat : (2697285527 : ℕ)^4113*50000000000000^3089 ≤ 21982189326479^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697285527 5000000000 21982189326479 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2220126921/10000000000 : ℝ), (5264186079/10000000000 : ℝ), (2697285527/5000000000 : ℝ)] ![(134804001949/1000000000000 : ℝ), (21277610567653/50000000000000 : ℝ), (21982189326479/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2220126921/10000000000 : ℝ)|^4113 ≤ (134804001949/1000000000000 : ℝ)^3089
        have hw : |(-2220126921/10000000000 : ℝ)|=(2220126921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264186079/10000000000 : ℝ)|^4113 ≤ (21277610567653/50000000000000 : ℝ)^3089
        have hw : |(5264186079/10000000000 : ℝ)|=(5264186079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697285527/5000000000 : ℝ)|^4113 ≤ (21982189326479/50000000000000 : ℝ)^3089
        have hw : |(2697285527/5000000000 : ℝ)|=(2697285527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s10_2 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312119451/10000000000 : ℝ)*x 0 + (-2155904121/10000000000 : ℝ)*x 1 + (2697285527/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312119451/10000000000 : ℝ)^4113 ≤ (43071939670583/100000000000000 : ℝ)^3089 := by
    have hnat : (5312119451 : ℕ)^4113*100000000000000^3089 ≤ 43071939670583^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312119451 10000000000 43071939670583 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2155904121/10000000000 : ℝ)^4113 ≤ (3240920415913/25000000000000 : ℝ)^3089 := by
    have hnat : (2155904121 : ℕ)^4113*25000000000000^3089 ≤ 3240920415913^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155904121 10000000000 3240920415913 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697285527/5000000000 : ℝ)^4113 ≤ (21982189326479/50000000000000 : ℝ)^3089 := by
    have hnat : (2697285527 : ℕ)^4113*50000000000000^3089 ≤ 21982189326479^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697285527 5000000000 21982189326479 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312119451/10000000000 : ℝ), (-2155904121/10000000000 : ℝ), (2697285527/5000000000 : ℝ)] ![(43071939670583/100000000000000 : ℝ), (3240920415913/25000000000000 : ℝ), (21982189326479/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312119451/10000000000 : ℝ)|^4113 ≤ (43071939670583/100000000000000 : ℝ)^3089
        have hw : |(5312119451/10000000000 : ℝ)|=(5312119451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2155904121/10000000000 : ℝ)|^4113 ≤ (3240920415913/25000000000000 : ℝ)^3089
        have hw : |(-2155904121/10000000000 : ℝ)|=(2155904121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697285527/5000000000 : ℝ)|^4113 ≤ (21982189326479/50000000000000 : ℝ)^3089
        have hw : |(2697285527/5000000000 : ℝ)|=(2697285527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s10_3 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312119451/10000000000 : ℝ)*x 0 + (2697285527/5000000000 : ℝ)*x 1 + (-2155904121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312119451/10000000000 : ℝ)^4113 ≤ (43071939670583/100000000000000 : ℝ)^3089 := by
    have hnat : (5312119451 : ℕ)^4113*100000000000000^3089 ≤ 43071939670583^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312119451 10000000000 43071939670583 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697285527/5000000000 : ℝ)^4113 ≤ (21982189326479/50000000000000 : ℝ)^3089 := by
    have hnat : (2697285527 : ℕ)^4113*50000000000000^3089 ≤ 21982189326479^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697285527 5000000000 21982189326479 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2155904121/10000000000 : ℝ)^4113 ≤ (3240920415913/25000000000000 : ℝ)^3089 := by
    have hnat : (2155904121 : ℕ)^4113*25000000000000^3089 ≤ 3240920415913^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155904121 10000000000 3240920415913 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312119451/10000000000 : ℝ), (2697285527/5000000000 : ℝ), (-2155904121/10000000000 : ℝ)] ![(43071939670583/100000000000000 : ℝ), (21982189326479/50000000000000 : ℝ), (3240920415913/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312119451/10000000000 : ℝ)|^4113 ≤ (43071939670583/100000000000000 : ℝ)^3089
        have hw : |(5312119451/10000000000 : ℝ)|=(5312119451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697285527/5000000000 : ℝ)|^4113 ≤ (21982189326479/50000000000000 : ℝ)^3089
        have hw : |(2697285527/5000000000 : ℝ)|=(2697285527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2155904121/10000000000 : ℝ)|^4113 ≤ (3240920415913/25000000000000 : ℝ)^3089
        have hw : |(-2155904121/10000000000 : ℝ)|=(2155904121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s10_4 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2190135567/5000000000 : ℝ)*x 0 + (4509090869/10000000000 : ℝ)*x 1 + (4255227421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2190135567/5000000000 : ℝ)^4113 ≤ (2082279371113/6250000000000 : ℝ)^3089 := by
    have hnat : (2190135567 : ℕ)^4113*6250000000000^3089 ≤ 2082279371113^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190135567 5000000000 2082279371113 6250000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4509090869/10000000000 : ℝ)^4113 ≤ (34627399601421/100000000000000 : ℝ)^3089 := by
    have hnat : (4509090869 : ℕ)^4113*100000000000000^3089 ≤ 34627399601421^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4509090869 10000000000 34627399601421 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4255227421/10000000000 : ℝ)^4113 ≤ (32056130440189/100000000000000 : ℝ)^3089 := by
    have hnat : (4255227421 : ℕ)^4113*100000000000000^3089 ≤ 32056130440189^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4255227421 10000000000 32056130440189 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2190135567/5000000000 : ℝ), (4509090869/10000000000 : ℝ), (4255227421/10000000000 : ℝ)] ![(2082279371113/6250000000000 : ℝ), (34627399601421/100000000000000 : ℝ), (32056130440189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2190135567/5000000000 : ℝ)|^4113 ≤ (2082279371113/6250000000000 : ℝ)^3089
        have hw : |(2190135567/5000000000 : ℝ)|=(2190135567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4509090869/10000000000 : ℝ)|^4113 ≤ (34627399601421/100000000000000 : ℝ)^3089
        have hw : |(4509090869/10000000000 : ℝ)|=(4509090869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4255227421/10000000000 : ℝ)|^4113 ≤ (32056130440189/100000000000000 : ℝ)^3089
        have hw : |(4255227421/10000000000 : ℝ)|=(4255227421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1033_s10 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18418937/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6991/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5603/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5603/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13981/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6991/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5603/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6991/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5603/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6991/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5603/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6991/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5603/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6991/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5603/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6991/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5603/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5603/50000 : ℝ) ^ (8225/2048 : ℝ) ≤ (3044500142080191/20000000000000000000 : ℝ) := by
    have hpowers : (5603/50000 : ℝ)^8225 ≤ (3044500142080191/20000000000000000000 : ℝ)^2048 := by
      have hnat : (5603 : ℕ)^8225*20000000000000000000^2048 ≤ 3044500142080191^2048*50000^8225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5603 50000 3044500142080191 20000000000000000000 8225 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5603/50000 : ℝ)) (X := (3044500142080191/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (6991/50000 : ℝ) ^ (8225/2048 : ℝ) ≤ (37026231227375029/100000000000000000000 : ℝ) := by
    have hpowers : (6991/50000 : ℝ)^8225 ≤ (37026231227375029/100000000000000000000 : ℝ)^2048 := by
      have hnat : (6991 : ℕ)^8225*100000000000000000000^2048 ≤ 37026231227375029^2048*50000^8225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6991 50000 37026231227375029 100000000000000000000 8225 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6991/50000 : ℝ)) (X := (37026231227375029/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10003044500142080191/10000000000000000000 : ℝ) ≤ (10000757984633173/10000000000000000 : ℝ) ^ (8225/2048 : ℝ) := by
    have hpowers : (10003044500142080191/10000000000000000000 : ℝ)^2048 ≤ (10000757984633173/10000000000000000 : ℝ)^8225 := by
      have hnat : (10003044500142080191 : ℕ)^2048*10000000000000000^8225 ≤ 10000757984633173^8225*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003044500142080191 10000000000000000000 10000757984633173 10000000000000000 2048 8225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000757984633173/10000000000000000 : ℝ)) (X := (10003044500142080191/10000000000000000000 : ℝ)) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (6253265545746110999/6250000000000000000 : ℝ) ≤ (10001300722376983/10000000000000000 : ℝ) ^ (8225/2048 : ℝ) := by
    have hpowers : (6253265545746110999/6250000000000000000 : ℝ)^2048 ≤ (10001300722376983/10000000000000000 : ℝ)^8225 := by
      have hnat : (6253265545746110999 : ℕ)^2048*10000000000000000^8225 ≤ 10001300722376983^8225*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253265545746110999 6250000000000000000 10001300722376983 10000000000000000 2048 8225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001300722376983/10000000000000000 : ℝ)) (X := (6253265545746110999/6250000000000000000 : ℝ)) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50037026231227375029/50000000000000000000 : ℝ) ≤ (10001843460120793/10000000000000000 : ℝ) ^ (8225/2048 : ℝ) := by
    have hpowers : (50037026231227375029/50000000000000000000 : ℝ)^2048 ≤ (10001843460120793/10000000000000000 : ℝ)^8225 := by
      have hnat : (50037026231227375029 : ℕ)^2048*10000000000000000^8225 ≤ 10001843460120793^8225*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037026231227375029 50000000000000000000 10001843460120793 10000000000000000 2048 8225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001843460120793/10000000000000000 : ℝ)) (X := (50037026231227375029/50000000000000000000 : ℝ)) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3044500142080191/20000000000000000000 : ℝ) ≤ ((867185635219606829/867500000000000000 : ℝ)+2*(54273774381/27760000000000 : ℝ)*(5603/50000 : ℝ))^(8225/2048 : ℝ) := by
    rw [show (867185635219606829/867500000000000000 : ℝ)+2*(54273774381/27760000000000 : ℝ)*(5603/50000 : ℝ)=(10000757984633173/10000000000000000 : ℝ) by norm_num, show 1+2*(3044500142080191/20000000000000000000 : ℝ)=(10003044500142080191/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37026231227375029/100000000000000000000 : ℝ)+(3044500142080191/20000000000000000000 : ℝ) ≤ ((867185635219606829/867500000000000000 : ℝ)+(54273774381/27760000000000 : ℝ)*((6991/50000 : ℝ)+(5603/50000 : ℝ)))^(8225/2048 : ℝ) := by
    rw [show (867185635219606829/867500000000000000 : ℝ)+(54273774381/27760000000000 : ℝ)*((6991/50000 : ℝ)+(5603/50000 : ℝ))=(10001300722376983/10000000000000000 : ℝ) by norm_num, show 1+(37026231227375029/100000000000000000000 : ℝ)+(3044500142080191/20000000000000000000 : ℝ)=(6253265545746110999/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37026231227375029/100000000000000000000 : ℝ) ≤ ((867185635219606829/867500000000000000 : ℝ)+2*(54273774381/27760000000000 : ℝ)*(6991/50000 : ℝ))^(8225/2048 : ℝ) := by
    rw [show (867185635219606829/867500000000000000 : ℝ)+2*(54273774381/27760000000000 : ℝ)*(6991/50000 : ℝ)=(10001843460120793/10000000000000000 : ℝ) by norm_num, show 1+2*(37026231227375029/100000000000000000000 : ℝ)=(50037026231227375029/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (867185635219606829/867500000000000000 : ℝ)*(X 1 0+X 2 0)+(54273774381/27760000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8225/2048 : ℝ)) (lo := (5603/50000 : ℝ)) (hi := (6991/50000 : ℝ)) (c := (867185635219606829/867500000000000000 : ℝ)) (alpha := (54273774381/27760000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (867185635219606829/867500000000000000 : ℝ)*(X 0 1+X 2 1)+(54273774381/27760000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8225/2048 : ℝ)) (lo := (5603/50000 : ℝ)) (hi := (6991/50000 : ℝ)) (c := (867185635219606829/867500000000000000 : ℝ)) (alpha := (54273774381/27760000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (867185635219606829/867500000000000000 : ℝ)*(X 0 2+X 1 2)+(54273774381/27760000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8225/2048 : ℝ)) (lo := (5603/50000 : ℝ)) (hi := (6991/50000 : ℝ)) (c := (867185635219606829/867500000000000000 : ℝ)) (alpha := (54273774381/27760000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5345038631/10000000000 : ℝ)*X 2 0+(5263858251/10000000000 : ℝ)*X 2 1+(-2286616803/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s10_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-2220126921/10000000000 : ℝ)*X 0 0+(5264186079/10000000000 : ℝ)*X 0 1+(2697285527/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s10_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5312119451/10000000000 : ℝ)*X 1 0+(-2155904121/10000000000 : ℝ)*X 1 1+(2697285527/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s10_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5312119451/10000000000 : ℝ)*X 2 0+(2697285527/5000000000 : ℝ)*X 2 1+(-2155904121/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s10_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((2190135567/5000000000 : ℝ)*X 0 0+(4509090869/10000000000 : ℝ)*X 0 1+(4255227421/10000000000 : ℝ)*X 0 2+(2190135567/5000000000 : ℝ)*X 1 0+(4509090869/10000000000 : ℝ)*X 1 1+(4255227421/10000000000 : ℝ)*X 1 2+(2190135567/5000000000 : ℝ)*X 2 0+(4509090869/10000000000 : ℝ)*X 2 1+(4255227421/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s10_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6104867132441912753776083/2710937500000000000000000000000 : ℝ) := by norm_num
    linear_combination (106800287/25000000000000 : ℝ)*(base19) + (463931357/100000000000000 : ℝ)*(base23) + (9431049/6250000000000 : ℝ)*(lower1) + (11461913/25000000000000 : ℝ)*(upper3) + (8341777/50000000000000 : ℝ)*(lower4) + (23218431/50000000000000 : ℝ)*(upper5) + (2902175737903311/50000000000000 : ℝ)*(major0) + (2902175737903311/50000000000000 : ℝ)*(major1) + (2902175737903311/50000000000000 : ℝ)*(major2) + (429532511/50000000000000 : ℝ)*(sp0) + (7669583401435381/100000000000000 : ℝ)*(sp1) + (7669582974234233/100000000000000 : ℝ)*(sp2) + (7669582078439001/100000000000000 : ℝ)*(sp3) + (1969559737556591/50000000000000 : ℝ)*(sp4) + (1969559737556591/50000000000000 : ℝ)*(f.failure) + (7669583401435381/100000000000000 : ℝ)*(f.sum) + (1461544313513/694000000000000000000000000 : ℝ)*base65 + (1230175643449029569/43375000000000000000000000000000 : ℝ)*base67 + (580011836780095431/43375000000000000000000000000000 : ℝ)*base70 + (663041531583220431/43375000000000000000000000000000 : ℝ)*base72 + (2255296765781/694000000000000000000000000 : ℝ)*base73 + (8073634288377095431/43375000000000000000000000000000 : ℝ)*base76 + (364214121051970431/43375000000000000000000000000000 : ℝ)*base78 + (731294447740845431/43375000000000000000000000000000 : ℝ)*base80 + (5382866846001/694000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (3936233/625000000000000000000 : ℝ)*base90 + (3936233/625000000000000000000 : ℝ)*base92 + (3936233/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1033_s10 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18418937/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6991/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5603/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5603/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13981/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1033_s10 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1033_box_0 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-3264873/15625000 : ℝ)*x 0 + (268890303/500000000 : ℝ)*x 1 + (672225751/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3264873/15625000 : ℝ)^4113 ≤ (2486980440839/20000000000000 : ℝ)^3089 := by
    have hnat : (3264873 : ℕ)^4113*20000000000000^3089 ≤ 2486980440839^3089*15625000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3264873 15625000 2486980440839 20000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (268890303/500000000 : ℝ)^4113 ≤ (10945637292483/25000000000000 : ℝ)^3089 := by
    have hnat : (268890303 : ℕ)^4113*25000000000000^3089 ≤ 10945637292483^3089*500000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268890303 500000000 10945637292483 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (672225751/1250000000 : ℝ)^4113 ≤ (43782548606243/100000000000000 : ℝ)^3089 := by
    have hnat : (672225751 : ℕ)^4113*100000000000000^3089 ≤ 43782548606243^3089*1250000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672225751 1250000000 43782548606243 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3264873/15625000 : ℝ), (268890303/500000000 : ℝ), (672225751/1250000000 : ℝ)] ![(2486980440839/20000000000000 : ℝ), (10945637292483/25000000000000 : ℝ), (43782548606243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3264873/15625000 : ℝ)|^4113 ≤ (2486980440839/20000000000000 : ℝ)^3089
        have hw : |(-3264873/15625000 : ℝ)|=(3264873/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(268890303/500000000 : ℝ)|^4113 ≤ (10945637292483/25000000000000 : ℝ)^3089
        have hw : |(268890303/500000000 : ℝ)|=(268890303/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(672225751/1250000000 : ℝ)|^4113 ≤ (43782548606243/100000000000000 : ℝ)^3089
        have hw : |(672225751/1250000000 : ℝ)|=(672225751/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_box_1 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529481711/1000000000 : ℝ)*x 0 + (-2201770693/10000000000 : ℝ)*x 1 + (5377806939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529481711/1000000000 : ℝ)^4113 ≤ (857704851433/2000000000000 : ℝ)^3089 := by
    have hnat : (529481711 : ℕ)^4113*2000000000000^3089 ≤ 857704851433^3089*1000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529481711 1000000000 857704851433 2000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2201770693/10000000000 : ℝ)^4113 ≤ (3333049678317/25000000000000 : ℝ)^3089 := by
    have hnat : (2201770693 : ℕ)^4113*25000000000000^3089 ≤ 3333049678317^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2201770693 10000000000 3333049678317 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5377806939/10000000000 : ℝ)^4113 ≤ (8756511739691/20000000000000 : ℝ)^3089 := by
    have hnat : (5377806939 : ℕ)^4113*20000000000000^3089 ≤ 8756511739691^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377806939 10000000000 8756511739691 20000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529481711/1000000000 : ℝ), (-2201770693/10000000000 : ℝ), (5377806939/10000000000 : ℝ)] ![(857704851433/2000000000000 : ℝ), (3333049678317/25000000000000 : ℝ), (8756511739691/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529481711/1000000000 : ℝ)|^4113 ≤ (857704851433/2000000000000 : ℝ)^3089
        have hw : |(529481711/1000000000 : ℝ)|=(529481711/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2201770693/10000000000 : ℝ)|^4113 ≤ (3333049678317/25000000000000 : ℝ)^3089
        have hw : |(-2201770693/10000000000 : ℝ)|=(2201770693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5377806939/10000000000 : ℝ)|^4113 ≤ (8756511739691/20000000000000 : ℝ)^3089
        have hw : |(5377806939/10000000000 : ℝ)|=(5377806939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_box_2 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647409/5000000 : ℝ)*x 0 + (5377805897/10000000000 : ℝ)*x 1 + (-2201770903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647409/5000000 : ℝ)^4113 ≤ (10721313042451/25000000000000 : ℝ)^3089 := by
    have hnat : (2647409 : ℕ)^4113*25000000000000^3089 ≤ 10721313042451^3089*5000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647409 5000000 10721313042451 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377805897/10000000000 : ℝ)^4113 ≤ (21891273701491/50000000000000 : ℝ)^3089 := by
    have hnat : (5377805897 : ℕ)^4113*50000000000000^3089 ≤ 21891273701491^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377805897 10000000000 21891273701491 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2201770903/10000000000 : ℝ)^4113 ≤ (3333050101599/25000000000000 : ℝ)^3089 := by
    have hnat : (2201770903 : ℕ)^4113*25000000000000^3089 ≤ 3333050101599^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2201770903 10000000000 3333050101599 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647409/5000000 : ℝ), (5377805897/10000000000 : ℝ), (-2201770903/10000000000 : ℝ)] ![(10721313042451/25000000000000 : ℝ), (21891273701491/50000000000000 : ℝ), (3333050101599/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647409/5000000 : ℝ)|^4113 ≤ (10721313042451/25000000000000 : ℝ)^3089
        have hw : |(2647409/5000000 : ℝ)|=(2647409/5000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377805897/10000000000 : ℝ)|^4113 ≤ (21891273701491/50000000000000 : ℝ)^3089
        have hw : |(5377805897/10000000000 : ℝ)|=(5377805897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2201770903/10000000000 : ℝ)|^4113 ≤ (3333050101599/25000000000000 : ℝ)^3089
        have hw : |(-2201770903/10000000000 : ℝ)|=(2201770903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_box_3 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4489026271/10000000000 : ℝ)*x 0 + (865613011/2000000000 : ℝ)*x 1 + (4328065521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4489026271/10000000000 : ℝ)^4113 ≤ (34422386600201/100000000000000 : ℝ)^3089 := by
    have hnat : (4489026271 : ℕ)^4113*100000000000000^3089 ≤ 34422386600201^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489026271 10000000000 34422386600201 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (865613011/2000000000 : ℝ)^4113 ≤ (6557760867871/20000000000000 : ℝ)^3089 := by
    have hnat : (865613011 : ℕ)^4113*20000000000000^3089 ≤ 6557760867871^3089*2000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865613011 2000000000 6557760867871 20000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4328065521/10000000000 : ℝ)^4113 ≤ (8197202260003/25000000000000 : ℝ)^3089 := by
    have hnat : (4328065521 : ℕ)^4113*25000000000000^3089 ≤ 8197202260003^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4328065521 10000000000 8197202260003 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4489026271/10000000000 : ℝ), (865613011/2000000000 : ℝ), (4328065521/10000000000 : ℝ)] ![(34422386600201/100000000000000 : ℝ), (6557760867871/20000000000000 : ℝ), (8197202260003/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4489026271/10000000000 : ℝ)|^4113 ≤ (34422386600201/100000000000000 : ℝ)^3089
        have hw : |(4489026271/10000000000 : ℝ)|=(4489026271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(865613011/2000000000 : ℝ)|^4113 ≤ (6557760867871/20000000000000 : ℝ)^3089
        have hw : |(865613011/2000000000 : ℝ)|=(865613011/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4328065521/10000000000 : ℝ)|^4113 ≤ (8197202260003/25000000000000 : ℝ)^3089
        have hw : |(4328065521/10000000000 : ℝ)|=(4328065521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_box_4 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2352119073/10000000000 : ℝ)*x 0 + (1319896099/2500000000 : ℝ)*x 1 + (2639792629/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2352119073/10000000000 : ℝ)^4113 ≤ (1455790144231/10000000000000 : ℝ)^3089 := by
    have hnat : (2352119073 : ℕ)^4113*10000000000000^3089 ≤ 1455790144231^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2352119073 10000000000 1455790144231 10000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1319896099/2500000000 : ℝ)^4113 ≤ (21360522312357/50000000000000 : ℝ)^3089 := by
    have hnat : (1319896099 : ℕ)^4113*50000000000000^3089 ≤ 21360522312357^3089*2500000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319896099 2500000000 21360522312357 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2639792629/5000000000 : ℝ)^4113 ≤ (4272105391203/10000000000000 : ℝ)^3089 := by
    have hnat : (2639792629 : ℕ)^4113*10000000000000^3089 ≤ 4272105391203^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639792629 5000000000 4272105391203 10000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2352119073/10000000000 : ℝ), (1319896099/2500000000 : ℝ), (2639792629/5000000000 : ℝ)] ![(1455790144231/10000000000000 : ℝ), (21360522312357/50000000000000 : ℝ), (4272105391203/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2352119073/10000000000 : ℝ)|^4113 ≤ (1455790144231/10000000000000 : ℝ)^3089
        have hw : |(-2352119073/10000000000 : ℝ)|=(2352119073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1319896099/2500000000 : ℝ)|^4113 ≤ (21360522312357/50000000000000 : ℝ)^3089
        have hw : |(1319896099/2500000000 : ℝ)|=(1319896099/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2639792629/5000000000 : ℝ)|^4113 ≤ (4272105391203/10000000000000 : ℝ)^3089
        have hw : |(2639792629/5000000000 : ℝ)|=(2639792629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_box_5 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5364383871/10000000000 : ℝ)*x 0 + (-560016647/2500000000 : ℝ)*x 1 + (1319896061/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364383871/10000000000 : ℝ)^4113 ≤ (43637110377347/100000000000000 : ℝ)^3089 := by
    have hnat : (5364383871 : ℕ)^4113*100000000000000^3089 ≤ 43637110377347^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364383871 10000000000 43637110377347 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (560016647/2500000000 : ℝ)^4113 ≤ (3410461654599/25000000000000 : ℝ)^3089 := by
    have hnat : (560016647 : ℕ)^4113*25000000000000^3089 ≤ 3410461654599^3089*2500000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560016647 2500000000 3410461654599 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1319896061/2500000000 : ℝ)^4113 ≤ (10680260746761/25000000000000 : ℝ)^3089 := by
    have hnat : (1319896061 : ℕ)^4113*25000000000000^3089 ≤ 10680260746761^3089*2500000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319896061 2500000000 10680260746761 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364383871/10000000000 : ℝ), (-560016647/2500000000 : ℝ), (1319896061/2500000000 : ℝ)] ![(43637110377347/100000000000000 : ℝ), (3410461654599/25000000000000 : ℝ), (10680260746761/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364383871/10000000000 : ℝ)|^4113 ≤ (43637110377347/100000000000000 : ℝ)^3089
        have hw : |(5364383871/10000000000 : ℝ)|=(5364383871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-560016647/2500000000 : ℝ)|^4113 ≤ (3410461654599/25000000000000 : ℝ)^3089
        have hw : |(-560016647/2500000000 : ℝ)|=(560016647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1319896061/2500000000 : ℝ)|^4113 ≤ (10680260746761/25000000000000 : ℝ)^3089
        have hw : |(1319896061/2500000000 : ℝ)|=(1319896061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_box_6 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5364383201/10000000000 : ℝ)*x 0 + (5279585331/10000000000 : ℝ)*x 1 + (-56001651/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364383201/10000000000 : ℝ)^4113 ≤ (43637103120437/100000000000000 : ℝ)^3089 := by
    have hnat : (5364383201 : ℕ)^4113*100000000000000^3089 ≤ 43637103120437^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364383201 10000000000 43637103120437 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5279585331/10000000000 : ℝ)^4113 ≤ (42721054698543/100000000000000 : ℝ)^3089 := by
    have hnat : (5279585331 : ℕ)^4113*100000000000000^3089 ≤ 42721054698543^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279585331 10000000000 42721054698543 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (56001651/250000000 : ℝ)^4113 ≤ (1364184217481/10000000000000 : ℝ)^3089 := by
    have hnat : (56001651 : ℕ)^4113*10000000000000^3089 ≤ 1364184217481^3089*250000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56001651 250000000 1364184217481 10000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364383201/10000000000 : ℝ), (5279585331/10000000000 : ℝ), (-56001651/250000000 : ℝ)] ![(43637103120437/100000000000000 : ℝ), (42721054698543/100000000000000 : ℝ), (1364184217481/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364383201/10000000000 : ℝ)|^4113 ≤ (43637103120437/100000000000000 : ℝ)^3089
        have hw : |(5364383201/10000000000 : ℝ)|=(5364383201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5279585331/10000000000 : ℝ)|^4113 ≤ (42721054698543/100000000000000 : ℝ)^3089
        have hw : |(5279585331/10000000000 : ℝ)|=(5279585331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-56001651/250000000 : ℝ)|^4113 ≤ (1364184217481/10000000000000 : ℝ)^3089
        have hw : |(-56001651/250000000 : ℝ)|=(56001651/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_box_7 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2135590863/5000000000 : ℝ)*x 0 + (2218482671/5000000000 : ℝ)*x 1 + (4436966301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2135590863/5000000000 : ℝ)^4113 ≤ (16108130937717/50000000000000 : ℝ)^3089 := by
    have hnat : (2135590863 : ℕ)^4113*50000000000000^3089 ≤ 16108130937717^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135590863 5000000000 16108130937717 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2218482671/5000000000 : ℝ)^4113 ≤ (16945932088983/50000000000000 : ℝ)^3089 := by
    have hnat : (2218482671 : ℕ)^4113*50000000000000^3089 ≤ 16945932088983^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2218482671 5000000000 16945932088983 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4436966301/10000000000 : ℝ)^4113 ≤ (16945936965827/50000000000000 : ℝ)^3089 := by
    have hnat : (4436966301 : ℕ)^4113*50000000000000^3089 ≤ 16945936965827^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4436966301 10000000000 16945936965827 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2135590863/5000000000 : ℝ), (2218482671/5000000000 : ℝ), (4436966301/10000000000 : ℝ)] ![(16108130937717/50000000000000 : ℝ), (16945932088983/50000000000000 : ℝ), (16945936965827/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2135590863/5000000000 : ℝ)|^4113 ≤ (16108130937717/50000000000000 : ℝ)^3089
        have hw : |(2135590863/5000000000 : ℝ)|=(2135590863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2218482671/5000000000 : ℝ)|^4113 ≤ (16945932088983/50000000000000 : ℝ)^3089
        have hw : |(2218482671/5000000000 : ℝ)|=(2218482671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4436966301/10000000000 : ℝ)|^4113 ≤ (16945936965827/50000000000000 : ℝ)^3089
        have hw : |(4436966301/10000000000 : ℝ)|=(4436966301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_box_8 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1148670753/5000000000 : ℝ)*x 0 + (5213001519/10000000000 : ℝ)*x 1 + (269370067/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1148670753/5000000000 : ℝ)^4113 ≤ (14108230794831/100000000000000 : ℝ)^3089 := by
    have hnat : (1148670753 : ℕ)^4113*100000000000000^3089 ≤ 14108230794831^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1148670753 5000000000 14108230794831 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5213001519/10000000000 : ℝ)^4113 ≤ (2625323415781/6250000000000 : ℝ)^3089 := by
    have hnat : (5213001519 : ℕ)^4113*6250000000000^3089 ≤ 2625323415781^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5213001519 10000000000 2625323415781 6250000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269370067/500000000 : ℝ)^4113 ≤ (10971648633137/25000000000000 : ℝ)^3089 := by
    have hnat : (269370067 : ℕ)^4113*25000000000000^3089 ≤ 10971648633137^3089*500000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269370067 500000000 10971648633137 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1148670753/5000000000 : ℝ), (5213001519/10000000000 : ℝ), (269370067/500000000 : ℝ)] ![(14108230794831/100000000000000 : ℝ), (2625323415781/6250000000000 : ℝ), (10971648633137/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1148670753/5000000000 : ℝ)|^4113 ≤ (14108230794831/100000000000000 : ℝ)^3089
        have hw : |(-1148670753/5000000000 : ℝ)|=(1148670753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5213001519/10000000000 : ℝ)|^4113 ≤ (2625323415781/6250000000000 : ℝ)^3089
        have hw : |(5213001519/10000000000 : ℝ)|=(5213001519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269370067/500000000 : ℝ)|^4113 ≤ (10971648633137/25000000000000 : ℝ)^3089
        have hw : |(269370067/500000000 : ℝ)|=(269370067/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_box_9 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644008949/5000000000 : ℝ)*x 0 + (-2197958923/10000000000 : ℝ)*x 1 + (2693700573/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644008949/5000000000 : ℝ)^4113 ≤ (8562386494113/20000000000000 : ℝ)^3089 := by
    have hnat : (2644008949 : ℕ)^4113*20000000000000^3089 ≤ 8562386494113^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644008949 5000000000 8562386494113 20000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2197958923/10000000000 : ℝ)^4113 ≤ (16626843857/125000000000 : ℝ)^3089 := by
    have hnat : (2197958923 : ℕ)^4113*125000000000^3089 ≤ 16626843857^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197958923 10000000000 16626843857 125000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693700573/5000000000 : ℝ)^4113 ≤ (10971648107077/25000000000000 : ℝ)^3089 := by
    have hnat : (2693700573 : ℕ)^4113*25000000000000^3089 ≤ 10971648107077^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693700573 5000000000 10971648107077 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644008949/5000000000 : ℝ), (-2197958923/10000000000 : ℝ), (2693700573/5000000000 : ℝ)] ![(8562386494113/20000000000000 : ℝ), (16626843857/125000000000 : ℝ), (10971648107077/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644008949/5000000000 : ℝ)|^4113 ≤ (8562386494113/20000000000000 : ℝ)^3089
        have hw : |(2644008949/5000000000 : ℝ)|=(2644008949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2197958923/10000000000 : ℝ)|^4113 ≤ (16626843857/125000000000 : ℝ)^3089
        have hw : |(-2197958923/10000000000 : ℝ)|=(2197958923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693700573/5000000000 : ℝ)|^4113 ≤ (10971648107077/25000000000000 : ℝ)^3089
        have hw : |(2693700573/5000000000 : ℝ)|=(2693700573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_box_10 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5288018257/10000000000 : ℝ)*x 0 + (5387401283/10000000000 : ℝ)*x 1 + (-2197958259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288018257/10000000000 : ℝ)^4113 ≤ (42811936340531/100000000000000 : ℝ)^3089 := by
    have hnat : (5288018257 : ℕ)^4113*100000000000000^3089 ≤ 42811936340531^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288018257 10000000000 42811936340531 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5387401283/10000000000 : ℝ)^4113 ≤ (10971648478573/25000000000000 : ℝ)^3089 := by
    have hnat : (5387401283 : ℕ)^4113*25000000000000^3089 ≤ 10971648478573^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387401283 10000000000 10971648478573 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2197958259/10000000000 : ℝ)^4113 ≤ (2660293947033/20000000000000 : ℝ)^3089 := by
    have hnat : (2197958259 : ℕ)^4113*20000000000000^3089 ≤ 2660293947033^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197958259 10000000000 2660293947033 20000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288018257/10000000000 : ℝ), (5387401283/10000000000 : ℝ), (-2197958259/10000000000 : ℝ)] ![(42811936340531/100000000000000 : ℝ), (10971648478573/25000000000000 : ℝ), (2660293947033/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288018257/10000000000 : ℝ)|^4113 ≤ (42811936340531/100000000000000 : ℝ)^3089
        have hw : |(5288018257/10000000000 : ℝ)|=(5288018257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5387401283/10000000000 : ℝ)|^4113 ≤ (10971648478573/25000000000000 : ℝ)^3089
        have hw : |(5387401283/10000000000 : ℝ)|=(5387401283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2197958259/10000000000 : ℝ)|^4113 ≤ (2660293947033/20000000000000 : ℝ)^3089
        have hw : |(-2197958259/10000000000 : ℝ)|=(2197958259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_box_11 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4510033261/10000000000 : ℝ)*x 0 + (431742127/1000000000 : ℝ)*x 1 + (4317421329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4510033261/10000000000 : ℝ)^4113 ≤ (4329629509907/12500000000000 : ℝ)^3089 := by
    have hnat : (4510033261 : ℕ)^4113*12500000000000^3089 ≤ 4329629509907^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4510033261 10000000000 4329629509907 12500000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (431742127/1000000000 : ℝ)^4113 ≤ (32681481652981/100000000000000 : ℝ)^3089 := by
    have hnat : (431742127 : ℕ)^4113*100000000000000^3089 ≤ 32681481652981^3089*1000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431742127 1000000000 32681481652981 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4317421329/10000000000 : ℝ)^4113 ≤ (32681482247643/100000000000000 : ℝ)^3089 := by
    have hnat : (4317421329 : ℕ)^4113*100000000000000^3089 ≤ 32681482247643^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4317421329 10000000000 32681482247643 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4510033261/10000000000 : ℝ), (431742127/1000000000 : ℝ), (4317421329/10000000000 : ℝ)] ![(4329629509907/12500000000000 : ℝ), (32681481652981/100000000000000 : ℝ), (32681482247643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4510033261/10000000000 : ℝ)|^4113 ≤ (4329629509907/12500000000000 : ℝ)^3089
        have hw : |(4510033261/10000000000 : ℝ)|=(4510033261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(431742127/1000000000 : ℝ)|^4113 ≤ (32681481652981/100000000000000 : ℝ)^3089
        have hw : |(431742127/1000000000 : ℝ)|=(431742127/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4317421329/10000000000 : ℝ)|^4113 ≤ (32681482247643/100000000000000 : ℝ)^3089
        have hw : |(4317421329/10000000000 : ℝ)|=(4317421329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_box_12 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1072343493/5000000000 : ℝ)*x 0 + (2721513823/5000000000 : ℝ)*x 1 + (658950329/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072343493/5000000000 : ℝ)^4113 ≤ (3218487457937/25000000000000 : ℝ)^3089 := by
    have hnat : (1072343493 : ℕ)^4113*25000000000000^3089 ≤ 3218487457937^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072343493 5000000000 3218487457937 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2721513823/5000000000 : ℝ)^4113 ≤ (22245490333801/50000000000000 : ℝ)^3089 := by
    have hnat : (2721513823 : ℕ)^4113*50000000000000^3089 ≤ 22245490333801^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721513823 5000000000 22245490333801 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658950329/1250000000 : ℝ)^4113 ≤ (4263506947637/10000000000000 : ℝ)^3089 := by
    have hnat : (658950329 : ℕ)^4113*10000000000000^3089 ≤ 4263506947637^3089*1250000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658950329 1250000000 4263506947637 10000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1072343493/5000000000 : ℝ), (2721513823/5000000000 : ℝ), (658950329/1250000000 : ℝ)] ![(3218487457937/25000000000000 : ℝ), (22245490333801/50000000000000 : ℝ), (4263506947637/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1072343493/5000000000 : ℝ)|^4113 ≤ (3218487457937/25000000000000 : ℝ)^3089
        have hw : |(-1072343493/5000000000 : ℝ)|=(1072343493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2721513823/5000000000 : ℝ)|^4113 ≤ (22245490333801/50000000000000 : ℝ)^3089
        have hw : |(2721513823/5000000000 : ℝ)|=(2721513823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658950329/1250000000 : ℝ)|^4113 ≤ (4263506947637/10000000000000 : ℝ)^3089
        have hw : |(658950329/1250000000 : ℝ)|=(658950329/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_box_13 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5370034659/10000000000 : ℝ)*x 0 + (-2243119061/10000000000 : ℝ)*x 1 + (1054320539/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370034659/10000000000 : ℝ)^4113 ≤ (10924581481787/25000000000000 : ℝ)^3089 := by
    have hnat : (5370034659 : ℕ)^4113*25000000000000^3089 ≤ 10924581481787^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370034659 10000000000 10924581481787 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2243119061/10000000000 : ℝ)^4113 ≤ (13666603897687/100000000000000 : ℝ)^3089 := by
    have hnat : (2243119061 : ℕ)^4113*100000000000000^3089 ≤ 13666603897687^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243119061 10000000000 13666603897687 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054320539/2000000000 : ℝ)^4113 ≤ (42635070154801/100000000000000 : ℝ)^3089 := by
    have hnat : (1054320539 : ℕ)^4113*100000000000000^3089 ≤ 42635070154801^3089*2000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054320539 2000000000 42635070154801 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370034659/10000000000 : ℝ), (-2243119061/10000000000 : ℝ), (1054320539/2000000000 : ℝ)] ![(10924581481787/25000000000000 : ℝ), (13666603897687/100000000000000 : ℝ), (42635070154801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370034659/10000000000 : ℝ)|^4113 ≤ (10924581481787/25000000000000 : ℝ)^3089
        have hw : |(5370034659/10000000000 : ℝ)|=(5370034659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2243119061/10000000000 : ℝ)|^4113 ≤ (13666603897687/100000000000000 : ℝ)^3089
        have hw : |(-2243119061/10000000000 : ℝ)|=(2243119061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1054320539/2000000000 : ℝ)|^4113 ≤ (42635070154801/100000000000000 : ℝ)^3089
        have hw : |(1054320539/2000000000 : ℝ)|=(1054320539/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_box_14 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (671254339/1250000000 : ℝ)*x 0 + (5271602683/10000000000 : ℝ)*x 1 + (-2243119007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671254339/1250000000 : ℝ)^4113 ≤ (21849163250701/50000000000000 : ℝ)^3089 := by
    have hnat : (671254339 : ℕ)^4113*50000000000000^3089 ≤ 21849163250701^3089*1250000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671254339 1250000000 21849163250701 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5271602683/10000000000 : ℝ)^4113 ≤ (5329383753197/12500000000000 : ℝ)^3089 := by
    have hnat : (5271602683 : ℕ)^4113*12500000000000^3089 ≤ 5329383753197^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271602683 10000000000 5329383753197 12500000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2243119007/10000000000 : ℝ)^4113 ≤ (6833301729809/50000000000000 : ℝ)^3089 := by
    have hnat : (2243119007 : ℕ)^4113*50000000000000^3089 ≤ 6833301729809^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243119007 10000000000 6833301729809 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671254339/1250000000 : ℝ), (5271602683/10000000000 : ℝ), (-2243119007/10000000000 : ℝ)] ![(21849163250701/50000000000000 : ℝ), (5329383753197/12500000000000 : ℝ), (6833301729809/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671254339/1250000000 : ℝ)|^4113 ≤ (21849163250701/50000000000000 : ℝ)^3089
        have hw : |(671254339/1250000000 : ℝ)|=(671254339/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5271602683/10000000000 : ℝ)|^4113 ≤ (5329383753197/12500000000000 : ℝ)^3089
        have hw : |(5271602683/10000000000 : ℝ)|=(5271602683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2243119007/10000000000 : ℝ)|^4113 ≤ (6833301729809/50000000000000 : ℝ)^3089
        have hw : |(-2243119007/10000000000 : ℝ)|=(2243119007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_box_15 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1063312153/2500000000 : ℝ)*x 0 + (4445810791/10000000000 : ℝ)*x 1 + (277863177/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1063312153/2500000000 : ℝ)^4113 ≤ (32036283227703/100000000000000 : ℝ)^3089 := by
    have hnat : (1063312153 : ℕ)^4113*100000000000000^3089 ≤ 32036283227703^3089*2500000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063312153 2500000000 32036283227703 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4445810791/10000000000 : ℝ)^4113 ≤ (33981858171363/100000000000000 : ℝ)^3089 := by
    have hnat : (4445810791 : ℕ)^4113*100000000000000^3089 ≤ 33981858171363^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4445810791 10000000000 33981858171363 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (277863177/625000000 : ℝ)^4113 ≤ (8495464647159/25000000000000 : ℝ)^3089 := by
    have hnat : (277863177 : ℕ)^4113*25000000000000^3089 ≤ 8495464647159^3089*625000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277863177 625000000 8495464647159 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1063312153/2500000000 : ℝ), (4445810791/10000000000 : ℝ), (277863177/625000000 : ℝ)] ![(32036283227703/100000000000000 : ℝ), (33981858171363/100000000000000 : ℝ), (8495464647159/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1063312153/2500000000 : ℝ)|^4113 ≤ (32036283227703/100000000000000 : ℝ)^3089
        have hw : |(1063312153/2500000000 : ℝ)|=(1063312153/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4445810791/10000000000 : ℝ)|^4113 ≤ (33981858171363/100000000000000 : ℝ)^3089
        have hw : |(4445810791/10000000000 : ℝ)|=(4445810791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(277863177/625000000 : ℝ)|^4113 ≤ (8495464647159/25000000000000 : ℝ)^3089
        have hw : |(277863177/625000000 : ℝ)|=(277863177/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1033_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18418937/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13981/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5603/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62223/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(3701/6250 : ℝ) ∧ (19867/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (82877/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13981/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5603/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13981/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5603/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13981/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5603/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13981/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5603/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13981/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5603/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13981/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5603/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5603/50000 : ℝ) ^ (8225/2048 : ℝ) ≤ (3044500142080191/20000000000000000000 : ℝ) := by
    have hpowers : (5603/50000 : ℝ)^8225 ≤ (3044500142080191/20000000000000000000 : ℝ)^2048 := by
      have hnat : (5603 : ℕ)^8225*20000000000000000000^2048 ≤ 3044500142080191^2048*50000^8225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5603 50000 3044500142080191 20000000000000000000 8225 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5603/50000 : ℝ)) (X := (3044500142080191/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (13981/100000 : ℝ) ^ (8225/2048 : ℝ) ≤ (37015597162058539/100000000000000000000 : ℝ) := by
    have hpowers : (13981/100000 : ℝ)^8225 ≤ (37015597162058539/100000000000000000000 : ℝ)^2048 := by
      have hnat : (13981 : ℕ)^8225*100000000000000000000^2048 ≤ 37015597162058539^2048*100000^8225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13981 100000 37015597162058539 100000000000000000000 8225 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13981/100000 : ℝ)) (X := (37015597162058539/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10003044500142080191/10000000000000000000 : ℝ) ≤ (10000757984633173/10000000000000000 : ℝ) ^ (8225/2048 : ℝ) := by
    have hpowers : (10003044500142080191/10000000000000000000 : ℝ)^2048 ≤ (10000757984633173/10000000000000000 : ℝ)^8225 := by
      have hnat : (10003044500142080191 : ℕ)^2048*10000000000000000^8225 ≤ 10000757984633173^8225*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003044500142080191 10000000000000000000 10000757984633173 10000000000000000 2048 8225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000757984633173/10000000000000000 : ℝ)) (X := (10003044500142080191/10000000000000000000 : ℝ)) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50026119048936229747/50000000000000000000 : ℝ) ≤ (10001300457695829/10000000000000000 : ℝ) ^ (8225/2048 : ℝ) := by
    have hpowers : (50026119048936229747/50000000000000000000 : ℝ)^2048 ≤ (10001300457695829/10000000000000000 : ℝ)^8225 := by
      have hnat : (50026119048936229747 : ℕ)^2048*10000000000000000^8225 ≤ 10001300457695829^8225*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026119048936229747 50000000000000000000 10001300457695829 10000000000000000 2048 8225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001300457695829/10000000000000000 : ℝ)) (X := (50026119048936229747/50000000000000000000 : ℝ)) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50037015597162058539/50000000000000000000 : ℝ) ≤ (2000368586151697/2000000000000000 : ℝ) ^ (8225/2048 : ℝ) := by
    have hpowers : (50037015597162058539/50000000000000000000 : ℝ)^2048 ≤ (2000368586151697/2000000000000000 : ℝ)^8225 := by
      have hnat : (50037015597162058539 : ℕ)^2048*2000000000000000^8225 ≤ 2000368586151697^8225*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037015597162058539 50000000000000000000 2000368586151697 2000000000000000 2048 8225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000368586151697/2000000000000000 : ℝ)) (X := (50037015597162058539/50000000000000000000 : ℝ)) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3044500142080191/20000000000000000000 : ℝ) ≤ ((27739945501076808803/27750000000000000000 : ℝ)+2*(2119035401/1083984375000 : ℝ)*(5603/50000 : ℝ))^(8225/2048 : ℝ) := by
    rw [show (27739945501076808803/27750000000000000000 : ℝ)+2*(2119035401/1083984375000 : ℝ)*(5603/50000 : ℝ)=(10000757984633173/10000000000000000 : ℝ) by norm_num, show 1+2*(3044500142080191/20000000000000000000 : ℝ)=(10003044500142080191/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37015597162058539/100000000000000000000 : ℝ)+(3044500142080191/20000000000000000000 : ℝ) ≤ ((27739945501076808803/27750000000000000000 : ℝ)+(2119035401/1083984375000 : ℝ)*((13981/100000 : ℝ)+(5603/50000 : ℝ)))^(8225/2048 : ℝ) := by
    rw [show (27739945501076808803/27750000000000000000 : ℝ)+(2119035401/1083984375000 : ℝ)*((13981/100000 : ℝ)+(5603/50000 : ℝ))=(10001300457695829/10000000000000000 : ℝ) by norm_num, show 1+(37015597162058539/100000000000000000000 : ℝ)+(3044500142080191/20000000000000000000 : ℝ)=(50026119048936229747/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37015597162058539/100000000000000000000 : ℝ) ≤ ((27739945501076808803/27750000000000000000 : ℝ)+2*(2119035401/1083984375000 : ℝ)*(13981/100000 : ℝ))^(8225/2048 : ℝ) := by
    rw [show (27739945501076808803/27750000000000000000 : ℝ)+2*(2119035401/1083984375000 : ℝ)*(13981/100000 : ℝ)=(2000368586151697/2000000000000000 : ℝ) by norm_num, show 1+2*(37015597162058539/100000000000000000000 : ℝ)=(50037015597162058539/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27739945501076808803/27750000000000000000 : ℝ)*(X 1 0+X 2 0)+(2119035401/1083984375000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8225/2048 : ℝ)) (lo := (5603/50000 : ℝ)) (hi := (13981/100000 : ℝ)) (c := (27739945501076808803/27750000000000000000 : ℝ)) (alpha := (2119035401/1083984375000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27739945501076808803/27750000000000000000 : ℝ)*(X 0 1+X 2 1)+(2119035401/1083984375000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8225/2048 : ℝ)) (lo := (5603/50000 : ℝ)) (hi := (13981/100000 : ℝ)) (c := (27739945501076808803/27750000000000000000 : ℝ)) (alpha := (2119035401/1083984375000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27739945501076808803/27750000000000000000 : ℝ)*(X 0 2+X 1 2)+(2119035401/1083984375000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8225/2048 : ℝ)) (lo := (5603/50000 : ℝ)) (hi := (13981/100000 : ℝ)) (c := (27739945501076808803/27750000000000000000 : ℝ)) (alpha := (2119035401/1083984375000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-3264873/15625000 : ℝ)*X 0 0+(268890303/500000000 : ℝ)*X 0 1+(672225751/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((529481711/1000000000 : ℝ)*X 1 0+(-2201770693/10000000000 : ℝ)*X 1 1+(5377806939/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2647409/5000000 : ℝ)*X 2 0+(5377805897/10000000000 : ℝ)*X 2 1+(-2201770903/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4489026271/10000000000 : ℝ)*X 0 0+(865613011/2000000000 : ℝ)*X 0 1+(4328065521/10000000000 : ℝ)*X 0 2+(4489026271/10000000000 : ℝ)*X 1 0+(865613011/2000000000 : ℝ)*X 1 1+(4328065521/10000000000 : ℝ)*X 1 2+(4489026271/10000000000 : ℝ)*X 2 0+(865613011/2000000000 : ℝ)*X 2 1+(4328065521/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2352119073/10000000000 : ℝ)*X 0 0+(1319896099/2500000000 : ℝ)*X 0 1+(2639792629/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5364383871/10000000000 : ℝ)*X 1 0+(-560016647/2500000000 : ℝ)*X 1 1+(1319896061/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5364383201/10000000000 : ℝ)*X 2 0+(5279585331/10000000000 : ℝ)*X 2 1+(-56001651/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2135590863/5000000000 : ℝ)*X 0 0+(2218482671/5000000000 : ℝ)*X 0 1+(4436966301/10000000000 : ℝ)*X 0 2+(2135590863/5000000000 : ℝ)*X 1 0+(2218482671/5000000000 : ℝ)*X 1 1+(4436966301/10000000000 : ℝ)*X 1 2+(2135590863/5000000000 : ℝ)*X 2 0+(2218482671/5000000000 : ℝ)*X 2 1+(4436966301/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1148670753/5000000000 : ℝ)*X 0 0+(5213001519/10000000000 : ℝ)*X 0 1+(269370067/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2644008949/5000000000 : ℝ)*X 1 0+(-2197958923/10000000000 : ℝ)*X 1 1+(2693700573/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5288018257/10000000000 : ℝ)*X 2 0+(5387401283/10000000000 : ℝ)*X 2 1+(-2197958259/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4510033261/10000000000 : ℝ)*X 0 0+(431742127/1000000000 : ℝ)*X 0 1+(4317421329/10000000000 : ℝ)*X 0 2+(4510033261/10000000000 : ℝ)*X 1 0+(431742127/1000000000 : ℝ)*X 1 1+(4317421329/10000000000 : ℝ)*X 1 2+(4510033261/10000000000 : ℝ)*X 2 0+(431742127/1000000000 : ℝ)*X 2 1+(4317421329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1072343493/5000000000 : ℝ)*X 0 0+(2721513823/5000000000 : ℝ)*X 0 1+(658950329/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5370034659/10000000000 : ℝ)*X 1 0+(-2243119061/10000000000 : ℝ)*X 1 1+(1054320539/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((671254339/1250000000 : ℝ)*X 2 0+(5271602683/10000000000 : ℝ)*X 2 1+(-2243119007/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1063312153/2500000000 : ℝ)*X 0 0+(4445810791/10000000000 : ℝ)*X 0 1+(277863177/625000000 : ℝ)*X 0 2+(1063312153/2500000000 : ℝ)*X 1 0+(4445810791/10000000000 : ℝ)*X 1 1+(277863177/625000000 : ℝ)*X 1 2+(1063312153/2500000000 : ℝ)*X 2 0+(4445810791/10000000000 : ℝ)*X 2 1+(277863177/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62223/100000 : ℝ) ≤ (-8992826801864619716215428139329/14453125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2247051/2500000000000 : ℝ)*(upper1) + (1882097/1250000000000 : ℝ)*(lower4) + (102595147/20000000000000 : ℝ)*(upper5) + (29912811052721/781250000000 : ℝ)*(major0) + (29912811052721/781250000000 : ℝ)*(major1) + (29912811052721/781250000000 : ℝ)*(major2) + (4272682957/10000000000000 : ℝ)*(sp1) + (15445338501/100000000000000 : ℝ)*(sp2) + (15238745087/50000000000000 : ℝ)*(sp3) + (2539986577854971/50000000000000 : ℝ)*(sp4) + (5079937385875819/100000000000000 : ℝ)*(sp5) + (5079964667366887/100000000000000 : ℝ)*(sp6) + (2537509035611/97656250000 : ℝ)*(sp7) + (3478497723/50000000000000 : ℝ)*(sp12) + (1299219864977919/50000000000000 : ℝ)*(f.failure) + (1269995028176347/25000000000000 : ℝ)*(f.sum) + (2155238534317/867187500000000000000000000 : ℝ)*base66 + (140088974052306169/10839843750000000000000000000000 : ℝ)*base67 + (32661930895400761/2709960937500000000000000000000 : ℝ)*base69 + (109400035204927801/43359375000000000000000000000000 : ℝ)*base71 + (3522337013357/3468750000000000000000000000 : ℝ)*base73 + (18297361535622037/21679687500000000000000000000000 : ℝ)*base76 + (856402925276021551/43359375000000000000000000000000 : ℝ)*base77 + (300125215115159213/21679687500000000000000000000000 : ℝ)*base79 + (50279087952697/13875000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (3547897/625000000000000000000 : ℝ)*base90 + (3547897/625000000000000000000 : ℝ)*base92 + (3547897/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (3701/6250 : ℝ) ≤ (273887681271406771132125271031589/462500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (31973197/25000000000000 : ℝ)*(upper0) + (182409/2000000000000 : ℝ)*(lower1) + (26310939/25000000000000 : ℝ)*(upper4) + (71688797/100000000000000 : ℝ)*(upper5) + (3891192759746979/100000000000000 : ℝ)*(major0) + (3891192759746979/100000000000000 : ℝ)*(major1) + (3891192759746979/100000000000000 : ℝ)*(major2) + (5121890349962793/100000000000000 : ℝ)*(sp0) + (25609213654361/500000000000 : ℝ)*(sp1) + (80029092448263/1562500000000 : ℝ)*(sp2) + (1320374090937613/50000000000000 : ℝ)*(sp3) + (47619090593/100000000000000 : ℝ)*(sp5) + (5730431/78125000000 : ℝ)*(sp7) + (28433273961/100000000000000 : ℝ)*(sp10) + (2640755516826907/100000000000000 : ℝ)*(f.failure) + (5121890349962793/100000000000000 : ℝ)*(f.sum) + (19126075968829/2312500000000000000000000000 : ℝ)*base65 + (30823191925304085379/925000000000000000000000000000000 : ℝ)*base67 + (15629927065304085379/925000000000000000000000000000000 : ℝ)*base69 + (10658930205729085379/925000000000000000000000000000000 : ℝ)*base71 + (19536351070079/2312500000000000000000000000 : ℝ)*base73 + (11632306328404085379/925000000000000000000000000000000 : ℝ)*base75 + (9213234317279085379/925000000000000000000000000000000 : ℝ)*base77 + (10606753889829085379/925000000000000000000000000000000 : ℝ)*base79 + (1179575212033/4625000000000000000000000000 : ℝ)*base81 + (2437859/1250000000000000000000 : ℝ)*base89 + (2437859/1250000000000000000000 : ℝ)*base91 + (2437859/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (19867/25000 : ℝ) ≤ (91887525476975343612621665568287/115625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (179028263/100000000000000 : ℝ)*(upper0) + (47916883/50000000000000 : ℝ)*(lower3) + (85161011/20000000000000 : ℝ)*(upper4) + (1089881028559657/25000000000000 : ℝ)*(major0) + (1089881028559657/25000000000000 : ℝ)*(major1) + (1089881028559657/25000000000000 : ℝ)*(major2) + (101634371773/100000000000000 : ℝ)*(sp1) + (85020537383/20000000000000 : ℝ)*(sp2) + (4052510351/2500000000000 : ℝ)*(sp3) + (1309120209/12500000000000 : ℝ)*(sp4) + (716744920293883/12500000000000 : ℝ)*(sp8) + (2866934100470481/50000000000000 : ℝ)*(sp9) + (286677236631291/5000000000000 : ℝ)*(sp10) + (739606548828917/25000000000000 : ℝ)*(sp11) + (739647073932427/25000000000000 : ℝ)*(f.failure) + (1146793967062547/20000000000000 : ℝ)*(f.sum) + (16823963819383/3468750000000000000000000000 : ℝ)*base66 + (152630441417460571/693750000000000000000000000000000 : ℝ)*base67 + (9771343863542460571/693750000000000000000000000000000 : ℝ)*base69 + (10678770704754960571/693750000000000000000000000000000 : ℝ)*base71 + (26654097989093/13875000000000000000000000000 : ℝ)*base73 + (9862906262961210571/693750000000000000000000000000000 : ℝ)*base75 + (10444774494917460571/693750000000000000000000000000000 : ℝ)*base77 + (3470053803561210571/693750000000000000000000000000000 : ℝ)*base79 + (51143554843657/13875000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (2670099/312500000000000000000 : ℝ)*base89 + (2670099/312500000000000000000 : ℝ)*base91 + (2670099/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-82877/100000 : ℝ) ≤ (-191646460433146789527621934811311/231250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6544633/100000000000000 : ℝ)*(lower0) + (8881697/50000000000000 : ℝ)*(lower1) + (3091731/10000000000000 : ℝ)*(lower2) + (1625519/5000000000000 : ℝ)*(upper5) + (4393860262825237/100000000000000 : ℝ)*(major0) + (4393860262825237/100000000000000 : ℝ)*(major1) + (4393860262825237/100000000000000 : ℝ)*(major2) + (1535373621/100000000000000 : ℝ)*(sp0) + (29782874469/100000000000000 : ℝ)*(sp7) + (57884599/25000000000000 : ℝ)*(sp8) + (5833452972403049/100000000000000 : ℝ)*(sp12) + (2916727369657533/50000000000000 : ℝ)*(sp13) + (2916727369657533/50000000000000 : ℝ)*(sp14) + (1490930359239161/50000000000000 : ℝ)*(sp15) + (298189050135279/10000000000000 : ℝ)*(f.failure) + (2916727369657533/50000000000000 : ℝ)*(f.sum) + (6682148207257/3468750000000000000000000000 : ℝ)*base66 + (2938853854150638689/2775000000000000000000000000000000 : ℝ)*base68 + (19096427387824361311/2775000000000000000000000000000000 : ℝ)*base69 + (19196961744499361311/2775000000000000000000000000000000 : ℝ)*base71 + (26813197426139/6937500000000000000000000000 : ℝ)*base74 + (20494715771974361311/2775000000000000000000000000000000 : ℝ)*base75 + (15912198412549361311/2775000000000000000000000000000000 : ℝ)*base77 + (15616287319849361311/2775000000000000000000000000000000 : ℝ)*base79 + (14183107303153/13875000000000000000000000000 : ℝ)*base82 + (871577/125000000000000000000 : ℝ)*base90 + (871577/125000000000000000000 : ℝ)*base92 + (871577/125000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1033_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18418937/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13981/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5603/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(3701/6250 : ℝ) else (19867/25000 : ℝ) ≤ X j i ∧ X j i ≤ (82877/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1033_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1033_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18418937/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6991/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2241/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(3701/6250 : ℝ) else (19867/25000 : ℝ) ≤ X j i ∧ X j i ≤ (82877/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1033_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1033_s10 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1033_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18418937/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6991/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2241/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(3701/6250 : ℝ) else (19867/25000 : ℝ) ≤ X j i ∧ X j i ≤ (82877/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1033_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
