-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1242_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:19:28.881981+00:00
-- url     : https://prove2.me/submissions/95555bb8-079f-42c0-85ef-3a922b584a20

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
theorem support_rectangle_w1242_s3_0 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2117118289/10000000000 : ℝ)*x 0 + (5419660183/10000000000 : ℝ)*x 1 + (5240616657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2117118289/10000000000 : ℝ)^8435 ≤ (2573797658681/20000000000000 : ℝ)^6387 := by
    have hnat : (2117118289 : ℕ)^8435*20000000000000^6387 ≤ 2573797658681^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117118289 10000000000 2573797658681 20000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5419660183/10000000000 : ℝ)^8435 ≤ (11132939616113/25000000000000 : ℝ)^6387 := by
    have hnat : (5419660183 : ℕ)^8435*25000000000000^6387 ≤ 11132939616113^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419660183 10000000000 11132939616113 25000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5240616657/10000000000 : ℝ)^8435 ≤ (42599253228479/100000000000000 : ℝ)^6387 := by
    have hnat : (5240616657 : ℕ)^8435*100000000000000^6387 ≤ 42599253228479^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240616657 10000000000 42599253228479 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2117118289/10000000000 : ℝ), (5419660183/10000000000 : ℝ), (5240616657/10000000000 : ℝ)] ![(2573797658681/20000000000000 : ℝ), (11132939616113/25000000000000 : ℝ), (42599253228479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2117118289/10000000000 : ℝ)|^8435 ≤ (2573797658681/20000000000000 : ℝ)^6387
        have hw : |(-2117118289/10000000000 : ℝ)|=(2117118289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5419660183/10000000000 : ℝ)|^8435 ≤ (11132939616113/25000000000000 : ℝ)^6387
        have hw : |(5419660183/10000000000 : ℝ)|=(5419660183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5240616657/10000000000 : ℝ)|^8435 ≤ (42599253228479/100000000000000 : ℝ)^6387
        have hw : |(5240616657/10000000000 : ℝ)|=(5240616657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s3_1 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5351490123/10000000000 : ℝ)*x 0 + (-2208455393/10000000000 : ℝ)*x 1 + (5240616781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351490123/10000000000 : ℝ)^8435 ≤ (43793513608149/100000000000000 : ℝ)^6387 := by
    have hnat : (5351490123 : ℕ)^8435*100000000000000^6387 ≤ 43793513608149^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351490123 10000000000 43793513608149 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2208455393/10000000000 : ℝ)^8435 ≤ (6803615909039/50000000000000 : ℝ)^6387 := by
    have hnat : (2208455393 : ℕ)^8435*50000000000000^6387 ≤ 6803615909039^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2208455393 10000000000 6803615909039 50000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5240616781/10000000000 : ℝ)^8435 ≤ (42599254559637/100000000000000 : ℝ)^6387 := by
    have hnat : (5240616781 : ℕ)^8435*100000000000000^6387 ≤ 42599254559637^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240616781 10000000000 42599254559637 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351490123/10000000000 : ℝ), (-2208455393/10000000000 : ℝ), (5240616781/10000000000 : ℝ)] ![(43793513608149/100000000000000 : ℝ), (6803615909039/50000000000000 : ℝ), (42599254559637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351490123/10000000000 : ℝ)|^8435 ≤ (43793513608149/100000000000000 : ℝ)^6387
        have hw : |(5351490123/10000000000 : ℝ)|=(5351490123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2208455393/10000000000 : ℝ)|^8435 ≤ (6803615909039/50000000000000 : ℝ)^6387
        have hw : |(-2208455393/10000000000 : ℝ)|=(2208455393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5240616781/10000000000 : ℝ)|^8435 ≤ (42599254559637/100000000000000 : ℝ)^6387
        have hw : |(5240616781/10000000000 : ℝ)|=(5240616781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s3_2 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1337872511/2500000000 : ℝ)*x 0 + (20471161/39062500 : ℝ)*x 1 + (-552113731/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337872511/2500000000 : ℝ)^8435 ≤ (43793512754361/100000000000000 : ℝ)^6387 := by
    have hnat : (1337872511 : ℕ)^8435*100000000000000^6387 ≤ 43793512754361^6387*2500000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337872511 2500000000 43793512754361 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20471161/39062500 : ℝ)^8435 ≤ (42599259229423/100000000000000 : ℝ)^6387 := by
    have hnat : (20471161 : ℕ)^8435*100000000000000^6387 ≤ 42599259229423^6387*39062500^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20471161 39062500 42599259229423 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (552113731/2500000000 : ℝ)^8435 ≤ (13607228001781/100000000000000 : ℝ)^6387 := by
    have hnat : (552113731 : ℕ)^8435*100000000000000^6387 ≤ 13607228001781^6387*2500000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552113731 2500000000 13607228001781 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337872511/2500000000 : ℝ), (20471161/39062500 : ℝ), (-552113731/2500000000 : ℝ)] ![(43793512754361/100000000000000 : ℝ), (42599259229423/100000000000000 : ℝ), (13607228001781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337872511/2500000000 : ℝ)|^8435 ≤ (43793512754361/100000000000000 : ℝ)^6387
        have hw : |(1337872511/2500000000 : ℝ)|=(1337872511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(20471161/39062500 : ℝ)|^8435 ≤ (42599259229423/100000000000000 : ℝ)^6387
        have hw : |(20471161/39062500 : ℝ)|=(20471161/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-552113731/2500000000 : ℝ)|^8435 ≤ (13607228001781/100000000000000 : ℝ)^6387
        have hw : |(-552113731/2500000000 : ℝ)|=(552113731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s3_3 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1087268603/2500000000 : ℝ)*x 0 + (1042789109/2500000000 : ℝ)*x 1 + (4534357439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087268603/2500000000 : ℝ)^8435 ≤ (33300312286301/100000000000000 : ℝ)^6387 := by
    have hnat : (1087268603 : ℕ)^8435*100000000000000^6387 ≤ 33300312286301^6387*2500000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087268603 2500000000 33300312286301 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042789109/2500000000 : ℝ)^8435 ≤ (1969569147773/6250000000000 : ℝ)^6387 := by
    have hnat : (1042789109 : ℕ)^8435*6250000000000^6387 ≤ 1969569147773^6387*2500000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042789109 2500000000 1969569147773 6250000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4534357439/10000000000 : ℝ)^8435 ≤ (2199161333627/6250000000000 : ℝ)^6387 := by
    have hnat : (4534357439 : ℕ)^8435*6250000000000^6387 ≤ 2199161333627^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4534357439 10000000000 2199161333627 6250000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087268603/2500000000 : ℝ), (1042789109/2500000000 : ℝ), (4534357439/10000000000 : ℝ)] ![(33300312286301/100000000000000 : ℝ), (1969569147773/6250000000000 : ℝ), (2199161333627/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087268603/2500000000 : ℝ)|^8435 ≤ (33300312286301/100000000000000 : ℝ)^6387
        have hw : |(1087268603/2500000000 : ℝ)|=(1087268603/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1042789109/2500000000 : ℝ)|^8435 ≤ (1969569147773/6250000000000 : ℝ)^6387
        have hw : |(1042789109/2500000000 : ℝ)|=(1042789109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4534357439/10000000000 : ℝ)|^8435 ≤ (2199161333627/6250000000000 : ℝ)^6387
        have hw : |(4534357439/10000000000 : ℝ)|=(4534357439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s3_4 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-132320783/625000000 : ℝ)*x 0 + (5241267423/10000000000 : ℝ)*x 1 + (541900583/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132320783/625000000 : ℝ)^8435 ≤ (12869102598979/100000000000000 : ℝ)^6387 := by
    have hnat : (132320783 : ℕ)^8435*100000000000000^6387 ≤ 12869102598979^6387*625000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132320783 625000000 12869102598979 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5241267423/10000000000 : ℝ)^8435 ≤ (42606239432501/100000000000000 : ℝ)^6387 := by
    have hnat : (5241267423 : ℕ)^8435*100000000000000^6387 ≤ 42606239432501^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241267423 10000000000 42606239432501 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541900583/1000000000 : ℝ)^8435 ≤ (8904931590543/20000000000000 : ℝ)^6387 := by
    have hnat : (541900583 : ℕ)^8435*20000000000000^6387 ≤ 8904931590543^6387*1000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541900583 1000000000 8904931590543 20000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-132320783/625000000 : ℝ), (5241267423/10000000000 : ℝ), (541900583/1000000000 : ℝ)] ![(12869102598979/100000000000000 : ℝ), (42606239432501/100000000000000 : ℝ), (8904931590543/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-132320783/625000000 : ℝ)|^8435 ≤ (12869102598979/100000000000000 : ℝ)^6387
        have hw : |(-132320783/625000000 : ℝ)|=(132320783/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5241267423/10000000000 : ℝ)|^8435 ≤ (42606239432501/100000000000000 : ℝ)^6387
        have hw : |(5241267423/10000000000 : ℝ)|=(5241267423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541900583/1000000000 : ℝ)|^8435 ≤ (8904931590543/20000000000000 : ℝ)^6387
        have hw : |(541900583/1000000000 : ℝ)|=(541900583/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s3_5 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2652905701/5000000000 : ℝ)*x 0 + (-2030066869/10000000000 : ℝ)*x 1 + (1083801167/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652905701/5000000000 : ℝ)^8435 ≤ (43300520011599/100000000000000 : ℝ)^6387 := by
    have hnat : (2652905701 : ℕ)^8435*100000000000000^6387 ≤ 43300520011599^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652905701 5000000000 43300520011599 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2030066869/10000000000 : ℝ)^8435 ≤ (12174821960473/100000000000000 : ℝ)^6387 := by
    have hnat : (2030066869 : ℕ)^8435*100000000000000^6387 ≤ 12174821960473^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2030066869 10000000000 12174821960473 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083801167/2000000000 : ℝ)^8435 ≤ (4452465800697/10000000000000 : ℝ)^6387 := by
    have hnat : (1083801167 : ℕ)^8435*10000000000000^6387 ≤ 4452465800697^6387*2000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083801167 2000000000 4452465800697 10000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652905701/5000000000 : ℝ), (-2030066869/10000000000 : ℝ), (1083801167/2000000000 : ℝ)] ![(43300520011599/100000000000000 : ℝ), (12174821960473/100000000000000 : ℝ), (4452465800697/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652905701/5000000000 : ℝ)|^8435 ≤ (43300520011599/100000000000000 : ℝ)^6387
        have hw : |(2652905701/5000000000 : ℝ)|=(2652905701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2030066869/10000000000 : ℝ)|^8435 ≤ (12174821960473/100000000000000 : ℝ)^6387
        have hw : |(-2030066869/10000000000 : ℝ)|=(2030066869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083801167/2000000000 : ℝ)|^8435 ≤ (4452465800697/10000000000000 : ℝ)^6387
        have hw : |(1083801167/2000000000 : ℝ)|=(1083801167/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s3_6 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2652906311/5000000000 : ℝ)*x 0 + (5419005099/10000000000 : ℝ)*x 1 + (-1015033109/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652906311/5000000000 : ℝ)^8435 ≤ (2706283322531/6250000000000 : ℝ)^6387 := by
    have hnat : (2652906311 : ℕ)^8435*6250000000000^6387 ≤ 2706283322531^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652906311 5000000000 2706283322531 6250000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5419005099/10000000000 : ℝ)^8435 ≤ (8904930004129/20000000000000 : ℝ)^6387 := by
    have hnat : (5419005099 : ℕ)^8435*20000000000000^6387 ≤ 8904930004129^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419005099 10000000000 8904930004129 20000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1015033109/5000000000 : ℝ)^8435 ≤ (3043704201093/25000000000000 : ℝ)^6387 := by
    have hnat : (1015033109 : ℕ)^8435*25000000000000^6387 ≤ 3043704201093^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015033109 5000000000 3043704201093 25000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652906311/5000000000 : ℝ), (5419005099/10000000000 : ℝ), (-1015033109/5000000000 : ℝ)] ![(2706283322531/6250000000000 : ℝ), (8904930004129/20000000000000 : ℝ), (3043704201093/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652906311/5000000000 : ℝ)|^8435 ≤ (2706283322531/6250000000000 : ℝ)^6387
        have hw : |(2652906311/5000000000 : ℝ)|=(2652906311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5419005099/10000000000 : ℝ)|^8435 ≤ (8904930004129/20000000000000 : ℝ)^6387
        have hw : |(5419005099/10000000000 : ℝ)|=(5419005099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1015033109/5000000000 : ℝ)|^8435 ≤ (3043704201093/25000000000000 : ℝ)^6387
        have hw : |(-1015033109/5000000000 : ℝ)|=(1015033109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s3_7 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4349103267/10000000000 : ℝ)*x 0 + (566629707/1250000000 : ℝ)*x 1 + (4172482653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349103267/10000000000 : ℝ)^8435 ≤ (33300604070103/100000000000000 : ℝ)^6387 := by
    have hnat : (4349103267 : ℕ)^8435*100000000000000^6387 ≤ 33300604070103^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349103267 10000000000 33300604070103 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (566629707/1250000000 : ℝ)^8435 ≤ (17586528254963/50000000000000 : ℝ)^6387 := by
    have hnat : (566629707 : ℕ)^8435*50000000000000^6387 ≤ 17586528254963^6387*1250000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566629707 1250000000 17586528254963 50000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172482653/10000000000 : ℝ)^8435 ≤ (1576316970233/5000000000000 : ℝ)^6387 := by
    have hnat : (4172482653 : ℕ)^8435*5000000000000^6387 ≤ 1576316970233^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172482653 10000000000 1576316970233 5000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349103267/10000000000 : ℝ), (566629707/1250000000 : ℝ), (4172482653/10000000000 : ℝ)] ![(33300604070103/100000000000000 : ℝ), (17586528254963/50000000000000 : ℝ), (1576316970233/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349103267/10000000000 : ℝ)|^8435 ≤ (33300604070103/100000000000000 : ℝ)^6387
        have hw : |(4349103267/10000000000 : ℝ)|=(4349103267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(566629707/1250000000 : ℝ)|^8435 ≤ (17586528254963/50000000000000 : ℝ)^6387
        have hw : |(566629707/1250000000 : ℝ)|=(566629707/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172482653/10000000000 : ℝ)|^8435 ≤ (1576316970233/5000000000000 : ℝ)^6387
        have hw : |(4172482653/10000000000 : ℝ)|=(4172482653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1242_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151428527/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16223/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9499/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10911/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14701/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16223/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9499/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16223/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9499/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16223/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9499/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16223/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9499/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16223/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9499/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16223/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9499/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9499/100000 : ℝ) ^ (4217/1024 : ℝ) ≤ (6164669763189907/100000000000000000000 : ℝ) := by
    have hpowers : (9499/100000 : ℝ)^4217 ≤ (6164669763189907/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9499 : ℕ)^4217*100000000000000000000^1024 ≤ 6164669763189907^1024*100000^4217 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9499 100000 6164669763189907 100000000000000000000 4217 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9499/100000 : ℝ)) (X := (6164669763189907/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16223/100000 : ℝ) ^ (4217/1024 : ℝ) ≤ (55871529790939819/100000000000000000000 : ℝ) := by
    have hpowers : (16223/100000 : ℝ)^4217 ≤ (55871529790939819/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16223 : ℕ)^4217*100000000000000000000^1024 ≤ 55871529790939819^1024*100000^4217 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16223 100000 55871529790939819 100000000000000000000 4217 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16223/100000 : ℝ)) (X := (55871529790939819/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006164669763189907/50000000000000000000 : ℝ) ≤ (5000149687626347/5000000000000000 : ℝ) ^ (4217/1024 : ℝ) := by
    have hpowers : (50006164669763189907/50000000000000000000 : ℝ)^1024 ≤ (5000149687626347/5000000000000000 : ℝ)^4217 := by
      have hnat : (50006164669763189907 : ℕ)^1024*5000000000000000^4217 ≤ 5000149687626347^4217*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006164669763189907 50000000000000000000 5000149687626347 5000000000000000 1024 4217 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000149687626347/5000000000000000 : ℝ)) (X := (50006164669763189907/50000000000000000000 : ℝ)) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50031018099777064863/50000000000000000000 : ℝ) ≤ (10001506050609793/10000000000000000 : ℝ) ^ (4217/1024 : ℝ) := by
    have hpowers : (50031018099777064863/50000000000000000000 : ℝ)^1024 ≤ (10001506050609793/10000000000000000 : ℝ)^4217 := by
      have hnat : (50031018099777064863 : ℕ)^1024*10000000000000000^4217 ≤ 10001506050609793^4217*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031018099777064863 50000000000000000000 10001506050609793 10000000000000000 1024 4217 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001506050609793/10000000000000000 : ℝ)) (X := (50031018099777064863/50000000000000000000 : ℝ)) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50055871529790939819/50000000000000000000 : ℝ) ≤ (2500678181491723/2500000000000000 : ℝ) ^ (4217/1024 : ℝ) := by
    have hpowers : (50055871529790939819/50000000000000000000 : ℝ)^1024 ≤ (2500678181491723/2500000000000000 : ℝ)^4217 := by
      have hnat : (50055871529790939819 : ℕ)^1024*2500000000000000^4217 ≤ 2500678181491723^4217*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50055871529790939819 50000000000000000000 2500678181491723 2500000000000000 1024 4217 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500678181491723/2500000000000000 : ℝ)) (X := (50055871529790939819/50000000000000000000 : ℝ)) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6164669763189907/100000000000000000000 : ℝ) ≤ ((33609544290382473827/33620000000000000000 : ℝ)+2*(1206675357099/672400000000000 : ℝ)*(9499/100000 : ℝ))^(4217/1024 : ℝ) := by
    rw [show (33609544290382473827/33620000000000000000 : ℝ)+2*(1206675357099/672400000000000 : ℝ)*(9499/100000 : ℝ)=(5000149687626347/5000000000000000 : ℝ) by norm_num, show 1+2*(6164669763189907/100000000000000000000 : ℝ)=(50006164669763189907/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(55871529790939819/100000000000000000000 : ℝ)+(6164669763189907/100000000000000000000 : ℝ) ≤ ((33609544290382473827/33620000000000000000 : ℝ)+(1206675357099/672400000000000 : ℝ)*((16223/100000 : ℝ)+(9499/100000 : ℝ)))^(4217/1024 : ℝ) := by
    rw [show (33609544290382473827/33620000000000000000 : ℝ)+(1206675357099/672400000000000 : ℝ)*((16223/100000 : ℝ)+(9499/100000 : ℝ))=(10001506050609793/10000000000000000 : ℝ) by norm_num, show 1+(55871529790939819/100000000000000000000 : ℝ)+(6164669763189907/100000000000000000000 : ℝ)=(50031018099777064863/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(55871529790939819/100000000000000000000 : ℝ) ≤ ((33609544290382473827/33620000000000000000 : ℝ)+2*(1206675357099/672400000000000 : ℝ)*(16223/100000 : ℝ))^(4217/1024 : ℝ) := by
    rw [show (33609544290382473827/33620000000000000000 : ℝ)+2*(1206675357099/672400000000000 : ℝ)*(16223/100000 : ℝ)=(2500678181491723/2500000000000000 : ℝ) by norm_num, show 1+2*(55871529790939819/100000000000000000000 : ℝ)=(50055871529790939819/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (33609544290382473827/33620000000000000000 : ℝ)*(X 1 0+X 2 0)+(1206675357099/672400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4217/1024 : ℝ)) (lo := (9499/100000 : ℝ)) (hi := (16223/100000 : ℝ)) (c := (33609544290382473827/33620000000000000000 : ℝ)) (alpha := (1206675357099/672400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (33609544290382473827/33620000000000000000 : ℝ)*(X 0 1+X 2 1)+(1206675357099/672400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4217/1024 : ℝ)) (lo := (9499/100000 : ℝ)) (hi := (16223/100000 : ℝ)) (c := (33609544290382473827/33620000000000000000 : ℝ)) (alpha := (1206675357099/672400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (33609544290382473827/33620000000000000000 : ℝ)*(X 0 2+X 1 2)+(1206675357099/672400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4217/1024 : ℝ)) (lo := (9499/100000 : ℝ)) (hi := (16223/100000 : ℝ)) (c := (33609544290382473827/33620000000000000000 : ℝ)) (alpha := (1206675357099/672400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2117118289/10000000000 : ℝ)*X 0 0+(5419660183/10000000000 : ℝ)*X 0 1+(5240616657/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351490123/10000000000 : ℝ)*X 1 0+(-2208455393/10000000000 : ℝ)*X 1 1+(5240616781/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337872511/2500000000 : ℝ)*X 2 0+(20471161/39062500 : ℝ)*X 2 1+(-552113731/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1087268603/2500000000 : ℝ)*X 0 0+(1042789109/2500000000 : ℝ)*X 0 1+(4534357439/10000000000 : ℝ)*X 0 2+(1087268603/2500000000 : ℝ)*X 1 0+(1042789109/2500000000 : ℝ)*X 1 1+(4534357439/10000000000 : ℝ)*X 1 2+(1087268603/2500000000 : ℝ)*X 2 0+(1042789109/2500000000 : ℝ)*X 2 1+(4534357439/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-132320783/625000000 : ℝ)*X 0 0+(5241267423/10000000000 : ℝ)*X 0 1+(541900583/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652905701/5000000000 : ℝ)*X 1 0+(-2030066869/10000000000 : ℝ)*X 1 1+(1083801167/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652906311/5000000000 : ℝ)*X 2 0+(5419005099/10000000000 : ℝ)*X 2 1+(-1015033109/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4349103267/10000000000 : ℝ)*X 0 0+(566629707/1250000000 : ℝ)*X 0 1+(4172482653/10000000000 : ℝ)*X 0 2+(4349103267/10000000000 : ℝ)*X 1 0+(566629707/1250000000 : ℝ)*X 1 1+(4172482653/10000000000 : ℝ)*X 1 2+(4349103267/10000000000 : ℝ)*X 2 0+(566629707/1250000000 : ℝ)*X 2 1+(4172482653/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3328308776796681542241229407/420250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (109121479/10000000000000 : ℝ)*(base19) + (339587143/50000000000000 : ℝ)*(base23) + (196460903/100000000000000 : ℝ)*(lower2) + (47518967/50000000000000 : ℝ)*(upper5) + (1042327593035847/25000000000000 : ℝ)*(major0) + (1042327593035847/25000000000000 : ℝ)*(major1) + (1042327593035847/25000000000000 : ℝ)*(major2) + (5585264110142317/100000000000000 : ℝ)*(sp0) + (2792648007343433/50000000000000 : ℝ)*(sp1) + (1117060164604273/20000000000000 : ℝ)*(sp2) + (137665383152783/5000000000000 : ℝ)*(sp3) + (37392053333/100000000000000 : ℝ)*(sp4) + (879258799/20000000000000 : ℝ)*(sp5) + (11315041107/100000000000000 : ℝ)*(sp7) + (21510304516381/781250000000 : ℝ)*(f.failure) + (5585301502195651/100000000000000 : ℝ)*(f.sum) + (24985610894207/8405000000000000000000000000 : ℝ)*base66 + (2338069169048073531/840500000000000000000000000000000 : ℝ)*base68 + (5681654499907926469/840500000000000000000000000000000 : ℝ)*base69 + (6565058124135573531/840500000000000000000000000000000 : ℝ)*base72 + (662414546271/4202500000000000000000000000 : ℝ)*base74 + (531030276928073531/840500000000000000000000000000000 : ℝ)*base76 + (10879658434908426469/840500000000000000000000000000000 : ℝ)*base77 + (1762398086333073531/840500000000000000000000000000000 : ℝ)*base80 + (10083430938849/4202500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (325787/78125000000000000000 : ℝ)*base89 + (325787/78125000000000000000 : ℝ)*base91 + (325787/78125000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (269704804707886593961539/33620000000000000000000000000 : ℝ) := by norm_num
    linear_combination (887426471/100000000000000 : ℝ)*(base19) + (22164833/781250000000 : ℝ)*(base23) + (97862191/50000000000000 : ℝ)*(upper3) + (189965327/100000000000000 : ℝ)*(lower4) + (90845271/50000000000000 : ℝ)*(upper5) + (4199879797265293/100000000000000 : ℝ)*(major0) + (4199879797265293/100000000000000 : ℝ)*(major1) + (4199879797265293/100000000000000 : ℝ)*(major2) + (478994171/4000000000000 : ℝ)*(sp1) + (11646401149/25000000000000 : ℝ)*(sp2) + (1125250597378643/20000000000000 : ℝ)*(sp4) + (5626240124612469/100000000000000 : ℝ)*(sp5) + (2813101782094997/50000000000000 : ℝ)*(sp6) + (1386753170116121/50000000000000 : ℝ)*(sp7) + (1386753170116121/50000000000000 : ℝ)*(f.failure) + (1125250597378643/20000000000000 : ℝ)*(f.sum) + (171919688764727/33620000000000000000000000000 : ℝ)*base65 + (17795293557315663689/3362000000000000000000000000000000 : ℝ)*base68 + (16542954538313663689/3362000000000000000000000000000000 : ℝ)*base70 + (4100093597324336311/3362000000000000000000000000000000 : ℝ)*base71 + (93521071234913/33620000000000000000000000000 : ℝ)*base74 + (31829638860593663689/3362000000000000000000000000000000 : ℝ)*base76 + (1721313425626336311/3362000000000000000000000000000000 : ℝ)*base77 + (45753670202370336311/3362000000000000000000000000000000 : ℝ)*base79 + (79528313404407/33620000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (28016233/5000000000000000000000 : ℝ)*base90 + (28016233/5000000000000000000000 : ℝ)*base92 + (28016233/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1242_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151428527/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16223/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9499/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10911/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14701/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1242_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1242_s4_0 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-66231529/312500000 : ℝ)*x 0 + (5397496997/10000000000 : ℝ)*x 1 + (5261278909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66231529/312500000 : ℝ)^8435 ≤ (12887379889207/100000000000000 : ℝ)^6387 := by
    have hnat : (66231529 : ℕ)^8435*100000000000000^6387 ≤ 12887379889207^6387*312500000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66231529 312500000 12887379889207 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397496997/10000000000 : ℝ)^8435 ≤ (11072853648183/25000000000000 : ℝ)^6387 := by
    have hnat : (5397496997 : ℕ)^8435*25000000000000^6387 ≤ 11072853648183^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397496997 10000000000 11072853648183 25000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261278909/10000000000 : ℝ)^8435 ≤ (42821205509127/100000000000000 : ℝ)^6387 := by
    have hnat : (5261278909 : ℕ)^8435*100000000000000^6387 ≤ 42821205509127^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261278909 10000000000 42821205509127 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-66231529/312500000 : ℝ), (5397496997/10000000000 : ℝ), (5261278909/10000000000 : ℝ)] ![(12887379889207/100000000000000 : ℝ), (11072853648183/25000000000000 : ℝ), (42821205509127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-66231529/312500000 : ℝ)|^8435 ≤ (12887379889207/100000000000000 : ℝ)^6387
        have hw : |(-66231529/312500000 : ℝ)|=(66231529/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397496997/10000000000 : ℝ)|^8435 ≤ (11072853648183/25000000000000 : ℝ)^6387
        have hw : |(5397496997/10000000000 : ℝ)|=(5397496997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261278909/10000000000 : ℝ)|^8435 ≤ (42821205509127/100000000000000 : ℝ)^6387
        have hw : |(5261278909/10000000000 : ℝ)|=(5261278909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s4_1 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345903269/10000000000 : ℝ)*x 0 + (-437713849/2000000000 : ℝ)*x 1 + (657659863/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345903269/10000000000 : ℝ)^8435 ≤ (43733144071693/100000000000000 : ℝ)^6387 := by
    have hnat : (5345903269 : ℕ)^8435*100000000000000^6387 ≤ 43733144071693^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345903269 10000000000 43733144071693 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (437713849/2000000000 : ℝ)^8435 ≤ (13445650451057/100000000000000 : ℝ)^6387 := by
    have hnat : (437713849 : ℕ)^8435*100000000000000^6387 ≤ 13445650451057^6387*2000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437713849 2000000000 13445650451057 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657659863/1250000000 : ℝ)^8435 ≤ (42821205455383/100000000000000 : ℝ)^6387 := by
    have hnat : (657659863 : ℕ)^8435*100000000000000^6387 ≤ 42821205455383^6387*1250000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657659863 1250000000 42821205455383 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345903269/10000000000 : ℝ), (-437713849/2000000000 : ℝ), (657659863/1250000000 : ℝ)] ![(43733144071693/100000000000000 : ℝ), (13445650451057/100000000000000 : ℝ), (42821205455383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345903269/10000000000 : ℝ)|^8435 ≤ (43733144071693/100000000000000 : ℝ)^6387
        have hw : |(5345903269/10000000000 : ℝ)|=(5345903269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-437713849/2000000000 : ℝ)|^8435 ≤ (13445650451057/100000000000000 : ℝ)^6387
        have hw : |(-437713849/2000000000 : ℝ)|=(437713849/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(657659863/1250000000 : ℝ)|^8435 ≤ (42821205455383/100000000000000 : ℝ)^6387
        have hw : |(657659863/1250000000 : ℝ)|=(657659863/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s4_2 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672951631/5000000000 : ℝ)*x 0 + (5261278927/10000000000 : ℝ)*x 1 + (-87542769/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672951631/5000000000 : ℝ)^8435 ≤ (21866571998033/50000000000000 : ℝ)^6387 := by
    have hnat : (2672951631 : ℕ)^8435*50000000000000^6387 ≤ 21866571998033^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672951631 5000000000 21866571998033 50000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5261278927/10000000000 : ℝ)^8435 ≤ (42821205702603/100000000000000 : ℝ)^6387 := by
    have hnat : (5261278927 : ℕ)^8435*100000000000000^6387 ≤ 42821205702603^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261278927 10000000000 42821205702603 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (87542769/400000000 : ℝ)^8435 ≤ (13445650288787/100000000000000 : ℝ)^6387 := by
    have hnat : (87542769 : ℕ)^8435*100000000000000^6387 ≤ 13445650288787^6387*400000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87542769 400000000 13445650288787 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672951631/5000000000 : ℝ), (5261278927/10000000000 : ℝ), (-87542769/400000000 : ℝ)] ![(21866571998033/50000000000000 : ℝ), (42821205702603/100000000000000 : ℝ), (13445650288787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672951631/5000000000 : ℝ)|^8435 ≤ (21866571998033/50000000000000 : ℝ)^6387
        have hw : |(2672951631/5000000000 : ℝ)|=(2672951631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5261278927/10000000000 : ℝ)|^8435 ≤ (42821205702603/100000000000000 : ℝ)^6387
        have hw : |(5261278927/10000000000 : ℝ)|=(5261278927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-87542769/400000000 : ℝ)|^8435 ≤ (13445650288787/100000000000000 : ℝ)^6387
        have hw : |(-87542769/400000000 : ℝ)|=(87542769/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s4_3 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (271903059/625000000 : ℝ)*x 0 + (84288351/200000000 : ℝ)*x 1 + (4490745507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271903059/625000000 : ℝ)^8435 ≤ (8328553085157/25000000000000 : ℝ)^6387 := by
    have hnat : (271903059 : ℕ)^8435*25000000000000^6387 ≤ 8328553085157^6387*625000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271903059 625000000 8328553085157 25000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84288351/200000000 : ℝ)^8435 ≤ (15972730675783/50000000000000 : ℝ)^6387 := by
    have hnat : (84288351 : ℕ)^8435*50000000000000^6387 ≤ 15972730675783^6387*200000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84288351 200000000 15972730675783 50000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4490745507/10000000000 : ℝ)^8435 ≤ (1085635196621/3125000000000 : ℝ)^6387 := by
    have hnat : (4490745507 : ℕ)^8435*3125000000000^6387 ≤ 1085635196621^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490745507 10000000000 1085635196621 3125000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(271903059/625000000 : ℝ), (84288351/200000000 : ℝ), (4490745507/10000000000 : ℝ)] ![(8328553085157/25000000000000 : ℝ), (15972730675783/50000000000000 : ℝ), (1085635196621/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(271903059/625000000 : ℝ)|^8435 ≤ (8328553085157/25000000000000 : ℝ)^6387
        have hw : |(271903059/625000000 : ℝ)|=(271903059/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84288351/200000000 : ℝ)|^8435 ≤ (15972730675783/50000000000000 : ℝ)^6387
        have hw : |(84288351/200000000 : ℝ)|=(84288351/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4490745507/10000000000 : ℝ)|^8435 ≤ (1085635196621/3125000000000 : ℝ)^6387
        have hw : |(4490745507/10000000000 : ℝ)|=(4490745507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s4_4 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1059707571/5000000000 : ℝ)*x 0 + (5261656129/10000000000 : ℝ)*x 1 + (2698559121/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059707571/5000000000 : ℝ)^8435 ≤ (2577485958047/20000000000000 : ℝ)^6387 := by
    have hnat : (1059707571 : ℕ)^8435*20000000000000^6387 ≤ 2577485958047^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059707571 5000000000 2577485958047 20000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5261656129/10000000000 : ℝ)^8435 ≤ (42825260178419/100000000000000 : ℝ)^6387 := by
    have hnat : (5261656129 : ℕ)^8435*100000000000000^6387 ≤ 42825260178419^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261656129 10000000000 42825260178419 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698559121/5000000000 : ℝ)^8435 ≤ (44287310012009/100000000000000 : ℝ)^6387 := by
    have hnat : (2698559121 : ℕ)^8435*100000000000000^6387 ≤ 44287310012009^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698559121 5000000000 44287310012009 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1059707571/5000000000 : ℝ), (5261656129/10000000000 : ℝ), (2698559121/5000000000 : ℝ)] ![(2577485958047/20000000000000 : ℝ), (42825260178419/100000000000000 : ℝ), (44287310012009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1059707571/5000000000 : ℝ)|^8435 ≤ (2577485958047/20000000000000 : ℝ)^6387
        have hw : |(-1059707571/5000000000 : ℝ)|=(1059707571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5261656129/10000000000 : ℝ)|^8435 ≤ (42825260178419/100000000000000 : ℝ)^6387
        have hw : |(5261656129/10000000000 : ℝ)|=(5261656129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698559121/5000000000 : ℝ)|^8435 ≤ (44287310012009/100000000000000 : ℝ)^6387
        have hw : |(2698559121/5000000000 : ℝ)|=(2698559121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s4_5 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311148407/10000000000 : ℝ)*x 0 + (-2052729807/10000000000 : ℝ)*x 1 + (5397118279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311148407/10000000000 : ℝ)^8435 ≤ (5419756296589/12500000000000 : ℝ)^6387 := by
    have hnat : (5311148407 : ℕ)^8435*12500000000000^6387 ≤ 5419756296589^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311148407 10000000000 5419756296589 12500000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2052729807/10000000000 : ℝ)^8435 ≤ (12354639196519/100000000000000 : ℝ)^6387 := by
    have hnat : (2052729807 : ℕ)^8435*100000000000000^6387 ≤ 12354639196519^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2052729807 10000000000 12354639196519 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5397118279/10000000000 : ℝ)^8435 ≤ (1771492416519/4000000000000 : ℝ)^6387 := by
    have hnat : (5397118279 : ℕ)^8435*4000000000000^6387 ≤ 1771492416519^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397118279 10000000000 1771492416519 4000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311148407/10000000000 : ℝ), (-2052729807/10000000000 : ℝ), (5397118279/10000000000 : ℝ)] ![(5419756296589/12500000000000 : ℝ), (12354639196519/100000000000000 : ℝ), (1771492416519/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311148407/10000000000 : ℝ)|^8435 ≤ (5419756296589/12500000000000 : ℝ)^6387
        have hw : |(5311148407/10000000000 : ℝ)|=(5311148407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2052729807/10000000000 : ℝ)|^8435 ≤ (12354639196519/100000000000000 : ℝ)^6387
        have hw : |(-2052729807/10000000000 : ℝ)|=(2052729807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5397118279/10000000000 : ℝ)|^8435 ≤ (1771492416519/4000000000000 : ℝ)^6387
        have hw : |(5397118279/10000000000 : ℝ)|=(5397118279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s4_6 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655574207/5000000000 : ℝ)*x 0 + (269855911/500000000 : ℝ)*x 1 + (-2052729879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655574207/5000000000 : ℝ)^8435 ≤ (2167902522409/5000000000000 : ℝ)^6387 := by
    have hnat : (2655574207 : ℕ)^8435*5000000000000^6387 ≤ 2167902522409^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655574207 5000000000 2167902522409 5000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269855911/500000000 : ℝ)^8435 ≤ (44287309773597/100000000000000 : ℝ)^6387 := by
    have hnat : (269855911 : ℕ)^8435*100000000000000^6387 ≤ 44287309773597^6387*500000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269855911 500000000 44287309773597 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2052729879/10000000000 : ℝ)^8435 ≤ (12354639768813/100000000000000 : ℝ)^6387 := by
    have hnat : (2052729879 : ℕ)^8435*100000000000000^6387 ≤ 12354639768813^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2052729879 10000000000 12354639768813 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655574207/5000000000 : ℝ), (269855911/500000000 : ℝ), (-2052729879/10000000000 : ℝ)] ![(2167902522409/5000000000000 : ℝ), (44287309773597/100000000000000 : ℝ), (12354639768813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655574207/5000000000 : ℝ)|^8435 ≤ (2167902522409/5000000000000 : ℝ)^6387
        have hw : |(2655574207/5000000000 : ℝ)|=(2655574207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269855911/500000000 : ℝ)|^8435 ≤ (44287309773597/100000000000000 : ℝ)^6387
        have hw : |(269855911/500000000 : ℝ)|=(269855911/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2052729879/10000000000 : ℝ)|^8435 ≤ (12354639768813/100000000000000 : ℝ)^6387
        have hw : |(-2052729879/10000000000 : ℝ)|=(2052729879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s4_7 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (87009229/200000000 : ℝ)*x 0 + (4489980231/10000000000 : ℝ)*x 1 + (1053796473/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (87009229/200000000 : ℝ)^8435 ≤ (33314338814923/100000000000000 : ℝ)^6387 := by
    have hnat : (87009229 : ℕ)^8435*100000000000000^6387 ≤ 33314338814923^6387*200000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87009229 200000000 33314338814923 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4489980231/10000000000 : ℝ)^8435 ≤ (4341563504573/12500000000000 : ℝ)^6387 := by
    have hnat : (4489980231 : ℕ)^8435*12500000000000^6387 ≤ 4341563504573^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489980231 10000000000 4341563504573 12500000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053796473/2500000000 : ℝ)^8435 ≤ (3994144141859/12500000000000 : ℝ)^6387 := by
    have hnat : (1053796473 : ℕ)^8435*12500000000000^6387 ≤ 3994144141859^6387*2500000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053796473 2500000000 3994144141859 12500000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(87009229/200000000 : ℝ), (4489980231/10000000000 : ℝ), (1053796473/2500000000 : ℝ)] ![(33314338814923/100000000000000 : ℝ), (4341563504573/12500000000000 : ℝ), (3994144141859/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(87009229/200000000 : ℝ)|^8435 ≤ (33314338814923/100000000000000 : ℝ)^6387
        have hw : |(87009229/200000000 : ℝ)|=(87009229/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4489980231/10000000000 : ℝ)|^8435 ≤ (4341563504573/12500000000000 : ℝ)^6387
        have hw : |(4489980231/10000000000 : ℝ)|=(4489980231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053796473/2500000000 : ℝ)|^8435 ≤ (3994144141859/12500000000000 : ℝ)^6387
        have hw : |(1053796473/2500000000 : ℝ)|=(1053796473/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1242_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151428527/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14701/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10911/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1419/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14237/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14701/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10911/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14701/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10911/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14701/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10911/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14701/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10911/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14701/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10911/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14701/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10911/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10911/100000 : ℝ) ^ (4217/1024 : ℝ) ≤ (10908584254418379/100000000000000000000 : ℝ) := by
    have hpowers : (10911/100000 : ℝ)^4217 ≤ (10908584254418379/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10911 : ℕ)^4217*100000000000000000000^1024 ≤ 10908584254418379^1024*100000^4217 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10911 100000 10908584254418379 100000000000000000000 4217 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10911/100000 : ℝ)) (X := (10908584254418379/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14701/100000 : ℝ) ^ (4217/1024 : ℝ) ≤ (2327436560197837/6250000000000000000 : ℝ) := by
    have hpowers : (14701/100000 : ℝ)^4217 ≤ (2327436560197837/6250000000000000000 : ℝ)^1024 := by
      have hnat : (14701 : ℕ)^4217*6250000000000000000^1024 ≤ 2327436560197837^1024*100000^4217 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14701 100000 2327436560197837 6250000000000000000 4217 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14701/100000 : ℝ)) (X := (2327436560197837/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010908584254418379/50000000000000000000 : ℝ) ≤ (1000052973525041/1000000000000000 : ℝ) ^ (4217/1024 : ℝ) := by
    have hpowers : (50010908584254418379/50000000000000000000 : ℝ)^1024 ≤ (1000052973525041/1000000000000000 : ℝ)^4217 := by
      have hnat : (50010908584254418379 : ℕ)^1024*1000000000000000^4217 ≤ 1000052973525041^4217*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010908584254418379 50000000000000000000 1000052973525041 1000000000000000 1024 4217 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000052973525041/1000000000000000 : ℝ)) (X := (50010908584254418379/50000000000000000000 : ℝ)) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048147569217583771/100000000000000000000 : ℝ) ≤ (10001168938260079/10000000000000000 : ℝ) ^ (4217/1024 : ℝ) := by
    have hpowers : (100048147569217583771/100000000000000000000 : ℝ)^1024 ≤ (10001168938260079/10000000000000000 : ℝ)^4217 := by
      have hnat : (100048147569217583771 : ℕ)^1024*10000000000000000^4217 ≤ 10001168938260079^4217*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048147569217583771 100000000000000000000 10001168938260079 10000000000000000 1024 4217 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001168938260079/10000000000000000 : ℝ)) (X := (100048147569217583771/100000000000000000000 : ℝ)) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3127327436560197837/3125000000000000000 : ℝ) ≤ (2500452035317437/2500000000000000 : ℝ) ^ (4217/1024 : ℝ) := by
    have hpowers : (3127327436560197837/3125000000000000000 : ℝ)^1024 ≤ (2500452035317437/2500000000000000 : ℝ)^4217 := by
      have hnat : (3127327436560197837 : ℕ)^1024*2500000000000000^4217 ≤ 2500452035317437^4217*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127327436560197837 3125000000000000000 2500452035317437 2500000000000000 1024 4217 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500452035317437/2500000000000000 : ℝ)) (X := (3127327436560197837/3125000000000000000 : ℝ)) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10908584254418379/100000000000000000000 : ℝ) ≤ ((18944029504261028491/18950000000000000000 : ℝ)+2*(639203009669/379000000000000 : ℝ)*(10911/100000 : ℝ))^(4217/1024 : ℝ) := by
    rw [show (18944029504261028491/18950000000000000000 : ℝ)+2*(639203009669/379000000000000 : ℝ)*(10911/100000 : ℝ)=(1000052973525041/1000000000000000 : ℝ) by norm_num, show 1+2*(10908584254418379/100000000000000000000 : ℝ)=(50010908584254418379/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2327436560197837/6250000000000000000 : ℝ)+(10908584254418379/100000000000000000000 : ℝ) ≤ ((18944029504261028491/18950000000000000000 : ℝ)+(639203009669/379000000000000 : ℝ)*((14701/100000 : ℝ)+(10911/100000 : ℝ)))^(4217/1024 : ℝ) := by
    rw [show (18944029504261028491/18950000000000000000 : ℝ)+(639203009669/379000000000000 : ℝ)*((14701/100000 : ℝ)+(10911/100000 : ℝ))=(10001168938260079/10000000000000000 : ℝ) by norm_num, show 1+(2327436560197837/6250000000000000000 : ℝ)+(10908584254418379/100000000000000000000 : ℝ)=(100048147569217583771/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2327436560197837/6250000000000000000 : ℝ) ≤ ((18944029504261028491/18950000000000000000 : ℝ)+2*(639203009669/379000000000000 : ℝ)*(14701/100000 : ℝ))^(4217/1024 : ℝ) := by
    rw [show (18944029504261028491/18950000000000000000 : ℝ)+2*(639203009669/379000000000000 : ℝ)*(14701/100000 : ℝ)=(2500452035317437/2500000000000000 : ℝ) by norm_num, show 1+2*(2327436560197837/6250000000000000000 : ℝ)=(3127327436560197837/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18944029504261028491/18950000000000000000 : ℝ)*(X 1 0+X 2 0)+(639203009669/379000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4217/1024 : ℝ)) (lo := (10911/100000 : ℝ)) (hi := (14701/100000 : ℝ)) (c := (18944029504261028491/18950000000000000000 : ℝ)) (alpha := (639203009669/379000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18944029504261028491/18950000000000000000 : ℝ)*(X 0 1+X 2 1)+(639203009669/379000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4217/1024 : ℝ)) (lo := (10911/100000 : ℝ)) (hi := (14701/100000 : ℝ)) (c := (18944029504261028491/18950000000000000000 : ℝ)) (alpha := (639203009669/379000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18944029504261028491/18950000000000000000 : ℝ)*(X 0 2+X 1 2)+(639203009669/379000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4217/1024 : ℝ)) (lo := (10911/100000 : ℝ)) (hi := (14701/100000 : ℝ)) (c := (18944029504261028491/18950000000000000000 : ℝ)) (alpha := (639203009669/379000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-66231529/312500000 : ℝ)*X 0 0+(5397496997/10000000000 : ℝ)*X 0 1+(5261278909/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345903269/10000000000 : ℝ)*X 1 0+(-437713849/2000000000 : ℝ)*X 1 1+(657659863/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672951631/5000000000 : ℝ)*X 2 0+(5261278927/10000000000 : ℝ)*X 2 1+(-87542769/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((271903059/625000000 : ℝ)*X 0 0+(84288351/200000000 : ℝ)*X 0 1+(4490745507/10000000000 : ℝ)*X 0 2+(271903059/625000000 : ℝ)*X 1 0+(84288351/200000000 : ℝ)*X 1 1+(4490745507/10000000000 : ℝ)*X 1 2+(271903059/625000000 : ℝ)*X 2 0+(84288351/200000000 : ℝ)*X 2 1+(4490745507/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1059707571/5000000000 : ℝ)*X 0 0+(5261656129/10000000000 : ℝ)*X 0 1+(2698559121/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311148407/10000000000 : ℝ)*X 1 0+(-2052729807/10000000000 : ℝ)*X 1 1+(5397118279/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2655574207/5000000000 : ℝ)*X 2 0+(269855911/500000000 : ℝ)*X 2 1+(-2052729879/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((87009229/200000000 : ℝ)*X 0 0+(4489980231/10000000000 : ℝ)*X 0 1+(1053796473/2500000000 : ℝ)*X 0 2+(87009229/200000000 : ℝ)*X 1 0+(4489980231/10000000000 : ℝ)*X 1 1+(1053796473/2500000000 : ℝ)*X 1 2+(87009229/200000000 : ℝ)*X 2 0+(4489980231/10000000000 : ℝ)*X 2 1+(1053796473/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3780048570457084724049689973/947500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (193587989/25000000000000 : ℝ)*(base19) + (692195437/100000000000000 : ℝ)*(base23) + (7756247/20000000000000 : ℝ)*(lower2) + (84637747/100000000000000 : ℝ)*(upper3) + (11977061/20000000000000 : ℝ)*(upper5) + (5480059115616501/100000000000000 : ℝ)*(major0) + (5480059115616501/100000000000000 : ℝ)*(major1) + (5480059115616501/100000000000000 : ℝ)*(major2) + (458824347575013/6250000000000 : ℝ)*(sp0) + (7341209298980867/100000000000000 : ℝ)*(sp1) + (3670604690568693/50000000000000 : ℝ)*(sp2) + (3618897726586377/100000000000000 : ℝ)*(sp3) + (4102426523/20000000000000 : ℝ)*(sp4) + (10298330553/100000000000000 : ℝ)*(sp7) + (361890802491693/10000000000000 : ℝ)*(f.failure) + (7341210073332823/100000000000000 : ℝ)*(f.sum) + (60528364128631/18950000000000000000000000000 : ℝ)*base66 + (19443253622380820009/1895000000000000000000000000000000 : ℝ)*base68 + (27275781680484179991/1895000000000000000000000000000000 : ℝ)*base69 + (18085931744895820009/1895000000000000000000000000000000 : ℝ)*base72 + (11880073000069/18950000000000000000000000000 : ℝ)*base73 + (3859549395585820009/1895000000000000000000000000000000 : ℝ)*base76 + (4987969322549179991/1895000000000000000000000000000000 : ℝ)*base77 + (14293291922725820009/1895000000000000000000000000000000 : ℝ)*base80 + (51895046741419/18950000000000000000000000000 : ℝ)*base81 + (9273789/1000000000000000000000 : ℝ)*base90 + (9273789/1000000000000000000000 : ℝ)*base92 + (9273789/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8362637554728034096473/1184375000000000000000000000 : ℝ) := by norm_num
    linear_combination (763288081/50000000000000 : ℝ)*(base19) + (777774617/50000000000000 : ℝ)*(base23) + (32416201/25000000000000 : ℝ)*(upper3) + (24315689/100000000000000 : ℝ)*(lower4) + (164959927/100000000000000 : ℝ)*(upper5) + (86103305275209/1562500000000 : ℝ)*(major0) + (86103305275209/1562500000000 : ℝ)*(major1) + (86103305275209/1562500000000 : ℝ)*(major2) + (2209646727/5000000000000 : ℝ)*(sp1) + (802747163/2000000000000 : ℝ)*(sp2) + (7382138681296357/100000000000000 : ℝ)*(sp4) + (1476418592357131/20000000000000 : ℝ)*(sp5) + (7382096988388973/100000000000000 : ℝ)*(sp6) + (3639084158570317/100000000000000 : ℝ)*(sp7) + (3639084158570317/100000000000000 : ℝ)*(f.failure) + (7382138681296357/100000000000000 : ℝ)*(f.sum) + (1636698958293/2368750000000000000000000000 : ℝ)*base65 + (186480459463970381/29609375000000000000000000000000 : ℝ)*base68 + (26559836554751631/29609375000000000000000000000000 : ℝ)*base70 + (53724907983444497/14804687500000000000000000000000 : ℝ)*base71 + (25341672412089/4737500000000000000000000000 : ℝ)*base74 + (12733529545216593/3701171875000000000000000000000 : ℝ)*base75 + (40407892938032881/29609375000000000000000000000000 : ℝ)*base78 + (25940093520667561/7402343750000000000000000000000 : ℝ)*base79 + (4114868513447/9475000000000000000000000000 : ℝ)*base81 + (70766941/10000000000000000000000 : ℝ)*base90 + (70766941/10000000000000000000000 : ℝ)*base92 + (70766941/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1242_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151428527/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14701/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10911/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1419/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1242_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1242_s5_0 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-211985761/1000000000 : ℝ)*x 0 + (674051243/1250000000 : ℝ)*x 1 + (658258891/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211985761/1000000000 : ℝ)^8435 ≤ (12890983114593/100000000000000 : ℝ)^6387 := by
    have hnat : (211985761 : ℕ)^8435*100000000000000^6387 ≤ 12890983114593^6387*1000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211985761 1000000000 12890983114593 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674051243/1250000000 : ℝ)^8435 ≤ (44236293739417/100000000000000 : ℝ)^6387 := by
    have hnat : (674051243 : ℕ)^8435*100000000000000^6387 ≤ 44236293739417^6387*1250000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674051243 1250000000 44236293739417 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658258891/1250000000 : ℝ)^8435 ≤ (42872723129567/100000000000000 : ℝ)^6387 := by
    have hnat : (658258891 : ℕ)^8435*100000000000000^6387 ≤ 42872723129567^6387*1250000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658258891 1250000000 42872723129567 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-211985761/1000000000 : ℝ), (674051243/1250000000 : ℝ), (658258891/1250000000 : ℝ)] ![(12890983114593/100000000000000 : ℝ), (44236293739417/100000000000000 : ℝ), (42872723129567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-211985761/1000000000 : ℝ)|^8435 ≤ (12890983114593/100000000000000 : ℝ)^6387
        have hw : |(-211985761/1000000000 : ℝ)|=(211985761/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674051243/1250000000 : ℝ)|^8435 ≤ (44236293739417/100000000000000 : ℝ)^6387
        have hw : |(674051243/1250000000 : ℝ)|=(674051243/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658258891/1250000000 : ℝ)|^8435 ≤ (42872723129567/100000000000000 : ℝ)^6387
        have hw : |(658258891/1250000000 : ℝ)|=(658258891/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s5_1 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344616301/10000000000 : ℝ)*x 0 + (-1091965849/5000000000 : ℝ)*x 1 + (5266071133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344616301/10000000000 : ℝ)^8435 ≤ (8743848084763/20000000000000 : ℝ)^6387 := by
    have hnat : (5344616301 : ℕ)^8435*20000000000000^6387 ≤ 8743848084763^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344616301 10000000000 8743848084763 20000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1091965849/5000000000 : ℝ)^8435 ≤ (268160727529/2000000000000 : ℝ)^6387 := by
    have hnat : (1091965849 : ℕ)^8435*2000000000000^6387 ≤ 268160727529^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091965849 5000000000 268160727529 2000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266071133/10000000000 : ℝ)^8435 ≤ (21436361591663/50000000000000 : ℝ)^6387 := by
    have hnat : (5266071133 : ℕ)^8435*50000000000000^6387 ≤ 21436361591663^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266071133 10000000000 21436361591663 50000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344616301/10000000000 : ℝ), (-1091965849/5000000000 : ℝ), (5266071133/10000000000 : ℝ)] ![(8743848084763/20000000000000 : ℝ), (268160727529/2000000000000 : ℝ), (21436361591663/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344616301/10000000000 : ℝ)|^8435 ≤ (8743848084763/20000000000000 : ℝ)^6387
        have hw : |(5344616301/10000000000 : ℝ)|=(5344616301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1091965849/5000000000 : ℝ)|^8435 ≤ (268160727529/2000000000000 : ℝ)^6387
        have hw : |(-1091965849/5000000000 : ℝ)|=(1091965849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266071133/10000000000 : ℝ)|^8435 ≤ (21436361591663/50000000000000 : ℝ)^6387
        have hw : |(5266071133/10000000000 : ℝ)|=(5266071133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s5_2 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336154189/2500000000 : ℝ)*x 0 + (658258881/1250000000 : ℝ)*x 1 + (-545982801/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336154189/2500000000 : ℝ)^8435 ≤ (43719245339179/100000000000000 : ℝ)^6387 := by
    have hnat : (1336154189 : ℕ)^8435*100000000000000^6387 ≤ 43719245339179^6387*2500000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336154189 2500000000 43719245339179 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658258881/1250000000 : ℝ)^8435 ≤ (42872722269421/100000000000000 : ℝ)^6387 := by
    have hnat : (658258881 : ℕ)^8435*100000000000000^6387 ≤ 42872722269421^6387*1250000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658258881 1250000000 42872722269421 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (545982801/2500000000 : ℝ)^8435 ≤ (13408032371093/100000000000000 : ℝ)^6387 := by
    have hnat : (545982801 : ℕ)^8435*100000000000000^6387 ≤ 13408032371093^6387*2500000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545982801 2500000000 13408032371093 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336154189/2500000000 : ℝ), (658258881/1250000000 : ℝ), (-545982801/2500000000 : ℝ)] ![(43719245339179/100000000000000 : ℝ), (42872722269421/100000000000000 : ℝ), (13408032371093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336154189/2500000000 : ℝ)|^8435 ≤ (43719245339179/100000000000000 : ℝ)^6387
        have hw : |(1336154189/2500000000 : ℝ)|=(1336154189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658258881/1250000000 : ℝ)|^8435 ≤ (42872722269421/100000000000000 : ℝ)^6387
        have hw : |(658258881/1250000000 : ℝ)|=(658258881/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-545982801/2500000000 : ℝ)|^8435 ≤ (13408032371093/100000000000000 : ℝ)^6387
        have hw : |(-545982801/2500000000 : ℝ)|=(545982801/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s5_3 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2175356423/5000000000 : ℝ)*x 0 + (4224404981/10000000000 : ℝ)*x 1 + (4480690841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175356423/5000000000 : ℝ)^8435 ≤ (33316881229859/100000000000000 : ℝ)^6387 := by
    have hnat : (2175356423 : ℕ)^8435*100000000000000^6387 ≤ 33316881229859^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175356423 5000000000 33316881229859 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4224404981/10000000000 : ℝ)^8435 ≤ (16022739708847/50000000000000 : ℝ)^6387 := by
    have hnat : (4224404981 : ℕ)^8435*50000000000000^6387 ≤ 16022739708847^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224404981 10000000000 16022739708847 50000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4480690841/10000000000 : ℝ)^8435 ≤ (34637639339483/100000000000000 : ℝ)^6387 := by
    have hnat : (4480690841 : ℕ)^8435*100000000000000^6387 ≤ 34637639339483^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4480690841 10000000000 34637639339483 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2175356423/5000000000 : ℝ), (4224404981/10000000000 : ℝ), (4480690841/10000000000 : ℝ)] ![(33316881229859/100000000000000 : ℝ), (16022739708847/50000000000000 : ℝ), (34637639339483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2175356423/5000000000 : ℝ)|^8435 ≤ (33316881229859/100000000000000 : ℝ)^6387
        have hw : |(2175356423/5000000000 : ℝ)|=(2175356423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4224404981/10000000000 : ℝ)|^8435 ≤ (16022739708847/50000000000000 : ℝ)^6387
        have hw : |(4224404981/10000000000 : ℝ)|=(4224404981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4480690841/10000000000 : ℝ)|^8435 ≤ (34637639339483/100000000000000 : ℝ)^6387
        have hw : |(4480690841/10000000000 : ℝ)|=(4480690841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s5_4 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-16958901/80000000 : ℝ)*x 0 + (131659897/250000000 : ℝ)*x 1 + (674010491/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16958901/80000000 : ℝ)^8435 ≤ (6445511694939/50000000000000 : ℝ)^6387 := by
    have hnat : (16958901 : ℕ)^8435*50000000000000^6387 ≤ 6445511694939^6387*80000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16958901 80000000 6445511694939 50000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131659897/250000000 : ℝ)^8435 ≤ (42876214843433/100000000000000 : ℝ)^6387 := by
    have hnat : (131659897 : ℕ)^8435*100000000000000^6387 ≤ 42876214843433^6387*250000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131659897 250000000 42876214843433 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674010491/1250000000 : ℝ)^8435 ≤ (5529095219447/12500000000000 : ℝ)^6387 := by
    have hnat : (674010491 : ℕ)^8435*12500000000000^6387 ≤ 5529095219447^6387*1250000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674010491 1250000000 5529095219447 12500000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-16958901/80000000 : ℝ), (131659897/250000000 : ℝ), (674010491/1250000000 : ℝ)] ![(6445511694939/50000000000000 : ℝ), (42876214843433/100000000000000 : ℝ), (5529095219447/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-16958901/80000000 : ℝ)|^8435 ≤ (6445511694939/50000000000000 : ℝ)^6387
        have hw : |(-16958901/80000000 : ℝ)|=(16958901/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131659897/250000000 : ℝ)|^8435 ≤ (42876214843433/100000000000000 : ℝ)^6387
        have hw : |(131659897/250000000 : ℝ)|=(131659897/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674010491/1250000000 : ℝ)|^8435 ≤ (5529095219447/12500000000000 : ℝ)^6387
        have hw : |(674010491/1250000000 : ℝ)|=(674010491/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s5_5 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312380857/10000000000 : ℝ)*x 0 + (-2057918687/10000000000 : ℝ)*x 1 + (674010493/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312380857/10000000000 : ℝ)^8435 ≤ (21685669114841/50000000000000 : ℝ)^6387 := by
    have hnat : (5312380857 : ℕ)^8435*50000000000000^6387 ≤ 21685669114841^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312380857 10000000000 21685669114841 50000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2057918687/10000000000 : ℝ)^8435 ≤ (3098974958809/25000000000000 : ℝ)^6387 := by
    have hnat : (2057918687 : ℕ)^8435*25000000000000^6387 ≤ 3098974958809^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2057918687 10000000000 3098974958809 25000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674010493/1250000000 : ℝ)^8435 ≤ (8846552385783/20000000000000 : ℝ)^6387 := by
    have hnat : (674010493 : ℕ)^8435*20000000000000^6387 ≤ 8846552385783^6387*1250000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674010493 1250000000 8846552385783 20000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312380857/10000000000 : ℝ), (-2057918687/10000000000 : ℝ), (674010493/1250000000 : ℝ)] ![(21685669114841/50000000000000 : ℝ), (3098974958809/25000000000000 : ℝ), (8846552385783/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312380857/10000000000 : ℝ)|^8435 ≤ (21685669114841/50000000000000 : ℝ)^6387
        have hw : |(5312380857/10000000000 : ℝ)|=(5312380857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2057918687/10000000000 : ℝ)|^8435 ≤ (3098974958809/25000000000000 : ℝ)^6387
        have hw : |(-2057918687/10000000000 : ℝ)|=(2057918687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674010493/1250000000 : ℝ)|^8435 ≤ (8846552385783/20000000000000 : ℝ)^6387
        have hw : |(674010493/1250000000 : ℝ)|=(674010493/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s5_6 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312380859/10000000000 : ℝ)*x 0 + (1078416787/2000000000 : ℝ)*x 1 + (-411583739/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312380859/10000000000 : ℝ)^8435 ≤ (21685669125623/50000000000000 : ℝ)^6387 := by
    have hnat : (5312380859 : ℕ)^8435*50000000000000^6387 ≤ 21685669125623^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312380859 10000000000 21685669125623 50000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078416787/2000000000 : ℝ)^8435 ≤ (11058190457853/25000000000000 : ℝ)^6387 := by
    have hnat : (1078416787 : ℕ)^8435*25000000000000^6387 ≤ 11058190457853^6387*2000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078416787 2000000000 11058190457853 25000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (411583739/2000000000 : ℝ)^8435 ≤ (3098974974719/25000000000000 : ℝ)^6387 := by
    have hnat : (411583739 : ℕ)^8435*25000000000000^6387 ≤ 3098974974719^6387*2000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411583739 2000000000 3098974974719 25000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312380859/10000000000 : ℝ), (1078416787/2000000000 : ℝ), (-411583739/2000000000 : ℝ)] ![(21685669125623/50000000000000 : ℝ), (11058190457853/25000000000000 : ℝ), (3098974974719/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312380859/10000000000 : ℝ)|^8435 ≤ (21685669125623/50000000000000 : ℝ)^6387
        have hw : |(5312380859/10000000000 : ℝ)|=(5312380859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078416787/2000000000 : ℝ)|^8435 ≤ (11058190457853/25000000000000 : ℝ)^6387
        have hw : |(1078416787/2000000000 : ℝ)|=(1078416787/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-411583739/2000000000 : ℝ)|^8435 ≤ (3098974974719/25000000000000 : ℝ)^6387
        have hw : |(-411583739/2000000000 : ℝ)|=(411583739/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1242_s5_7 (p : ℝ) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2175361533/5000000000 : ℝ)*x 0 + (4480032551/10000000000 : ℝ)*x 1 + (8252081/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175361533/5000000000 : ℝ)^8435 ≤ (33316984587633/100000000000000 : ℝ)^6387 := by
    have hnat : (2175361533 : ℕ)^8435*100000000000000^6387 ≤ 33316984587633^6387*5000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175361533 5000000000 33316984587633 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4480032551/10000000000 : ℝ)^8435 ≤ (34630918887153/100000000000000 : ℝ)^6387 := by
    have hnat : (4480032551 : ℕ)^8435*100000000000000^6387 ≤ 34630918887153^6387*10000000000^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4480032551 10000000000 34630918887153 100000000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8252081/19531250 : ℝ)^8435 ≤ (4006512063741/12500000000000 : ℝ)^6387 := by
    have hnat : (8252081 : ℕ)^8435*12500000000000^6387 ≤ 4006512063741^6387*19531250^8435 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8252081 19531250 4006512063741 12500000000000 8435 6387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8435/2048 : ℝ)) 8435 6387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2175361533/5000000000 : ℝ), (4480032551/10000000000 : ℝ), (8252081/19531250 : ℝ)] ![(33316984587633/100000000000000 : ℝ), (34630918887153/100000000000000 : ℝ), (4006512063741/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2175361533/5000000000 : ℝ)|^8435 ≤ (33316984587633/100000000000000 : ℝ)^6387
        have hw : |(2175361533/5000000000 : ℝ)|=(2175361533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4480032551/10000000000 : ℝ)|^8435 ≤ (34630918887153/100000000000000 : ℝ)^6387
        have hw : |(4480032551/10000000000 : ℝ)|=(4480032551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8252081/19531250 : ℝ)|^8435 ≤ (4006512063741/12500000000000 : ℝ)^6387
        have hw : |(8252081/19531250 : ℝ)|=(8252081/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1242_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151428527/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1419/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (5727/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1413/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1419/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1419/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1419/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1419/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1419/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1419/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1419/12500 : ℝ) ^ (4217/1024 : ℝ) ≤ (12842011182089177/100000000000000000000 : ℝ) := by
    have hpowers : (1419/12500 : ℝ)^4217 ≤ (12842011182089177/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1419 : ℕ)^4217*100000000000000000000^1024 ≤ 12842011182089177^1024*12500^4217 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1419 12500 12842011182089177 100000000000000000000 4217 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1419/12500 : ℝ)) (X := (12842011182089177/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14237/100000 : ℝ) ^ (4217/1024 : ℝ) ≤ (16315802268018041/50000000000000000000 : ℝ) := by
    have hpowers : (14237/100000 : ℝ)^4217 ≤ (16315802268018041/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14237 : ℕ)^4217*50000000000000000000^1024 ≤ 16315802268018041^1024*100000^4217 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14237 100000 16315802268018041 50000000000000000000 4217 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14237/100000 : ℝ)) (X := (16315802268018041/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50012842011182089177/50000000000000000000 : ℝ) ≤ (10000623615886379/10000000000000000 : ℝ) ^ (4217/1024 : ℝ) := by
    have hpowers : (50012842011182089177/50000000000000000000 : ℝ)^1024 ≤ (10000623615886379/10000000000000000 : ℝ)^4217 := by
      have hnat : (50012842011182089177 : ℕ)^1024*10000000000000000^4217 ≤ 10000623615886379^4217*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50012842011182089177 50000000000000000000 10000623615886379 10000000000000000 1024 4217 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000623615886379/10000000000000000 : ℝ)) (X := (50012842011182089177/50000000000000000000 : ℝ)) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045473615718125259/100000000000000000000 : ℝ) ≤ (10001104030546359/10000000000000000 : ℝ) ^ (4217/1024 : ℝ) := by
    have hpowers : (100045473615718125259/100000000000000000000 : ℝ)^1024 ≤ (10001104030546359/10000000000000000 : ℝ)^4217 := by
      have hnat : (100045473615718125259 : ℕ)^1024*10000000000000000^4217 ≤ 10001104030546359^4217*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045473615718125259 100000000000000000000 10001104030546359 10000000000000000 1024 4217 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001104030546359/10000000000000000 : ℝ)) (X := (100045473615718125259/100000000000000000000 : ℝ)) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016315802268018041/25000000000000000000 : ℝ) ≤ (10001584445206339/10000000000000000 : ℝ) ^ (4217/1024 : ℝ) := by
    have hpowers : (25016315802268018041/25000000000000000000 : ℝ)^1024 ≤ (10001584445206339/10000000000000000 : ℝ)^4217 := by
      have hnat : (25016315802268018041 : ℕ)^1024*10000000000000000^4217 ≤ 10001584445206339^4217*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016315802268018041 25000000000000000000 10001584445206339 10000000000000000 1024 4217 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001584445206339/10000000000000000 : ℝ)) (X := (25016315802268018041/25000000000000000000 : ℝ)) (by norm_num) 4217 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(12842011182089177/100000000000000000000 : ℝ) ≤ ((5768178359478403499/5770000000000000000 : ℝ)+2*(24020732999/14425000000000 : ℝ)*(1419/12500 : ℝ))^(4217/1024 : ℝ) := by
    rw [show (5768178359478403499/5770000000000000000 : ℝ)+2*(24020732999/14425000000000 : ℝ)*(1419/12500 : ℝ)=(10000623615886379/10000000000000000 : ℝ) by norm_num, show 1+2*(12842011182089177/100000000000000000000 : ℝ)=(50012842011182089177/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16315802268018041/50000000000000000000 : ℝ)+(12842011182089177/100000000000000000000 : ℝ) ≤ ((5768178359478403499/5770000000000000000 : ℝ)+(24020732999/14425000000000 : ℝ)*((14237/100000 : ℝ)+(1419/12500 : ℝ)))^(4217/1024 : ℝ) := by
    rw [show (5768178359478403499/5770000000000000000 : ℝ)+(24020732999/14425000000000 : ℝ)*((14237/100000 : ℝ)+(1419/12500 : ℝ))=(10001104030546359/10000000000000000 : ℝ) by norm_num, show 1+(16315802268018041/50000000000000000000 : ℝ)+(12842011182089177/100000000000000000000 : ℝ)=(100045473615718125259/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16315802268018041/50000000000000000000 : ℝ) ≤ ((5768178359478403499/5770000000000000000 : ℝ)+2*(24020732999/14425000000000 : ℝ)*(14237/100000 : ℝ))^(4217/1024 : ℝ) := by
    rw [show (5768178359478403499/5770000000000000000 : ℝ)+2*(24020732999/14425000000000 : ℝ)*(14237/100000 : ℝ)=(10001584445206339/10000000000000000 : ℝ) by norm_num, show 1+2*(16315802268018041/50000000000000000000 : ℝ)=(25016315802268018041/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5768178359478403499/5770000000000000000 : ℝ)*(X 1 0+X 2 0)+(24020732999/14425000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4217/1024 : ℝ)) (lo := (1419/12500 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (5768178359478403499/5770000000000000000 : ℝ)) (alpha := (24020732999/14425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5768178359478403499/5770000000000000000 : ℝ)*(X 0 1+X 2 1)+(24020732999/14425000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4217/1024 : ℝ)) (lo := (1419/12500 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (5768178359478403499/5770000000000000000 : ℝ)) (alpha := (24020732999/14425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5768178359478403499/5770000000000000000 : ℝ)*(X 0 2+X 1 2)+(24020732999/14425000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4217/1024 : ℝ)) (lo := (1419/12500 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (5768178359478403499/5770000000000000000 : ℝ)) (alpha := (24020732999/14425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-211985761/1000000000 : ℝ)*X 0 0+(674051243/1250000000 : ℝ)*X 0 1+(658258891/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344616301/10000000000 : ℝ)*X 1 0+(-1091965849/5000000000 : ℝ)*X 1 1+(5266071133/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336154189/2500000000 : ℝ)*X 2 0+(658258881/1250000000 : ℝ)*X 2 1+(-545982801/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2175356423/5000000000 : ℝ)*X 0 0+(4224404981/10000000000 : ℝ)*X 0 1+(4480690841/10000000000 : ℝ)*X 0 2+(2175356423/5000000000 : ℝ)*X 1 0+(4224404981/10000000000 : ℝ)*X 1 1+(4480690841/10000000000 : ℝ)*X 1 2+(2175356423/5000000000 : ℝ)*X 2 0+(4224404981/10000000000 : ℝ)*X 2 1+(4480690841/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-16958901/80000000 : ℝ)*X 0 0+(131659897/250000000 : ℝ)*X 0 1+(674010491/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312380857/10000000000 : ℝ)*X 1 0+(-2057918687/10000000000 : ℝ)*X 1 1+(674010493/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312380859/10000000000 : ℝ)*X 2 0+(1078416787/2000000000 : ℝ)*X 2 1+(-411583739/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2175361533/5000000000 : ℝ)*X 0 0+(4480032551/10000000000 : ℝ)*X 0 1+(8252081/19531250 : ℝ)*X 0 2+(2175361533/5000000000 : ℝ)*X 1 0+(4480032551/10000000000 : ℝ)*X 1 1+(8252081/19531250 : ℝ)*X 1 2+(2175361533/5000000000 : ℝ)*X 2 0+(4480032551/10000000000 : ℝ)*X 2 1+(8252081/19531250 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1242_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (303951479479524465751008027/57700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14207997/3125000000000 : ℝ)*(base19) + (265142203/20000000000000 : ℝ)*(base23) + (7765661/100000000000000 : ℝ)*(lower2) + (1546811/3125000000000 : ℝ)*(upper5) + (1181723562827497/20000000000000 : ℝ)*(major0) + (1181723562827497/20000000000000 : ℝ)*(major1) + (1181723562827497/20000000000000 : ℝ)*(major2) + (3957632191865199/50000000000000 : ℝ)*(sp0) + (3957640661612689/50000000000000 : ℝ)*(sp1) + (1583063111546469/20000000000000 : ℝ)*(sp2) + (975475999337473/25000000000000 : ℝ)*(sp3) + (52499712961/100000000000000 : ℝ)*(sp4) + (17552781039/50000000000000 : ℝ)*(sp5) + (7285944353/50000000000000 : ℝ)*(sp7) + (3901918569238599/100000000000000 : ℝ)*(f.failure) + (49470730521521/625000000000 : ℝ)*(f.sum) + (1681824258141/577000000000000000000000000 : ℝ)*base65 + (451721247230587997/115400000000000000000000000000000 : ℝ)*base68 + (193511289902987997/115400000000000000000000000000000 : ℝ)*base70 + (643732237821387997/115400000000000000000000000000000 : ℝ)*base72 + (185856561333/18031250000000000000000000 : ℝ)*base73 + (3419258542274587997/115400000000000000000000000000000 : ℝ)*base76 + (1094039793439787997/115400000000000000000000000000000 : ℝ)*base78 + (4554695449217787997/115400000000000000000000000000000 : ℝ)*base80 + (224433123791/144250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (58113673/10000000000000000000000 : ℝ)*base89 + (58113673/10000000000000000000000 : ℝ)*base91 + (58113673/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (638979916088641376171238531/144250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (795885917/100000000000000 : ℝ)*(base19) + (168076213/20000000000000 : ℝ)*(base23) + (45146201/50000000000000 : ℝ)*(upper3) + (20026183/100000000000000 : ℝ)*(lower4) + (88049591/100000000000000 : ℝ)*(upper5) + (5939140192834323/100000000000000 : ℝ)*(major0) + (5939140192834323/100000000000000 : ℝ)*(major1) + (5939140192834323/100000000000000 : ℝ)*(major2) + (22948069513/100000000000000 : ℝ)*(sp1) + (4714881383/20000000000000 : ℝ)*(sp2) + (7956205375041921/100000000000000 : ℝ)*(sp4) + (7956181631086491/100000000000000 : ℝ)*(sp5) + (397809048012697/5000000000000 : ℝ)*(sp6) + (1961037431485523/50000000000000 : ℝ)*(sp7) + (1961037431485523/50000000000000 : ℝ)*(f.failure) + (7956205375041921/100000000000000 : ℝ)*(f.sum) + (22882011427027/2885000000000000000000000000 : ℝ)*base66 + (2897622005880703823/577000000000000000000000000000000 : ℝ)*base68 + (1207453742078703823/577000000000000000000000000000000 : ℝ)*base70 + (3000430371450703823/577000000000000000000000000000000 : ℝ)*base72 + (23960982801467/2885000000000000000000000000 : ℝ)*base74 + (10054434939043703823/577000000000000000000000000000000 : ℝ)*base76 + (5738853907450703823/577000000000000000000000000000000 : ℝ)*base78 + (5950519892939296177/577000000000000000000000000000000 : ℝ)*base79 + (144371496453/721250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (19714621/5000000000000000000000 : ℝ)*base89 + (19714621/5000000000000000000000 : ℝ)*base91 + (19714621/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1242_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151428527/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1419/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5727/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1413/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1242_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1242_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151428527/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16223/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9499/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5727/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1413/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1242_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1242_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1242_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4217/1024 : ℝ) ≤ p) (hpb : p ≤ (8435/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151428527/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16223/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9499/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5727/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1413/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1242_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
