-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1626_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:59:08.99044+00:00
-- url     : https://prove2.me/submissions/e1ae2cb7-9895-4a42-97fa-500b9c0cd7d9

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
theorem support_rectangle_w1626_s3_0 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1664750569/10000000000 : ℝ)*x 0 + (5454933983/10000000000 : ℝ)*x 1 + (2590968729/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1664750569/10000000000 : ℝ)^4823 ≤ (5133789260481/50000000000000 : ℝ)^3799 := by
    have hnat : (1664750569 : ℕ)^4823*50000000000000^3799 ≤ 5133789260481^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1664750569 10000000000 5133789260481 50000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5454933983/10000000000 : ℝ)^4823 ≤ (11581972622337/25000000000000 : ℝ)^3799 := by
    have hnat : (5454933983 : ℕ)^4823*25000000000000^3799 ≤ 11581972622337^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5454933983 10000000000 11581972622337 25000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2590968729/5000000000 : ℝ)^4823 ≤ (43404530971523/100000000000000 : ℝ)^3799 := by
    have hnat : (2590968729 : ℕ)^4823*100000000000000^3799 ≤ 43404530971523^3799*5000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590968729 5000000000 43404530971523 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1664750569/10000000000 : ℝ), (5454933983/10000000000 : ℝ), (2590968729/5000000000 : ℝ)] ![(5133789260481/50000000000000 : ℝ), (11581972622337/25000000000000 : ℝ), (43404530971523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1664750569/10000000000 : ℝ)|^4823 ≤ (5133789260481/50000000000000 : ℝ)^3799
        have hw : |(-1664750569/10000000000 : ℝ)|=(1664750569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5454933983/10000000000 : ℝ)|^4823 ≤ (11581972622337/25000000000000 : ℝ)^3799
        have hw : |(5454933983/10000000000 : ℝ)|=(5454933983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2590968729/5000000000 : ℝ)|^4823 ≤ (43404530971523/100000000000000 : ℝ)^3799
        have hw : |(2590968729/5000000000 : ℝ)|=(2590968729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_s3_1 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070272311/2000000000 : ℝ)*x 0 + (-1805431833/10000000000 : ℝ)*x 1 + (259096909/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070272311/2000000000 : ℝ)^4823 ≤ (22607019598907/50000000000000 : ℝ)^3799 := by
    have hnat : (1070272311 : ℕ)^4823*50000000000000^3799 ≤ 22607019598907^3799*2000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070272311 2000000000 22607019598907 50000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1805431833/10000000000 : ℝ)^4823 ≤ (2276284427877/20000000000000 : ℝ)^3799 := by
    have hnat : (1805431833 : ℕ)^4823*20000000000000^3799 ≤ 2276284427877^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1805431833 10000000000 2276284427877 20000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (259096909/500000000 : ℝ)^4823 ≤ (43404538649169/100000000000000 : ℝ)^3799 := by
    have hnat : (259096909 : ℕ)^4823*100000000000000^3799 ≤ 43404538649169^3799*500000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259096909 500000000 43404538649169 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070272311/2000000000 : ℝ), (-1805431833/10000000000 : ℝ), (259096909/500000000 : ℝ)] ![(22607019598907/50000000000000 : ℝ), (2276284427877/20000000000000 : ℝ), (43404538649169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070272311/2000000000 : ℝ)|^4823 ≤ (22607019598907/50000000000000 : ℝ)^3799
        have hw : |(1070272311/2000000000 : ℝ)|=(1070272311/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1805431833/10000000000 : ℝ)|^4823 ≤ (2276284427877/20000000000000 : ℝ)^3799
        have hw : |(-1805431833/10000000000 : ℝ)|=(1805431833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(259096909/500000000 : ℝ)|^4823 ≤ (43404538649169/100000000000000 : ℝ)^3799
        have hw : |(259096909/500000000 : ℝ)|=(259096909/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_s3_2 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351361677/10000000000 : ℝ)*x 0 + (1295484457/2500000000 : ℝ)*x 1 + (-1805432137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351361677/10000000000 : ℝ)^4823 ≤ (11303510126611/25000000000000 : ℝ)^3799 := by
    have hnat : (5351361677 : ℕ)^4823*25000000000000^3799 ≤ 11303510126611^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351361677 10000000000 11303510126611 25000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1295484457/2500000000 : ℝ)^4823 ≤ (868090698121/2000000000000 : ℝ)^3799 := by
    have hnat : (1295484457 : ℕ)^4823*2000000000000^3799 ≤ 868090698121^3799*2500000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295484457 2500000000 868090698121 2000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1805432137/10000000000 : ℝ)^4823 ≤ (2845356143089/25000000000000 : ℝ)^3799 := by
    have hnat : (1805432137 : ℕ)^4823*25000000000000^3799 ≤ 2845356143089^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1805432137 10000000000 2845356143089 25000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351361677/10000000000 : ℝ), (1295484457/2500000000 : ℝ), (-1805432137/10000000000 : ℝ)] ![(11303510126611/25000000000000 : ℝ), (868090698121/2000000000000 : ℝ), (2845356143089/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351361677/10000000000 : ℝ)|^4823 ≤ (11303510126611/25000000000000 : ℝ)^3799
        have hw : |(5351361677/10000000000 : ℝ)|=(5351361677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1295484457/2500000000 : ℝ)|^4823 ≤ (868090698121/2000000000000 : ℝ)^3799
        have hw : |(1295484457/2500000000 : ℝ)|=(1295484457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1805432137/10000000000 : ℝ)|^4823 ≤ (2845356143089/25000000000000 : ℝ)^3799
        have hw : |(-1805432137/10000000000 : ℝ)|=(1805432137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_s3_3 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4199498027/10000000000 : ℝ)*x 0 + (773499353/2000000000 : ℝ)*x 1 + (2276247229/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4199498027/10000000000 : ℝ)^4823 ≤ (33237799528573/100000000000000 : ℝ)^3799 := by
    have hnat : (4199498027 : ℕ)^4823*100000000000000^3799 ≤ 33237799528573^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4199498027 10000000000 33237799528573 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (773499353/2000000000 : ℝ)^4823 ≤ (29938078681617/100000000000000 : ℝ)^3799 := by
    have hnat : (773499353 : ℕ)^4823*100000000000000^3799 ≤ 29938078681617^3799*2000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      773499353 2000000000 29938078681617 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2276247229/5000000000 : ℝ)^4823 ≤ (18412060890243/50000000000000 : ℝ)^3799 := by
    have hnat : (2276247229 : ℕ)^4823*50000000000000^3799 ≤ 18412060890243^3799*5000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2276247229 5000000000 18412060890243 50000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4199498027/10000000000 : ℝ), (773499353/2000000000 : ℝ), (2276247229/5000000000 : ℝ)] ![(33237799528573/100000000000000 : ℝ), (29938078681617/100000000000000 : ℝ), (18412060890243/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4199498027/10000000000 : ℝ)|^4823 ≤ (33237799528573/100000000000000 : ℝ)^3799
        have hw : |(4199498027/10000000000 : ℝ)|=(4199498027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(773499353/2000000000 : ℝ)|^4823 ≤ (29938078681617/100000000000000 : ℝ)^3799
        have hw : |(773499353/2000000000 : ℝ)|=(773499353/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2276247229/5000000000 : ℝ)|^4823 ≤ (18412060890243/50000000000000 : ℝ)^3799
        have hw : |(2276247229/5000000000 : ℝ)|=(2276247229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_s3_4 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-166481927/1000000000 : ℝ)*x 0 + (1295996447/2500000000 : ℝ)*x 1 + (5452863699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166481927/1000000000 : ℝ)^4823 ≤ (513405822953/5000000000000 : ℝ)^3799 := by
    have hnat : (166481927 : ℕ)^4823*5000000000000^3799 ≤ 513405822953^3799*1000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166481927 1000000000 513405822953 5000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1295996447/2500000000 : ℝ)^4823 ≤ (1085657844569/2500000000000 : ℝ)^3799 := by
    have hnat : (1295996447 : ℕ)^4823*2500000000000^3799 ≤ 1085657844569^3799*2500000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295996447 2500000000 1085657844569 2500000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5452863699/10000000000 : ℝ)^4823 ≤ (11576392435857/25000000000000 : ℝ)^3799 := by
    have hnat : (5452863699 : ℕ)^4823*25000000000000^3799 ≤ 11576392435857^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5452863699 10000000000 11576392435857 25000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-166481927/1000000000 : ℝ), (1295996447/2500000000 : ℝ), (5452863699/10000000000 : ℝ)] ![(513405822953/5000000000000 : ℝ), (1085657844569/2500000000000 : ℝ), (11576392435857/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-166481927/1000000000 : ℝ)|^4823 ≤ (513405822953/5000000000000 : ℝ)^3799
        have hw : |(-166481927/1000000000 : ℝ)|=(166481927/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1295996447/2500000000 : ℝ)|^4823 ≤ (1085657844569/2500000000000 : ℝ)^3799
        have hw : |(1295996447/2500000000 : ℝ)|=(1295996447/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5452863699/10000000000 : ℝ)|^4823 ≤ (11576392435857/25000000000000 : ℝ)^3799
        have hw : |(5452863699/10000000000 : ℝ)|=(5452863699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_s3_5 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278666711/10000000000 : ℝ)*x 0 + (-1534506143/10000000000 : ℝ)*x 1 + (2726431851/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278666711/10000000000 : ℝ)^4823 ≤ (22217856090401/50000000000000 : ℝ)^3799 := by
    have hnat : (5278666711 : ℕ)^4823*50000000000000^3799 ≤ 22217856090401^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278666711 10000000000 22217856090401 50000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1534506143/10000000000 : ℝ)^4823 ≤ (4629359012943/50000000000000 : ℝ)^3799 := by
    have hnat : (1534506143 : ℕ)^4823*50000000000000^3799 ≤ 4629359012943^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1534506143 10000000000 4629359012943 50000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2726431851/5000000000 : ℝ)^4823 ≤ (4630556977577/10000000000000 : ℝ)^3799 := by
    have hnat : (2726431851 : ℕ)^4823*10000000000000^3799 ≤ 4630556977577^3799*5000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2726431851 5000000000 4630556977577 10000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278666711/10000000000 : ℝ), (-1534506143/10000000000 : ℝ), (2726431851/5000000000 : ℝ)] ![(22217856090401/50000000000000 : ℝ), (4629359012943/50000000000000 : ℝ), (4630556977577/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278666711/10000000000 : ℝ)|^4823 ≤ (22217856090401/50000000000000 : ℝ)^3799
        have hw : |(5278666711/10000000000 : ℝ)|=(5278666711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1534506143/10000000000 : ℝ)|^4823 ≤ (4629359012943/50000000000000 : ℝ)^3799
        have hw : |(-1534506143/10000000000 : ℝ)|=(1534506143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2726431851/5000000000 : ℝ)|^4823 ≤ (4630556977577/10000000000000 : ℝ)^3799
        have hw : |(2726431851/5000000000 : ℝ)|=(2726431851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_s3_6 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278666731/10000000000 : ℝ)*x 0 + (2726431847/5000000000 : ℝ)*x 1 + (-767253063/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278666731/10000000000 : ℝ)^4823 ≤ (22217856197271/50000000000000 : ℝ)^3799 := by
    have hnat : (5278666731 : ℕ)^4823*50000000000000^3799 ≤ 22217856197271^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278666731 10000000000 22217856197271 50000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2726431847/5000000000 : ℝ)^4823 ≤ (46305569689523/100000000000000 : ℝ)^3799 := by
    have hnat : (2726431847 : ℕ)^4823*100000000000000^3799 ≤ 46305569689523^3799*5000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2726431847 5000000000 46305569689523 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (767253063/5000000000 : ℝ)^4823 ≤ (4629358947833/50000000000000 : ℝ)^3799 := by
    have hnat : (767253063 : ℕ)^4823*50000000000000^3799 ≤ 4629358947833^3799*5000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      767253063 5000000000 4629358947833 50000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278666731/10000000000 : ℝ), (2726431847/5000000000 : ℝ), (-767253063/5000000000 : ℝ)] ![(22217856197271/50000000000000 : ℝ), (46305569689523/100000000000000 : ℝ), (4629358947833/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278666731/10000000000 : ℝ)|^4823 ≤ (22217856197271/50000000000000 : ℝ)^3799
        have hw : |(5278666731/10000000000 : ℝ)|=(5278666731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2726431847/5000000000 : ℝ)|^4823 ≤ (46305569689523/100000000000000 : ℝ)^3799
        have hw : |(2726431847/5000000000 : ℝ)|=(2726431847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-767253063/5000000000 : ℝ)|^4823 ≤ (4629358947833/50000000000000 : ℝ)^3799
        have hw : |(-767253063/5000000000 : ℝ)|=(767253063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_s3_7 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (839933973/2000000000 : ℝ)*x 0 + (4547355391/10000000000 : ℝ)*x 1 + (3872689299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (839933973/2000000000 : ℝ)^4823 ≤ (33239526179139/100000000000000 : ℝ)^3799 := by
    have hnat : (839933973 : ℕ)^4823*100000000000000^3799 ≤ 33239526179139^3799*2000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      839933973 2000000000 33239526179139 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4547355391/10000000000 : ℝ)^4823 ≤ (18385678196913/50000000000000 : ℝ)^3799 := by
    have hnat : (4547355391 : ℕ)^4823*50000000000000^3799 ≤ 18385678196913^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4547355391 10000000000 18385678196913 50000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3872689299/10000000000 : ℝ)^4823 ≤ (29989117408751/100000000000000 : ℝ)^3799 := by
    have hnat : (3872689299 : ℕ)^4823*100000000000000^3799 ≤ 29989117408751^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3872689299 10000000000 29989117408751 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(839933973/2000000000 : ℝ), (4547355391/10000000000 : ℝ), (3872689299/10000000000 : ℝ)] ![(33239526179139/100000000000000 : ℝ), (18385678196913/50000000000000 : ℝ), (29989117408751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(839933973/2000000000 : ℝ)|^4823 ≤ (33239526179139/100000000000000 : ℝ)^3799
        have hw : |(839933973/2000000000 : ℝ)|=(839933973/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4547355391/10000000000 : ℝ)|^4823 ≤ (18385678196913/50000000000000 : ℝ)^3799
        have hw : |(4547355391/10000000000 : ℝ)|=(4547355391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3872689299/10000000000 : ℝ)|^4823 ≤ (29989117408751/100000000000000 : ℝ)^3799
        have hw : |(3872689299/10000000000 : ℝ)|=(3872689299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1626_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5483111/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1643/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10431/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (329/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8161/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1643/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10431/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1643/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10431/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1643/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10431/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1643/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10431/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1643/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10431/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1643/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10431/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10431/100000 : ℝ) ^ (4819/1024 : ℝ) ≤ (599968186561271/25000000000000000000 : ℝ) := by
    have hpowers : (10431/100000 : ℝ)^4819 ≤ (599968186561271/25000000000000000000 : ℝ)^1024 := by
      have hnat : (10431 : ℕ)^4819*25000000000000000000^1024 ≤ 599968186561271^1024*100000^4819 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10431 100000 599968186561271 25000000000000000000 4819 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10431/100000 : ℝ)) (X := (599968186561271/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4819 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1643/10000 : ℝ) ^ (4819/1024 : ℝ) ≤ (20358579802645277/100000000000000000000 : ℝ) := by
    have hpowers : (1643/10000 : ℝ)^4819 ≤ (20358579802645277/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1643 : ℕ)^4819*100000000000000000000^1024 ≤ 20358579802645277^1024*10000^4819 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1643 10000 20358579802645277 100000000000000000000 4819 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1643/10000 : ℝ)) (X := (20358579802645277/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4819 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500599968186561271/12500000000000000000 : ℝ) ≤ (1000010198892921/1000000000000000 : ℝ) ^ (4819/1024 : ℝ) := by
    have hpowers : (12500599968186561271/12500000000000000000 : ℝ)^1024 ≤ (1000010198892921/1000000000000000 : ℝ)^4819 := by
      have hnat : (12500599968186561271 : ℕ)^1024*1000000000000000^4819 ≤ 1000010198892921^4819*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500599968186561271 12500000000000000000 1000010198892921 1000000000000000 1024 4819 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000010198892921/1000000000000000 : ℝ)) (X := (12500599968186561271/12500000000000000000 : ℝ)) (by norm_num) 4819 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100022758452548890361/100000000000000000000 : ℝ) ≤ (10000483556076149/10000000000000000 : ℝ) ^ (4819/1024 : ℝ) := by
    have hpowers : (100022758452548890361/100000000000000000000 : ℝ)^1024 ≤ (10000483556076149/10000000000000000 : ℝ)^4819 := by
      have hnat : (100022758452548890361 : ℕ)^1024*10000000000000000^4819 ≤ 10000483556076149^4819*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100022758452548890361 100000000000000000000 10000483556076149 10000000000000000 1024 4819 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000483556076149/10000000000000000 : ℝ)) (X := (100022758452548890361/100000000000000000000 : ℝ)) (by norm_num) 4819 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50020358579802645277/50000000000000000000 : ℝ) ≤ (625054070201443/625000000000000 : ℝ) ^ (4819/1024 : ℝ) := by
    have hpowers : (50020358579802645277/50000000000000000000 : ℝ)^1024 ≤ (625054070201443/625000000000000 : ℝ)^4819 := by
      have hnat : (50020358579802645277 : ℕ)^1024*625000000000000^4819 ≤ 625054070201443^4819*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020358579802645277 50000000000000000000 625054070201443 625000000000000 1024 4819 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625054070201443/625000000000000 : ℝ)) (X := (50020358579802645277/50000000000000000000 : ℝ)) (by norm_num) 4819 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(599968186561271/25000000000000000000 : ℝ) ≤ ((14995662894441722343/14997500000000000000 : ℝ)+2*(381567146939/599900000000000 : ℝ)*(10431/100000 : ℝ))^(4819/1024 : ℝ) := by
    rw [show (14995662894441722343/14997500000000000000 : ℝ)+2*(381567146939/599900000000000 : ℝ)*(10431/100000 : ℝ)=(1000010198892921/1000000000000000 : ℝ) by norm_num, show 1+2*(599968186561271/25000000000000000000 : ℝ)=(12500599968186561271/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(20358579802645277/100000000000000000000 : ℝ)+(599968186561271/25000000000000000000 : ℝ) ≤ ((14995662894441722343/14997500000000000000 : ℝ)+(381567146939/599900000000000 : ℝ)*((1643/10000 : ℝ)+(10431/100000 : ℝ)))^(4819/1024 : ℝ) := by
    rw [show (14995662894441722343/14997500000000000000 : ℝ)+(381567146939/599900000000000 : ℝ)*((1643/10000 : ℝ)+(10431/100000 : ℝ))=(10000483556076149/10000000000000000 : ℝ) by norm_num, show 1+(20358579802645277/100000000000000000000 : ℝ)+(599968186561271/25000000000000000000 : ℝ)=(100022758452548890361/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(20358579802645277/100000000000000000000 : ℝ) ≤ ((14995662894441722343/14997500000000000000 : ℝ)+2*(381567146939/599900000000000 : ℝ)*(1643/10000 : ℝ))^(4819/1024 : ℝ) := by
    rw [show (14995662894441722343/14997500000000000000 : ℝ)+2*(381567146939/599900000000000 : ℝ)*(1643/10000 : ℝ)=(625054070201443/625000000000000 : ℝ) by norm_num, show 1+2*(20358579802645277/100000000000000000000 : ℝ)=(50020358579802645277/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14995662894441722343/14997500000000000000 : ℝ)*(X 1 0+X 2 0)+(381567146939/599900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4819/1024 : ℝ)) (lo := (10431/100000 : ℝ)) (hi := (1643/10000 : ℝ)) (c := (14995662894441722343/14997500000000000000 : ℝ)) (alpha := (381567146939/599900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14995662894441722343/14997500000000000000 : ℝ)*(X 0 1+X 2 1)+(381567146939/599900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4819/1024 : ℝ)) (lo := (10431/100000 : ℝ)) (hi := (1643/10000 : ℝ)) (c := (14995662894441722343/14997500000000000000 : ℝ)) (alpha := (381567146939/599900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14995662894441722343/14997500000000000000 : ℝ)*(X 0 2+X 1 2)+(381567146939/599900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4819/1024 : ℝ)) (lo := (10431/100000 : ℝ)) (hi := (1643/10000 : ℝ)) (c := (14995662894441722343/14997500000000000000 : ℝ)) (alpha := (381567146939/599900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1664750569/10000000000 : ℝ)*X 0 0+(5454933983/10000000000 : ℝ)*X 0 1+(2590968729/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070272311/2000000000 : ℝ)*X 1 0+(-1805431833/10000000000 : ℝ)*X 1 1+(259096909/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351361677/10000000000 : ℝ)*X 2 0+(1295484457/2500000000 : ℝ)*X 2 1+(-1805432137/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4199498027/10000000000 : ℝ)*X 0 0+(773499353/2000000000 : ℝ)*X 0 1+(2276247229/5000000000 : ℝ)*X 0 2+(4199498027/10000000000 : ℝ)*X 1 0+(773499353/2000000000 : ℝ)*X 1 1+(2276247229/5000000000 : ℝ)*X 1 2+(4199498027/10000000000 : ℝ)*X 2 0+(773499353/2000000000 : ℝ)*X 2 1+(2276247229/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-166481927/1000000000 : ℝ)*X 0 0+(1295996447/2500000000 : ℝ)*X 0 1+(5452863699/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5278666711/10000000000 : ℝ)*X 1 0+(-1534506143/10000000000 : ℝ)*X 1 1+(2726431851/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5278666731/10000000000 : ℝ)*X 2 0+(2726431847/5000000000 : ℝ)*X 2 1+(-767253063/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((839933973/2000000000 : ℝ)*X 0 0+(4547355391/10000000000 : ℝ)*X 0 1+(3872689299/10000000000 : ℝ)*X 0 2+(839933973/2000000000 : ℝ)*X 1 0+(4547355391/10000000000 : ℝ)*X 1 1+(3872689299/10000000000 : ℝ)*X 1 2+(839933973/2000000000 : ℝ)*X 2 0+(4547355391/10000000000 : ℝ)*X 2 1+(3872689299/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (735541951258022252472047907/74987500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (41078669/6250000000000 : ℝ)*(base19) + (88944283/10000000000000 : ℝ)*(base23) + (28429477/100000000000000 : ℝ)*(lower2) + (113450357/100000000000000 : ℝ)*(upper3) + (53994967/50000000000000 : ℝ)*(lower4) + (256147834706917/10000000000000 : ℝ)*(major0) + (256147834706917/10000000000000 : ℝ)*(major1) + (256147834706917/10000000000000 : ℝ)*(major2) + (1831535411253739/50000000000000 : ℝ)*(sp0) + (366308742809891/10000000000000 : ℝ)*(sp1) + (114471474872337/3125000000000 : ℝ)*(sp2) + (36496581182599/2500000000000 : ℝ)*(sp3) + (2157856267/12500000000000 : ℝ)*(sp4) + (5034514729/100000000000000 : ℝ)*(sp7) + (1459868281818689/100000000000000 : ℝ)*(f.failure) + (1831544042678807/50000000000000 : ℝ)*(f.sum) + (42904612411071/5999000000000000000000000000 : ℝ)*base66 + (718431512259146531/149975000000000000000000000000000 : ℝ)*base67 + (1891261934238096531/149975000000000000000000000000000 : ℝ)*base69 + (106805636389003469/149975000000000000000000000000000 : ℝ)*base72 + (1443300208307/1199800000000000000000000000 : ℝ)*base73 + (2050166473933396531/149975000000000000000000000000000 : ℝ)*base75 + (458336195896053469/149975000000000000000000000000000 : ℝ)*base78 + (1039024504686896531/149975000000000000000000000000000 : ℝ)*base79 + (16943976521369/5999000000000000000000000000 : ℝ)*base81 + (2588521/312500000000000000000 : ℝ)*base90 + (2588521/312500000000000000000 : ℝ)*base92 + (2588521/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (66673752710151857800397931/6695312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1493350281/100000000000000 : ℝ)*(base19) + (328091351/20000000000000 : ℝ)*(base23) + (21049759/10000000000000 : ℝ)*(upper3) + (28809653/50000000000000 : ℝ)*(lower4) + (202027857/100000000000000 : ℝ)*(upper5) + (325085878188173/12500000000000 : ℝ)*(major0) + (325085878188173/12500000000000 : ℝ)*(major1) + (325085878188173/12500000000000 : ℝ)*(major2) + (866778591/5000000000000 : ℝ)*(sp1) + (3813625561/20000000000000 : ℝ)*(sp2) + (1859579579861693/50000000000000 : ℝ)*(sp4) + (929785082700321/25000000000000 : ℝ)*(sp5) + (1859569225569413/50000000000000 : ℝ)*(sp6) + (46319204979529/3125000000000 : ℝ)*(sp7) + (46319204979529/3125000000000 : ℝ)*(f.failure) + (1859579579861693/50000000000000 : ℝ)*(f.sum) + (4939508161981/7498750000000000000000000000 : ℝ)*base66 + (1726741882784625661/187468750000000000000000000000000 : ℝ)*base68 + (624302891369938161/187468750000000000000000000000000 : ℝ)*base70 + (437685522824375661/187468750000000000000000000000000 : ℝ)*base72 + (2909960330909/1874687500000000000000000000 : ℝ)*base74 + (146584327134874339/187468750000000000000000000000000 : ℝ)*base75 + (510327745081656911/187468750000000000000000000000000 : ℝ)*base78 + (2491999184140375661/187468750000000000000000000000000 : ℝ)*base80 + (139499920669869/29995000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (78469/9765625000000000000 : ℝ)*base89 + (78469/9765625000000000000 : ℝ)*base91 + (78469/9765625000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1626_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5483111/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1643/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10431/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (329/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8161/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1626_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1626_s4_0 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1664830989/10000000000 : ℝ)*x 0 + (681816383/1250000000 : ℝ)*x 1 + (5182286769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1664830989/10000000000 : ℝ)^4823 ≤ (641763013813/6250000000000 : ℝ)^3799 := by
    have hnat : (1664830989 : ℕ)^4823*6250000000000^3799 ≤ 641763013813^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1664830989 10000000000 641763013813 6250000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (681816383/1250000000 : ℝ)^4823 ≤ (2316177312163/5000000000000 : ℝ)^3799 := by
    have hnat : (681816383 : ℕ)^4823*5000000000000^3799 ≤ 2316177312163^3799*1250000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681816383 1250000000 2316177312163 5000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5182286769/10000000000 : ℝ)^4823 ≤ (8681649105789/20000000000000 : ℝ)^3799 := by
    have hnat : (5182286769 : ℕ)^4823*20000000000000^3799 ≤ 8681649105789^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182286769 10000000000 8681649105789 20000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1664830989/10000000000 : ℝ), (681816383/1250000000 : ℝ), (5182286769/10000000000 : ℝ)] ![(641763013813/6250000000000 : ℝ), (2316177312163/5000000000000 : ℝ), (8681649105789/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1664830989/10000000000 : ℝ)|^4823 ≤ (641763013813/6250000000000 : ℝ)^3799
        have hw : |(-1664830989/10000000000 : ℝ)|=(1664830989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(681816383/1250000000 : ℝ)|^4823 ≤ (2316177312163/5000000000000 : ℝ)^3799
        have hw : |(681816383/1250000000 : ℝ)|=(681816383/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5182286769/10000000000 : ℝ)|^4823 ≤ (8681649105789/20000000000000 : ℝ)^3799
        have hw : |(5182286769/10000000000 : ℝ)|=(5182286769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_s4_1 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668906703/1250000000 : ℝ)*x 0 + (-72204541/400000000 : ℝ)*x 1 + (1036457321/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668906703/1250000000 : ℝ)^4823 ≤ (22606440740953/50000000000000 : ℝ)^3799 := by
    have hnat : (668906703 : ℕ)^4823*50000000000000^3799 ≤ 22606440740953^3799*1250000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668906703 1250000000 22606440740953 50000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (72204541/400000000 : ℝ)^4823 ≤ (1137887471889/10000000000000 : ℝ)^3799 := by
    have hnat : (72204541 : ℕ)^4823*10000000000000^3799 ≤ 1137887471889^3799*400000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      72204541 400000000 1137887471889 10000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036457321/2000000000 : ℝ)^4823 ≤ (43408243784961/100000000000000 : ℝ)^3799 := by
    have hnat : (1036457321 : ℕ)^4823*100000000000000^3799 ≤ 43408243784961^3799*2000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036457321 2000000000 43408243784961 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668906703/1250000000 : ℝ), (-72204541/400000000 : ℝ), (1036457321/2000000000 : ℝ)] ![(22606440740953/50000000000000 : ℝ), (1137887471889/10000000000000 : ℝ), (43408243784961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668906703/1250000000 : ℝ)|^4823 ≤ (22606440740953/50000000000000 : ℝ)^3799
        have hw : |(668906703/1250000000 : ℝ)|=(668906703/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-72204541/400000000 : ℝ)|^4823 ≤ (1137887471889/10000000000000 : ℝ)^3799
        have hw : |(-72204541/400000000 : ℝ)|=(72204541/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1036457321/2000000000 : ℝ)|^4823 ≤ (43408243784961/100000000000000 : ℝ)^3799
        have hw : |(1036457321/2000000000 : ℝ)|=(1036457321/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_s4_2 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337813373/2500000000 : ℝ)*x 0 + (129557169/250000000 : ℝ)*x 1 + (-225639187/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337813373/2500000000 : ℝ)^4823 ≤ (45212880066019/100000000000000 : ℝ)^3799 := by
    have hnat : (1337813373 : ℕ)^4823*100000000000000^3799 ≤ 45212880066019^3799*2500000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337813373 2500000000 45212880066019 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129557169/250000000 : ℝ)^4823 ≤ (43408245433239/100000000000000 : ℝ)^3799 := by
    have hnat : (129557169 : ℕ)^4823*100000000000000^3799 ≤ 43408245433239^3799*250000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129557169 250000000 43408245433239 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (225639187/1250000000 : ℝ)^4823 ≤ (11378874486809/100000000000000 : ℝ)^3799 := by
    have hnat : (225639187 : ℕ)^4823*100000000000000^3799 ≤ 11378874486809^3799*1250000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225639187 1250000000 11378874486809 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337813373/2500000000 : ℝ), (129557169/250000000 : ℝ), (-225639187/1250000000 : ℝ)] ![(45212880066019/100000000000000 : ℝ), (43408245433239/100000000000000 : ℝ), (11378874486809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337813373/2500000000 : ℝ)|^4823 ≤ (45212880066019/100000000000000 : ℝ)^3799
        have hw : |(1337813373/2500000000 : ℝ)|=(1337813373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(129557169/250000000 : ℝ)|^4823 ≤ (43408245433239/100000000000000 : ℝ)^3799
        have hw : |(129557169/250000000 : ℝ)|=(129557169/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-225639187/1250000000 : ℝ)|^4823 ≤ (11378874486809/100000000000000 : ℝ)^3799
        have hw : |(-225639187/1250000000 : ℝ)|=(225639187/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_s4_3 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4199550943/10000000000 : ℝ)*x 0 + (773686607/2000000000 : ℝ)*x 1 + (568943327/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4199550943/10000000000 : ℝ)^4823 ≤ (2077395702087/6250000000000 : ℝ)^3799 := by
    have hnat : (4199550943 : ℕ)^4823*6250000000000^3799 ≤ 2077395702087^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4199550943 10000000000 2077395702087 6250000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (773686607/2000000000 : ℝ)^4823 ≤ (5989456030309/20000000000000 : ℝ)^3799 := by
    have hnat : (773686607 : ℕ)^4823*20000000000000^3799 ≤ 5989456030309^3799*2000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      773686607 2000000000 5989456030309 20000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (568943327/1250000000 : ℝ)^4823 ≤ (36814388601663/100000000000000 : ℝ)^3799 := by
    have hnat : (568943327 : ℕ)^4823*100000000000000^3799 ≤ 36814388601663^3799*1250000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      568943327 1250000000 36814388601663 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4199550943/10000000000 : ℝ), (773686607/2000000000 : ℝ), (568943327/1250000000 : ℝ)] ![(2077395702087/6250000000000 : ℝ), (5989456030309/20000000000000 : ℝ), (36814388601663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4199550943/10000000000 : ℝ)|^4823 ≤ (2077395702087/6250000000000 : ℝ)^3799
        have hw : |(4199550943/10000000000 : ℝ)|=(4199550943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(773686607/2000000000 : ℝ)|^4823 ≤ (5989456030309/20000000000000 : ℝ)^3799
        have hw : |(773686607/2000000000 : ℝ)|=(773686607/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(568943327/1250000000 : ℝ)|^4823 ≤ (36814388601663/100000000000000 : ℝ)^3799
        have hw : |(568943327/1250000000 : ℝ)|=(568943327/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_s4_4 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-332979711/2000000000 : ℝ)*x 0 + (1296080859/2500000000 : ℝ)*x 1 + (5452473031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332979711/2000000000 : ℝ)^4823 ≤ (10268737278743/100000000000000 : ℝ)^3799 := by
    have hnat : (332979711 : ℕ)^4823*100000000000000^3799 ≤ 10268737278743^3799*2000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332979711 2000000000 10268737278743 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1296080859/2500000000 : ℝ)^4823 ≤ (5428738087221/12500000000000 : ℝ)^3799 := by
    have hnat : (1296080859 : ℕ)^4823*12500000000000^3799 ≤ 5428738087221^3799*2500000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296080859 2500000000 5428738087221 12500000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5452473031/10000000000 : ℝ)^4823 ≤ (46301358016513/100000000000000 : ℝ)^3799 := by
    have hnat : (5452473031 : ℕ)^4823*100000000000000^3799 ≤ 46301358016513^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5452473031 10000000000 46301358016513 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-332979711/2000000000 : ℝ), (1296080859/2500000000 : ℝ), (5452473031/10000000000 : ℝ)] ![(10268737278743/100000000000000 : ℝ), (5428738087221/12500000000000 : ℝ), (46301358016513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-332979711/2000000000 : ℝ)|^4823 ≤ (10268737278743/100000000000000 : ℝ)^3799
        have hw : |(-332979711/2000000000 : ℝ)|=(332979711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1296080859/2500000000 : ℝ)|^4823 ≤ (5428738087221/12500000000000 : ℝ)^3799
        have hw : |(1296080859/2500000000 : ℝ)|=(1296080859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5452473031/10000000000 : ℝ)|^4823 ≤ (46301358016513/100000000000000 : ℝ)^3799
        have hw : |(5452473031/10000000000 : ℝ)|=(5452473031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_s4_5 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639379639/5000000000 : ℝ)*x 0 + (-1534927057/10000000000 : ℝ)*x 1 + (5452472861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639379639/5000000000 : ℝ)^4823 ≤ (44436701446811/100000000000000 : ℝ)^3799 := by
    have hnat : (2639379639 : ℕ)^4823*100000000000000^3799 ≤ 44436701446811^3799*5000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639379639 5000000000 44436701446811 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1534927057/10000000000 : ℝ)^4823 ≤ (2315485589223/25000000000000 : ℝ)^3799 := by
    have hnat : (1534927057 : ℕ)^4823*25000000000000^3799 ≤ 2315485589223^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1534927057 10000000000 2315485589223 25000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5452472861/10000000000 : ℝ)^4823 ≤ (46301356183789/100000000000000 : ℝ)^3799 := by
    have hnat : (5452472861 : ℕ)^4823*100000000000000^3799 ≤ 46301356183789^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5452472861 10000000000 46301356183789 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639379639/5000000000 : ℝ), (-1534927057/10000000000 : ℝ), (5452472861/10000000000 : ℝ)] ![(44436701446811/100000000000000 : ℝ), (2315485589223/25000000000000 : ℝ), (46301356183789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639379639/5000000000 : ℝ)|^4823 ≤ (44436701446811/100000000000000 : ℝ)^3799
        have hw : |(2639379639/5000000000 : ℝ)|=(2639379639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1534927057/10000000000 : ℝ)|^4823 ≤ (2315485589223/25000000000000 : ℝ)^3799
        have hw : |(-1534927057/10000000000 : ℝ)|=(1534927057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5452472861/10000000000 : ℝ)|^4823 ≤ (46301356183789/100000000000000 : ℝ)^3799
        have hw : |(5452472861/10000000000 : ℝ)|=(5452472861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_s4_6 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (131968979/250000000 : ℝ)*x 0 + (5452472841/10000000000 : ℝ)*x 1 + (-6139709/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131968979/250000000 : ℝ)^4823 ≤ (44436700185739/100000000000000 : ℝ)^3799 := by
    have hnat : (131968979 : ℕ)^4823*100000000000000^3799 ≤ 44436700185739^3799*250000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131968979 250000000 44436700185739 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5452472841/10000000000 : ℝ)^4823 ≤ (23150677984087/50000000000000 : ℝ)^3799 := by
    have hnat : (5452472841 : ℕ)^4823*50000000000000^3799 ≤ 23150677984087^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5452472841 10000000000 23150677984087 50000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6139709/40000000 : ℝ)^4823 ≤ (4630971917693/50000000000000 : ℝ)^3799 := by
    have hnat : (6139709 : ℕ)^4823*50000000000000^3799 ≤ 4630971917693^3799*40000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6139709 40000000 4630971917693 50000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(131968979/250000000 : ℝ), (5452472841/10000000000 : ℝ), (-6139709/40000000 : ℝ)] ![(44436700185739/100000000000000 : ℝ), (23150677984087/50000000000000 : ℝ), (4630971917693/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(131968979/250000000 : ℝ)|^4823 ≤ (44436700185739/100000000000000 : ℝ)^3799
        have hw : |(131968979/250000000 : ℝ)|=(131968979/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5452472841/10000000000 : ℝ)|^4823 ≤ (23150677984087/50000000000000 : ℝ)^3799
        have hw : |(5452472841/10000000000 : ℝ)|=(5452472841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6139709/40000000 : ℝ)|^4823 ≤ (4630971917693/50000000000000 : ℝ)^3799
        have hw : |(-6139709/40000000 : ℝ)|=(6139709/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_s4_7 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (839944127/2000000000 : ℝ)*x 0 + (909287167/2000000000 : ℝ)*x 1 + (968399397/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (839944127/2000000000 : ℝ)^4823 ≤ (4155004540793/12500000000000 : ℝ)^3799 := by
    have hnat : (839944127 : ℕ)^4823*12500000000000^3799 ≤ 4155004540793^3799*2000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      839944127 2000000000 4155004540793 12500000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (909287167/2000000000 : ℝ)^4823 ≤ (18380958272199/50000000000000 : ℝ)^3799 := by
    have hnat : (909287167 : ℕ)^4823*50000000000000^3799 ≤ 18380958272199^3799*2000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      909287167 2000000000 18380958272199 50000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (968399397/2500000000 : ℝ)^4823 ≤ (299980471069/1000000000000 : ℝ)^3799 := by
    have hnat : (968399397 : ℕ)^4823*1000000000000^3799 ≤ 299980471069^3799*2500000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      968399397 2500000000 299980471069 1000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(839944127/2000000000 : ℝ), (909287167/2000000000 : ℝ), (968399397/2500000000 : ℝ)] ![(4155004540793/12500000000000 : ℝ), (18380958272199/50000000000000 : ℝ), (299980471069/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(839944127/2000000000 : ℝ)|^4823 ≤ (4155004540793/12500000000000 : ℝ)^3799
        have hw : |(839944127/2000000000 : ℝ)|=(839944127/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(909287167/2000000000 : ℝ)|^4823 ≤ (18380958272199/50000000000000 : ℝ)^3799
        have hw : |(909287167/2000000000 : ℝ)|=(909287167/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(968399397/2500000000 : ℝ)|^4823 ≤ (299980471069/1000000000000 : ℝ)^3799
        have hw : |(968399397/2500000000 : ℝ)|=(968399397/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1626_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5483111/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8161/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (329/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (1317/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16313/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8161/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (329/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8161/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (329/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8161/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (329/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8161/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (329/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8161/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (329/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8161/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (329/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (329/3125 : ℝ) ^ (4819/1024 : ℝ) ≤ (5013444642767/200000000000000000 : ℝ) := by
    have hpowers : (329/3125 : ℝ)^4819 ≤ (5013444642767/200000000000000000 : ℝ)^1024 := by
      have hnat : (329 : ℕ)^4819*200000000000000000^1024 ≤ 5013444642767^1024*3125^4819 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        329 3125 5013444642767 200000000000000000 4819 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (329/3125 : ℝ)) (X := (5013444642767/200000000000000000 : ℝ)) (by norm_num) (by norm_num) 4819 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8161/50000 : ℝ) ^ (4819/1024 : ℝ) ≤ (19736422988646001/100000000000000000000 : ℝ) := by
    have hpowers : (8161/50000 : ℝ)^4819 ≤ (19736422988646001/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8161 : ℕ)^4819*100000000000000000000^1024 ≤ 19736422988646001^1024*50000^4819 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8161 50000 19736422988646001 100000000000000000000 4819 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8161/50000 : ℝ)) (X := (19736422988646001/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4819 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (100005013444642767/100000000000000000 : ℝ) ≤ (5000053264847203/5000000000000000 : ℝ) ^ (4819/1024 : ℝ) := by
    have hpowers : (100005013444642767/100000000000000000 : ℝ)^1024 ≤ (5000053264847203/5000000000000000 : ℝ)^4819 := by
      have hnat : (100005013444642767 : ℕ)^1024*5000000000000000^4819 ≤ 5000053264847203^4819*100000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100005013444642767 100000000000000000 5000053264847203 5000000000000000 1024 4819 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000053264847203/5000000000000000 : ℝ)) (X := (100005013444642767/100000000000000000 : ℝ)) (by norm_num) 4819 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100022243145310029501/100000000000000000000 : ℝ) ≤ (50002363040691/50000000000000 : ℝ) ^ (4819/1024 : ℝ) := by
    have hpowers : (100022243145310029501/100000000000000000000 : ℝ)^1024 ≤ (50002363040691/50000000000000 : ℝ)^4819 := by
      have hnat : (100022243145310029501 : ℕ)^1024*50000000000000^4819 ≤ 50002363040691^4819*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100022243145310029501 100000000000000000000 50002363040691 50000000000000 1024 4819 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (50002363040691/50000000000000 : ℝ)) (X := (100022243145310029501/100000000000000000000 : ℝ)) (by norm_num) 4819 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50019736422988646001/50000000000000000000 : ℝ) ≤ (5000419343290997/5000000000000000 : ℝ) ^ (4819/1024 : ℝ) := by
    have hpowers : (50019736422988646001/50000000000000000000 : ℝ)^1024 ≤ (5000419343290997/5000000000000000 : ℝ)^4819 := by
      have hnat : (50019736422988646001 : ℕ)^1024*5000000000000000^4819 ≤ 5000419343290997^4819*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019736422988646001 50000000000000000000 5000419343290997 5000000000000000 1024 4819 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000419343290997/5000000000000000 : ℝ)) (X := (50019736422988646001/50000000000000000000 : ℝ)) (by norm_num) 4819 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5013444642767/200000000000000000 : ℝ) ≤ ((579329090853368619/579400000000000000 : ℝ)+2*(183039221897/289700000000000 : ℝ)*(329/3125 : ℝ))^(4819/1024 : ℝ) := by
    rw [show (579329090853368619/579400000000000000 : ℝ)+2*(183039221897/289700000000000 : ℝ)*(329/3125 : ℝ)=(5000053264847203/5000000000000000 : ℝ) by norm_num, show 1+2*(5013444642767/200000000000000000 : ℝ)=(100005013444642767/100000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(19736422988646001/100000000000000000000 : ℝ)+(5013444642767/200000000000000000 : ℝ) ≤ ((579329090853368619/579400000000000000 : ℝ)+(183039221897/289700000000000 : ℝ)*((8161/50000 : ℝ)+(329/3125 : ℝ)))^(4819/1024 : ℝ) := by
    rw [show (579329090853368619/579400000000000000 : ℝ)+(183039221897/289700000000000 : ℝ)*((8161/50000 : ℝ)+(329/3125 : ℝ))=(50002363040691/50000000000000 : ℝ) by norm_num, show 1+(19736422988646001/100000000000000000000 : ℝ)+(5013444642767/200000000000000000 : ℝ)=(100022243145310029501/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(19736422988646001/100000000000000000000 : ℝ) ≤ ((579329090853368619/579400000000000000 : ℝ)+2*(183039221897/289700000000000 : ℝ)*(8161/50000 : ℝ))^(4819/1024 : ℝ) := by
    rw [show (579329090853368619/579400000000000000 : ℝ)+2*(183039221897/289700000000000 : ℝ)*(8161/50000 : ℝ)=(5000419343290997/5000000000000000 : ℝ) by norm_num, show 1+2*(19736422988646001/100000000000000000000 : ℝ)=(50019736422988646001/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (579329090853368619/579400000000000000 : ℝ)*(X 1 0+X 2 0)+(183039221897/289700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4819/1024 : ℝ)) (lo := (329/3125 : ℝ)) (hi := (8161/50000 : ℝ)) (c := (579329090853368619/579400000000000000 : ℝ)) (alpha := (183039221897/289700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (579329090853368619/579400000000000000 : ℝ)*(X 0 1+X 2 1)+(183039221897/289700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4819/1024 : ℝ)) (lo := (329/3125 : ℝ)) (hi := (8161/50000 : ℝ)) (c := (579329090853368619/579400000000000000 : ℝ)) (alpha := (183039221897/289700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (579329090853368619/579400000000000000 : ℝ)*(X 0 2+X 1 2)+(183039221897/289700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4819/1024 : ℝ)) (lo := (329/3125 : ℝ)) (hi := (8161/50000 : ℝ)) (c := (579329090853368619/579400000000000000 : ℝ)) (alpha := (183039221897/289700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1664830989/10000000000 : ℝ)*X 0 0+(681816383/1250000000 : ℝ)*X 0 1+(5182286769/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668906703/1250000000 : ℝ)*X 1 0+(-72204541/400000000 : ℝ)*X 1 1+(1036457321/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337813373/2500000000 : ℝ)*X 2 0+(129557169/250000000 : ℝ)*X 2 1+(-225639187/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4199550943/10000000000 : ℝ)*X 0 0+(773686607/2000000000 : ℝ)*X 0 1+(568943327/1250000000 : ℝ)*X 0 2+(4199550943/10000000000 : ℝ)*X 1 0+(773686607/2000000000 : ℝ)*X 1 1+(568943327/1250000000 : ℝ)*X 1 2+(4199550943/10000000000 : ℝ)*X 2 0+(773686607/2000000000 : ℝ)*X 2 1+(568943327/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-332979711/2000000000 : ℝ)*X 0 0+(1296080859/2500000000 : ℝ)*X 0 1+(5452473031/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2639379639/5000000000 : ℝ)*X 1 0+(-1534927057/10000000000 : ℝ)*X 1 1+(5452472861/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((131968979/250000000 : ℝ)*X 2 0+(5452472841/10000000000 : ℝ)*X 2 1+(-6139709/40000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((839944127/2000000000 : ℝ)*X 0 0+(909287167/2000000000 : ℝ)*X 0 1+(968399397/2500000000 : ℝ)*X 0 2+(839944127/2000000000 : ℝ)*X 1 0+(909287167/2000000000 : ℝ)*X 1 1+(968399397/2500000000 : ℝ)*X 1 2+(839944127/2000000000 : ℝ)*X 2 0+(909287167/2000000000 : ℝ)*X 2 1+(968399397/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10758012046631932300305657/3621250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (496044873/100000000000000 : ℝ)*(base19) + (89942631/25000000000000 : ℝ)*(base23) + (24437889/100000000000000 : ℝ)*(lower2) + (8702137/12500000000000 : ℝ)*(upper3) + (45605033/100000000000000 : ℝ)*(upper5) + (642133806771599/25000000000000 : ℝ)*(major0) + (642133806771599/25000000000000 : ℝ)*(major1) + (642133806771599/25000000000000 : ℝ)*(major2) + (1836588046659657/50000000000000 : ℝ)*(sp0) + (918294909019777/25000000000000 : ℝ)*(sp1) + (3673179772353457/100000000000000 : ℝ)*(sp2) + (731943860326601/50000000000000 : ℝ)*(sp3) + (4038804667/100000000000000 : ℝ)*(sp4) + (625592227/25000000000000 : ℝ)*(sp7) + (146389022302211/10000000000000 : ℝ)*(f.failure) + (183659006606199/5000000000000 : ℝ)*(f.sum) + (101533314780737/14485000000000000000000000000 : ℝ)*base65 + (26121474885027781/14485000000000000000000000000000 : ℝ)*base67 + (2205895105342781/14485000000000000000000000000000 : ℝ)*base69 + (17014584245472219/14485000000000000000000000000000 : ℝ)*base72 + (5619842401769/7242500000000000000000000000 : ℝ)*base74 + (124170229591797781/14485000000000000000000000000000 : ℝ)*base75 + (214834723717307781/14485000000000000000000000000000 : ℝ)*base77 + (104153858662207781/14485000000000000000000000000000 : ℝ)*base79 + (2734208518707/3621250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (291579/31250000000000000000 : ℝ)*base90 + (291579/31250000000000000000 : ℝ)*base92 + (291579/31250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (42598667348014437766389/14485000000000000000000000000 : ℝ) := by norm_num
    linear_combination (302623067/50000000000000 : ℝ)*(base19) + (577224299/100000000000000 : ℝ)*(base23) + (61668733/50000000000000 : ℝ)*(lower1) + (20110647/100000000000000 : ℝ)*(upper3) + (23781779/50000000000000 : ℝ)*(lower4) + (62294899/100000000000000 : ℝ)*(upper5) + (2607747828331871/100000000000000 : ℝ)*(major0) + (2607747828331871/100000000000000 : ℝ)*(major1) + (2607747828331871/100000000000000 : ℝ)*(major2) + (2531285089/100000000000000 : ℝ)*(sp1) + (3729256822351779/100000000000000 : ℝ)*(sp4) + (745850737164111/20000000000000 : ℝ)*(sp5) + (93231406128187/2500000000000 : ℝ)*(sp6) + (1486238736282577/100000000000000 : ℝ)*(sp7) + (1486238736282577/100000000000000 : ℝ)*(f.failure) + (3729256822351779/100000000000000 : ℝ)*(f.sum) + (54641305410037/14485000000000000000000000000 : ℝ)*base65 + (260234465091870149/57940000000000000000000000000000 : ℝ)*base67 + (309261096676969851/57940000000000000000000000000000 : ℝ)*base70 + (698903490262790149/57940000000000000000000000000000 : ℝ)*base71 + (531148587291/452656250000000000000000000 : ℝ)*base73 + (628091148478090149/57940000000000000000000000000000 : ℝ)*base75 + (41566521530769851/57940000000000000000000000000000 : ℝ)*base78 + (132412054313969851/57940000000000000000000000000000 : ℝ)*base80 + (36885023908573/14485000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (182047/312500000000000000000 : ℝ)*base89 + (182047/312500000000000000000 : ℝ)*base91 + (182047/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1626_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5483111/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8161/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (329/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1317/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16313/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1626_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1626_box_0 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-349477687/2500000000 : ℝ)*x 0 + (5414037851/10000000000 : ℝ)*x 1 + (2707018197/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (349477687/2500000000 : ℝ)^4823 ≤ (8225229567821/100000000000000 : ℝ)^3799 := by
    have hnat : (349477687 : ℕ)^4823*100000000000000^3799 ≤ 8225229567821^3799*2500000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      349477687 2500000000 8225229567821 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414037851/10000000000 : ℝ)^4823 ≤ (1433981032719/3125000000000 : ℝ)^3799 := by
    have hnat : (5414037851 : ℕ)^4823*3125000000000^3799 ≤ 1433981032719^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414037851 10000000000 1433981032719 3125000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707018197/5000000000 : ℝ)^4823 ≤ (45887377369407/100000000000000 : ℝ)^3799 := by
    have hnat : (2707018197 : ℕ)^4823*100000000000000^3799 ≤ 45887377369407^3799*5000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707018197 5000000000 45887377369407 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-349477687/2500000000 : ℝ), (5414037851/10000000000 : ℝ), (2707018197/5000000000 : ℝ)] ![(8225229567821/100000000000000 : ℝ), (1433981032719/3125000000000 : ℝ), (45887377369407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-349477687/2500000000 : ℝ)|^4823 ≤ (8225229567821/100000000000000 : ℝ)^3799
        have hw : |(-349477687/2500000000 : ℝ)|=(349477687/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414037851/10000000000 : ℝ)|^4823 ≤ (1433981032719/3125000000000 : ℝ)^3799
        have hw : |(5414037851/10000000000 : ℝ)|=(5414037851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707018197/5000000000 : ℝ)|^4823 ≤ (45887377369407/100000000000000 : ℝ)^3799
        have hw : |(2707018197/5000000000 : ℝ)|=(2707018197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_box_1 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42010037/80000000 : ℝ)*x 0 + (-813292111/5000000000 : ℝ)*x 1 + (2707018059/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42010037/80000000 : ℝ)^4823 ≤ (44142964465239/100000000000000 : ℝ)^3799 := by
    have hnat : (42010037 : ℕ)^4823*100000000000000^3799 ≤ 44142964465239^3799*80000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42010037 80000000 44142964465239 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (813292111/5000000000 : ℝ)^4823 ≤ (398786444857/4000000000000 : ℝ)^3799 := by
    have hnat : (813292111 : ℕ)^4823*4000000000000^3799 ≤ 398786444857^3799*5000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      813292111 5000000000 398786444857 4000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707018059/5000000000 : ℝ)^4823 ≤ (22943687199797/50000000000000 : ℝ)^3799 := by
    have hnat : (2707018059 : ℕ)^4823*50000000000000^3799 ≤ 22943687199797^3799*5000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707018059 5000000000 22943687199797 50000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42010037/80000000 : ℝ), (-813292111/5000000000 : ℝ), (2707018059/5000000000 : ℝ)] ![(44142964465239/100000000000000 : ℝ), (398786444857/4000000000000 : ℝ), (22943687199797/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42010037/80000000 : ℝ)|^4823 ≤ (44142964465239/100000000000000 : ℝ)^3799
        have hw : |(42010037/80000000 : ℝ)|=(42010037/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-813292111/5000000000 : ℝ)|^4823 ≤ (398786444857/4000000000000 : ℝ)^3799
        have hw : |(-813292111/5000000000 : ℝ)|=(813292111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707018059/5000000000 : ℝ)|^4823 ≤ (22943687199797/50000000000000 : ℝ)^3799
        have hw : |(2707018059/5000000000 : ℝ)|=(2707018059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_box_2 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251253477/10000000000 : ℝ)*x 0 + (5414037361/10000000000 : ℝ)*x 1 + (-1626584077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251253477/10000000000 : ℝ)^4823 ≤ (44142952213767/100000000000000 : ℝ)^3799 := by
    have hnat : (5251253477 : ℕ)^4823*100000000000000^3799 ≤ 44142952213767^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251253477 10000000000 44142952213767 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414037361/10000000000 : ℝ)^4823 ≤ (22943693887257/50000000000000 : ℝ)^3799 := by
    have hnat : (5414037361 : ℕ)^4823*50000000000000^3799 ≤ 22943693887257^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414037361 10000000000 22943693887257 50000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1626584077/10000000000 : ℝ)^4823 ≤ (9969659993137/100000000000000 : ℝ)^3799 := by
    have hnat : (1626584077 : ℕ)^4823*100000000000000^3799 ≤ 9969659993137^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1626584077 10000000000 9969659993137 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251253477/10000000000 : ℝ), (5414037361/10000000000 : ℝ), (-1626584077/10000000000 : ℝ)] ![(44142952213767/100000000000000 : ℝ), (22943693887257/50000000000000 : ℝ), (9969659993137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251253477/10000000000 : ℝ)|^4823 ≤ (44142952213767/100000000000000 : ℝ)^3799
        have hw : |(5251253477/10000000000 : ℝ)|=(5251253477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414037361/10000000000 : ℝ)|^4823 ≤ (22943693887257/50000000000000 : ℝ)^3799
        have hw : |(5414037361/10000000000 : ℝ)|=(5414037361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1626584077/10000000000 : ℝ)|^4823 ≤ (9969659993137/100000000000000 : ℝ)^3799
        have hw : |(-1626584077/10000000000 : ℝ)|=(1626584077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_box_3 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2239043507/5000000000 : ℝ)*x 0 + (254544997/625000000 : ℝ)*x 1 + (4072719179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2239043507/5000000000 : ℝ)^4823 ≤ (36061716700307/100000000000000 : ℝ)^3799 := by
    have hnat : (2239043507 : ℕ)^4823*100000000000000^3799 ≤ 36061716700307^3799*5000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239043507 5000000000 36061716700307 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (254544997/625000000 : ℝ)^4823 ≤ (31969145495307/100000000000000 : ℝ)^3799 := by
    have hnat : (254544997 : ℕ)^4823*100000000000000^3799 ≤ 31969145495307^3799*625000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254544997 625000000 31969145495307 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4072719179/10000000000 : ℝ)^4823 ≤ (15984568896029/50000000000000 : ℝ)^3799 := by
    have hnat : (4072719179 : ℕ)^4823*50000000000000^3799 ≤ 15984568896029^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4072719179 10000000000 15984568896029 50000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2239043507/5000000000 : ℝ), (254544997/625000000 : ℝ), (4072719179/10000000000 : ℝ)] ![(36061716700307/100000000000000 : ℝ), (31969145495307/100000000000000 : ℝ), (15984568896029/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2239043507/5000000000 : ℝ)|^4823 ≤ (36061716700307/100000000000000 : ℝ)^3799
        have hw : |(2239043507/5000000000 : ℝ)|=(2239043507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(254544997/625000000 : ℝ)|^4823 ≤ (31969145495307/100000000000000 : ℝ)^3799
        have hw : |(254544997/625000000 : ℝ)|=(254544997/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4072719179/10000000000 : ℝ)|^4823 ≤ (15984568896029/50000000000000 : ℝ)^3799
        have hw : |(4072719179/10000000000 : ℝ)|=(4072719179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_box_4 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-971224631/5000000000 : ℝ)*x 0 + (5214913243/10000000000 : ℝ)*x 1 + (325932097/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (971224631/5000000000 : ℝ)^4823 ≤ (12489014550671/100000000000000 : ℝ)^3799 := by
    have hnat : (971224631 : ℕ)^4823*100000000000000^3799 ≤ 12489014550671^3799*5000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      971224631 5000000000 12489014550671 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5214913243/10000000000 : ℝ)^4823 ≤ (21877745535391/50000000000000 : ℝ)^3799 := by
    have hnat : (5214913243 : ℕ)^4823*50000000000000^3799 ≤ 21877745535391^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214913243 10000000000 21877745535391 50000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (325932097/625000000 : ℝ)^4823 ≤ (10938873590567/25000000000000 : ℝ)^3799 := by
    have hnat : (325932097 : ℕ)^4823*25000000000000^3799 ≤ 10938873590567^3799*625000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325932097 625000000 10938873590567 25000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-971224631/5000000000 : ℝ), (5214913243/10000000000 : ℝ), (325932097/625000000 : ℝ)] ![(12489014550671/100000000000000 : ℝ), (21877745535391/50000000000000 : ℝ), (10938873590567/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-971224631/5000000000 : ℝ)|^4823 ≤ (12489014550671/100000000000000 : ℝ)^3799
        have hw : |(-971224631/5000000000 : ℝ)|=(971224631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5214913243/10000000000 : ℝ)|^4823 ≤ (21877745535391/50000000000000 : ℝ)^3799
        have hw : |(5214913243/10000000000 : ℝ)|=(5214913243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(325932097/625000000 : ℝ)|^4823 ≤ (10938873590567/25000000000000 : ℝ)^3799
        have hw : |(325932097/625000000 : ℝ)|=(325932097/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_box_5 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (673547047/1250000000 : ℝ)*x 0 + (-1711253089/10000000000 : ℝ)*x 1 + (521491349/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (673547047/1250000000 : ℝ)^4823 ≤ (45611447209683/100000000000000 : ℝ)^3799 := by
    have hnat : (673547047 : ℕ)^4823*100000000000000^3799 ≤ 45611447209683^3799*1250000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673547047 1250000000 45611447209683 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1711253089/10000000000 : ℝ)^4823 ≤ (5316529539847/50000000000000 : ℝ)^3799 := by
    have hnat : (1711253089 : ℕ)^4823*50000000000000^3799 ≤ 5316529539847^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1711253089 10000000000 5316529539847 50000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521491349/1000000000 : ℝ)^4823 ≤ (546943671273/1250000000000 : ℝ)^3799 := by
    have hnat : (521491349 : ℕ)^4823*1250000000000^3799 ≤ 546943671273^3799*1000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521491349 1000000000 546943671273 1250000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(673547047/1250000000 : ℝ), (-1711253089/10000000000 : ℝ), (521491349/1000000000 : ℝ)] ![(45611447209683/100000000000000 : ℝ), (5316529539847/50000000000000 : ℝ), (546943671273/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(673547047/1250000000 : ℝ)|^4823 ≤ (45611447209683/100000000000000 : ℝ)^3799
        have hw : |(673547047/1250000000 : ℝ)|=(673547047/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1711253089/10000000000 : ℝ)|^4823 ≤ (5316529539847/50000000000000 : ℝ)^3799
        have hw : |(-1711253089/10000000000 : ℝ)|=(1711253089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(521491349/1000000000 : ℝ)|^4823 ≤ (546943671273/1250000000000 : ℝ)^3799
        have hw : |(521491349/1000000000 : ℝ)|=(521491349/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_box_6 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5388376513/10000000000 : ℝ)*x 0 + (2607456483/5000000000 : ℝ)*x 1 + (-1711253609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5388376513/10000000000 : ℝ)^4823 ≤ (45611448681943/100000000000000 : ℝ)^3799 := by
    have hnat : (5388376513 : ℕ)^4823*100000000000000^3799 ≤ 45611448681943^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388376513 10000000000 45611448681943 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2607456483/5000000000 : ℝ)^4823 ≤ (43755488120163/100000000000000 : ℝ)^3799 := by
    have hnat : (2607456483 : ℕ)^4823*100000000000000^3799 ≤ 43755488120163^3799*5000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607456483 5000000000 43755488120163 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1711253609/10000000000 : ℝ)^4823 ≤ (1063306318169/10000000000000 : ℝ)^3799 := by
    have hnat : (1711253609 : ℕ)^4823*10000000000000^3799 ≤ 1063306318169^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1711253609 10000000000 1063306318169 10000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5388376513/10000000000 : ℝ), (2607456483/5000000000 : ℝ), (-1711253609/10000000000 : ℝ)] ![(45611448681943/100000000000000 : ℝ), (43755488120163/100000000000000 : ℝ), (1063306318169/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5388376513/10000000000 : ℝ)|^4823 ≤ (45611448681943/100000000000000 : ℝ)^3799
        have hw : |(5388376513/10000000000 : ℝ)|=(5388376513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2607456483/5000000000 : ℝ)|^4823 ≤ (43755488120163/100000000000000 : ℝ)^3799
        have hw : |(2607456483/5000000000 : ℝ)|=(2607456483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1711253609/10000000000 : ℝ)|^4823 ≤ (1063306318169/10000000000000 : ℝ)^3799
        have hw : |(-1711253609/10000000000 : ℝ)|=(1711253609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_box_7 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1957442863/5000000000 : ℝ)*x 0 + (4353984631/10000000000 : ℝ)*x 1 + (2176992287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1957442863/5000000000 : ℝ)^4823 ≤ (3800569910851/12500000000000 : ℝ)^3799 := by
    have hnat : (1957442863 : ℕ)^4823*12500000000000^3799 ≤ 3800569910851^3799*5000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1957442863 5000000000 3800569910851 12500000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4353984631/10000000000 : ℝ)^4823 ≤ (3479772064067/10000000000000 : ℝ)^3799 := by
    have hnat : (4353984631 : ℕ)^4823*10000000000000^3799 ≤ 3479772064067^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353984631 10000000000 3479772064067 10000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2176992287/5000000000 : ℝ)^4823 ≤ (1391908802493/4000000000000 : ℝ)^3799 := by
    have hnat : (2176992287 : ℕ)^4823*4000000000000^3799 ≤ 1391908802493^3799*5000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176992287 5000000000 1391908802493 4000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1957442863/5000000000 : ℝ), (4353984631/10000000000 : ℝ), (2176992287/5000000000 : ℝ)] ![(3800569910851/12500000000000 : ℝ), (3479772064067/10000000000000 : ℝ), (1391908802493/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1957442863/5000000000 : ℝ)|^4823 ≤ (3800569910851/12500000000000 : ℝ)^3799
        have hw : |(1957442863/5000000000 : ℝ)|=(1957442863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4353984631/10000000000 : ℝ)|^4823 ≤ (3479772064067/10000000000000 : ℝ)^3799
        have hw : |(4353984631/10000000000 : ℝ)|=(4353984631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2176992287/5000000000 : ℝ)|^4823 ≤ (1391908802493/4000000000000 : ℝ)^3799
        have hw : |(2176992287/5000000000 : ℝ)|=(2176992287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_box_8 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1826509359/10000000000 : ℝ)*x 0 + (5072287689/10000000000 : ℝ)*x 1 + (2721894239/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1826509359/10000000000 : ℝ)^4823 ≤ (45118649823/390625000000 : ℝ)^3799 := by
    have hnat : (1826509359 : ℕ)^4823*390625000000^3799 ≤ 45118649823^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1826509359 10000000000 45118649823 390625000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5072287689/10000000000 : ℝ)^4823 ≤ (42241873333123/100000000000000 : ℝ)^3799 := by
    have hnat : (5072287689 : ℕ)^4823*100000000000000^3799 ≤ 42241873333123^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5072287689 10000000000 42241873333123 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2721894239/5000000000 : ℝ)^4823 ≤ (4620775230073/10000000000000 : ℝ)^3799 := by
    have hnat : (2721894239 : ℕ)^4823*10000000000000^3799 ≤ 4620775230073^3799*5000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721894239 5000000000 4620775230073 10000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1826509359/10000000000 : ℝ), (5072287689/10000000000 : ℝ), (2721894239/5000000000 : ℝ)] ![(45118649823/390625000000 : ℝ), (42241873333123/100000000000000 : ℝ), (4620775230073/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1826509359/10000000000 : ℝ)|^4823 ≤ (45118649823/390625000000 : ℝ)^3799
        have hw : |(-1826509359/10000000000 : ℝ)|=(1826509359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5072287689/10000000000 : ℝ)|^4823 ≤ (42241873333123/100000000000000 : ℝ)^3799
        have hw : |(5072287689/10000000000 : ℝ)|=(5072287689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2721894239/5000000000 : ℝ)|^4823 ≤ (4620775230073/10000000000000 : ℝ)^3799
        have hw : |(2721894239/5000000000 : ℝ)|=(2721894239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_box_9 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1307691003/2500000000 : ℝ)*x 0 + (-1613485271/10000000000 : ℝ)*x 1 + (5443788389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1307691003/2500000000 : ℝ)^4823 ≤ (21962201732337/50000000000000 : ℝ)^3799 := by
    have hnat : (1307691003 : ℕ)^4823*50000000000000^3799 ≤ 21962201732337^3799*2500000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307691003 2500000000 21962201732337 50000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1613485271/10000000000 : ℝ)^4823 ≤ (986784517769/10000000000000 : ℝ)^3799 := by
    have hnat : (1613485271 : ℕ)^4823*10000000000000^3799 ≤ 986784517769^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1613485271 10000000000 986784517769 10000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5443788389/10000000000 : ℝ)^4823 ≤ (23103875670829/50000000000000 : ℝ)^3799 := by
    have hnat : (5443788389 : ℕ)^4823*50000000000000^3799 ≤ 23103875670829^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443788389 10000000000 23103875670829 50000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1307691003/2500000000 : ℝ), (-1613485271/10000000000 : ℝ), (5443788389/10000000000 : ℝ)] ![(21962201732337/50000000000000 : ℝ), (986784517769/10000000000000 : ℝ), (23103875670829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1307691003/2500000000 : ℝ)|^4823 ≤ (21962201732337/50000000000000 : ℝ)^3799
        have hw : |(1307691003/2500000000 : ℝ)|=(1307691003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1613485271/10000000000 : ℝ)|^4823 ≤ (986784517769/10000000000000 : ℝ)^3799
        have hw : |(-1613485271/10000000000 : ℝ)|=(1613485271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5443788389/10000000000 : ℝ)|^4823 ≤ (23103875670829/50000000000000 : ℝ)^3799
        have hw : |(5443788389/10000000000 : ℝ)|=(5443788389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_box_10 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2615381973/5000000000 : ℝ)*x 0 + (5443788399/10000000000 : ℝ)*x 1 + (-403371337/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2615381973/5000000000 : ℝ)^4823 ≤ (43924402761063/100000000000000 : ℝ)^3799 := by
    have hnat : (2615381973 : ℕ)^4823*100000000000000^3799 ≤ 43924402761063^3799*5000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615381973 5000000000 43924402761063 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5443788399/10000000000 : ℝ)^4823 ≤ (23103875724709/50000000000000 : ℝ)^3799 := by
    have hnat : (5443788399 : ℕ)^4823*50000000000000^3799 ≤ 23103875724709^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443788399 10000000000 23103875724709 50000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (403371337/2500000000 : ℝ)^4823 ≤ (1973569155109/20000000000000 : ℝ)^3799 := by
    have hnat : (403371337 : ℕ)^4823*20000000000000^3799 ≤ 1973569155109^3799*2500000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403371337 2500000000 1973569155109 20000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2615381973/5000000000 : ℝ), (5443788399/10000000000 : ℝ), (-403371337/2500000000 : ℝ)] ![(43924402761063/100000000000000 : ℝ), (23103875724709/50000000000000 : ℝ), (1973569155109/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2615381973/5000000000 : ℝ)|^4823 ≤ (43924402761063/100000000000000 : ℝ)^3799
        have hw : |(2615381973/5000000000 : ℝ)|=(2615381973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5443788399/10000000000 : ℝ)|^4823 ≤ (23103875724709/50000000000000 : ℝ)^3799
        have hw : |(5443788399/10000000000 : ℝ)|=(5443788399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-403371337/2500000000 : ℝ)|^4823 ≤ (1973569155109/20000000000000 : ℝ)^3799
        have hw : |(-403371337/2500000000 : ℝ)|=(403371337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_box_11 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1139961517/2500000000 : ℝ)*x 0 + (4030619489/10000000000 : ℝ)*x 1 + (4030619491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1139961517/2500000000 : ℝ)^4823 ≤ (18449816185963/50000000000000 : ℝ)^3799 := by
    have hnat : (1139961517 : ℕ)^4823*50000000000000^3799 ≤ 18449816185963^3799*2500000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1139961517 2500000000 18449816185963 50000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4030619489/10000000000 : ℝ)^4823 ≤ (31550183796233/100000000000000 : ℝ)^3799 := by
    have hnat : (4030619489 : ℕ)^4823*100000000000000^3799 ≤ 31550183796233^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4030619489 10000000000 31550183796233 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4030619491/10000000000 : ℝ)^4823 ≤ (7887545954027/25000000000000 : ℝ)^3799 := by
    have hnat : (4030619491 : ℕ)^4823*25000000000000^3799 ≤ 7887545954027^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4030619491 10000000000 7887545954027 25000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1139961517/2500000000 : ℝ), (4030619489/10000000000 : ℝ), (4030619491/10000000000 : ℝ)] ![(18449816185963/50000000000000 : ℝ), (31550183796233/100000000000000 : ℝ), (7887545954027/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1139961517/2500000000 : ℝ)|^4823 ≤ (18449816185963/50000000000000 : ℝ)^3799
        have hw : |(1139961517/2500000000 : ℝ)|=(1139961517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4030619489/10000000000 : ℝ)|^4823 ≤ (31550183796233/100000000000000 : ℝ)^3799
        have hw : |(4030619489/10000000000 : ℝ)|=(4030619489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4030619491/10000000000 : ℝ)|^4823 ≤ (7887545954027/25000000000000 : ℝ)^3799
        have hw : |(4030619491/10000000000 : ℝ)|=(4030619491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_box_12 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-756198669/5000000000 : ℝ)*x 0 + (555101097/1000000000 : ℝ)*x 1 + (5195054277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (756198669/5000000000 : ℝ)^4823 ≤ (9089694030831/100000000000000 : ℝ)^3799 := by
    have hnat : (756198669 : ℕ)^4823*100000000000000^3799 ≤ 9089694030831^3799*5000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      756198669 5000000000 9089694030831 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (555101097/1000000000 : ℝ)^4823 ≤ (23683122515587/50000000000000 : ℝ)^3799 := by
    have hnat : (555101097 : ℕ)^4823*50000000000000^3799 ≤ 23683122515587^3799*1000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      555101097 1000000000 23683122515587 50000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5195054277/10000000000 : ℝ)^4823 ≤ (43544060920327/100000000000000 : ℝ)^3799 := by
    have hnat : (5195054277 : ℕ)^4823*100000000000000^3799 ≤ 43544060920327^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195054277 10000000000 43544060920327 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-756198669/5000000000 : ℝ), (555101097/1000000000 : ℝ), (5195054277/10000000000 : ℝ)] ![(9089694030831/100000000000000 : ℝ), (23683122515587/50000000000000 : ℝ), (43544060920327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-756198669/5000000000 : ℝ)|^4823 ≤ (9089694030831/100000000000000 : ℝ)^3799
        have hw : |(-756198669/5000000000 : ℝ)|=(756198669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(555101097/1000000000 : ℝ)|^4823 ≤ (23683122515587/50000000000000 : ℝ)^3799
        have hw : |(555101097/1000000000 : ℝ)|=(555101097/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5195054277/10000000000 : ℝ)|^4823 ≤ (43544060920327/100000000000000 : ℝ)^3799
        have hw : |(5195054277/10000000000 : ℝ)|=(5195054277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_box_13 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5402060763/10000000000 : ℝ)*x 0 + (-1719403433/10000000000 : ℝ)*x 1 + (1298763321/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5402060763/10000000000 : ℝ)^4823 ≤ (22879277855891/50000000000000 : ℝ)^3799 := by
    have hnat : (5402060763 : ℕ)^4823*50000000000000^3799 ≤ 22879277855891^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402060763 10000000000 22879277855891 50000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1719403433/10000000000 : ℝ)^4823 ≤ (10697393923081/100000000000000 : ℝ)^3799 := by
    have hnat : (1719403433 : ℕ)^4823*100000000000000^3799 ≤ 10697393923081^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1719403433 10000000000 10697393923081 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1298763321/2500000000 : ℝ)^4823 ≤ (10886012588427/25000000000000 : ℝ)^3799 := by
    have hnat : (1298763321 : ℕ)^4823*25000000000000^3799 ≤ 10886012588427^3799*2500000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298763321 2500000000 10886012588427 25000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5402060763/10000000000 : ℝ), (-1719403433/10000000000 : ℝ), (1298763321/2500000000 : ℝ)] ![(22879277855891/50000000000000 : ℝ), (10697393923081/100000000000000 : ℝ), (10886012588427/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5402060763/10000000000 : ℝ)|^4823 ≤ (22879277855891/50000000000000 : ℝ)^3799
        have hw : |(5402060763/10000000000 : ℝ)|=(5402060763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1719403433/10000000000 : ℝ)|^4823 ≤ (10697393923081/100000000000000 : ℝ)^3799
        have hw : |(-1719403433/10000000000 : ℝ)|=(1719403433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1298763321/2500000000 : ℝ)|^4823 ≤ (10886012588427/25000000000000 : ℝ)^3799
        have hw : |(1298763321/2500000000 : ℝ)|=(1298763321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_box_14 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2701030217/5000000000 : ℝ)*x 0 + (5195052961/10000000000 : ℝ)*x 1 + (-429851079/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2701030217/5000000000 : ℝ)^4823 ≤ (1429954755431/3125000000000 : ℝ)^3799 := by
    have hnat : (2701030217 : ℕ)^4823*3125000000000^3799 ≤ 1429954755431^3799*5000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701030217 5000000000 1429954755431 3125000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5195052961/10000000000 : ℝ)^4823 ≤ (4354404691663/10000000000000 : ℝ)^3799 := by
    have hnat : (5195052961 : ℕ)^4823*10000000000000^3799 ≤ 4354404691663^3799*10000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195052961 10000000000 4354404691663 10000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (429851079/2500000000 : ℝ)^4823 ≤ (5348700448757/50000000000000 : ℝ)^3799 := by
    have hnat : (429851079 : ℕ)^4823*50000000000000^3799 ≤ 5348700448757^3799*2500000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429851079 2500000000 5348700448757 50000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2701030217/5000000000 : ℝ), (5195052961/10000000000 : ℝ), (-429851079/2500000000 : ℝ)] ![(1429954755431/3125000000000 : ℝ), (4354404691663/10000000000000 : ℝ), (5348700448757/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2701030217/5000000000 : ℝ)|^4823 ≤ (1429954755431/3125000000000 : ℝ)^3799
        have hw : |(2701030217/5000000000 : ℝ)|=(2701030217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5195052961/10000000000 : ℝ)|^4823 ≤ (4354404691663/10000000000000 : ℝ)^3799
        have hw : |(5195052961/10000000000 : ℝ)|=(5195052961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-429851079/2500000000 : ℝ)|^4823 ≤ (5348700448757/50000000000000 : ℝ)^3799
        have hw : |(-429851079/2500000000 : ℝ)|=(429851079/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1626_box_15 (p : ℝ) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (771417711/2000000000 : ℝ)*x 0 + (273874157/625000000 : ℝ)*x 1 + (2190993311/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (771417711/2000000000 : ℝ)^4823 ≤ (29835829384661/100000000000000 : ℝ)^3799 := by
    have hnat : (771417711 : ℕ)^4823*100000000000000^3799 ≤ 29835829384661^3799*2000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      771417711 2000000000 29835829384661 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273874157/625000000 : ℝ)^4823 ≤ (35082084735943/100000000000000 : ℝ)^3799 := by
    have hnat : (273874157 : ℕ)^4823*100000000000000^3799 ≤ 35082084735943^3799*625000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273874157 625000000 35082084735943 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2190993311/5000000000 : ℝ)^4823 ≤ (35082085853977/100000000000000 : ℝ)^3799 := by
    have hnat : (2190993311 : ℕ)^4823*100000000000000^3799 ≤ 35082085853977^3799*5000000000^4823 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190993311 5000000000 35082085853977 100000000000000 4823 3799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4823/1024 : ℝ)) 4823 3799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(771417711/2000000000 : ℝ), (273874157/625000000 : ℝ), (2190993311/5000000000 : ℝ)] ![(29835829384661/100000000000000 : ℝ), (35082084735943/100000000000000 : ℝ), (35082085853977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(771417711/2000000000 : ℝ)|^4823 ≤ (29835829384661/100000000000000 : ℝ)^3799
        have hw : |(771417711/2000000000 : ℝ)|=(771417711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(273874157/625000000 : ℝ)|^4823 ≤ (35082084735943/100000000000000 : ℝ)^3799
        have hw : |(273874157/625000000 : ℝ)|=(273874157/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2190993311/5000000000 : ℝ)|^4823 ≤ (35082085853977/100000000000000 : ℝ)^3799
        have hw : |(2190993311/5000000000 : ℝ)|=(2190993311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1626_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5483111/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16313/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1317/12500 : ℝ)*pair X i i ≤ pair X i h) :
    -(32487/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58367/100000 : ℝ) ∧ (80747/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (87987/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16313/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1317/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16313/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1317/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16313/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1317/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16313/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1317/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16313/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1317/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16313/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1317/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1317/12500 : ℝ) ^ (4819/1024 : ℝ) ≤ (2515699064898603/100000000000000000000 : ℝ) := by
    have hpowers : (1317/12500 : ℝ)^4819 ≤ (2515699064898603/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1317 : ℕ)^4819*100000000000000000000^1024 ≤ 2515699064898603^1024*12500^4819 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1317 12500 2515699064898603 100000000000000000000 4819 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1317/12500 : ℝ)) (X := (2515699064898603/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4819 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16313/100000 : ℝ) ^ (4819/1024 : ℝ) ≤ (9842630300902819/50000000000000000000 : ℝ) := by
    have hpowers : (16313/100000 : ℝ)^4819 ≤ (9842630300902819/50000000000000000000 : ℝ)^1024 := by
      have hnat : (16313 : ℕ)^4819*50000000000000000000^1024 ≤ 9842630300902819^1024*100000^4819 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16313 100000 9842630300902819 50000000000000000000 4819 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16313/100000 : ℝ)) (X := (9842630300902819/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4819 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002515699064898603/50000000000000000000 : ℝ) ≤ (5000053455588473/5000000000000000 : ℝ) ^ (4819/1024 : ℝ) := by
    have hpowers : (50002515699064898603/50000000000000000000 : ℝ)^1024 ≤ (5000053455588473/5000000000000000 : ℝ)^4819 := by
      have hnat : (50002515699064898603 : ℕ)^1024*5000000000000000^4819 ≤ 5000053455588473^4819*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002515699064898603 50000000000000000000 5000053455588473 5000000000000000 1024 4819 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000053455588473/5000000000000000 : ℝ)) (X := (50002515699064898603/50000000000000000000 : ℝ)) (by norm_num) 4819 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100022200959666704241/100000000000000000000 : ℝ) ≤ (2500117927970737/2500000000000000 : ℝ) ^ (4819/1024 : ℝ) := by
    have hpowers : (100022200959666704241/100000000000000000000 : ℝ)^1024 ≤ (2500117927970737/2500000000000000 : ℝ)^4819 := by
      have hnat : (100022200959666704241 : ℕ)^1024*2500000000000000^4819 ≤ 2500117927970737^4819*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100022200959666704241 100000000000000000000 2500117927970737 2500000000000000 1024 4819 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500117927970737/2500000000000000 : ℝ)) (X := (100022200959666704241/100000000000000000000 : ℝ)) (by norm_num) 4819 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25009842630300902819/25000000000000000000 : ℝ) ≤ (200016730251779/200000000000000 : ℝ) ^ (4819/1024 : ℝ) := by
    have hpowers : (25009842630300902819/25000000000000000000 : ℝ)^1024 ≤ (200016730251779/200000000000000 : ℝ)^4819 := by
      have hnat : (25009842630300902819 : ℕ)^1024*200000000000000^4819 ≤ 200016730251779^4819*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009842630300902819 25000000000000000000 200016730251779 200000000000000 1024 4819 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200016730251779/200000000000000 : ℝ)) (X := (25009842630300902819/25000000000000000000 : ℝ)) (by norm_num) 4819 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2515699064898603/100000000000000000000 : ℝ) ≤ ((28881465272696171449/28885000000000000000 : ℝ)+2*(182400353001/288850000000000 : ℝ)*(1317/12500 : ℝ))^(4819/1024 : ℝ) := by
    rw [show (28881465272696171449/28885000000000000000 : ℝ)+2*(182400353001/288850000000000 : ℝ)*(1317/12500 : ℝ)=(5000053455588473/5000000000000000 : ℝ) by norm_num, show 1+2*(2515699064898603/100000000000000000000 : ℝ)=(50002515699064898603/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9842630300902819/50000000000000000000 : ℝ)+(2515699064898603/100000000000000000000 : ℝ) ≤ ((28881465272696171449/28885000000000000000 : ℝ)+(182400353001/288850000000000 : ℝ)*((16313/100000 : ℝ)+(1317/12500 : ℝ)))^(4819/1024 : ℝ) := by
    rw [show (28881465272696171449/28885000000000000000 : ℝ)+(182400353001/288850000000000 : ℝ)*((16313/100000 : ℝ)+(1317/12500 : ℝ))=(2500117927970737/2500000000000000 : ℝ) by norm_num, show 1+(9842630300902819/50000000000000000000 : ℝ)+(2515699064898603/100000000000000000000 : ℝ)=(100022200959666704241/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9842630300902819/50000000000000000000 : ℝ) ≤ ((28881465272696171449/28885000000000000000 : ℝ)+2*(182400353001/288850000000000 : ℝ)*(16313/100000 : ℝ))^(4819/1024 : ℝ) := by
    rw [show (28881465272696171449/28885000000000000000 : ℝ)+2*(182400353001/288850000000000 : ℝ)*(16313/100000 : ℝ)=(200016730251779/200000000000000 : ℝ) by norm_num, show 1+2*(9842630300902819/50000000000000000000 : ℝ)=(25009842630300902819/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28881465272696171449/28885000000000000000 : ℝ)*(X 1 0+X 2 0)+(182400353001/288850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4819/1024 : ℝ)) (lo := (1317/12500 : ℝ)) (hi := (16313/100000 : ℝ)) (c := (28881465272696171449/28885000000000000000 : ℝ)) (alpha := (182400353001/288850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28881465272696171449/28885000000000000000 : ℝ)*(X 0 1+X 2 1)+(182400353001/288850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4819/1024 : ℝ)) (lo := (1317/12500 : ℝ)) (hi := (16313/100000 : ℝ)) (c := (28881465272696171449/28885000000000000000 : ℝ)) (alpha := (182400353001/288850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28881465272696171449/28885000000000000000 : ℝ)*(X 0 2+X 1 2)+(182400353001/288850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4819/1024 : ℝ)) (lo := (1317/12500 : ℝ)) (hi := (16313/100000 : ℝ)) (c := (28881465272696171449/28885000000000000000 : ℝ)) (alpha := (182400353001/288850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-349477687/2500000000 : ℝ)*X 0 0+(5414037851/10000000000 : ℝ)*X 0 1+(2707018197/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((42010037/80000000 : ℝ)*X 1 0+(-813292111/5000000000 : ℝ)*X 1 1+(2707018059/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5251253477/10000000000 : ℝ)*X 2 0+(5414037361/10000000000 : ℝ)*X 2 1+(-1626584077/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2239043507/5000000000 : ℝ)*X 0 0+(254544997/625000000 : ℝ)*X 0 1+(4072719179/10000000000 : ℝ)*X 0 2+(2239043507/5000000000 : ℝ)*X 1 0+(254544997/625000000 : ℝ)*X 1 1+(4072719179/10000000000 : ℝ)*X 1 2+(2239043507/5000000000 : ℝ)*X 2 0+(254544997/625000000 : ℝ)*X 2 1+(4072719179/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-971224631/5000000000 : ℝ)*X 0 0+(5214913243/10000000000 : ℝ)*X 0 1+(325932097/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((673547047/1250000000 : ℝ)*X 1 0+(-1711253089/10000000000 : ℝ)*X 1 1+(521491349/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5388376513/10000000000 : ℝ)*X 2 0+(2607456483/5000000000 : ℝ)*X 2 1+(-1711253609/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1957442863/5000000000 : ℝ)*X 0 0+(4353984631/10000000000 : ℝ)*X 0 1+(2176992287/5000000000 : ℝ)*X 0 2+(1957442863/5000000000 : ℝ)*X 1 0+(4353984631/10000000000 : ℝ)*X 1 1+(2176992287/5000000000 : ℝ)*X 1 2+(1957442863/5000000000 : ℝ)*X 2 0+(4353984631/10000000000 : ℝ)*X 2 1+(2176992287/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1826509359/10000000000 : ℝ)*X 0 0+(5072287689/10000000000 : ℝ)*X 0 1+(2721894239/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1307691003/2500000000 : ℝ)*X 1 0+(-1613485271/10000000000 : ℝ)*X 1 1+(5443788389/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2615381973/5000000000 : ℝ)*X 2 0+(5443788399/10000000000 : ℝ)*X 2 1+(-403371337/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1139961517/2500000000 : ℝ)*X 0 0+(4030619489/10000000000 : ℝ)*X 0 1+(4030619491/10000000000 : ℝ)*X 0 2+(1139961517/2500000000 : ℝ)*X 1 0+(4030619489/10000000000 : ℝ)*X 1 1+(4030619491/10000000000 : ℝ)*X 1 2+(1139961517/2500000000 : ℝ)*X 2 0+(4030619489/10000000000 : ℝ)*X 2 1+(4030619491/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-756198669/5000000000 : ℝ)*X 0 0+(555101097/1000000000 : ℝ)*X 0 1+(5195054277/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5402060763/10000000000 : ℝ)*X 1 0+(-1719403433/10000000000 : ℝ)*X 1 1+(1298763321/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2701030217/5000000000 : ℝ)*X 2 0+(5195052961/10000000000 : ℝ)*X 2 1+(-429851079/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((771417711/2000000000 : ℝ)*X 0 0+(273874157/625000000 : ℝ)*X 0 1+(2190993311/5000000000 : ℝ)*X 0 2+(771417711/2000000000 : ℝ)*X 1 0+(273874157/625000000 : ℝ)*X 1 1+(2190993311/5000000000 : ℝ)*X 1 2+(771417711/2000000000 : ℝ)*X 2 0+(273874157/625000000 : ℝ)*X 2 1+(2190993311/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1626_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-32487/50000 : ℝ) ≤ (-8852345231924773236490336278639/13625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (108370091/100000000000000 : ℝ)*(lower0) + (37340653/50000000000000 : ℝ)*(lower3) + (130160667/100000000000000 : ℝ)*(lower4) + (856448671564161/50000000000000 : ℝ)*(major0) + (856448671564161/50000000000000 : ℝ)*(major1) + (856448671564161/50000000000000 : ℝ)*(major2) + (8972963757/100000000000000 : ℝ)*(sp2) + (617804216766293/25000000000000 : ℝ)*(sp4) + (123559348913661/5000000000000 : ℝ)*(sp5) + (617801987292173/25000000000000 : ℝ)*(sp6) + (24405729492267/2500000000000 : ℝ)*(sp7) + (13766819/25000000000000 : ℝ)*(sp12) + (7485964807/25000000000000 : ℝ)*(sp13) + (5698150751/100000000000000 : ℝ)*(sp15) + (97623487784143/10000000000000 : ℝ)*(f.failure) + (77225528816639/3125000000000 : ℝ)*(f.sum) + (2222422268737/545000000000000000000000000 : ℝ)*base66 + (121772914109376213/27250000000000000000000000000000 : ℝ)*base67 + (8195245033123787/27250000000000000000000000000000 : ℝ)*base70 + (31951189947126213/27250000000000000000000000000000 : ℝ)*base71 + (358314585447/136250000000000000000000000 : ℝ)*base73 + (147067293715876213/27250000000000000000000000000000 : ℝ)*base75 + (63239665480123787/27250000000000000000000000000000 : ℝ)*base78 + (95664819010126213/27250000000000000000000000000000 : ℝ)*base79 + (2756708981377/545000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (516127/31250000000000000000 : ℝ)*base90 + (516127/31250000000000000000 : ℝ)*base92 + (516127/31250000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (58367/100000 : ℝ) ≤ (842999495789151309091499396877381/1444250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19642709/50000000000000 : ℝ)*(upper2) + (4206823/50000000000000 : ℝ)*(upper3) + (12007483/6250000000000 : ℝ)*(lower5) + (1799933750225777/100000000000000 : ℝ)*(major0) + (1799933750225777/100000000000000 : ℝ)*(major1) + (1799933750225777/100000000000000 : ℝ)*(major2) + (2554565340935139/100000000000000 : ℝ)*(sp0) + (1277269407664177/50000000000000 : ℝ)*(sp1) + (319319710070001/12500000000000 : ℝ)*(sp2) + (205167077332579/20000000000000 : ℝ)*(sp3) + (6830733177/50000000000000 : ℝ)*(sp6) + (2159053043/50000000000000 : ℝ)*(sp7) + (750136403/12500000000000 : ℝ)*(sp8) + (4065837251/12500000000000 : ℝ)*(sp9) + (1025839704768981/100000000000000 : ℝ)*(f.failure) + (2554571342026363/100000000000000 : ℝ)*(f.sum) + (8075973466003/3610625000000000000000000000 : ℝ)*base65 + (9047381143264559127/2888500000000000000000000000000000 : ℝ)*base68 + (15978543931309440873/2888500000000000000000000000000000 : ℝ)*base69 + (14843788315216940873/2888500000000000000000000000000000 : ℝ)*base71 + (17632736659201/7221250000000000000000000000 : ℝ)*base73 + (6747460742061559127/2888500000000000000000000000000000 : ℝ)*base76 + (5959149166244940873/2888500000000000000000000000000000 : ℝ)*base77 + (12851154146545940873/2888500000000000000000000000000000 : ℝ)*base79 + (112534305752759/28885000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (945109/312500000000000000000 : ℝ)*base90 + (945109/312500000000000000000 : ℝ)*base92 + (945109/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (80747/100000 : ℝ) ≤ (29155769648749551168725514047031/36106250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17617907/100000000000000 : ℝ)*(upper0) + (779711/2500000000000 : ℝ)*(upper1) + (14311657/50000000000000 : ℝ)*(upper2) + (95055048236077/5000000000000 : ℝ)*(major0) + (95055048236077/5000000000000 : ℝ)*(major1) + (95055048236077/5000000000000 : ℝ)*(major2) + (3155867257/12500000000000 : ℝ)*(sp1) + (3989842859/20000000000000 : ℝ)*(sp2) + (2426665609/50000000000000 : ℝ)*(sp3) + (593195957/20000000000000 : ℝ)*(sp4) + (2691784191991679/100000000000000 : ℝ)*(sp8) + (42058779859897/1562500000000 : ℝ)*(sp9) + (2691767208757169/100000000000000 : ℝ)*(sp10) + (1083493276609031/100000000000000 : ℝ)*(sp11) + (4333992519761/400000000000 : ℝ)*(f.failure) + (336473394746433/12500000000000 : ℝ)*(f.sum) + (36947446475183/5777000000000000000000000000 : ℝ)*base65 + (811242249168440573/144425000000000000000000000000000 : ℝ)*base67 + (843871489823740573/144425000000000000000000000000000 : ℝ)*base69 + (1082332917114065573/144425000000000000000000000000000 : ℝ)*base71 + (24378254461601/5777000000000000000000000000 : ℝ)*base73 + (296849462940590573/144425000000000000000000000000000 : ℝ)*base75 + (1781861081527540573/144425000000000000000000000000000 : ℝ)*base77 + (414438615561059427/144425000000000000000000000000000 : ℝ)*base80 + (3216273530929/1444250000000000000000000000 : ℝ)*base82 + (6471/1250000000000000000 : ℝ)*base89 + (6471/1250000000000000000 : ℝ)*base91 + (6471/1250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-87987/100000 : ℝ) ≤ (-317677448904326894731467499293003/361062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6818869/12500000000000 : ℝ)*(lower0) + (4649937/6250000000000 : ℝ)*(upper1) + (67983211/25000000000000 : ℝ)*(lower4) + (971983396570049/50000000000000 : ℝ)*(major0) + (971983396570049/50000000000000 : ℝ)*(major1) + (971983396570049/50000000000000 : ℝ)*(major2) + (241859529/20000000000000 : ℝ)*(sp4) + (104213087877/100000000000000 : ℝ)*(sp5) + (235396722517/100000000000000 : ℝ)*(sp6) + (11785487851/25000000000000 : ℝ)*(sp7) + (2809331663200697/100000000000000 : ℝ)*(sp12) + (561845731882093/20000000000000 : ℝ)*(sp13) + (112363899031033/4000000000000 : ℝ)*(sp14) + (27697039800993/2500000000000 : ℝ)*(sp15) + (276982183497781/25000000000000 : ℝ)*(f.failure) + (1404666436249171/50000000000000 : ℝ)*(f.sum) + (10075896735271/7221250000000000000000000000 : ℝ)*base66 + (2620856290783981001/1444250000000000000000000000000000 : ℝ)*base67 + (8043875734205981001/1444250000000000000000000000000000 : ℝ)*base69 + (204320657509518999/1444250000000000000000000000000000 : ℝ)*base72 + (18846295086643/14442500000000000000000000000 : ℝ)*base73 + (13454669276421731001/1444250000000000000000000000000000 : ℝ)*base75 + (6525346035853481001/1444250000000000000000000000000000 : ℝ)*base77 + (9483839249310481001/1444250000000000000000000000000000 : ℝ)*base79 + (34408567377241/28885000000000000000000000000 : ℝ)*base81 + (85809/78125000000000000000 : ℝ)*base90 + (85809/78125000000000000000 : ℝ)*base92 + (85809/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1626_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5483111/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16313/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1317/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(32487/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58367/100000 : ℝ) else (80747/100000 : ℝ) ≤ X j i ∧ X j i ≤ (87987/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1626_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1626_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5483111/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1643/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10431/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(32487/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58367/100000 : ℝ) else (80747/100000 : ℝ) ≤ X j i ∧ X j i ≤ (87987/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1626_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1626_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1626_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4819/1024 : ℝ) ≤ p) (hpb : p ≤ (4823/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5483111/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1643/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10431/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(32487/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58367/100000 : ℝ) else (80747/100000 : ℝ) ≤ X j i ∧ X j i ≤ (87987/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1626_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
