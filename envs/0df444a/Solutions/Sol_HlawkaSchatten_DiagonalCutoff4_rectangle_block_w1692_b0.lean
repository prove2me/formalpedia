-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1692_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:39:28.83104+00:00
-- url     : https://prove2.me/submissions/d27f5141-dd18-4315-87ab-fa8739679290

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
theorem support_rectangle_w1692_s0_0 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-173913851/1250000000 : ℝ)*x 0 + (5735355241/10000000000 : ℝ)*x 1 + (988040831/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (173913851/1250000000 : ℝ)^5159 ≤ (4268447462567/50000000000000 : ℝ)^4135 := by
    have hnat : (173913851 : ℕ)^5159*50000000000000^4135 ≤ 4268447462567^4135*1250000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173913851 1250000000 4268447462567 50000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5735355241/10000000000 : ℝ)^5159 ≤ (49976944304647/100000000000000 : ℝ)^4135 := by
    have hnat : (5735355241 : ℕ)^5159*100000000000000^4135 ≤ 49976944304647^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5735355241 10000000000 49976944304647 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (988040831/2000000000 : ℝ)^5159 ≤ (41486160753641/100000000000000 : ℝ)^4135 := by
    have hnat : (988040831 : ℕ)^5159*100000000000000^4135 ≤ 41486160753641^4135*2000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      988040831 2000000000 41486160753641 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-173913851/1250000000 : ℝ), (5735355241/10000000000 : ℝ), (988040831/2000000000 : ℝ)] ![(4268447462567/50000000000000 : ℝ), (49976944304647/100000000000000 : ℝ), (41486160753641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-173913851/1250000000 : ℝ)|^5159 ≤ (4268447462567/50000000000000 : ℝ)^4135
        have hw : |(-173913851/1250000000 : ℝ)|=(173913851/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5735355241/10000000000 : ℝ)|^5159 ≤ (49976944304647/100000000000000 : ℝ)^4135
        have hw : |(5735355241/10000000000 : ℝ)|=(5735355241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(988040831/2000000000 : ℝ)|^5159 ≤ (41486160753641/100000000000000 : ℝ)^4135
        have hw : |(988040831/2000000000 : ℝ)|=(988040831/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_s0_1 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2708567979/5000000000 : ℝ)*x 0 + (-364905631/2000000000 : ℝ)*x 1 + (617525661/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2708567979/5000000000 : ℝ)^5159 ≤ (9308290204271/20000000000000 : ℝ)^4135 := by
    have hnat : (2708567979 : ℕ)^5159*20000000000000^4135 ≤ 9308290204271^4135*5000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708567979 5000000000 9308290204271 20000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (364905631/2000000000 : ℝ)^5159 ≤ (11972376336779/100000000000000 : ℝ)^4135 := by
    have hnat : (364905631 : ℕ)^5159*100000000000000^4135 ≤ 11972376336779^4135*2000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      364905631 2000000000 11972376336779 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (617525661/1250000000 : ℝ)^5159 ≤ (8297234524879/20000000000000 : ℝ)^4135 := by
    have hnat : (617525661 : ℕ)^5159*20000000000000^4135 ≤ 8297234524879^4135*1250000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      617525661 1250000000 8297234524879 20000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2708567979/5000000000 : ℝ), (-364905631/2000000000 : ℝ), (617525661/1250000000 : ℝ)] ![(9308290204271/20000000000000 : ℝ), (11972376336779/100000000000000 : ℝ), (8297234524879/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2708567979/5000000000 : ℝ)|^5159 ≤ (9308290204271/20000000000000 : ℝ)^4135
        have hw : |(2708567979/5000000000 : ℝ)|=(2708567979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-364905631/2000000000 : ℝ)|^5159 ≤ (11972376336779/100000000000000 : ℝ)^4135
        have hw : |(-364905631/2000000000 : ℝ)|=(364905631/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(617525661/1250000000 : ℝ)|^5159 ≤ (8297234524879/20000000000000 : ℝ)^4135
        have hw : |(617525661/1250000000 : ℝ)|=(617525661/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_s0_2 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5417138343/10000000000 : ℝ)*x 0 + (4940204269/10000000000 : ℝ)*x 1 + (-1824526337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5417138343/10000000000 : ℝ)^5159 ≤ (46541476586521/100000000000000 : ℝ)^4135 := by
    have hnat : (5417138343 : ℕ)^5159*100000000000000^4135 ≤ 46541476586521^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417138343 10000000000 46541476586521 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4940204269/10000000000 : ℝ)^5159 ≤ (41486161948051/100000000000000 : ℝ)^4135 := by
    have hnat : (4940204269 : ℕ)^5159*100000000000000^4135 ≤ 41486161948051^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4940204269 10000000000 41486161948051 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1824526337/10000000000 : ℝ)^5159 ≤ (5986180726493/50000000000000 : ℝ)^4135 := by
    have hnat : (1824526337 : ℕ)^5159*50000000000000^4135 ≤ 5986180726493^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1824526337 10000000000 5986180726493 50000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5417138343/10000000000 : ℝ), (4940204269/10000000000 : ℝ), (-1824526337/10000000000 : ℝ)] ![(46541476586521/100000000000000 : ℝ), (41486161948051/100000000000000 : ℝ), (5986180726493/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5417138343/10000000000 : ℝ)|^5159 ≤ (46541476586521/100000000000000 : ℝ)^4135
        have hw : |(5417138343/10000000000 : ℝ)|=(5417138343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4940204269/10000000000 : ℝ)|^5159 ≤ (41486161948051/100000000000000 : ℝ)^4135
        have hw : |(4940204269/10000000000 : ℝ)|=(4940204269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1824526337/10000000000 : ℝ)|^5159 ≤ (5986180726493/50000000000000 : ℝ)^4135
        have hw : |(-1824526337/10000000000 : ℝ)|=(1824526337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_s0_3 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2027451023/5000000000 : ℝ)*x 0 + (60971087/200000000 : ℝ)*x 1 + (2629728949/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2027451023/5000000000 : ℝ)^5159 ≤ (16213240118347/50000000000000 : ℝ)^4135 := by
    have hnat : (2027451023 : ℕ)^5159*50000000000000^4135 ≤ 16213240118347^4135*5000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2027451023 5000000000 16213240118347 50000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (60971087/200000000 : ℝ)^5159 ≤ (22716106332311/100000000000000 : ℝ)^4135 := by
    have hnat : (60971087 : ℕ)^5159*100000000000000^4135 ≤ 22716106332311^4135*200000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60971087 200000000 22716106332311 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2629728949/5000000000 : ℝ)^5159 ≤ (22428706709343/50000000000000 : ℝ)^4135 := by
    have hnat : (2629728949 : ℕ)^5159*50000000000000^4135 ≤ 22428706709343^4135*5000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629728949 5000000000 22428706709343 50000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2027451023/5000000000 : ℝ), (60971087/200000000 : ℝ), (2629728949/5000000000 : ℝ)] ![(16213240118347/50000000000000 : ℝ), (22716106332311/100000000000000 : ℝ), (22428706709343/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2027451023/5000000000 : ℝ)|^5159 ≤ (16213240118347/50000000000000 : ℝ)^4135
        have hw : |(2027451023/5000000000 : ℝ)|=(2027451023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(60971087/200000000 : ℝ)|^5159 ≤ (22716106332311/100000000000000 : ℝ)^4135
        have hw : |(60971087/200000000 : ℝ)|=(60971087/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2629728949/5000000000 : ℝ)|^5159 ≤ (22428706709343/50000000000000 : ℝ)^4135
        have hw : |(2629728949/5000000000 : ℝ)|=(2629728949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_s0_4 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-348320997/2500000000 : ℝ)*x 0 + (4960122523/10000000000 : ℝ)*x 1 + (2857375593/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (348320997/2500000000 : ℝ)^5159 ≤ (1069000373253/12500000000000 : ℝ)^4135 := by
    have hnat : (348320997 : ℕ)^5159*12500000000000^4135 ≤ 1069000373253^4135*2500000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      348320997 2500000000 1069000373253 12500000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4960122523/10000000000 : ℝ)^5159 ≤ (41694955062289/100000000000000 : ℝ)^4135 := by
    have hnat : (4960122523 : ℕ)^5159*100000000000000^4135 ≤ 41694955062289^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4960122523 10000000000 41694955062289 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2857375593/5000000000 : ℝ)^5159 ≤ (49753041935317/100000000000000 : ℝ)^4135 := by
    have hnat : (2857375593 : ℕ)^5159*100000000000000^4135 ≤ 49753041935317^4135*5000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2857375593 5000000000 49753041935317 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-348320997/2500000000 : ℝ), (4960122523/10000000000 : ℝ), (2857375593/5000000000 : ℝ)] ![(1069000373253/12500000000000 : ℝ), (41694955062289/100000000000000 : ℝ), (49753041935317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-348320997/2500000000 : ℝ)|^5159 ≤ (1069000373253/12500000000000 : ℝ)^4135
        have hw : |(-348320997/2500000000 : ℝ)|=(348320997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4960122523/10000000000 : ℝ)|^5159 ≤ (41694955062289/100000000000000 : ℝ)^4135
        have hw : |(4960122523/10000000000 : ℝ)|=(4960122523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2857375593/5000000000 : ℝ)|^5159 ≤ (49753041935317/100000000000000 : ℝ)^4135
        have hw : |(2857375593/5000000000 : ℝ)|=(2857375593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_s0_5 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5201186241/10000000000 : ℝ)*x 0 + (-16405959/156250000 : ℝ)*x 1 + (5714751179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5201186241/10000000000 : ℝ)^5159 ≤ (5529774572317/12500000000000 : ℝ)^4135 := by
    have hnat : (5201186241 : ℕ)^5159*12500000000000^4135 ≤ 5529774572317^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5201186241 10000000000 5529774572317 12500000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16405959/156250000 : ℝ)^5159 ≤ (1201752311573/20000000000000 : ℝ)^4135 := by
    have hnat : (16405959 : ℕ)^5159*20000000000000^4135 ≤ 1201752311573^4135*156250000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16405959 156250000 1201752311573 20000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5714751179/10000000000 : ℝ)^5159 ≤ (49753041859283/100000000000000 : ℝ)^4135 := by
    have hnat : (5714751179 : ℕ)^5159*100000000000000^4135 ≤ 49753041859283^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5714751179 10000000000 49753041859283 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5201186241/10000000000 : ℝ), (-16405959/156250000 : ℝ), (5714751179/10000000000 : ℝ)] ![(5529774572317/12500000000000 : ℝ), (1201752311573/20000000000000 : ℝ), (49753041859283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5201186241/10000000000 : ℝ)|^5159 ≤ (5529774572317/12500000000000 : ℝ)^4135
        have hw : |(5201186241/10000000000 : ℝ)|=(5201186241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-16405959/156250000 : ℝ)|^5159 ≤ (1201752311573/20000000000000 : ℝ)^4135
        have hw : |(-16405959/156250000 : ℝ)|=(16405959/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5714751179/10000000000 : ℝ)|^5159 ≤ (49753041859283/100000000000000 : ℝ)^4135
        have hw : |(5714751179/10000000000 : ℝ)|=(5714751179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_s0_6 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1300296569/2500000000 : ℝ)*x 0 + (5714751257/10000000000 : ℝ)*x 1 + (-262495301/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1300296569/2500000000 : ℝ)^5159 ≤ (8847639389989/20000000000000 : ℝ)^4135 := by
    have hnat : (1300296569 : ℕ)^5159*20000000000000^4135 ≤ 8847639389989^4135*2500000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1300296569 2500000000 8847639389989 20000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5714751257/10000000000 : ℝ)^5159 ≤ (12438260676631/25000000000000 : ℝ)^4135 := by
    have hnat : (5714751257 : ℕ)^5159*25000000000000^4135 ≤ 12438260676631^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5714751257 10000000000 12438260676631 25000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262495301/2500000000 : ℝ)^5159 ≤ (6008760329799/100000000000000 : ℝ)^4135 := by
    have hnat : (262495301 : ℕ)^5159*100000000000000^4135 ≤ 6008760329799^4135*2500000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262495301 2500000000 6008760329799 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1300296569/2500000000 : ℝ), (5714751257/10000000000 : ℝ), (-262495301/2500000000 : ℝ)] ![(8847639389989/20000000000000 : ℝ), (12438260676631/25000000000000 : ℝ), (6008760329799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1300296569/2500000000 : ℝ)|^5159 ≤ (8847639389989/20000000000000 : ℝ)^4135
        have hw : |(1300296569/2500000000 : ℝ)|=(1300296569/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5714751257/10000000000 : ℝ)|^5159 ≤ (12438260676631/25000000000000 : ℝ)^4135
        have hw : |(5714751257/10000000000 : ℝ)|=(5714751257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-262495301/2500000000 : ℝ)|^5159 ≤ (6008760329799/100000000000000 : ℝ)^4135
        have hw : |(-262495301/2500000000 : ℝ)|=(262495301/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_s0_7 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4060388727/10000000000 : ℝ)*x 0 + (5204073349/10000000000 : ℝ)*x 1 + (194115163/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4060388727/10000000000 : ℝ)^5159 ≤ (32481231216979/100000000000000 : ℝ)^4135 := by
    have hnat : (4060388727 : ℕ)^5159*100000000000000^4135 ≤ 32481231216979^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4060388727 10000000000 32481231216979 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5204073349/10000000000 : ℝ)^5159 ≤ (44268835812131/100000000000000 : ℝ)^4135 := by
    have hnat : (5204073349 : ℕ)^5159*100000000000000^4135 ≤ 44268835812131^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5204073349 10000000000 44268835812131 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (194115163/625000000 : ℝ)^5159 ≤ (11624966476807/50000000000000 : ℝ)^4135 := by
    have hnat : (194115163 : ℕ)^5159*50000000000000^4135 ≤ 11624966476807^4135*625000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194115163 625000000 11624966476807 50000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4060388727/10000000000 : ℝ), (5204073349/10000000000 : ℝ), (194115163/625000000 : ℝ)] ![(32481231216979/100000000000000 : ℝ), (44268835812131/100000000000000 : ℝ), (11624966476807/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4060388727/10000000000 : ℝ)|^5159 ≤ (32481231216979/100000000000000 : ℝ)^4135
        have hw : |(4060388727/10000000000 : ℝ)|=(4060388727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5204073349/10000000000 : ℝ)|^5159 ≤ (44268835812131/100000000000000 : ℝ)^4135
        have hw : |(5204073349/10000000000 : ℝ)|=(5204073349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(194115163/625000000 : ℝ)|^5159 ≤ (11624966476807/50000000000000 : ℝ)^4135
        have hw : |(194115163/625000000 : ℝ)|=(194115163/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1692_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94512017/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (5497/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (22563/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (5151/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5151 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5151*1^1024 ≤ 0^1024*1^5151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5151 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5151 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5151/1024 : ℝ) ≤ (248996334202081059/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5151 ≤ (248996334202081059/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5151*25000000000000000000^1024 ≤ 248996334202081059^1024*5^5151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 248996334202081059 25000000000000000000 5151 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (248996334202081059/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5151 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5151/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5151 := by
      have hnat : (1 : ℕ)^1024*1^5151 ≤ 1^5151*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5151 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25248996334202081059/25000000000000000000 : ℝ) ≤ (10019721294102633/10000000000000000 : ℝ) ^ (5151/1024 : ℝ) := by
    have hpowers : (25248996334202081059/25000000000000000000 : ℝ)^1024 ≤ (10019721294102633/10000000000000000 : ℝ)^5151 := by
      have hnat : (25248996334202081059 : ℕ)^1024*10000000000000000^5151 ≤ 10019721294102633^5151*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25248996334202081059 25000000000000000000 10019721294102633 10000000000000000 1024 5151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10019721294102633/10000000000000000 : ℝ)) (X := (25248996334202081059/25000000000000000000 : ℝ)) (by norm_num) 5151 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12748996334202081059/12500000000000000000 : ℝ) ≤ (5019721294102633/5000000000000000 : ℝ) ^ (5151/1024 : ℝ) := by
    have hpowers : (12748996334202081059/12500000000000000000 : ℝ)^1024 ≤ (5019721294102633/5000000000000000 : ℝ)^5151 := by
      have hnat : (12748996334202081059 : ℕ)^1024*5000000000000000^5151 ≤ 5019721294102633^5151*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12748996334202081059 12500000000000000000 5019721294102633 5000000000000000 1024 5151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5019721294102633/5000000000000000 : ℝ)) (X := (12748996334202081059/12500000000000000000 : ℝ)) (by norm_num) 5151 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(19721294102633/4000000000000000 : ℝ)*(0 : ℝ))^(5151/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(19721294102633/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(248996334202081059/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(19721294102633/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5151/1024 : ℝ) := by
    rw [show (1 : ℝ)+(19721294102633/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10019721294102633/10000000000000000 : ℝ) by norm_num, show 1+(248996334202081059/25000000000000000000 : ℝ)+(0 : ℝ)=(25248996334202081059/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(248996334202081059/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(19721294102633/4000000000000000 : ℝ)*(2/5 : ℝ))^(5151/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(19721294102633/4000000000000000 : ℝ)*(2/5 : ℝ)=(5019721294102633/5000000000000000 : ℝ) by norm_num, show 1+2*(248996334202081059/25000000000000000000 : ℝ)=(12748996334202081059/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(19721294102633/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5151/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (19721294102633/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(19721294102633/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5151/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (19721294102633/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(19721294102633/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5151/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (19721294102633/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-173913851/1250000000 : ℝ)*X 0 0+(5735355241/10000000000 : ℝ)*X 0 1+(988040831/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2708567979/5000000000 : ℝ)*X 1 0+(-364905631/2000000000 : ℝ)*X 1 1+(617525661/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5417138343/10000000000 : ℝ)*X 2 0+(4940204269/10000000000 : ℝ)*X 2 1+(-1824526337/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2027451023/5000000000 : ℝ)*X 0 0+(60971087/200000000 : ℝ)*X 0 1+(2629728949/5000000000 : ℝ)*X 0 2+(2027451023/5000000000 : ℝ)*X 1 0+(60971087/200000000 : ℝ)*X 1 1+(2629728949/5000000000 : ℝ)*X 1 2+(2027451023/5000000000 : ℝ)*X 2 0+(60971087/200000000 : ℝ)*X 2 1+(2629728949/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-348320997/2500000000 : ℝ)*X 0 0+(4960122523/10000000000 : ℝ)*X 0 1+(2857375593/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5201186241/10000000000 : ℝ)*X 1 0+(-16405959/156250000 : ℝ)*X 1 1+(5714751179/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1300296569/2500000000 : ℝ)*X 2 0+(5714751257/10000000000 : ℝ)*X 2 1+(-262495301/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4060388727/10000000000 : ℝ)*X 0 0+(5204073349/10000000000 : ℝ)*X 0 1+(194115163/625000000 : ℝ)*X 0 2+(4060388727/10000000000 : ℝ)*X 1 0+(5204073349/10000000000 : ℝ)*X 1 1+(194115163/625000000 : ℝ)*X 1 2+(4060388727/10000000000 : ℝ)*X 2 0+(5204073349/10000000000 : ℝ)*X 2 1+(194115163/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6527752391286776241/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (113850443/12500000000000 : ℝ)*(base19) + (644282949/50000000000000 : ℝ)*(base23) + (6899543/4000000000000 : ℝ)*(base24) + (933559/50000000000000 : ℝ)*(upper4) + (225108497/100000000000000 : ℝ)*(upper5) + (854971686845781/100000000000000 : ℝ)*(major0) + (854971686845781/100000000000000 : ℝ)*(major1) + (854971686845781/100000000000000 : ℝ)*(major2) + (251525382405511/20000000000000 : ℝ)*(sp0) + (1257633790782071/100000000000000 : ℝ)*(sp1) + (628816620265571/50000000000000 : ℝ)*(sp2) + (90461241567543/20000000000000 : ℝ)*(sp3) + (389477903/5000000000000 : ℝ)*(sp4) + (2246676477/100000000000000 : ℝ)*(sp7) + (28269278407137/6250000000000 : ℝ)*(f.failure) + (78602168849101/6250000000000 : ℝ)*(f.sum) + (342439732758627/200000000000000000000000000000 : ℝ)*base66 + (2262467513841373/400000000000000000000000000000 : ℝ)*base67 + (3167574548641373/400000000000000000000000000000 : ℝ)*base69 + (2700037182241373/400000000000000000000000000000 : ℝ)*base71 + (97005886558627/200000000000000000000000000000 : ℝ)*base74 + (1438198043441373/400000000000000000000000000000 : ℝ)*base75 + (596849707041373/400000000000000000000000000000 : ℝ)*base77 + (2099269888641373/400000000000000000000000000000 : ℝ)*base79 + (884956989358627/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (559671/312500000000000000000 : ℝ)*base90 + (559671/312500000000000000000 : ℝ)*base92 + (559671/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1178590727620744377/250000000000000000000000 : ℝ) := by norm_num
    linear_combination (68069347/6250000000000 : ℝ)*(base19) + (557061443/50000000000000 : ℝ)*(base23) + (1119003/20000000000000 : ℝ)*(base32) + (88304451/50000000000000 : ℝ)*(upper3) + (153986443/100000000000000 : ℝ)*(upper5) + (900873559844449/100000000000000 : ℝ)*(major0) + (900873559844449/100000000000000 : ℝ)*(major1) + (900873559844449/100000000000000 : ℝ)*(major2) + (933366363/25000000000000 : ℝ)*(sp1) + (2060548553/50000000000000 : ℝ)*(sp2) + (1325154890741391/100000000000000 : ℝ)*(sp4) + (331287517041597/25000000000000 : ℝ)*(sp5) + (1325149655521399/100000000000000 : ℝ)*(sp6) + (238296033103527/50000000000000 : ℝ)*(sp7) + (47659207180207/10000000000000 : ℝ)*(f.failure) + (1325154890741391/100000000000000 : ℝ)*(f.sum) + (292997931334217/200000000000000000000000000000 : ℝ)*base65 + (5167203185734217/400000000000000000000000000000 : ℝ)*base67 + (830894101865783/400000000000000000000000000000 : ℝ)*base70 + (492403791465783/400000000000000000000000000000 : ℝ)*base72 + (1834221941734217/200000000000000000000000000000 : ℝ)*base73 + (867030862665783/400000000000000000000000000000 : ℝ)*base76 + (51549774665783/400000000000000000000000000000 : ℝ)*base78 + (5054025360134217/400000000000000000000000000000 : ℝ)*base79 + (523353821465783/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1047519/500000000000000000000 : ℝ)*base89 + (1047519/500000000000000000000 : ℝ)*base91 + (1047519/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1692_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94512017/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5497/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (22563/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1692_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1692_s1_0 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-147449539/1000000000 : ℝ)*x 0 + (2751691117/5000000000 : ℝ)*x 1 + (1279421813/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (147449539/1000000000 : ℝ)^5159 ≤ (4589174277109/50000000000000 : ℝ)^4135 := by
    have hnat : (147449539 : ℕ)^5159*50000000000000^4135 ≤ 4589174277109^4135*1000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147449539 1000000000 4589174277109 50000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2751691117/5000000000 : ℝ)^5159 ≤ (47467752735313/100000000000000 : ℝ)^4135 := by
    have hnat : (2751691117 : ℕ)^5159*100000000000000^4135 ≤ 47467752735313^4135*5000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2751691117 5000000000 47467752735313 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1279421813/2500000000 : ℝ)^5159 ≤ (8670779740453/20000000000000 : ℝ)^4135 := by
    have hnat : (1279421813 : ℕ)^5159*20000000000000^4135 ≤ 8670779740453^4135*2500000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1279421813 2500000000 8670779740453 20000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-147449539/1000000000 : ℝ), (2751691117/5000000000 : ℝ), (1279421813/2500000000 : ℝ)] ![(4589174277109/50000000000000 : ℝ), (47467752735313/100000000000000 : ℝ), (8670779740453/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-147449539/1000000000 : ℝ)|^5159 ≤ (4589174277109/50000000000000 : ℝ)^4135
        have hw : |(-147449539/1000000000 : ℝ)|=(147449539/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2751691117/5000000000 : ℝ)|^5159 ≤ (47467752735313/100000000000000 : ℝ)^4135
        have hw : |(2751691117/5000000000 : ℝ)|=(2751691117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1279421813/2500000000 : ℝ)|^5159 ≤ (8670779740453/20000000000000 : ℝ)^4135
        have hw : |(1279421813/2500000000 : ℝ)|=(1279421813/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_s1_1 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5355336863/10000000000 : ℝ)*x 0 + (-837828001/5000000000 : ℝ)*x 1 + (5117686893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355336863/10000000000 : ℝ)^5159 ≤ (45879955899631/100000000000000 : ℝ)^4135 := by
    have hnat : (5355336863 : ℕ)^5159*100000000000000^4135 ≤ 45879955899631^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355336863 10000000000 45879955899631 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (837828001/5000000000 : ℝ)^5159 ≤ (1076614917927/10000000000000 : ℝ)^4135 := by
    have hnat : (837828001 : ℕ)^5159*10000000000000^4135 ≤ 1076614917927^4135*5000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      837828001 5000000000 1076614917927 10000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5117686893/10000000000 : ℝ)^5159 ≤ (21676947453951/50000000000000 : ℝ)^4135 := by
    have hnat : (5117686893 : ℕ)^5159*50000000000000^4135 ≤ 21676947453951^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5117686893 10000000000 21676947453951 50000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355336863/10000000000 : ℝ), (-837828001/5000000000 : ℝ), (5117686893/10000000000 : ℝ)] ![(45879955899631/100000000000000 : ℝ), (1076614917927/10000000000000 : ℝ), (21676947453951/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355336863/10000000000 : ℝ)|^5159 ≤ (45879955899631/100000000000000 : ℝ)^4135
        have hw : |(5355336863/10000000000 : ℝ)|=(5355336863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-837828001/5000000000 : ℝ)|^5159 ≤ (1076614917927/10000000000000 : ℝ)^4135
        have hw : |(-837828001/5000000000 : ℝ)|=(837828001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5117686893/10000000000 : ℝ)|^5159 ≤ (21676947453951/50000000000000 : ℝ)^4135
        have hw : |(5117686893/10000000000 : ℝ)|=(5117686893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_s1_2 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5355335987/10000000000 : ℝ)*x 0 + (5117687653/10000000000 : ℝ)*x 1 + (-1675656167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355335987/10000000000 : ℝ)^5159 ≤ (22939973268151/50000000000000 : ℝ)^4135 := by
    have hnat : (5355335987 : ℕ)^5159*50000000000000^4135 ≤ 22939973268151^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355335987 10000000000 22939973268151 50000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5117687653/10000000000 : ℝ)^5159 ≤ (43353902940537/100000000000000 : ℝ)^4135 := by
    have hnat : (5117687653 : ℕ)^5159*100000000000000^4135 ≤ 43353902940537^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5117687653 10000000000 43353902940537 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1675656167/10000000000 : ℝ)^5159 ≤ (10766150501933/100000000000000 : ℝ)^4135 := by
    have hnat : (1675656167 : ℕ)^5159*100000000000000^4135 ≤ 10766150501933^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1675656167 10000000000 10766150501933 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355335987/10000000000 : ℝ), (5117687653/10000000000 : ℝ), (-1675656167/10000000000 : ℝ)] ![(22939973268151/50000000000000 : ℝ), (43353902940537/100000000000000 : ℝ), (10766150501933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355335987/10000000000 : ℝ)|^5159 ≤ (22939973268151/50000000000000 : ℝ)^4135
        have hw : |(5355335987/10000000000 : ℝ)|=(5355335987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5117687653/10000000000 : ℝ)|^5159 ≤ (43353902940537/100000000000000 : ℝ)^4135
        have hw : |(5117687653/10000000000 : ℝ)|=(5117687653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1675656167/10000000000 : ℝ)|^5159 ≤ (10766150501933/100000000000000 : ℝ)^4135
        have hw : |(-1675656167/10000000000 : ℝ)|=(1675656167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_s1_3 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (164975857/400000000 : ℝ)*x 0 + (3611303147/10000000000 : ℝ)*x 1 + (585465061/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (164975857/400000000 : ℝ)^5159 ≤ (33121305894603/100000000000000 : ℝ)^4135 := by
    have hnat : (164975857 : ℕ)^5159*100000000000000^4135 ≤ 33121305894603^4135*400000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164975857 400000000 33121305894603 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3611303147/10000000000 : ℝ)^5159 ≤ (28062278218199/100000000000000 : ℝ)^4135 := by
    have hnat : (3611303147 : ℕ)^5159*100000000000000^4135 ≤ 28062278218199^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3611303147 10000000000 28062278218199 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (585465061/1250000000 : ℝ)^5159 ≤ (9704103969827/25000000000000 : ℝ)^4135 := by
    have hnat : (585465061 : ℕ)^5159*25000000000000^4135 ≤ 9704103969827^4135*1250000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      585465061 1250000000 9704103969827 25000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(164975857/400000000 : ℝ), (3611303147/10000000000 : ℝ), (585465061/1250000000 : ℝ)] ![(33121305894603/100000000000000 : ℝ), (28062278218199/100000000000000 : ℝ), (9704103969827/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(164975857/400000000 : ℝ)|^5159 ≤ (33121305894603/100000000000000 : ℝ)^4135
        have hw : |(164975857/400000000 : ℝ)|=(164975857/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3611303147/10000000000 : ℝ)|^5159 ≤ (28062278218199/100000000000000 : ℝ)^4135
        have hw : |(3611303147/10000000000 : ℝ)|=(3611303147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(585465061/1250000000 : ℝ)|^5159 ≤ (9704103969827/25000000000000 : ℝ)^4135
        have hw : |(585465061/1250000000 : ℝ)|=(585465061/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_s1_4 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-737358749/5000000000 : ℝ)*x 0 + (1280591819/2500000000 : ℝ)*x 1 + (274931217/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (737358749/5000000000 : ℝ)^5159 ≤ (36720294127/400000000000 : ℝ)^4135 := by
    have hnat : (737358749 : ℕ)^5159*400000000000^4135 ≤ 36720294127^4135*5000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      737358749 5000000000 36720294127 400000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1280591819/2500000000 : ℝ)^5159 ≤ (43403368675177/100000000000000 : ℝ)^4135 := by
    have hnat : (1280591819 : ℕ)^5159*100000000000000^4135 ≤ 43403368675177^4135*2500000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1280591819 2500000000 43403368675177 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (274931217/500000000 : ℝ)^5159 ≤ (23708278884173/50000000000000 : ℝ)^4135 := by
    have hnat : (274931217 : ℕ)^5159*50000000000000^4135 ≤ 23708278884173^4135*500000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274931217 500000000 23708278884173 50000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-737358749/5000000000 : ℝ), (1280591819/2500000000 : ℝ), (274931217/500000000 : ℝ)] ![(36720294127/400000000000 : ℝ), (43403368675177/100000000000000 : ℝ), (23708278884173/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-737358749/5000000000 : ℝ)|^5159 ≤ (36720294127/400000000000 : ℝ)^4135
        have hw : |(-737358749/5000000000 : ℝ)|=(737358749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1280591819/2500000000 : ℝ)|^5159 ≤ (43403368675177/100000000000000 : ℝ)^4135
        have hw : |(1280591819/2500000000 : ℝ)|=(1280591819/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(274931217/500000000 : ℝ)|^5159 ≤ (23708278884173/50000000000000 : ℝ)^4135
        have hw : |(274931217/500000000 : ℝ)|=(274931217/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_s1_5 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2626067977/5000000000 : ℝ)*x 0 + (-1294719803/10000000000 : ℝ)*x 1 + (5498624531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2626067977/5000000000 : ℝ)^5159 ≤ (8955902780281/20000000000000 : ℝ)^4135 := by
    have hnat : (2626067977 : ℕ)^5159*20000000000000^4135 ≤ 8955902780281^4135*5000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626067977 5000000000 8955902780281 20000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1294719803/10000000000 : ℝ)^5159 ≤ (1950981564639/25000000000000 : ℝ)^4135 := by
    have hnat : (1294719803 : ℕ)^5159*25000000000000^4135 ≤ 1950981564639^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294719803 10000000000 1950981564639 25000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5498624531/10000000000 : ℝ)^5159 ≤ (47416559823287/100000000000000 : ℝ)^4135 := by
    have hnat : (5498624531 : ℕ)^5159*100000000000000^4135 ≤ 47416559823287^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5498624531 10000000000 47416559823287 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2626067977/5000000000 : ℝ), (-1294719803/10000000000 : ℝ), (5498624531/10000000000 : ℝ)] ![(8955902780281/20000000000000 : ℝ), (1950981564639/25000000000000 : ℝ), (47416559823287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2626067977/5000000000 : ℝ)|^5159 ≤ (8955902780281/20000000000000 : ℝ)^4135
        have hw : |(2626067977/5000000000 : ℝ)|=(2626067977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1294719803/10000000000 : ℝ)|^5159 ≤ (1950981564639/25000000000000 : ℝ)^4135
        have hw : |(-1294719803/10000000000 : ℝ)|=(1294719803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5498624531/10000000000 : ℝ)|^5159 ≤ (47416559823287/100000000000000 : ℝ)^4135
        have hw : |(5498624531/10000000000 : ℝ)|=(5498624531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_s1_6 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5252136309/10000000000 : ℝ)*x 0 + (274931239/500000000 : ℝ)*x 1 + (-40459967/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5252136309/10000000000 : ℝ)^5159 ≤ (8955903535533/20000000000000 : ℝ)^4135 := by
    have hnat : (5252136309 : ℕ)^5159*20000000000000^4135 ≤ 8955903535533^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252136309 10000000000 8955903535533 20000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (274931239/500000000 : ℝ)^5159 ≤ (47416562502241/100000000000000 : ℝ)^4135 := by
    have hnat : (274931239 : ℕ)^5159*100000000000000^4135 ≤ 47416562502241^4135*500000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274931239 500000000 47416562502241 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40459967/312500000 : ℝ)^5159 ≤ (3901959899367/50000000000000 : ℝ)^4135 := by
    have hnat : (40459967 : ℕ)^5159*50000000000000^4135 ≤ 3901959899367^4135*312500000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40459967 312500000 3901959899367 50000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5252136309/10000000000 : ℝ), (274931239/500000000 : ℝ), (-40459967/312500000 : ℝ)] ![(8955903535533/20000000000000 : ℝ), (47416562502241/100000000000000 : ℝ), (3901959899367/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5252136309/10000000000 : ℝ)|^5159 ≤ (8955903535533/20000000000000 : ℝ)^4135
        have hw : |(5252136309/10000000000 : ℝ)|=(5252136309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(274931239/500000000 : ℝ)|^5159 ≤ (47416562502241/100000000000000 : ℝ)^4135
        have hw : |(274931239/500000000 : ℝ)|=(274931239/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-40459967/312500000 : ℝ)|^5159 ≤ (3901959899367/50000000000000 : ℝ)^4135
        have hw : |(-40459967/312500000 : ℝ)|=(40459967/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_s1_7 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (412501457/1000000000 : ℝ)*x 0 + (2335353763/5000000000 : ℝ)*x 1 + (1812266007/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (412501457/1000000000 : ℝ)^5159 ≤ (258808588947/781250000000 : ℝ)^4135 := by
    have hnat : (412501457 : ℕ)^5159*781250000000^4135 ≤ 258808588947^4135*1000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412501457 1000000000 258808588947 781250000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2335353763/5000000000 : ℝ)^5159 ≤ (2417619378181/6250000000000 : ℝ)^4135 := by
    have hnat : (2335353763 : ℕ)^5159*6250000000000^4135 ≤ 2417619378181^4135*5000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2335353763 5000000000 2417619378181 6250000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1812266007/5000000000 : ℝ)^5159 ≤ (14095295276203/50000000000000 : ℝ)^4135 := by
    have hnat : (1812266007 : ℕ)^5159*50000000000000^4135 ≤ 14095295276203^4135*5000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1812266007 5000000000 14095295276203 50000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(412501457/1000000000 : ℝ), (2335353763/5000000000 : ℝ), (1812266007/5000000000 : ℝ)] ![(258808588947/781250000000 : ℝ), (2417619378181/6250000000000 : ℝ), (14095295276203/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(412501457/1000000000 : ℝ)|^5159 ≤ (258808588947/781250000000 : ℝ)^4135
        have hw : |(412501457/1000000000 : ℝ)|=(412501457/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2335353763/5000000000 : ℝ)|^5159 ≤ (2417619378181/6250000000000 : ℝ)^4135
        have hw : |(2335353763/5000000000 : ℝ)|=(2335353763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1812266007/5000000000 : ℝ)|^5159 ≤ (14095295276203/50000000000000 : ℝ)^4135
        have hw : |(1812266007/5000000000 : ℝ)|=(1812266007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1692_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94512017/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (22563/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5497/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (473/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2209/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (22563/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5497/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (22563/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5497/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (22563/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5497/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (22563/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5497/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (22563/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5497/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (22563/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5497/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5497/100000 : ℝ) ^ (5151/1024 : ℝ) ≤ (9194284874237/20000000000000000000 : ℝ) := by
    have hpowers : (5497/100000 : ℝ)^5151 ≤ (9194284874237/20000000000000000000 : ℝ)^1024 := by
      have hnat : (5497 : ℕ)^5151*20000000000000000000^1024 ≤ 9194284874237^1024*100000^5151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5497 100000 9194284874237 20000000000000000000 5151 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5497/100000 : ℝ)) (X := (9194284874237/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5151 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (22563/100000 : ℝ) ^ (5151/1024 : ℝ) ≤ (11179935870821577/20000000000000000000 : ℝ) := by
    have hpowers : (22563/100000 : ℝ)^5151 ≤ (11179935870821577/20000000000000000000 : ℝ)^1024 := by
      have hnat : (22563 : ℕ)^5151*20000000000000000000^1024 ≤ 11179935870821577^1024*100000^5151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22563 100000 11179935870821577 20000000000000000000 5151 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (22563/100000 : ℝ)) (X := (11179935870821577/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5151 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000009194284874237/10000000000000000000 : ℝ) ≤ (10000001827789603/10000000000000000 : ℝ) ^ (5151/1024 : ℝ) := by
    have hpowers : (10000009194284874237/10000000000000000000 : ℝ)^1024 ≤ (10000001827789603/10000000000000000 : ℝ)^5151 := by
      have hnat : (10000009194284874237 : ℕ)^1024*10000000000000000^5151 ≤ 10000001827789603^5151*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000009194284874237 10000000000000000000 10000001827789603 10000000000000000 1024 5151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001827789603/10000000000000000 : ℝ)) (X := (10000009194284874237/10000000000000000000 : ℝ)) (by norm_num) 5151 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10005594565077847907/10000000000000000000 : ℝ) ≤ (10001111929941453/10000000000000000 : ℝ) ^ (5151/1024 : ℝ) := by
    have hpowers : (10005594565077847907/10000000000000000000 : ℝ)^1024 ≤ (10001111929941453/10000000000000000 : ℝ)^5151 := by
      have hnat : (10005594565077847907 : ℕ)^1024*10000000000000000^5151 ≤ 10001111929941453^5151*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005594565077847907 10000000000000000000 10001111929941453 10000000000000000 1024 5151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001111929941453/10000000000000000 : ℝ)) (X := (10005594565077847907/10000000000000000000 : ℝ)) (by norm_num) 5151 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10011179935870821577/10000000000000000000 : ℝ) ≤ (10002222032093303/10000000000000000 : ℝ) ^ (5151/1024 : ℝ) := by
    have hpowers : (10011179935870821577/10000000000000000000 : ℝ)^1024 ≤ (10002222032093303/10000000000000000 : ℝ)^5151 := by
      have hnat : (10011179935870821577 : ℕ)^1024*10000000000000000^5151 ≤ 10002222032093303^5151*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10011179935870821577 10000000000000000000 10002222032093303 10000000000000000 1024 5151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002222032093303/10000000000000000 : ℝ)) (X := (10011179935870821577/10000000000000000000 : ℝ)) (by norm_num) 5151 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9194284874237/20000000000000000000 : ℝ) ≤ ((3709735363695650563/3710000000000000000 : ℝ)+2*(965306219/1484000000000 : ℝ)*(5497/100000 : ℝ))^(5151/1024 : ℝ) := by
    rw [show (3709735363695650563/3710000000000000000 : ℝ)+2*(965306219/1484000000000 : ℝ)*(5497/100000 : ℝ)=(10000001827789603/10000000000000000 : ℝ) by norm_num, show 1+2*(9194284874237/20000000000000000000 : ℝ)=(10000009194284874237/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11179935870821577/20000000000000000000 : ℝ)+(9194284874237/20000000000000000000 : ℝ) ≤ ((3709735363695650563/3710000000000000000 : ℝ)+(965306219/1484000000000 : ℝ)*((22563/100000 : ℝ)+(5497/100000 : ℝ)))^(5151/1024 : ℝ) := by
    rw [show (3709735363695650563/3710000000000000000 : ℝ)+(965306219/1484000000000 : ℝ)*((22563/100000 : ℝ)+(5497/100000 : ℝ))=(10001111929941453/10000000000000000 : ℝ) by norm_num, show 1+(11179935870821577/20000000000000000000 : ℝ)+(9194284874237/20000000000000000000 : ℝ)=(10005594565077847907/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11179935870821577/20000000000000000000 : ℝ) ≤ ((3709735363695650563/3710000000000000000 : ℝ)+2*(965306219/1484000000000 : ℝ)*(22563/100000 : ℝ))^(5151/1024 : ℝ) := by
    rw [show (3709735363695650563/3710000000000000000 : ℝ)+2*(965306219/1484000000000 : ℝ)*(22563/100000 : ℝ)=(10002222032093303/10000000000000000 : ℝ) by norm_num, show 1+2*(11179935870821577/20000000000000000000 : ℝ)=(10011179935870821577/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3709735363695650563/3710000000000000000 : ℝ)*(X 1 0+X 2 0)+(965306219/1484000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5151/1024 : ℝ)) (lo := (5497/100000 : ℝ)) (hi := (22563/100000 : ℝ)) (c := (3709735363695650563/3710000000000000000 : ℝ)) (alpha := (965306219/1484000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3709735363695650563/3710000000000000000 : ℝ)*(X 0 1+X 2 1)+(965306219/1484000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5151/1024 : ℝ)) (lo := (5497/100000 : ℝ)) (hi := (22563/100000 : ℝ)) (c := (3709735363695650563/3710000000000000000 : ℝ)) (alpha := (965306219/1484000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3709735363695650563/3710000000000000000 : ℝ)*(X 0 2+X 1 2)+(965306219/1484000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5151/1024 : ℝ)) (lo := (5497/100000 : ℝ)) (hi := (22563/100000 : ℝ)) (c := (3709735363695650563/3710000000000000000 : ℝ)) (alpha := (965306219/1484000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-147449539/1000000000 : ℝ)*X 0 0+(2751691117/5000000000 : ℝ)*X 0 1+(1279421813/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5355336863/10000000000 : ℝ)*X 1 0+(-837828001/5000000000 : ℝ)*X 1 1+(5117686893/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5355335987/10000000000 : ℝ)*X 2 0+(5117687653/10000000000 : ℝ)*X 2 1+(-1675656167/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((164975857/400000000 : ℝ)*X 0 0+(3611303147/10000000000 : ℝ)*X 0 1+(585465061/1250000000 : ℝ)*X 0 2+(164975857/400000000 : ℝ)*X 1 0+(3611303147/10000000000 : ℝ)*X 1 1+(585465061/1250000000 : ℝ)*X 1 2+(164975857/400000000 : ℝ)*X 2 0+(3611303147/10000000000 : ℝ)*X 2 1+(585465061/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-737358749/5000000000 : ℝ)*X 0 0+(1280591819/2500000000 : ℝ)*X 0 1+(274931217/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2626067977/5000000000 : ℝ)*X 1 0+(-1294719803/10000000000 : ℝ)*X 1 1+(5498624531/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5252136309/10000000000 : ℝ)*X 2 0+(274931239/500000000 : ℝ)*X 2 1+(-40459967/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((412501457/1000000000 : ℝ)*X 0 0+(2335353763/5000000000 : ℝ)*X 0 1+(1812266007/5000000000 : ℝ)*X 0 2+(412501457/1000000000 : ℝ)*X 1 0+(2335353763/5000000000 : ℝ)*X 1 1+(1812266007/5000000000 : ℝ)*X 1 2+(412501457/1000000000 : ℝ)*X 2 0+(2335353763/5000000000 : ℝ)*X 2 1+(1812266007/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (586633835366889408134235429/92750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4678959/500000000000 : ℝ)*(base19) + (57925793/12500000000000 : ℝ)*(base23) + (549749/50000000000000 : ℝ)*(upper2) + (12081401/6250000000000 : ℝ)*(upper3) + (26954249/100000000000000 : ℝ)*(upper4) + (881303249273887/50000000000000 : ℝ)*(major0) + (881303249273887/50000000000000 : ℝ)*(major1) + (881303249273887/50000000000000 : ℝ)*(major2) + (162045678564589/6250000000000 : ℝ)*(sp0) + (648183599269733/25000000000000 : ℝ)*(sp1) + (648183717366097/25000000000000 : ℝ)*(sp2) + (116559345084239/12500000000000 : ℝ)*(sp3) + (4475837307/100000000000000 : ℝ)*(sp4) + (336590141/12500000000000 : ℝ)*(sp7) + (5827984083719/625000000000 : ℝ)*(f.failure) + (2592735332870731/100000000000000 : ℝ)*(f.sum) + (268194677509/92750000000000000000000000 : ℝ)*base65 + (191993772604751619/185500000000000000000000000000000 : ℝ)*base68 + (727420738132751619/185500000000000000000000000000000 : ℝ)*base70 + (2034213664032751619/185500000000000000000000000000000 : ℝ)*base72 + (10701011679/185500000000000000000000000 : ℝ)*base74 + (929592559536751619/185500000000000000000000000000000 : ℝ)*base76 + (255465412752751619/185500000000000000000000000000000 : ℝ)*base78 + (2330483482772751619/185500000000000000000000000000000 : ℝ)*base80 + (984754003381/185500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (176223/31250000000000000000 : ℝ)*base89 + (176223/31250000000000000000 : ℝ)*base91 + (176223/31250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (522152634616106401203935991/46375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16304299/2000000000000 : ℝ)*(base19) + (122906101/10000000000000 : ℝ)*(base23) + (245233889/100000000000000 : ℝ)*(upper3) + (49904107/100000000000000 : ℝ)*(lower4) + (234793447/100000000000000 : ℝ)*(upper5) + (903405185459881/50000000000000 : ℝ)*(major0) + (903405185459881/50000000000000 : ℝ)*(major1) + (903405185459881/50000000000000 : ℝ)*(major2) + (4527988909/100000000000000 : ℝ)*(sp1) + (11611700659/100000000000000 : ℝ)*(sp2) + (2657757594643433/100000000000000 : ℝ)*(sp4) + (1328876125719787/50000000000000 : ℝ)*(sp5) + (664436188470441/25000000000000 : ℝ)*(sp6) + (191172554376843/20000000000000 : ℝ)*(sp7) + (191172554376843/20000000000000 : ℝ)*(f.failure) + (2657757594643433/100000000000000 : ℝ)*(f.sum) + (1257022884277/185500000000000000000000000 : ℝ)*base65 + (496334277550063003/185500000000000000000000000000000 : ℝ)*base67 + (1228373793185936997/185500000000000000000000000000000 : ℝ)*base70 + (1762036390767563003/185500000000000000000000000000000 : ℝ)*base71 + (34161879323/18550000000000000000000000 : ℝ)*base74 + (889238499123563003/185500000000000000000000000000000 : ℝ)*base75 + (588751034034563003/185500000000000000000000000000000 : ℝ)*base77 + (954653442465563003/185500000000000000000000000000000 : ℝ)*base79 + (772415372521/371000000000000000000000000 : ℝ)*base82 + (9977669/1000000000000000000000 : ℝ)*base90 + (9977669/1000000000000000000000 : ℝ)*base92 + (9977669/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1692_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94512017/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (22563/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5497/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (473/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2209/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1692_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1692_s2_0 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1479602787/10000000000 : ℝ)*x 0 + (5482853011/10000000000 : ℝ)*x 1 + (1026963591/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1479602787/10000000000 : ℝ)^5159 ≤ (1152253856633/12500000000000 : ℝ)^4135 := by
    have hnat : (1479602787 : ℕ)^5159*12500000000000^4135 ≤ 1152253856633^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1479602787 10000000000 1152253856633 12500000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5482853011/10000000000 : ℝ)^5159 ≤ (47246936658251/100000000000000 : ℝ)^4135 := by
    have hnat : (5482853011 : ℕ)^5159*100000000000000^4135 ≤ 47246936658251^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5482853011 10000000000 47246936658251 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1026963591/2000000000 : ℝ)^5159 ≤ (4353503247427/10000000000000 : ℝ)^4135 := by
    have hnat : (1026963591 : ℕ)^5159*10000000000000^4135 ≤ 4353503247427^4135*2000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026963591 2000000000 4353503247427 10000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1479602787/10000000000 : ℝ), (5482853011/10000000000 : ℝ), (1026963591/2000000000 : ℝ)] ![(1152253856633/12500000000000 : ℝ), (47246936658251/100000000000000 : ℝ), (4353503247427/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1479602787/10000000000 : ℝ)|^5159 ≤ (1152253856633/12500000000000 : ℝ)^4135
        have hw : |(-1479602787/10000000000 : ℝ)|=(1479602787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5482853011/10000000000 : ℝ)|^5159 ≤ (47246936658251/100000000000000 : ℝ)^4135
        have hw : |(5482853011/10000000000 : ℝ)|=(5482853011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1026963591/2000000000 : ℝ)|^5159 ≤ (4353503247427/10000000000000 : ℝ)^4135
        have hw : |(1026963591/2000000000 : ℝ)|=(1026963591/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_s2_1 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337456593/2500000000 : ℝ)*x 0 + (-415097201/2500000000 : ℝ)*x 1 + (1283704507/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337456593/2500000000 : ℝ)^5159 ≤ (2863816452579/6250000000000 : ℝ)^4135 := by
    have hnat : (1337456593 : ℕ)^5159*6250000000000^4135 ≤ 2863816452579^4135*2500000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337456593 2500000000 2863816452579 6250000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (415097201/2500000000 : ℝ)^5159 ≤ (2128780699597/20000000000000 : ℝ)^4135 := by
    have hnat : (415097201 : ℕ)^5159*20000000000000^4135 ≤ 2128780699597^4135*2500000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415097201 2500000000 2128780699597 20000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1283704507/2500000000 : ℝ)^5159 ≤ (8707006649293/20000000000000 : ℝ)^4135 := by
    have hnat : (1283704507 : ℕ)^5159*20000000000000^4135 ≤ 8707006649293^4135*2500000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1283704507 2500000000 8707006649293 20000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337456593/2500000000 : ℝ), (-415097201/2500000000 : ℝ), (1283704507/2500000000 : ℝ)] ![(2863816452579/6250000000000 : ℝ), (2128780699597/20000000000000 : ℝ), (8707006649293/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337456593/2500000000 : ℝ)|^5159 ≤ (2863816452579/6250000000000 : ℝ)^4135
        have hw : |(1337456593/2500000000 : ℝ)|=(1337456593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-415097201/2500000000 : ℝ)|^5159 ≤ (2128780699597/20000000000000 : ℝ)^4135
        have hw : |(-415097201/2500000000 : ℝ)|=(415097201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1283704507/2500000000 : ℝ)|^5159 ≤ (8707006649293/20000000000000 : ℝ)^4135
        have hw : |(1283704507/2500000000 : ℝ)|=(1283704507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_s2_2 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674913263/5000000000 : ℝ)*x 0 + (1283704439/2500000000 : ℝ)*x 1 + (-1660388957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674913263/5000000000 : ℝ)^5159 ≤ (45821064886909/100000000000000 : ℝ)^4135 := by
    have hnat : (2674913263 : ℕ)^5159*100000000000000^4135 ≤ 45821064886909^4135*5000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674913263 5000000000 45821064886909 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1283704439/2500000000 : ℝ)^5159 ≤ (43535030369247/100000000000000 : ℝ)^4135 := by
    have hnat : (1283704439 : ℕ)^5159*100000000000000^4135 ≤ 43535030369247^4135*2500000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1283704439 2500000000 43535030369247 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1660388957/10000000000 : ℝ)^5159 ≤ (5321952360839/50000000000000 : ℝ)^4135 := by
    have hnat : (1660388957 : ℕ)^5159*50000000000000^4135 ≤ 5321952360839^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1660388957 10000000000 5321952360839 50000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674913263/5000000000 : ℝ), (1283704439/2500000000 : ℝ), (-1660388957/10000000000 : ℝ)] ![(45821064886909/100000000000000 : ℝ), (43535030369247/100000000000000 : ℝ), (5321952360839/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674913263/5000000000 : ℝ)|^5159 ≤ (45821064886909/100000000000000 : ℝ)^4135
        have hw : |(2674913263/5000000000 : ℝ)|=(2674913263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1283704439/2500000000 : ℝ)|^5159 ≤ (43535030369247/100000000000000 : ℝ)^4135
        have hw : |(1283704439/2500000000 : ℝ)|=(1283704439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1660388957/10000000000 : ℝ)|^5159 ≤ (5321952360839/50000000000000 : ℝ)^4135
        have hw : |(-1660388957/10000000000 : ℝ)|=(1660388957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_s2_3 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4128328151/10000000000 : ℝ)*x 0 + (3663295049/10000000000 : ℝ)*x 1 + (2315500211/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4128328151/10000000000 : ℝ)^5159 ≤ (16580351828459/50000000000000 : ℝ)^4135 := by
    have hnat : (4128328151 : ℕ)^5159*50000000000000^4135 ≤ 16580351828459^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4128328151 10000000000 16580351828459 50000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3663295049/10000000000 : ℝ)^5159 ≤ (357090455273/1250000000000 : ℝ)^4135 := by
    have hnat : (3663295049 : ℕ)^5159*1250000000000^4135 ≤ 357090455273^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3663295049 10000000000 357090455273 1250000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2315500211/5000000000 : ℝ)^5159 ≤ (38272059909813/100000000000000 : ℝ)^4135 := by
    have hnat : (2315500211 : ℕ)^5159*100000000000000^4135 ≤ 38272059909813^4135*5000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2315500211 5000000000 38272059909813 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4128328151/10000000000 : ℝ), (3663295049/10000000000 : ℝ), (2315500211/5000000000 : ℝ)] ![(16580351828459/50000000000000 : ℝ), (357090455273/1250000000000 : ℝ), (38272059909813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4128328151/10000000000 : ℝ)|^5159 ≤ (16580351828459/50000000000000 : ℝ)^4135
        have hw : |(4128328151/10000000000 : ℝ)|=(4128328151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3663295049/10000000000 : ℝ)|^5159 ≤ (357090455273/1250000000000 : ℝ)^4135
        have hw : |(3663295049/10000000000 : ℝ)|=(3663295049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2315500211/5000000000 : ℝ)|^5159 ≤ (38272059909813/100000000000000 : ℝ)^4135
        have hw : |(2315500211/5000000000 : ℝ)|=(2315500211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_s2_4 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-184970763/1250000000 : ℝ)*x 0 + (2569316057/5000000000 : ℝ)*x 1 + (5478981537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (184970763/1250000000 : ℝ)^5159 ≤ (9219300316977/100000000000000 : ℝ)^4135 := by
    have hnat : (184970763 : ℕ)^5159*100000000000000^4135 ≤ 9219300316977^4135*1250000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      184970763 1250000000 9219300316977 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2569316057/5000000000 : ℝ)^5159 ≤ (43575382383663/100000000000000 : ℝ)^4135 := by
    have hnat : (2569316057 : ℕ)^5159*100000000000000^4135 ≤ 43575382383663^4135*5000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2569316057 5000000000 43575382383663 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5478981537/10000000000 : ℝ)^5159 ≤ (2950332330921/6250000000000 : ℝ)^4135 := by
    have hnat : (5478981537 : ℕ)^5159*6250000000000^4135 ≤ 2950332330921^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5478981537 10000000000 2950332330921 6250000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-184970763/1250000000 : ℝ), (2569316057/5000000000 : ℝ), (5478981537/10000000000 : ℝ)] ![(9219300316977/100000000000000 : ℝ), (43575382383663/100000000000000 : ℝ), (2950332330921/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-184970763/1250000000 : ℝ)|^5159 ≤ (9219300316977/100000000000000 : ℝ)^4135
        have hw : |(-184970763/1250000000 : ℝ)|=(184970763/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2569316057/5000000000 : ℝ)|^5159 ≤ (43575382383663/100000000000000 : ℝ)^4135
        have hw : |(2569316057/5000000000 : ℝ)|=(2569316057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5478981537/10000000000 : ℝ)|^5159 ≤ (2950332330921/6250000000000 : ℝ)^4135
        have hw : |(5478981537/10000000000 : ℝ)|=(5478981537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_s2_5 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628379647/5000000000 : ℝ)*x 0 + (-32905631/250000000 : ℝ)*x 1 + (1369745417/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628379647/5000000000 : ℝ)^5159 ≤ (2241434967211/5000000000000 : ℝ)^4135 := by
    have hnat : (2628379647 : ℕ)^5159*5000000000000^4135 ≤ 2241434967211^4135*5000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628379647 5000000000 2241434967211 5000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32905631/250000000 : ℝ)^5159 ≤ (124468467769/1562500000000 : ℝ)^4135 := by
    have hnat : (32905631 : ℕ)^5159*1562500000000^4135 ≤ 124468467769^4135*250000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32905631 250000000 124468467769 1562500000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1369745417/2500000000 : ℝ)^5159 ≤ (47205318702897/100000000000000 : ℝ)^4135 := by
    have hnat : (1369745417 : ℕ)^5159*100000000000000^4135 ≤ 47205318702897^4135*2500000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369745417 2500000000 47205318702897 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628379647/5000000000 : ℝ), (-32905631/250000000 : ℝ), (1369745417/2500000000 : ℝ)] ![(2241434967211/5000000000000 : ℝ), (124468467769/1562500000000 : ℝ), (47205318702897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628379647/5000000000 : ℝ)|^5159 ≤ (2241434967211/5000000000000 : ℝ)^4135
        have hw : |(2628379647/5000000000 : ℝ)|=(2628379647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-32905631/250000000 : ℝ)|^5159 ≤ (124468467769/1562500000000 : ℝ)^4135
        have hw : |(-32905631/250000000 : ℝ)|=(32905631/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1369745417/2500000000 : ℝ)|^5159 ≤ (47205318702897/100000000000000 : ℝ)^4135
        have hw : |(1369745417/2500000000 : ℝ)|=(1369745417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_s2_6 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1051351857/2000000000 : ℝ)*x 0 + (5478981683/10000000000 : ℝ)*x 1 + (-82264077/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051351857/2000000000 : ℝ)^5159 ≤ (44828699248463/100000000000000 : ℝ)^4135 := by
    have hnat : (1051351857 : ℕ)^5159*100000000000000^4135 ≤ 44828699248463^4135*2000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051351857 2000000000 44828699248463 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5478981683/10000000000 : ℝ)^5159 ≤ (47205318864137/100000000000000 : ℝ)^4135 := by
    have hnat : (5478981683 : ℕ)^5159*100000000000000^4135 ≤ 47205318864137^4135*10000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5478981683 10000000000 47205318864137 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82264077/625000000 : ℝ)^5159 ≤ (7965981876809/100000000000000 : ℝ)^4135 := by
    have hnat : (82264077 : ℕ)^5159*100000000000000^4135 ≤ 7965981876809^4135*625000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82264077 625000000 7965981876809 100000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051351857/2000000000 : ℝ), (5478981683/10000000000 : ℝ), (-82264077/625000000 : ℝ)] ![(44828699248463/100000000000000 : ℝ), (47205318864137/100000000000000 : ℝ), (7965981876809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051351857/2000000000 : ℝ)|^5159 ≤ (44828699248463/100000000000000 : ℝ)^4135
        have hw : |(1051351857/2000000000 : ℝ)|=(1051351857/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5478981683/10000000000 : ℝ)|^5159 ≤ (47205318864137/100000000000000 : ℝ)^4135
        have hw : |(5478981683/10000000000 : ℝ)|=(5478981683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-82264077/625000000 : ℝ)|^5159 ≤ (7965981876809/100000000000000 : ℝ)^4135
        have hw : |(-82264077/625000000 : ℝ)|=(82264077/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1692_s2_7 (p : ℝ) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (516097773/1250000000 : ℝ)*x 0 + (2310197387/5000000000 : ℝ)*x 1 + (229628737/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (516097773/1250000000 : ℝ)^5159 ≤ (16582626940967/50000000000000 : ℝ)^4135 := by
    have hnat : (516097773 : ℕ)^5159*50000000000000^4135 ≤ 16582626940967^4135*1250000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516097773 1250000000 16582626940967 50000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2310197387/5000000000 : ℝ)^5159 ≤ (3816273704601/10000000000000 : ℝ)^4135 := by
    have hnat : (2310197387 : ℕ)^5159*10000000000000^4135 ≤ 3816273704601^4135*5000000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2310197387 5000000000 3816273704601 10000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (229628737/625000000 : ℝ)^5159 ≤ (5734401812229/20000000000000 : ℝ)^4135 := by
    have hnat : (229628737 : ℕ)^5159*20000000000000^4135 ≤ 5734401812229^4135*625000000^5159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229628737 625000000 5734401812229 20000000000000 5159 4135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5159/1024 : ℝ)) 5159 4135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(516097773/1250000000 : ℝ), (2310197387/5000000000 : ℝ), (229628737/625000000 : ℝ)] ![(16582626940967/50000000000000 : ℝ), (3816273704601/10000000000000 : ℝ), (5734401812229/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(516097773/1250000000 : ℝ)|^5159 ≤ (16582626940967/50000000000000 : ℝ)^4135
        have hw : |(516097773/1250000000 : ℝ)|=(516097773/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2310197387/5000000000 : ℝ)|^5159 ≤ (3816273704601/10000000000000 : ℝ)^4135
        have hw : |(2310197387/5000000000 : ℝ)|=(2310197387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(229628737/625000000 : ℝ)|^5159 ≤ (5734401812229/20000000000000 : ℝ)^4135
        have hw : |(229628737/625000000 : ℝ)|=(229628737/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1692_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94512017/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2209/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (473/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (1229/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8621/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2209/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (473/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2209/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (473/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2209/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (473/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2209/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (473/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2209/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (473/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2209/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (473/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (473/5000 : ℝ) ^ (5151/1024 : ℝ) ≤ (705427500606671/100000000000000000000 : ℝ) := by
    have hpowers : (473/5000 : ℝ)^5151 ≤ (705427500606671/100000000000000000000 : ℝ)^1024 := by
      have hnat : (473 : ℕ)^5151*100000000000000000000^1024 ≤ 705427500606671^1024*5000^5151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        473 5000 705427500606671 100000000000000000000 5151 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (473/5000 : ℝ)) (X := (705427500606671/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5151 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2209/12500 : ℝ) ^ (5151/1024 : ℝ) ≤ (4088662600802803/25000000000000000000 : ℝ) := by
    have hpowers : (2209/12500 : ℝ)^5151 ≤ (4088662600802803/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2209 : ℕ)^5151*25000000000000000000^1024 ≤ 4088662600802803^1024*12500^5151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2209 12500 4088662600802803 25000000000000000000 5151 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2209/12500 : ℝ)) (X := (4088662600802803/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5151 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000705427500606671/50000000000000000000 : ℝ) ≤ (400001121884959/400000000000000 : ℝ) ^ (5151/1024 : ℝ) := by
    have hpowers : (50000705427500606671/50000000000000000000 : ℝ)^1024 ≤ (400001121884959/400000000000000 : ℝ)^5151 := by
      have hnat : (50000705427500606671 : ℕ)^1024*400000000000000^5151 ≤ 400001121884959^5151*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000705427500606671 50000000000000000000 400001121884959 400000000000000 1024 5151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400001121884959/400000000000000 : ℝ)) (X := (50000705427500606671/50000000000000000000 : ℝ)) (by norm_num) 5151 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100017060077903817883/100000000000000000000 : ℝ) ≤ (125004239061827/125000000000000 : ℝ) ^ (5151/1024 : ℝ) := by
    have hpowers : (100017060077903817883/100000000000000000000 : ℝ)^1024 ≤ (125004239061827/125000000000000 : ℝ)^5151 := by
      have hnat : (100017060077903817883 : ℕ)^1024*125000000000000^5151 ≤ 125004239061827^5151*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100017060077903817883 100000000000000000000 125004239061827 125000000000000 1024 5151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125004239061827/125000000000000 : ℝ)) (X := (100017060077903817883/100000000000000000000 : ℝ)) (by norm_num) 5151 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12504088662600802803/12500000000000000000 : ℝ) ≤ (2000130040553669/2000000000000000 : ℝ) ^ (5151/1024 : ℝ) := by
    have hpowers : (12504088662600802803/12500000000000000000 : ℝ)^1024 ≤ (2000130040553669/2000000000000000 : ℝ)^5151 := by
      have hnat : (12504088662600802803 : ℕ)^1024*2000000000000000^5151 ≤ 2000130040553669^5151*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12504088662600802803 12500000000000000000 2000130040553669 2000000000000000 1024 5151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000130040553669/2000000000000000 : ℝ)) (X := (12504088662600802803/12500000000000000000 : ℝ)) (by norm_num) 5151 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(705427500606671/100000000000000000000 : ℝ) ≤ ((32845737892234537/32848000000000000 : ℝ)+2*(62215564437/164240000000000 : ℝ)*(473/5000 : ℝ))^(5151/1024 : ℝ) := by
    rw [show (32845737892234537/32848000000000000 : ℝ)+2*(62215564437/164240000000000 : ℝ)*(473/5000 : ℝ)=(400001121884959/400000000000000 : ℝ) by norm_num, show 1+2*(705427500606671/100000000000000000000 : ℝ)=(50000705427500606671/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4088662600802803/25000000000000000000 : ℝ)+(705427500606671/100000000000000000000 : ℝ) ≤ ((32845737892234537/32848000000000000 : ℝ)+(62215564437/164240000000000 : ℝ)*((2209/12500 : ℝ)+(473/5000 : ℝ)))^(5151/1024 : ℝ) := by
    rw [show (32845737892234537/32848000000000000 : ℝ)+(62215564437/164240000000000 : ℝ)*((2209/12500 : ℝ)+(473/5000 : ℝ))=(125004239061827/125000000000000 : ℝ) by norm_num, show 1+(4088662600802803/25000000000000000000 : ℝ)+(705427500606671/100000000000000000000 : ℝ)=(100017060077903817883/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4088662600802803/25000000000000000000 : ℝ) ≤ ((32845737892234537/32848000000000000 : ℝ)+2*(62215564437/164240000000000 : ℝ)*(2209/12500 : ℝ))^(5151/1024 : ℝ) := by
    rw [show (32845737892234537/32848000000000000 : ℝ)+2*(62215564437/164240000000000 : ℝ)*(2209/12500 : ℝ)=(2000130040553669/2000000000000000 : ℝ) by norm_num, show 1+2*(4088662600802803/25000000000000000000 : ℝ)=(12504088662600802803/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (32845737892234537/32848000000000000 : ℝ)*(X 1 0+X 2 0)+(62215564437/164240000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5151/1024 : ℝ)) (lo := (473/5000 : ℝ)) (hi := (2209/12500 : ℝ)) (c := (32845737892234537/32848000000000000 : ℝ)) (alpha := (62215564437/164240000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (32845737892234537/32848000000000000 : ℝ)*(X 0 1+X 2 1)+(62215564437/164240000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5151/1024 : ℝ)) (lo := (473/5000 : ℝ)) (hi := (2209/12500 : ℝ)) (c := (32845737892234537/32848000000000000 : ℝ)) (alpha := (62215564437/164240000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (32845737892234537/32848000000000000 : ℝ)*(X 0 2+X 1 2)+(62215564437/164240000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5151/1024 : ℝ)) (lo := (473/5000 : ℝ)) (hi := (2209/12500 : ℝ)) (c := (32845737892234537/32848000000000000 : ℝ)) (alpha := (62215564437/164240000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1479602787/10000000000 : ℝ)*X 0 0+(5482853011/10000000000 : ℝ)*X 0 1+(1026963591/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337456593/2500000000 : ℝ)*X 1 0+(-415097201/2500000000 : ℝ)*X 1 1+(1283704507/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674913263/5000000000 : ℝ)*X 2 0+(1283704439/2500000000 : ℝ)*X 2 1+(-1660388957/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4128328151/10000000000 : ℝ)*X 0 0+(3663295049/10000000000 : ℝ)*X 0 1+(2315500211/5000000000 : ℝ)*X 0 2+(4128328151/10000000000 : ℝ)*X 1 0+(3663295049/10000000000 : ℝ)*X 1 1+(2315500211/5000000000 : ℝ)*X 1 2+(4128328151/10000000000 : ℝ)*X 2 0+(3663295049/10000000000 : ℝ)*X 2 1+(2315500211/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-184970763/1250000000 : ℝ)*X 0 0+(2569316057/5000000000 : ℝ)*X 0 1+(5478981537/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2628379647/5000000000 : ℝ)*X 1 0+(-32905631/250000000 : ℝ)*X 1 1+(1369745417/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1051351857/2000000000 : ℝ)*X 2 0+(5478981683/10000000000 : ℝ)*X 2 1+(-82264077/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((516097773/1250000000 : ℝ)*X 0 0+(2310197387/5000000000 : ℝ)*X 0 1+(229628737/625000000 : ℝ)*X 0 2+(516097773/1250000000 : ℝ)*X 1 0+(2310197387/5000000000 : ℝ)*X 1 1+(229628737/625000000 : ℝ)*X 1 2+(516097773/1250000000 : ℝ)*X 2 0+(2310197387/5000000000 : ℝ)*X 2 1+(229628737/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1692_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4972399167003656533130211/410600000000000000000000000000 : ℝ) := by norm_num
    linear_combination (224088813/12500000000000 : ℝ)*(base19) + (421952591/25000000000000 : ℝ)*(base23) + (100368669/100000000000000 : ℝ)*(lower2) + (344014479/100000000000000 : ℝ)*(upper3) + (24814467/20000000000000 : ℝ)*(upper5) + (488336727897399/25000000000000 : ℝ)*(major0) + (488336727897399/25000000000000 : ℝ)*(major1) + (488336727897399/25000000000000 : ℝ)*(major2) + (71832299713417/2500000000000 : ℝ)*(sp0) + (718326537953199/25000000000000 : ℝ)*(sp1) + (359163282089117/12500000000000 : ℝ)*(sp2) + (1033378023651891/100000000000000 : ℝ)*(sp3) + (797799331/5000000000000 : ℝ)*(sp4) + (1862833659/25000000000000 : ℝ)*(sp7) + (32293296093329/3125000000000 : ℝ)*(f.failure) + (28733079445233/1000000000000 : ℝ)*(f.sum) + (726450177831/1026500000000000000000000000 : ℝ)*base66 + (2321983013617737/821200000000000000000000000000 : ℝ)*base68 + (7449525082197063/821200000000000000000000000000 : ℝ)*base69 + (7997522827389463/821200000000000000000000000000 : ℝ)*base71 + (502670501851/513250000000000000000000000 : ℝ)*base74 + (2897808970499463/821200000000000000000000000000 : ℝ)*base75 + (662331022640663/821200000000000000000000000000 : ℝ)*base77 + (1056869767684937/821200000000000000000000000000 : ℝ)*base80 + (14215897359377/2053000000000000000000000000 : ℝ)*base81 + (284593/156250000000000000000 : ℝ)*base89 + (284593/156250000000000000000 : ℝ)*base91 + (284593/156250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (663977210681634988500189/102650000000000000000000000000 : ℝ) := by norm_num
    linear_combination (386090101/50000000000000 : ℝ)*(base19) + (914811277/100000000000000 : ℝ)*(base23) + (131364889/100000000000000 : ℝ)*(upper3) + (13266003/20000000000000 : ℝ)*(lower4) + (131637539/100000000000000 : ℝ)*(upper5) + (124839511164883/6250000000000 : ℝ)*(major0) + (124839511164883/6250000000000 : ℝ)*(major1) + (124839511164883/6250000000000 : ℝ)*(major2) + (1488995413/20000000000000 : ℝ)*(sp1) + (8658285427/100000000000000 : ℝ)*(sp2) + (367269511793609/12500000000000 : ℝ)*(sp4) + (587629575438321/20000000000000 : ℝ)*(sp5) + (367268315156521/12500000000000 : ℝ)*(sp6) + (1056708047315363/100000000000000 : ℝ)*(sp7) + (1056708047315363/100000000000000 : ℝ)*(f.failure) + (367269511793609/12500000000000 : ℝ)*(f.sum) + (200007543993/513250000000000000000000000 : ℝ)*base65 + (713985245022629/205300000000000000000000000000 : ℝ)*base68 + (726913476689629/205300000000000000000000000000 : ℝ)*base70 + (218265703624229/205300000000000000000000000000 : ℝ)*base72 + (1110800233439/1026500000000000000000000000 : ℝ)*base73 + (891615133978429/205300000000000000000000000000 : ℝ)*base76 + (121678506613829/205300000000000000000000000000 : ℝ)*base78 + (342968141907029/205300000000000000000000000000 : ℝ)*base80 + (4098392751791/2053000000000000000000000000 : ℝ)*base81 + (7782829/5000000000000000000000 : ℝ)*base90 + (7782829/5000000000000000000000 : ℝ)*base92 + (7782829/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1692_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94512017/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2209/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (473/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1229/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8621/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1692_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1692_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94512017/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1229/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8621/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1692_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1692_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1692_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5151/1024 : ℝ) ≤ p) (hpb : p ≤ (5159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (94512017/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1229/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8621/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1692_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
