-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1074_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:12:54.668353+00:00
-- url     : https://prove2.me/submissions/249f00af-5969-4da6-9420-faf299779c67

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
theorem support_rectangle_w1074_s3_0 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-274400193/1250000000 : ℝ)*x 0 + (543660957/1000000000 : ℝ)*x 1 + (2612618483/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (274400193/1250000000 : ℝ)^8267 ≤ (13323339626051/100000000000000 : ℝ)^6219 := by
    have hnat : (274400193 : ℕ)^8267*100000000000000^6219 ≤ 13323339626051^6219*1250000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274400193 1250000000 13323339626051 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543660957/1000000000 : ℝ)^8267 ≤ (11120086539427/25000000000000 : ℝ)^6219 := by
    have hnat : (543660957 : ℕ)^8267*25000000000000^6219 ≤ 11120086539427^6219*1000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543660957 1000000000 11120086539427 25000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2612618483/5000000000 : ℝ)^8267 ≤ (42196314201541/100000000000000 : ℝ)^6219 := by
    have hnat : (2612618483 : ℕ)^8267*100000000000000^6219 ≤ 42196314201541^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612618483 5000000000 42196314201541 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-274400193/1250000000 : ℝ), (543660957/1000000000 : ℝ), (2612618483/5000000000 : ℝ)] ![(13323339626051/100000000000000 : ℝ), (11120086539427/25000000000000 : ℝ), (42196314201541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-274400193/1250000000 : ℝ)|^8267 ≤ (13323339626051/100000000000000 : ℝ)^6219
        have hw : |(-274400193/1250000000 : ℝ)|=(274400193/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(543660957/1000000000 : ℝ)|^8267 ≤ (11120086539427/25000000000000 : ℝ)^6219
        have hw : |(543660957/1000000000 : ℝ)|=(543660957/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2612618483/5000000000 : ℝ)|^8267 ≤ (42196314201541/100000000000000 : ℝ)^6219
        have hw : |(2612618483/5000000000 : ℝ)|=(2612618483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s3_1 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2677743281/5000000000 : ℝ)*x 0 + (-2303419629/10000000000 : ℝ)*x 1 + (1306309257/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677743281/5000000000 : ℝ)^8267 ≤ (43600231004193/100000000000000 : ℝ)^6219 := by
    have hnat : (2677743281 : ℕ)^8267*100000000000000^6219 ≤ 43600231004193^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677743281 5000000000 43600231004193 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2303419629/10000000000 : ℝ)^8267 ≤ (7101727057027/50000000000000 : ℝ)^6219 := by
    have hnat : (2303419629 : ℕ)^8267*50000000000000^6219 ≤ 7101727057027^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2303419629 10000000000 7101727057027 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1306309257/2500000000 : ℝ)^8267 ≤ (21098157433551/50000000000000 : ℝ)^6219 := by
    have hnat : (1306309257 : ℕ)^8267*50000000000000^6219 ≤ 21098157433551^6219*2500000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306309257 2500000000 21098157433551 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677743281/5000000000 : ℝ), (-2303419629/10000000000 : ℝ), (1306309257/2500000000 : ℝ)] ![(43600231004193/100000000000000 : ℝ), (7101727057027/50000000000000 : ℝ), (21098157433551/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677743281/5000000000 : ℝ)|^8267 ≤ (43600231004193/100000000000000 : ℝ)^6219
        have hw : |(2677743281/5000000000 : ℝ)|=(2677743281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2303419629/10000000000 : ℝ)|^8267 ≤ (7101727057027/50000000000000 : ℝ)^6219
        have hw : |(-2303419629/10000000000 : ℝ)|=(2303419629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1306309257/2500000000 : ℝ)|^8267 ≤ (21098157433551/50000000000000 : ℝ)^6219
        have hw : |(1306309257/2500000000 : ℝ)|=(1306309257/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s3_2 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (535548653/1000000000 : ℝ)*x 0 + (5225237421/10000000000 : ℝ)*x 1 + (-2303419157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535548653/1000000000 : ℝ)^8267 ≤ (43600230657881/100000000000000 : ℝ)^6219 := by
    have hnat : (535548653 : ℕ)^8267*100000000000000^6219 ≤ 43600230657881^6219*1000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535548653 1000000000 43600230657881 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5225237421/10000000000 : ℝ)^8267 ≤ (42196319085897/100000000000000 : ℝ)^6219 := by
    have hnat : (5225237421 : ℕ)^8267*100000000000000^6219 ≤ 42196319085897^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225237421 10000000000 42196319085897 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2303419157/10000000000 : ℝ)^8267 ≤ (14203450245129/100000000000000 : ℝ)^6219 := by
    have hnat : (2303419157 : ℕ)^8267*100000000000000^6219 ≤ 14203450245129^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2303419157 10000000000 14203450245129 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535548653/1000000000 : ℝ), (5225237421/10000000000 : ℝ), (-2303419157/10000000000 : ℝ)] ![(43600230657881/100000000000000 : ℝ), (42196319085897/100000000000000 : ℝ), (14203450245129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535548653/1000000000 : ℝ)|^8267 ≤ (43600230657881/100000000000000 : ℝ)^6219
        have hw : |(535548653/1000000000 : ℝ)|=(535548653/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5225237421/10000000000 : ℝ)|^8267 ≤ (42196319085897/100000000000000 : ℝ)^6219
        have hw : |(5225237421/10000000000 : ℝ)|=(5225237421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2303419157/10000000000 : ℝ)|^8267 ≤ (14203450245129/100000000000000 : ℝ)^6219
        have hw : |(-2303419157/10000000000 : ℝ)|=(2303419157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s3_3 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4371603039/10000000000 : ℝ)*x 0 + (208455689/500000000 : ℝ)*x 1 + (183361253/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4371603039/10000000000 : ℝ)^8267 ≤ (8322214461861/25000000000000 : ℝ)^6219 := by
    have hnat : (4371603039 : ℕ)^8267*25000000000000^6219 ≤ 8322214461861^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4371603039 10000000000 8322214461861 25000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208455689/500000000 : ℝ)^8267 ≤ (31254968425807/100000000000000 : ℝ)^6219 := by
    have hnat : (208455689 : ℕ)^8267*100000000000000^6219 ≤ 31254968425807^6219*500000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208455689 500000000 31254968425807 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (183361253/400000000 : ℝ)^8267 ≤ (35456173700919/100000000000000 : ℝ)^6219 := by
    have hnat : (183361253 : ℕ)^8267*100000000000000^6219 ≤ 35456173700919^6219*400000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183361253 400000000 35456173700919 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4371603039/10000000000 : ℝ), (208455689/500000000 : ℝ), (183361253/400000000 : ℝ)] ![(8322214461861/25000000000000 : ℝ), (31254968425807/100000000000000 : ℝ), (35456173700919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4371603039/10000000000 : ℝ)|^8267 ≤ (8322214461861/25000000000000 : ℝ)^6219
        have hw : |(4371603039/10000000000 : ℝ)|=(4371603039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(208455689/500000000 : ℝ)|^8267 ≤ (31254968425807/100000000000000 : ℝ)^6219
        have hw : |(208455689/500000000 : ℝ)|=(208455689/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(183361253/400000000 : ℝ)|^8267 ≤ (35456173700919/100000000000000 : ℝ)^6219
        have hw : |(183361253/400000000 : ℝ)|=(183361253/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s3_4 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2195223869/10000000000 : ℝ)*x 0 + (5226098217/10000000000 : ℝ)*x 1 + (2717871443/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2195223869/10000000000 : ℝ)^8267 ≤ (13323519744531/100000000000000 : ℝ)^6219 := by
    have hnat : (2195223869 : ℕ)^8267*100000000000000^6219 ≤ 13323519744531^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2195223869 10000000000 13323519744531 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5226098217/10000000000 : ℝ)^8267 ≤ (42205559851199/100000000000000 : ℝ)^6219 := by
    have hnat : (5226098217 : ℕ)^8267*100000000000000^6219 ≤ 42205559851199^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226098217 10000000000 42205559851199 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2717871443/5000000000 : ℝ)^8267 ≤ (11117730097283/25000000000000 : ℝ)^6219 := by
    have hnat : (2717871443 : ℕ)^8267*25000000000000^6219 ≤ 11117730097283^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717871443 5000000000 11117730097283 25000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2195223869/10000000000 : ℝ), (5226098217/10000000000 : ℝ), (2717871443/5000000000 : ℝ)] ![(13323519744531/100000000000000 : ℝ), (42205559851199/100000000000000 : ℝ), (11117730097283/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2195223869/10000000000 : ℝ)|^8267 ≤ (13323519744531/100000000000000 : ℝ)^6219
        have hw : |(-2195223869/10000000000 : ℝ)|=(2195223869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5226098217/10000000000 : ℝ)|^8267 ≤ (42205559851199/100000000000000 : ℝ)^6219
        have hw : |(5226098217/10000000000 : ℝ)|=(5226098217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2717871443/5000000000 : ℝ)|^8267 ≤ (11117730097283/25000000000000 : ℝ)^6219
        have hw : |(2717871443/5000000000 : ℝ)|=(2717871443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s3_5 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5302209179/10000000000 : ℝ)*x 0 + (-2092914173/10000000000 : ℝ)*x 1 + (5435742803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302209179/10000000000 : ℝ)^8267 ≤ (21512298423281/50000000000000 : ℝ)^6219 := by
    have hnat : (5302209179 : ℕ)^8267*50000000000000^6219 ≤ 21512298423281^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302209179 10000000000 21512298423281 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2092914173/10000000000 : ℝ)^8267 ≤ (12504483652447/100000000000000 : ℝ)^6219 := by
    have hnat : (2092914173 : ℕ)^8267*100000000000000^6219 ≤ 12504483652447^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092914173 10000000000 12504483652447 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5435742803/10000000000 : ℝ)^8267 ≤ (1778836779459/4000000000000 : ℝ)^6219 := by
    have hnat : (5435742803 : ℕ)^8267*4000000000000^6219 ≤ 1778836779459^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435742803 10000000000 1778836779459 4000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302209179/10000000000 : ℝ), (-2092914173/10000000000 : ℝ), (5435742803/10000000000 : ℝ)] ![(21512298423281/50000000000000 : ℝ), (12504483652447/100000000000000 : ℝ), (1778836779459/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302209179/10000000000 : ℝ)|^8267 ≤ (21512298423281/50000000000000 : ℝ)^6219
        have hw : |(5302209179/10000000000 : ℝ)|=(5302209179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2092914173/10000000000 : ℝ)|^8267 ≤ (12504483652447/100000000000000 : ℝ)^6219
        have hw : |(-2092914173/10000000000 : ℝ)|=(2092914173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5435742803/10000000000 : ℝ)|^8267 ≤ (1778836779459/4000000000000 : ℝ)^6219
        have hw : |(5435742803/10000000000 : ℝ)|=(5435742803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s3_6 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5302209439/10000000000 : ℝ)*x 0 + (1358935803/2500000000 : ℝ)*x 1 + (-104645663/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302209439/10000000000 : ℝ)^8267 ≤ (5378074956387/12500000000000 : ℝ)^6219 := by
    have hnat : (5302209439 : ℕ)^8267*12500000000000^6219 ≤ 5378074956387^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302209439 10000000000 5378074956387 12500000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358935803/2500000000 : ℝ)^8267 ≤ (44470923934507/100000000000000 : ℝ)^6219 := by
    have hnat : (1358935803 : ℕ)^8267*100000000000000^6219 ≤ 44470923934507^6219*2500000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358935803 2500000000 44470923934507 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104645663/500000000 : ℝ)^8267 ≤ (3126119100301/25000000000000 : ℝ)^6219 := by
    have hnat : (104645663 : ℕ)^8267*25000000000000^6219 ≤ 3126119100301^6219*500000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104645663 500000000 3126119100301 25000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302209439/10000000000 : ℝ), (1358935803/2500000000 : ℝ), (-104645663/500000000 : ℝ)] ![(5378074956387/12500000000000 : ℝ), (44470923934507/100000000000000 : ℝ), (3126119100301/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302209439/10000000000 : ℝ)|^8267 ≤ (5378074956387/12500000000000 : ℝ)^6219
        have hw : |(5302209439/10000000000 : ℝ)|=(5302209439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1358935803/2500000000 : ℝ)|^8267 ≤ (44470923934507/100000000000000 : ℝ)^6219
        have hw : |(1358935803/2500000000 : ℝ)|=(1358935803/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-104645663/500000000 : ℝ)|^8267 ≤ (3126119100301/25000000000000 : ℝ)^6219
        have hw : |(-104645663/500000000 : ℝ)|=(104645663/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s3_7 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1092911327/2500000000 : ℝ)*x 0 + (458234127/1000000000 : ℝ)*x 1 + (2085407159/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092911327/2500000000 : ℝ)^8267 ≤ (33289285713881/100000000000000 : ℝ)^6219 := by
    have hnat : (1092911327 : ℕ)^8267*100000000000000^6219 ≤ 33289285713881^6219*2500000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092911327 2500000000 33289285713881 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (458234127/1000000000 : ℝ)^8267 ≤ (553731216369/1562500000000 : ℝ)^6219 := by
    have hnat : (458234127 : ℕ)^8267*1562500000000^6219 ≤ 553731216369^6219*1000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458234127 1000000000 553731216369 1562500000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2085407159/5000000000 : ℝ)^8267 ≤ (31271916415961/100000000000000 : ℝ)^6219 := by
    have hnat : (2085407159 : ℕ)^8267*100000000000000^6219 ≤ 31271916415961^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085407159 5000000000 31271916415961 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1092911327/2500000000 : ℝ), (458234127/1000000000 : ℝ), (2085407159/5000000000 : ℝ)] ![(33289285713881/100000000000000 : ℝ), (553731216369/1562500000000 : ℝ), (31271916415961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1092911327/2500000000 : ℝ)|^8267 ≤ (33289285713881/100000000000000 : ℝ)^6219
        have hw : |(1092911327/2500000000 : ℝ)|=(1092911327/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(458234127/1000000000 : ℝ)|^8267 ≤ (553731216369/1562500000000 : ℝ)^6219
        have hw : |(458234127/1000000000 : ℝ)|=(458234127/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2085407159/5000000000 : ℝ)|^8267 ≤ (31271916415961/100000000000000 : ℝ)^6219
        have hw : |(2085407159/5000000000 : ℝ)|=(2085407159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1074_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148148691/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3343/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8751/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5211/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7447/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3343/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8751/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3343/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8751/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3343/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8751/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3343/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8751/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3343/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8751/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3343/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8751/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8751/100000 : ℝ) ^ (4133/1024 : ℝ) ≤ (167824099556771/3125000000000000000 : ℝ) := by
    have hpowers : (8751/100000 : ℝ)^4133 ≤ (167824099556771/3125000000000000000 : ℝ)^1024 := by
      have hnat : (8751 : ℕ)^4133*3125000000000000000^1024 ≤ 167824099556771^1024*100000^4133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8751 100000 167824099556771 3125000000000000000 4133 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8751/100000 : ℝ)) (X := (167824099556771/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3343/20000 : ℝ) ^ (4133/1024 : ℝ) ≤ (73173557917336079/100000000000000000000 : ℝ) := by
    have hpowers : (3343/20000 : ℝ)^4133 ≤ (73173557917336079/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3343 : ℕ)^4133*100000000000000000000^1024 ≤ 73173557917336079^1024*20000^4133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3343 20000 73173557917336079 100000000000000000000 4133 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3343/20000 : ℝ)) (X := (73173557917336079/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562667824099556771/1562500000000000000 : ℝ) ≤ (1000026610394141/1000000000000000 : ℝ) ^ (4133/1024 : ℝ) := by
    have hpowers : (1562667824099556771/1562500000000000000 : ℝ)^1024 ≤ (1000026610394141/1000000000000000 : ℝ)^4133 := by
      have hnat : (1562667824099556771 : ℕ)^1024*1000000000000000^4133 ≤ 1000026610394141^4133*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562667824099556771 1562500000000000000 1000026610394141 1000000000000000 1024 4133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000026610394141/1000000000000000 : ℝ)) (X := (1562667824099556771/1562500000000000000 : ℝ)) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100078543929103152751/100000000000000000000 : ℝ) ≤ (10001945444811817/10000000000000000 : ℝ) ^ (4133/1024 : ℝ) := by
    have hpowers : (100078543929103152751/100000000000000000000 : ℝ)^1024 ≤ (10001945444811817/10000000000000000 : ℝ)^4133 := by
      have hnat : (100078543929103152751 : ℕ)^1024*10000000000000000^4133 ≤ 10001945444811817^4133*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100078543929103152751 100000000000000000000 10001945444811817 10000000000000000 1024 4133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001945444811817/10000000000000000 : ℝ)) (X := (100078543929103152751/100000000000000000000 : ℝ)) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50073173557917336079/50000000000000000000 : ℝ) ≤ (625226549105139/625000000000000 : ℝ) ^ (4133/1024 : ℝ) := by
    have hpowers : (50073173557917336079/50000000000000000000 : ℝ)^1024 ≤ (625226549105139/625000000000000 : ℝ)^4133 := by
      have hnat : (50073173557917336079 : ℕ)^1024*625000000000000^4133 ≤ 625226549105139^4133*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50073173557917336079 50000000000000000000 625226549105139 625000000000000 1024 4133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625226549105139/625000000000000 : ℝ)) (X := (50073173557917336079/50000000000000000000 : ℝ)) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(167824099556771/3125000000000000000 : ℝ) ≤ ((39806363713937762963/39820000000000000000 : ℝ)+2*(1679340870407/796400000000000 : ℝ)*(8751/100000 : ℝ))^(4133/1024 : ℝ) := by
    rw [show (39806363713937762963/39820000000000000000 : ℝ)+2*(1679340870407/796400000000000 : ℝ)*(8751/100000 : ℝ)=(1000026610394141/1000000000000000 : ℝ) by norm_num, show 1+2*(167824099556771/3125000000000000000 : ℝ)=(1562667824099556771/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(73173557917336079/100000000000000000000 : ℝ)+(167824099556771/3125000000000000000 : ℝ) ≤ ((39806363713937762963/39820000000000000000 : ℝ)+(1679340870407/796400000000000 : ℝ)*((3343/20000 : ℝ)+(8751/100000 : ℝ)))^(4133/1024 : ℝ) := by
    rw [show (39806363713937762963/39820000000000000000 : ℝ)+(1679340870407/796400000000000 : ℝ)*((3343/20000 : ℝ)+(8751/100000 : ℝ))=(10001945444811817/10000000000000000 : ℝ) by norm_num, show 1+(73173557917336079/100000000000000000000 : ℝ)+(167824099556771/3125000000000000000 : ℝ)=(100078543929103152751/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(73173557917336079/100000000000000000000 : ℝ) ≤ ((39806363713937762963/39820000000000000000 : ℝ)+2*(1679340870407/796400000000000 : ℝ)*(3343/20000 : ℝ))^(4133/1024 : ℝ) := by
    rw [show (39806363713937762963/39820000000000000000 : ℝ)+2*(1679340870407/796400000000000 : ℝ)*(3343/20000 : ℝ)=(625226549105139/625000000000000 : ℝ) by norm_num, show 1+2*(73173557917336079/100000000000000000000 : ℝ)=(50073173557917336079/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (39806363713937762963/39820000000000000000 : ℝ)*(X 1 0+X 2 0)+(1679340870407/796400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4133/1024 : ℝ)) (lo := (8751/100000 : ℝ)) (hi := (3343/20000 : ℝ)) (c := (39806363713937762963/39820000000000000000 : ℝ)) (alpha := (1679340870407/796400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (39806363713937762963/39820000000000000000 : ℝ)*(X 0 1+X 2 1)+(1679340870407/796400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4133/1024 : ℝ)) (lo := (8751/100000 : ℝ)) (hi := (3343/20000 : ℝ)) (c := (39806363713937762963/39820000000000000000 : ℝ)) (alpha := (1679340870407/796400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (39806363713937762963/39820000000000000000 : ℝ)*(X 0 2+X 1 2)+(1679340870407/796400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4133/1024 : ℝ)) (lo := (8751/100000 : ℝ)) (hi := (3343/20000 : ℝ)) (c := (39806363713937762963/39820000000000000000 : ℝ)) (alpha := (1679340870407/796400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-274400193/1250000000 : ℝ)*X 0 0+(543660957/1000000000 : ℝ)*X 0 1+(2612618483/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677743281/5000000000 : ℝ)*X 1 0+(-2303419629/10000000000 : ℝ)*X 1 1+(1306309257/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((535548653/1000000000 : ℝ)*X 2 0+(5225237421/10000000000 : ℝ)*X 2 1+(-2303419157/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4371603039/10000000000 : ℝ)*X 0 0+(208455689/500000000 : ℝ)*X 0 1+(183361253/400000000 : ℝ)*X 0 2+(4371603039/10000000000 : ℝ)*X 1 0+(208455689/500000000 : ℝ)*X 1 1+(183361253/400000000 : ℝ)*X 1 2+(4371603039/10000000000 : ℝ)*X 2 0+(208455689/500000000 : ℝ)*X 2 1+(183361253/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2195223869/10000000000 : ℝ)*X 0 0+(5226098217/10000000000 : ℝ)*X 0 1+(2717871443/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5302209179/10000000000 : ℝ)*X 1 0+(-2092914173/10000000000 : ℝ)*X 1 1+(5435742803/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5302209439/10000000000 : ℝ)*X 2 0+(1358935803/2500000000 : ℝ)*X 2 1+(-104645663/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1092911327/2500000000 : ℝ)*X 0 0+(458234127/1000000000 : ℝ)*X 0 1+(2085407159/5000000000 : ℝ)*X 0 2+(1092911327/2500000000 : ℝ)*X 1 0+(458234127/1000000000 : ℝ)*X 1 1+(2085407159/5000000000 : ℝ)*X 1 2+(1092911327/2500000000 : ℝ)*X 2 0+(458234127/1000000000 : ℝ)*X 2 1+(2085407159/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4240531362999291094654583877/497750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2194427601/100000000000000 : ℝ)*(base19) + (870946513/50000000000000 : ℝ)*(base23) + (227214877/100000000000000 : ℝ)*(lower2) + (26732637/25000000000000 : ℝ)*(upper3) + (9503057/4000000000000 : ℝ)*(upper5) + (892652399551631/25000000000000 : ℝ)*(major0) + (892652399551631/25000000000000 : ℝ)*(major1) + (892652399551631/25000000000000 : ℝ)*(major2) + (236551008829603/5000000000000 : ℝ)*(sp0) + (1182766017654469/25000000000000 : ℝ)*(sp1) + (4731064523152451/100000000000000 : ℝ)*(sp2) + (602533774451243/25000000000000 : ℝ)*(sp3) + (46088453417/100000000000000 : ℝ)*(sp4) + (17549582593/100000000000000 : ℝ)*(sp7) + (1205076323693783/50000000000000 : ℝ)*(f.failure) + (4731066265045477/100000000000000 : ℝ)*(f.sum) + (587047023991/1244375000000000000000000000 : ℝ)*base66 + (1061465239135607347/995500000000000000000000000000000 : ℝ)*base68 + (7028738064919107347/995500000000000000000000000000000 : ℝ)*base70 + (1058694668063107347/995500000000000000000000000000000 : ℝ)*base72 + (23672818090787/9955000000000000000000000000 : ℝ)*base73 + (1553170605942107347/995500000000000000000000000000000 : ℝ)*base76 + (1568393373832107347/995500000000000000000000000000000 : ℝ)*base78 + (8627063333816607347/995500000000000000000000000000000 : ℝ)*base80 + (243012338271/1244375000000000000000000000 : ℝ)*base82 + (36288053/5000000000000000000000 : ℝ)*base89 + (36288053/5000000000000000000000 : ℝ)*base91 + (36288053/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (294851852623954585366147773/248875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (221475607/100000000000000 : ℝ)*(base19) + (278667047/25000000000000 : ℝ)*(base23) + (202783243/100000000000000 : ℝ)*(upper2) + (3485327/6250000000000 : ℝ)*(upper3) + (93413637/100000000000000 : ℝ)*(upper5) + (449996948581681/12500000000000 : ℝ)*(major0) + (449996948581681/12500000000000 : ℝ)*(major1) + (449996948581681/12500000000000 : ℝ)*(major2) + (136127513/50000000000000 : ℝ)*(sp1) + (6955958349/25000000000000 : ℝ)*(sp2) + (596247064938627/12500000000000 : ℝ)*(sp4) + (4769976025778383/100000000000000 : ℝ)*(sp5) + (596243447625929/12500000000000 : ℝ)*(sp6) + (1214987309153291/50000000000000 : ℝ)*(sp7) + (1214987309153291/50000000000000 : ℝ)*(f.failure) + (596247064938627/12500000000000 : ℝ)*(f.sum) + (11449403472913/4977500000000000000000000000 : ℝ)*base66 + (4187720391657430803/497750000000000000000000000000000 : ℝ)*base67 + (4025036956347430803/497750000000000000000000000000000 : ℝ)*base69 + (4303998866736680803/497750000000000000000000000000000 : ℝ)*base71 + (43498660322951/9955000000000000000000000000 : ℝ)*base74 + (618102413574680803/497750000000000000000000000000000 : ℝ)*base75 + (3219218266044430803/497750000000000000000000000000000 : ℝ)*base77 + (3773971265020430803/497750000000000000000000000000000 : ℝ)*base79 + (6388337380193/4977500000000000000000000000 : ℝ)*base82 + (20007919/5000000000000000000000 : ℝ)*base90 + (20007919/5000000000000000000000 : ℝ)*base92 + (20007919/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1074_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148148691/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3343/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8751/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5211/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7447/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1074_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1074_s4_0 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-549701723/2500000000 : ℝ)*x 0 + (2702686093/5000000000 : ℝ)*x 1 + (1313529579/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (549701723/2500000000 : ℝ)^8267 ≤ (13352435449793/100000000000000 : ℝ)^6219 := by
    have hnat : (549701723 : ℕ)^8267*100000000000000^6219 ≤ 13352435449793^6219*2500000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549701723 2500000000 13352435449793 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2702686093/5000000000 : ℝ)^8267 ≤ (44140931611533/100000000000000 : ℝ)^6219 := by
    have hnat : (2702686093 : ℕ)^8267*100000000000000^6219 ≤ 44140931611533^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702686093 5000000000 44140931611533 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313529579/2500000000 : ℝ)^8267 ≤ (21253316463811/50000000000000 : ℝ)^6219 := by
    have hnat : (1313529579 : ℕ)^8267*50000000000000^6219 ≤ 21253316463811^6219*2500000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313529579 2500000000 21253316463811 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-549701723/2500000000 : ℝ), (2702686093/5000000000 : ℝ), (1313529579/2500000000 : ℝ)] ![(13352435449793/100000000000000 : ℝ), (44140931611533/100000000000000 : ℝ), (21253316463811/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-549701723/2500000000 : ℝ)|^8267 ≤ (13352435449793/100000000000000 : ℝ)^6219
        have hw : |(-549701723/2500000000 : ℝ)|=(549701723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2702686093/5000000000 : ℝ)|^8267 ≤ (44140931611533/100000000000000 : ℝ)^6219
        have hw : |(2702686093/5000000000 : ℝ)|=(2702686093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313529579/2500000000 : ℝ)|^8267 ≤ (21253316463811/50000000000000 : ℝ)^6219
        have hw : |(1313529579/2500000000 : ℝ)|=(1313529579/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s4_1 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5347740371/10000000000 : ℝ)*x 0 + (-2275731461/10000000000 : ℝ)*x 1 + (1313529559/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347740371/10000000000 : ℝ)^8267 ≤ (8703283964611/20000000000000 : ℝ)^6219 := by
    have hnat : (5347740371 : ℕ)^8267*20000000000000^6219 ≤ 8703283964611^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347740371 10000000000 8703283964611 20000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2275731461/10000000000 : ℝ)^8267 ≤ (3494237022583/25000000000000 : ℝ)^6219 := by
    have hnat : (2275731461 : ℕ)^8267*25000000000000^6219 ≤ 3494237022583^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2275731461 10000000000 3494237022583 25000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313529559/2500000000 : ℝ)^8267 ≤ (21253316033637/50000000000000 : ℝ)^6219 := by
    have hnat : (1313529559 : ℕ)^8267*50000000000000^6219 ≤ 21253316033637^6219*2500000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313529559 2500000000 21253316033637 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347740371/10000000000 : ℝ), (-2275731461/10000000000 : ℝ), (1313529559/2500000000 : ℝ)] ![(8703283964611/20000000000000 : ℝ), (3494237022583/25000000000000 : ℝ), (21253316033637/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347740371/10000000000 : ℝ)|^8267 ≤ (8703283964611/20000000000000 : ℝ)^6219
        have hw : |(5347740371/10000000000 : ℝ)|=(5347740371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2275731461/10000000000 : ℝ)|^8267 ≤ (3494237022583/25000000000000 : ℝ)^6219
        have hw : |(-2275731461/10000000000 : ℝ)|=(2275731461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313529559/2500000000 : ℝ)|^8267 ≤ (21253316033637/50000000000000 : ℝ)^6219
        have hw : |(1313529559/2500000000 : ℝ)|=(1313529559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s4_2 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2673870253/5000000000 : ℝ)*x 0 + (2627059111/5000000000 : ℝ)*x 1 + (-1137865651/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673870253/5000000000 : ℝ)^8267 ≤ (21758210641681/50000000000000 : ℝ)^6219 := by
    have hnat : (2673870253 : ℕ)^8267*50000000000000^6219 ≤ 21758210641681^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673870253 5000000000 21758210641681 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2627059111/5000000000 : ℝ)^8267 ≤ (42506631916713/100000000000000 : ℝ)^6219 := by
    have hnat : (2627059111 : ℕ)^8267*100000000000000^6219 ≤ 42506631916713^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627059111 5000000000 42506631916713 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1137865651/5000000000 : ℝ)^8267 ≤ (13976946792209/100000000000000 : ℝ)^6219 := by
    have hnat : (1137865651 : ℕ)^8267*100000000000000^6219 ≤ 13976946792209^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1137865651 5000000000 13976946792209 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673870253/5000000000 : ℝ), (2627059111/5000000000 : ℝ), (-1137865651/5000000000 : ℝ)] ![(21758210641681/50000000000000 : ℝ), (42506631916713/100000000000000 : ℝ), (13976946792209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673870253/5000000000 : ℝ)|^8267 ≤ (21758210641681/50000000000000 : ℝ)^6219
        have hw : |(2673870253/5000000000 : ℝ)|=(2673870253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2627059111/5000000000 : ℝ)|^8267 ≤ (42506631916713/100000000000000 : ℝ)^6219
        have hw : |(2627059111/5000000000 : ℝ)|=(2627059111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1137865651/5000000000 : ℝ)|^8267 ≤ (13976946792209/100000000000000 : ℝ)^6219
        have hw : |(-1137865651/5000000000 : ℝ)|=(1137865651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s4_3 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4373745609/10000000000 : ℝ)*x 0 + (2113919101/5000000000 : ℝ)*x 1 + (1131186393/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4373745609/10000000000 : ℝ)^8267 ≤ (1665527382549/5000000000000 : ℝ)^6219 := by
    have hnat : (4373745609 : ℕ)^8267*5000000000000^6219 ≤ 1665527382549^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4373745609 10000000000 1665527382549 5000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2113919101/5000000000 : ℝ)^8267 ≤ (3184154456073/10000000000000 : ℝ)^6219 := by
    have hnat : (2113919101 : ℕ)^8267*10000000000000^6219 ≤ 3184154456073^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113919101 5000000000 3184154456073 10000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1131186393/2500000000 : ℝ)^8267 ≤ (2177994235773/6250000000000 : ℝ)^6219 := by
    have hnat : (1131186393 : ℕ)^8267*6250000000000^6219 ≤ 2177994235773^6219*2500000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131186393 2500000000 2177994235773 6250000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4373745609/10000000000 : ℝ), (2113919101/5000000000 : ℝ), (1131186393/2500000000 : ℝ)] ![(1665527382549/5000000000000 : ℝ), (3184154456073/10000000000000 : ℝ), (2177994235773/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4373745609/10000000000 : ℝ)|^8267 ≤ (1665527382549/5000000000000 : ℝ)^6219
        have hw : |(4373745609/10000000000 : ℝ)|=(4373745609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2113919101/5000000000 : ℝ)|^8267 ≤ (3184154456073/10000000000000 : ℝ)^6219
        have hw : |(2113919101/5000000000 : ℝ)|=(2113919101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1131186393/2500000000 : ℝ)|^8267 ≤ (2177994235773/6250000000000 : ℝ)^6219
        have hw : |(1131186393/2500000000 : ℝ)|=(1131186393/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s4_4 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-549703787/2500000000 : ℝ)*x 0 + (5254560063/10000000000 : ℝ)*x 1 + (1351232099/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (549703787/2500000000 : ℝ)^8267 ≤ (6676251047639/50000000000000 : ℝ)^6219 := by
    have hnat : (549703787 : ℕ)^8267*50000000000000^6219 ≤ 6676251047639^6219*2500000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549703787 2500000000 6676251047639 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5254560063/10000000000 : ℝ)^8267 ≤ (42511383696011/100000000000000 : ℝ)^6219 := by
    have hnat : (5254560063 : ℕ)^8267*100000000000000^6219 ≤ 42511383696011^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254560063 10000000000 42511383696011 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351232099/2500000000 : ℝ)^8267 ≤ (11034028546767/25000000000000 : ℝ)^6219 := by
    have hnat : (1351232099 : ℕ)^8267*25000000000000^6219 ≤ 11034028546767^6219*2500000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351232099 2500000000 11034028546767 25000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-549703787/2500000000 : ℝ), (5254560063/10000000000 : ℝ), (1351232099/2500000000 : ℝ)] ![(6676251047639/50000000000000 : ℝ), (42511383696011/100000000000000 : ℝ), (11034028546767/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-549703787/2500000000 : ℝ)|^8267 ≤ (6676251047639/50000000000000 : ℝ)^6219
        have hw : |(-549703787/2500000000 : ℝ)|=(549703787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5254560063/10000000000 : ℝ)|^8267 ≤ (42511383696011/100000000000000 : ℝ)^6219
        have hw : |(5254560063/10000000000 : ℝ)|=(5254560063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351232099/2500000000 : ℝ)|^8267 ≤ (11034028546767/25000000000000 : ℝ)^6219
        have hw : |(1351232099/2500000000 : ℝ)|=(1351232099/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s4_5 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2654810177/5000000000 : ℝ)*x 0 + (-424984239/2000000000 : ℝ)*x 1 + (5404928431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2654810177/5000000000 : ℝ)^8267 ≤ (43104557127509/100000000000000 : ℝ)^6219 := by
    have hnat : (2654810177 : ℕ)^8267*100000000000000^6219 ≤ 43104557127509^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2654810177 5000000000 43104557127509 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (424984239/2000000000 : ℝ)^8267 ≤ (12759328296343/100000000000000 : ℝ)^6219 := by
    have hnat : (424984239 : ℕ)^8267*100000000000000^6219 ≤ 12759328296343^6219*2000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424984239 2000000000 12759328296343 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5404928431/10000000000 : ℝ)^8267 ≤ (22068057283497/50000000000000 : ℝ)^6219 := by
    have hnat : (5404928431 : ℕ)^8267*50000000000000^6219 ≤ 22068057283497^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404928431 10000000000 22068057283497 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2654810177/5000000000 : ℝ), (-424984239/2000000000 : ℝ), (5404928431/10000000000 : ℝ)] ![(43104557127509/100000000000000 : ℝ), (12759328296343/100000000000000 : ℝ), (22068057283497/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2654810177/5000000000 : ℝ)|^8267 ≤ (43104557127509/100000000000000 : ℝ)^6219
        have hw : |(2654810177/5000000000 : ℝ)|=(2654810177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-424984239/2000000000 : ℝ)|^8267 ≤ (12759328296343/100000000000000 : ℝ)^6219
        have hw : |(-424984239/2000000000 : ℝ)|=(424984239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5404928431/10000000000 : ℝ)|^8267 ≤ (22068057283497/50000000000000 : ℝ)^6219
        have hw : |(5404928431/10000000000 : ℝ)|=(5404928431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s4_6 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5309620387/10000000000 : ℝ)*x 0 + (5404928401/10000000000 : ℝ)*x 1 + (-212492119/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309620387/10000000000 : ℝ)^8267 ≤ (43104557483633/100000000000000 : ℝ)^6219 := by
    have hnat : (5309620387 : ℕ)^8267*100000000000000^6219 ≤ 43104557483633^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309620387 10000000000 43104557483633 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5404928401/10000000000 : ℝ)^8267 ≤ (44136114241343/100000000000000 : ℝ)^6219 := by
    have hnat : (5404928401 : ℕ)^8267*100000000000000^6219 ≤ 44136114241343^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404928401 10000000000 44136114241343 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (212492119/1000000000 : ℝ)^8267 ≤ (12759328256433/100000000000000 : ℝ)^6219 := by
    have hnat : (212492119 : ℕ)^8267*100000000000000^6219 ≤ 12759328256433^6219*1000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212492119 1000000000 12759328256433 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309620387/10000000000 : ℝ), (5404928401/10000000000 : ℝ), (-212492119/1000000000 : ℝ)] ![(43104557483633/100000000000000 : ℝ), (44136114241343/100000000000000 : ℝ), (12759328256433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309620387/10000000000 : ℝ)|^8267 ≤ (43104557483633/100000000000000 : ℝ)^6219
        have hw : |(5309620387/10000000000 : ℝ)|=(5309620387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5404928401/10000000000 : ℝ)|^8267 ≤ (44136114241343/100000000000000 : ℝ)^6219
        have hw : |(5404928401/10000000000 : ℝ)|=(5404928401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-212492119/1000000000 : ℝ)|^8267 ≤ (12759328256433/100000000000000 : ℝ)^6219
        have hw : |(-212492119/1000000000 : ℝ)|=(212492119/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s4_7 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4373761103/10000000000 : ℝ)*x 0 + (226193919/500000000 : ℝ)*x 1 + (4228709269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4373761103/10000000000 : ℝ)^8267 ≤ (33310704513591/100000000000000 : ℝ)^6219 := by
    have hnat : (4373761103 : ℕ)^8267*100000000000000^6219 ≤ 33310704513591^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4373761103 10000000000 33310704513591 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (226193919/500000000 : ℝ)^8267 ≤ (8709757461787/25000000000000 : ℝ)^6219 := by
    have hnat : (226193919 : ℕ)^8267*25000000000000^6219 ≤ 8709757461787^6219*500000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226193919 500000000 8709757461787 25000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4228709269/10000000000 : ℝ)^8267 ≤ (3981283203011/12500000000000 : ℝ)^6219 := by
    have hnat : (4228709269 : ℕ)^8267*12500000000000^6219 ≤ 3981283203011^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228709269 10000000000 3981283203011 12500000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4373761103/10000000000 : ℝ), (226193919/500000000 : ℝ), (4228709269/10000000000 : ℝ)] ![(33310704513591/100000000000000 : ℝ), (8709757461787/25000000000000 : ℝ), (3981283203011/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4373761103/10000000000 : ℝ)|^8267 ≤ (33310704513591/100000000000000 : ℝ)^6219
        have hw : |(4373761103/10000000000 : ℝ)|=(4373761103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(226193919/500000000 : ℝ)|^8267 ≤ (8709757461787/25000000000000 : ℝ)^6219
        have hw : |(226193919/500000000 : ℝ)|=(226193919/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4228709269/10000000000 : ℝ)|^8267 ≤ (3981283203011/12500000000000 : ℝ)^6219
        have hw : |(4228709269/10000000000 : ℝ)|=(4228709269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1074_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148148691/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7447/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5211/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11039/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7121/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7447/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5211/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7447/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5211/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7447/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5211/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7447/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5211/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7447/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5211/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7447/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5211/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5211/50000 : ℝ) ^ (4133/1024 : ℝ) ≤ (10872266404513059/100000000000000000000 : ℝ) := by
    have hpowers : (5211/50000 : ℝ)^4133 ≤ (10872266404513059/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5211 : ℕ)^4133*100000000000000000000^1024 ≤ 10872266404513059^1024*50000^4133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5211 50000 10872266404513059 100000000000000000000 4133 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5211/50000 : ℝ)) (X := (10872266404513059/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7447/50000 : ℝ) ^ (4133/1024 : ℝ) ≤ (22968571016342959/50000000000000000000 : ℝ) := by
    have hpowers : (7447/50000 : ℝ)^4133 ≤ (22968571016342959/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7447 : ℕ)^4133*50000000000000000000^1024 ≤ 22968571016342959^1024*50000^4133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7447 50000 22968571016342959 50000000000000000000 4133 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7447/50000 : ℝ)) (X := (22968571016342959/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010872266404513059/50000000000000000000 : ℝ) ≤ (2500134675663941/2500000000000000 : ℝ) ^ (4133/1024 : ℝ) := by
    have hpowers : (50010872266404513059/50000000000000000000 : ℝ)^1024 ≤ (2500134675663941/2500000000000000 : ℝ)^4133 := by
      have hnat : (50010872266404513059 : ℕ)^1024*2500000000000000^4133 ≤ 2500134675663941^4133*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010872266404513059 50000000000000000000 2500134675663941 2500000000000000 1024 4133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500134675663941/2500000000000000 : ℝ)) (X := (50010872266404513059/50000000000000000000 : ℝ)) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100056809408437198977/100000000000000000000 : ℝ) ≤ (2500351805035777/2500000000000000 : ℝ) ^ (4133/1024 : ℝ) := by
    have hpowers : (100056809408437198977/100000000000000000000 : ℝ)^1024 ≤ (2500351805035777/2500000000000000 : ℝ)^4133 := by
      have hnat : (100056809408437198977 : ℕ)^1024*2500000000000000^4133 ≤ 2500351805035777^4133*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100056809408437198977 100000000000000000000 2500351805035777 2500000000000000 1024 4133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500351805035777/2500000000000000 : ℝ)) (X := (100056809408437198977/100000000000000000000 : ℝ)) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25022968571016342959/25000000000000000000 : ℝ) ≤ (2500568934407613/2500000000000000 : ℝ) ^ (4133/1024 : ℝ) := by
    have hpowers : (25022968571016342959/25000000000000000000 : ℝ)^1024 ≤ (2500568934407613/2500000000000000 : ℝ)^4133 := by
      have hnat : (25022968571016342959 : ℕ)^1024*2500000000000000^4133 ≤ 2500568934407613^4133*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25022968571016342959 25000000000000000000 2500568934407613 2500000000000000 1024 4133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500568934407613/2500000000000000 : ℝ)) (X := (25022968571016342959/25000000000000000000 : ℝ)) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10872266404513059/100000000000000000000 : ℝ) ≤ ((107462273316755717/107500000000000000 : ℝ)+2*(4175564843/2150000000000 : ℝ)*(5211/50000 : ℝ))^(4133/1024 : ℝ) := by
    rw [show (107462273316755717/107500000000000000 : ℝ)+2*(4175564843/2150000000000 : ℝ)*(5211/50000 : ℝ)=(2500134675663941/2500000000000000 : ℝ) by norm_num, show 1+2*(10872266404513059/100000000000000000000 : ℝ)=(50010872266404513059/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(22968571016342959/50000000000000000000 : ℝ)+(10872266404513059/100000000000000000000 : ℝ) ≤ ((107462273316755717/107500000000000000 : ℝ)+(4175564843/2150000000000 : ℝ)*((7447/50000 : ℝ)+(5211/50000 : ℝ)))^(4133/1024 : ℝ) := by
    rw [show (107462273316755717/107500000000000000 : ℝ)+(4175564843/2150000000000 : ℝ)*((7447/50000 : ℝ)+(5211/50000 : ℝ))=(2500351805035777/2500000000000000 : ℝ) by norm_num, show 1+(22968571016342959/50000000000000000000 : ℝ)+(10872266404513059/100000000000000000000 : ℝ)=(100056809408437198977/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(22968571016342959/50000000000000000000 : ℝ) ≤ ((107462273316755717/107500000000000000 : ℝ)+2*(4175564843/2150000000000 : ℝ)*(7447/50000 : ℝ))^(4133/1024 : ℝ) := by
    rw [show (107462273316755717/107500000000000000 : ℝ)+2*(4175564843/2150000000000 : ℝ)*(7447/50000 : ℝ)=(2500568934407613/2500000000000000 : ℝ) by norm_num, show 1+2*(22968571016342959/50000000000000000000 : ℝ)=(25022968571016342959/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (107462273316755717/107500000000000000 : ℝ)*(X 1 0+X 2 0)+(4175564843/2150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4133/1024 : ℝ)) (lo := (5211/50000 : ℝ)) (hi := (7447/50000 : ℝ)) (c := (107462273316755717/107500000000000000 : ℝ)) (alpha := (4175564843/2150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (107462273316755717/107500000000000000 : ℝ)*(X 0 1+X 2 1)+(4175564843/2150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4133/1024 : ℝ)) (lo := (5211/50000 : ℝ)) (hi := (7447/50000 : ℝ)) (c := (107462273316755717/107500000000000000 : ℝ)) (alpha := (4175564843/2150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (107462273316755717/107500000000000000 : ℝ)*(X 0 2+X 1 2)+(4175564843/2150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4133/1024 : ℝ)) (lo := (5211/50000 : ℝ)) (hi := (7447/50000 : ℝ)) (c := (107462273316755717/107500000000000000 : ℝ)) (alpha := (4175564843/2150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-549701723/2500000000 : ℝ)*X 0 0+(2702686093/5000000000 : ℝ)*X 0 1+(1313529579/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347740371/10000000000 : ℝ)*X 1 0+(-2275731461/10000000000 : ℝ)*X 1 1+(1313529559/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673870253/5000000000 : ℝ)*X 2 0+(2627059111/5000000000 : ℝ)*X 2 1+(-1137865651/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4373745609/10000000000 : ℝ)*X 0 0+(2113919101/5000000000 : ℝ)*X 0 1+(1131186393/2500000000 : ℝ)*X 0 2+(4373745609/10000000000 : ℝ)*X 1 0+(2113919101/5000000000 : ℝ)*X 1 1+(1131186393/2500000000 : ℝ)*X 1 2+(4373745609/10000000000 : ℝ)*X 2 0+(2113919101/5000000000 : ℝ)*X 2 1+(1131186393/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-549703787/2500000000 : ℝ)*X 0 0+(5254560063/10000000000 : ℝ)*X 0 1+(1351232099/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2654810177/5000000000 : ℝ)*X 1 0+(-424984239/2000000000 : ℝ)*X 1 1+(5404928431/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5309620387/10000000000 : ℝ)*X 2 0+(5404928401/10000000000 : ℝ)*X 2 1+(-212492119/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4373761103/10000000000 : ℝ)*X 0 0+(226193919/500000000 : ℝ)*X 0 1+(4228709269/10000000000 : ℝ)*X 0 2+(4373761103/10000000000 : ℝ)*X 1 0+(226193919/500000000 : ℝ)*X 1 1+(4228709269/10000000000 : ℝ)*X 1 2+(4373761103/10000000000 : ℝ)*X 2 0+(226193919/500000000 : ℝ)*X 2 1+(4228709269/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (40645397911206963248802729/5375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (251738091/20000000000000 : ℝ)*(base19) + (183356367/20000000000000 : ℝ)*(base23) + (272098391/100000000000000 : ℝ)*(lower2) + (34040469/20000000000000 : ℝ)*(upper3) + (17038447/50000000000000 : ℝ)*(upper5) + (4989763126509293/100000000000000 : ℝ)*(major0) + (4989763126509293/100000000000000 : ℝ)*(major1) + (4989763126509293/100000000000000 : ℝ)*(major2) + (826427926877421/12500000000000 : ℝ)*(sp0) + (1652861743337207/25000000000000 : ℝ)*(sp1) + (826430914407181/12500000000000 : ℝ)*(sp2) + (842015748995359/25000000000000 : ℝ)*(sp3) + (12408509957/50000000000000 : ℝ)*(sp4) + (14772933373/100000000000000 : ℝ)*(sp7) + (421009721114351/12500000000000 : ℝ)*(f.failure) + (3305724116019641/50000000000000 : ℝ)*(f.sum) + (1887761962227/215000000000000000000000000 : ℝ)*base66 + (131218027440171919/10750000000000000000000000000000 : ℝ)*base68 + (31685616969421919/10750000000000000000000000000000 : ℝ)*base70 + (135249850296921919/10750000000000000000000000000000 : ℝ)*base72 + (932695895181/107500000000000000000000000 : ℝ)*base74 + (192982972611421919/10750000000000000000000000000000 : ℝ)*base76 + (220461375421921919/10750000000000000000000000000000 : ℝ)*base78 + (98316840019671919/10750000000000000000000000000000 : ℝ)*base80 + (721965008903/215000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (535459/1250000000000000000000 : ℝ)*base90 + (535459/1250000000000000000000 : ℝ)*base92 + (535459/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6156822200935024213401063/671875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (788600441/50000000000000 : ℝ)*(base19) + (1719285439/100000000000000 : ℝ)*(base23) + (177748193/100000000000000 : ℝ)*(upper3) + (43786861/100000000000000 : ℝ)*(lower4) + (87392173/50000000000000 : ℝ)*(upper5) + (313694511523131/6250000000000 : ℝ)*(major0) + (313694511523131/6250000000000 : ℝ)*(major1) + (313694511523131/6250000000000 : ℝ)*(major2) + (236333109/625000000000 : ℝ)*(sp1) + (20180012531/50000000000000 : ℝ)*(sp2) + (6650335752905363/100000000000000 : ℝ)*(sp4) + (10391088066261/156250000000 : ℝ)*(sp5) + (3325146836797431/50000000000000 : ℝ)*(sp6) + (3387888310380073/100000000000000 : ℝ)*(sp7) + (3387888310380073/100000000000000 : ℝ)*(f.failure) + (6650335752905363/100000000000000 : ℝ)*(f.sum) + (253260983931/215000000000000000000000000 : ℝ)*base65 + (84758982835763/167968750000000000000000000000 : ℝ)*base67 + (1533062008742013/167968750000000000000000000000 : ℝ)*base69 + (1563215177531599/335937500000000000000000000000 : ℝ)*base72 + (242881696661/53750000000000000000000000 : ℝ)*base74 + (466528678692361/20996093750000000000000000000 : ℝ)*base75 + (176520973693403/41992187500000000000000000000 : ℝ)*base78 + (10159135697733677/671875000000000000000000000000 : ℝ)*base79 + (788112541261/215000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (72565557/10000000000000000000000 : ℝ)*base90 + (72565557/10000000000000000000000 : ℝ)*base92 + (72565557/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1074_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148148691/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7447/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5211/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11039/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7121/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1074_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1074_s5_0 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1099805247/5000000000 : ℝ)*x 0 + (1349192553/2500000000 : ℝ)*x 1 + (5262193513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1099805247/5000000000 : ℝ)^8267 ≤ (3339730702151/25000000000000 : ℝ)^6219 := by
    have hnat : (1099805247 : ℕ)^8267*25000000000000^6219 ≤ 3339730702151^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099805247 5000000000 3339730702151 25000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349192553/2500000000 : ℝ)^8267 ≤ (44047578769363/100000000000000 : ℝ)^6219 := by
    have hnat : (1349192553 : ℕ)^8267*100000000000000^6219 ≤ 44047578769363^6219*2500000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349192553 2500000000 44047578769363 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5262193513/10000000000 : ℝ)^8267 ≤ (21296749203071/50000000000000 : ℝ)^6219 := by
    have hnat : (5262193513 : ℕ)^8267*50000000000000^6219 ≤ 21296749203071^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262193513 10000000000 21296749203071 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1099805247/5000000000 : ℝ), (1349192553/2500000000 : ℝ), (5262193513/10000000000 : ℝ)] ![(3339730702151/25000000000000 : ℝ), (44047578769363/100000000000000 : ℝ), (21296749203071/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1099805247/5000000000 : ℝ)|^8267 ≤ (3339730702151/25000000000000 : ℝ)^6219
        have hw : |(-1099805247/5000000000 : ℝ)|=(1099805247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1349192553/2500000000 : ℝ)|^8267 ≤ (44047578769363/100000000000000 : ℝ)^6219
        have hw : |(1349192553/2500000000 : ℝ)|=(1349192553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5262193513/10000000000 : ℝ)|^8267 ≤ (21296749203071/50000000000000 : ℝ)^6219
        have hw : |(5262193513/10000000000 : ℝ)|=(5262193513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s5_1 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672799019/5000000000 : ℝ)*x 0 + (-28349087/125000000 : ℝ)*x 1 + (1052438483/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672799019/5000000000 : ℝ)^8267 ≤ (43493247554593/100000000000000 : ℝ)^6219 := by
    have hnat : (2672799019 : ℕ)^8267*100000000000000^6219 ≤ 43493247554593^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672799019 5000000000 43493247554593 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (28349087/125000000 : ℝ)^8267 ≤ (278265316909/2000000000000 : ℝ)^6219 := by
    have hnat : (28349087 : ℕ)^8267*2000000000000^6219 ≤ 278265316909^6219*125000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28349087 125000000 278265316909 2000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052438483/2000000000 : ℝ)^8267 ≤ (42593486591891/100000000000000 : ℝ)^6219 := by
    have hnat : (1052438483 : ℕ)^8267*100000000000000^6219 ≤ 42593486591891^6219*2000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052438483 2000000000 42593486591891 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672799019/5000000000 : ℝ), (-28349087/125000000 : ℝ), (1052438483/2000000000 : ℝ)] ![(43493247554593/100000000000000 : ℝ), (278265316909/2000000000000 : ℝ), (42593486591891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672799019/5000000000 : ℝ)|^8267 ≤ (43493247554593/100000000000000 : ℝ)^6219
        have hw : |(2672799019/5000000000 : ℝ)|=(2672799019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-28349087/125000000 : ℝ)|^8267 ≤ (278265316909/2000000000000 : ℝ)^6219
        have hw : |(-28349087/125000000 : ℝ)|=(28349087/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052438483/2000000000 : ℝ)|^8267 ≤ (42593486591891/100000000000000 : ℝ)^6219
        have hw : |(1052438483/2000000000 : ℝ)|=(1052438483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s5_2 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1069119559/2000000000 : ℝ)*x 0 + (2631096681/5000000000 : ℝ)*x 1 + (-141745377/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069119559/2000000000 : ℝ)^8267 ≤ (43493244926389/100000000000000 : ℝ)^6219 := by
    have hnat : (1069119559 : ℕ)^8267*100000000000000^6219 ≤ 43493244926389^6219*2000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069119559 2000000000 43493244926389 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631096681/5000000000 : ℝ)^8267 ≤ (42593496781413/100000000000000 : ℝ)^6219 := by
    have hnat : (2631096681 : ℕ)^8267*100000000000000^6219 ≤ 42593496781413^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631096681 5000000000 42593496781413 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (141745377/625000000 : ℝ)^8267 ≤ (13913258277551/100000000000000 : ℝ)^6219 := by
    have hnat : (141745377 : ℕ)^8267*100000000000000^6219 ≤ 13913258277551^6219*625000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141745377 625000000 13913258277551 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069119559/2000000000 : ℝ), (2631096681/5000000000 : ℝ), (-141745377/625000000 : ℝ)] ![(43493244926389/100000000000000 : ℝ), (42593496781413/100000000000000 : ℝ), (13913258277551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069119559/2000000000 : ℝ)|^8267 ≤ (43493244926389/100000000000000 : ℝ)^6219
        have hw : |(1069119559/2000000000 : ℝ)|=(1069119559/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631096681/5000000000 : ℝ)|^8267 ≤ (42593496781413/100000000000000 : ℝ)^6219
        have hw : |(2631096681/5000000000 : ℝ)|=(2631096681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-141745377/625000000 : ℝ)|^8267 ≤ (13913258277551/100000000000000 : ℝ)^6219
        have hw : |(-141745377/625000000 : ℝ)|=(141745377/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s5_3 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4374213993/10000000000 : ℝ)*x 0 + (265259053/625000000 : ℝ)*x 1 + (4508316213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4374213993/10000000000 : ℝ)^8267 ≤ (83288224231/250000000000 : ℝ)^6219 := by
    have hnat : (4374213993 : ℕ)^8267*250000000000^6219 ≤ 83288224231^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4374213993 10000000000 83288224231 250000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (265259053/625000000 : ℝ)^8267 ≤ (32004903639927/100000000000000 : ℝ)^6219 := by
    have hnat : (265259053 : ℕ)^8267*100000000000000^6219 ≤ 32004903639927^6219*625000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265259053 625000000 32004903639927 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4508316213/10000000000 : ℝ)^8267 ≤ (34679806653001/100000000000000 : ℝ)^6219 := by
    have hnat : (4508316213 : ℕ)^8267*100000000000000^6219 ≤ 34679806653001^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508316213 10000000000 34679806653001 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4374213993/10000000000 : ℝ), (265259053/625000000 : ℝ), (4508316213/10000000000 : ℝ)] ![(83288224231/250000000000 : ℝ), (32004903639927/100000000000000 : ℝ), (34679806653001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4374213993/10000000000 : ℝ)|^8267 ≤ (83288224231/250000000000 : ℝ)^6219
        have hw : |(4374213993/10000000000 : ℝ)|=(4374213993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(265259053/625000000 : ℝ)|^8267 ≤ (32004903639927/100000000000000 : ℝ)^6219
        have hw : |(265259053/625000000 : ℝ)|=(265259053/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4508316213/10000000000 : ℝ)|^8267 ≤ (34679806653001/100000000000000 : ℝ)^6219
        have hw : |(4508316213/10000000000 : ℝ)|=(4508316213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s5_4 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-219961609/1000000000 : ℝ)*x 0 + (1315635803/2500000000 : ℝ)*x 1 + (5396419237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (219961609/1000000000 : ℝ)^8267 ≤ (3339741996753/25000000000000 : ℝ)^6219 := by
    have hnat : (219961609 : ℕ)^8267*25000000000000^6219 ≤ 3339741996753^6219*1000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219961609 1000000000 3339741996753 25000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315635803/2500000000 : ℝ)^8267 ≤ (8519452227167/20000000000000 : ℝ)^6219 := by
    have hnat : (1315635803 : ℕ)^8267*20000000000000^6219 ≤ 8519452227167^6219*2500000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315635803 2500000000 8519452227167 20000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396419237/10000000000 : ℝ)^8267 ≤ (44043770856279/100000000000000 : ℝ)^6219 := by
    have hnat : (5396419237 : ℕ)^8267*100000000000000^6219 ≤ 44043770856279^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396419237 10000000000 44043770856279 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-219961609/1000000000 : ℝ), (1315635803/2500000000 : ℝ), (5396419237/10000000000 : ℝ)] ![(3339741996753/25000000000000 : ℝ), (8519452227167/20000000000000 : ℝ), (44043770856279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-219961609/1000000000 : ℝ)|^8267 ≤ (3339741996753/25000000000000 : ℝ)^6219
        have hw : |(-219961609/1000000000 : ℝ)|=(219961609/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315635803/2500000000 : ℝ)|^8267 ≤ (8519452227167/20000000000000 : ℝ)^6219
        have hw : |(1315635803/2500000000 : ℝ)|=(1315635803/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396419237/10000000000 : ℝ)|^8267 ≤ (44043770856279/100000000000000 : ℝ)^6219
        have hw : |(5396419237/10000000000 : ℝ)|=(5396419237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s5_5 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1327919839/2500000000 : ℝ)*x 0 + (-533425073/2500000000 : ℝ)*x 1 + (5396419219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327919839/2500000000 : ℝ)^8267 ≤ (43126778536581/100000000000000 : ℝ)^6219 := by
    have hnat : (1327919839 : ℕ)^8267*100000000000000^6219 ≤ 43126778536581^6219*2500000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327919839 2500000000 43126778536581 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (533425073/2500000000 : ℝ)^8267 ≤ (6414725389217/50000000000000 : ℝ)^6219 := by
    have hnat : (533425073 : ℕ)^8267*50000000000000^6219 ≤ 6414725389217^6219*2500000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533425073 2500000000 6414725389217 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396419219/10000000000 : ℝ)^8267 ≤ (4404377066099/10000000000000 : ℝ)^6219 := by
    have hnat : (5396419219 : ℕ)^8267*10000000000000^6219 ≤ 4404377066099^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396419219 10000000000 4404377066099 10000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327919839/2500000000 : ℝ), (-533425073/2500000000 : ℝ), (5396419219/10000000000 : ℝ)] ![(43126778536581/100000000000000 : ℝ), (6414725389217/50000000000000 : ℝ), (4404377066099/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327919839/2500000000 : ℝ)|^8267 ≤ (43126778536581/100000000000000 : ℝ)^6219
        have hw : |(1327919839/2500000000 : ℝ)|=(1327919839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-533425073/2500000000 : ℝ)|^8267 ≤ (6414725389217/50000000000000 : ℝ)^6219
        have hw : |(-533425073/2500000000 : ℝ)|=(533425073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396419219/10000000000 : ℝ)|^8267 ≤ (4404377066099/10000000000000 : ℝ)^6219
        have hw : |(5396419219/10000000000 : ℝ)|=(5396419219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s5_6 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (331979959/625000000 : ℝ)*x 0 + (2698209619/5000000000 : ℝ)*x 1 + (-2133700283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331979959/625000000 : ℝ)^8267 ≤ (8625355681413/20000000000000 : ℝ)^6219 := by
    have hnat : (331979959 : ℕ)^8267*20000000000000^6219 ≤ 8625355681413^6219*625000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331979959 625000000 8625355681413 20000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698209619/5000000000 : ℝ)^8267 ≤ (44043770867129/100000000000000 : ℝ)^6219 := by
    have hnat : (2698209619 : ℕ)^8267*100000000000000^6219 ≤ 44043770867129^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698209619 5000000000 44043770867129 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2133700283/10000000000 : ℝ)^8267 ≤ (12829450706499/100000000000000 : ℝ)^6219 := by
    have hnat : (2133700283 : ℕ)^8267*100000000000000^6219 ≤ 12829450706499^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133700283 10000000000 12829450706499 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331979959/625000000 : ℝ), (2698209619/5000000000 : ℝ), (-2133700283/10000000000 : ℝ)] ![(8625355681413/20000000000000 : ℝ), (44043770867129/100000000000000 : ℝ), (12829450706499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331979959/625000000 : ℝ)|^8267 ≤ (8625355681413/20000000000000 : ℝ)^6219
        have hw : |(331979959/625000000 : ℝ)|=(331979959/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698209619/5000000000 : ℝ)|^8267 ≤ (44043770867129/100000000000000 : ℝ)^6219
        have hw : |(2698209619/5000000000 : ℝ)|=(2698209619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2133700283/10000000000 : ℝ)|^8267 ≤ (12829450706499/100000000000000 : ℝ)^6219
        have hw : |(-2133700283/10000000000 : ℝ)|=(2133700283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s5_7 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (136694537/312500000 : ℝ)*x 0 + (4507629337/10000000000 : ℝ)*x 1 + (4244834181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136694537/312500000 : ℝ)^8267 ≤ (33315402995039/100000000000000 : ℝ)^6219 := by
    have hnat : (136694537 : ℕ)^8267*100000000000000^6219 ≤ 33315402995039^6219*312500000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136694537 312500000 33315402995039 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4507629337/10000000000 : ℝ)^8267 ≤ (34672783095779/100000000000000 : ℝ)^6219 := by
    have hnat : (4507629337 : ℕ)^8267*100000000000000^6219 ≤ 34672783095779^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507629337 10000000000 34672783095779 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4244834181/10000000000 : ℝ)^8267 ≤ (32011813899973/100000000000000 : ℝ)^6219 := by
    have hnat : (4244834181 : ℕ)^8267*100000000000000^6219 ≤ 32011813899973^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244834181 10000000000 32011813899973 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(136694537/312500000 : ℝ), (4507629337/10000000000 : ℝ), (4244834181/10000000000 : ℝ)] ![(33315402995039/100000000000000 : ℝ), (34672783095779/100000000000000 : ℝ), (32011813899973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(136694537/312500000 : ℝ)|^8267 ≤ (33315402995039/100000000000000 : ℝ)^6219
        have hw : |(136694537/312500000 : ℝ)|=(136694537/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4507629337/10000000000 : ℝ)|^8267 ≤ (34672783095779/100000000000000 : ℝ)^6219
        have hw : |(4507629337/10000000000 : ℝ)|=(4507629337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4244834181/10000000000 : ℝ)|^8267 ≤ (32011813899973/100000000000000 : ℝ)^6219
        have hw : |(4244834181/10000000000 : ℝ)|=(4244834181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1074_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148148691/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7121/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11039/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11211/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7031/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7121/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11039/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7121/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11039/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7121/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11039/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7121/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11039/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7121/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11039/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7121/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11039/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11039/100000 : ℝ) ^ (4133/1024 : ℝ) ≤ (6856576047585827/50000000000000000000 : ℝ) := by
    have hpowers : (11039/100000 : ℝ)^4133 ≤ (6856576047585827/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11039 : ℕ)^4133*50000000000000000000^1024 ≤ 6856576047585827^1024*100000^4133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11039 100000 6856576047585827 50000000000000000000 4133 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11039/100000 : ℝ)) (X := (6856576047585827/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7121/50000 : ℝ) ^ (4133/1024 : ℝ) ≤ (7668846771569901/20000000000000000000 : ℝ) := by
    have hpowers : (7121/50000 : ℝ)^4133 ≤ (7668846771569901/20000000000000000000 : ℝ)^1024 := by
      have hnat : (7121 : ℕ)^4133*20000000000000000000^1024 ≤ 7668846771569901^1024*50000^4133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7121 50000 7668846771569901 20000000000000000000 4133 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7121/50000 : ℝ)) (X := (7668846771569901/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006856576047585827/25000000000000000000 : ℝ) ≤ (10000679449283309/10000000000000000 : ℝ) ^ (4133/1024 : ℝ) := by
    have hpowers : (25006856576047585827/25000000000000000000 : ℝ)^1024 ≤ (10000679449283309/10000000000000000 : ℝ)^4133 := by
      have hnat : (25006856576047585827 : ℕ)^1024*10000000000000000^4133 ≤ 10000679449283309^4133*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006856576047585827 25000000000000000000 10000679449283309 10000000000000000 1024 4133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000679449283309/10000000000000000 : ℝ)) (X := (25006856576047585827/25000000000000000000 : ℝ)) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052057385953021159/100000000000000000000 : ℝ) ≤ (10001289531310053/10000000000000000 : ℝ) ^ (4133/1024 : ℝ) := by
    have hpowers : (100052057385953021159/100000000000000000000 : ℝ)^1024 ≤ (10001289531310053/10000000000000000 : ℝ)^4133 := by
      have hnat : (100052057385953021159 : ℕ)^1024*10000000000000000^4133 ≤ 10001289531310053^4133*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052057385953021159 100000000000000000000 10001289531310053 10000000000000000 1024 4133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001289531310053/10000000000000000 : ℝ)) (X := (100052057385953021159/100000000000000000000 : ℝ)) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007668846771569901/10000000000000000000 : ℝ) ≤ (10001899613336797/10000000000000000 : ℝ) ^ (4133/1024 : ℝ) := by
    have hpowers : (10007668846771569901/10000000000000000000 : ℝ)^1024 ≤ (10001899613336797/10000000000000000 : ℝ)^4133 := by
      have hnat : (10007668846771569901 : ℕ)^1024*10000000000000000^4133 ≤ 10001899613336797^4133*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007668846771569901 10000000000000000000 10001899613336797 10000000000000000 1024 4133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001899613336797/10000000000000000 : ℝ)) (X := (10007668846771569901/10000000000000000000 : ℝ)) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6856576047585827/50000000000000000000 : ℝ) ≤ ((6403741377013596939/6406000000000000000 : ℝ)+2*(76260253343/40037500000000 : ℝ)*(11039/100000 : ℝ))^(4133/1024 : ℝ) := by
    rw [show (6403741377013596939/6406000000000000000 : ℝ)+2*(76260253343/40037500000000 : ℝ)*(11039/100000 : ℝ)=(10000679449283309/10000000000000000 : ℝ) by norm_num, show 1+2*(6856576047585827/50000000000000000000 : ℝ)=(25006856576047585827/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7668846771569901/20000000000000000000 : ℝ)+(6856576047585827/50000000000000000000 : ℝ) ≤ ((6403741377013596939/6406000000000000000 : ℝ)+(76260253343/40037500000000 : ℝ)*((7121/50000 : ℝ)+(11039/100000 : ℝ)))^(4133/1024 : ℝ) := by
    rw [show (6403741377013596939/6406000000000000000 : ℝ)+(76260253343/40037500000000 : ℝ)*((7121/50000 : ℝ)+(11039/100000 : ℝ))=(10001289531310053/10000000000000000 : ℝ) by norm_num, show 1+(7668846771569901/20000000000000000000 : ℝ)+(6856576047585827/50000000000000000000 : ℝ)=(100052057385953021159/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7668846771569901/20000000000000000000 : ℝ) ≤ ((6403741377013596939/6406000000000000000 : ℝ)+2*(76260253343/40037500000000 : ℝ)*(7121/50000 : ℝ))^(4133/1024 : ℝ) := by
    rw [show (6403741377013596939/6406000000000000000 : ℝ)+2*(76260253343/40037500000000 : ℝ)*(7121/50000 : ℝ)=(10001899613336797/10000000000000000 : ℝ) by norm_num, show 1+2*(7668846771569901/20000000000000000000 : ℝ)=(10007668846771569901/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6403741377013596939/6406000000000000000 : ℝ)*(X 1 0+X 2 0)+(76260253343/40037500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4133/1024 : ℝ)) (lo := (11039/100000 : ℝ)) (hi := (7121/50000 : ℝ)) (c := (6403741377013596939/6406000000000000000 : ℝ)) (alpha := (76260253343/40037500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6403741377013596939/6406000000000000000 : ℝ)*(X 0 1+X 2 1)+(76260253343/40037500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4133/1024 : ℝ)) (lo := (11039/100000 : ℝ)) (hi := (7121/50000 : ℝ)) (c := (6403741377013596939/6406000000000000000 : ℝ)) (alpha := (76260253343/40037500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6403741377013596939/6406000000000000000 : ℝ)*(X 0 2+X 1 2)+(76260253343/40037500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4133/1024 : ℝ)) (lo := (11039/100000 : ℝ)) (hi := (7121/50000 : ℝ)) (c := (6403741377013596939/6406000000000000000 : ℝ)) (alpha := (76260253343/40037500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1099805247/5000000000 : ℝ)*X 0 0+(1349192553/2500000000 : ℝ)*X 0 1+(5262193513/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672799019/5000000000 : ℝ)*X 1 0+(-28349087/125000000 : ℝ)*X 1 1+(1052438483/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069119559/2000000000 : ℝ)*X 2 0+(2631096681/5000000000 : ℝ)*X 2 1+(-141745377/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4374213993/10000000000 : ℝ)*X 0 0+(265259053/625000000 : ℝ)*X 0 1+(4508316213/10000000000 : ℝ)*X 0 2+(4374213993/10000000000 : ℝ)*X 1 0+(265259053/625000000 : ℝ)*X 1 1+(4508316213/10000000000 : ℝ)*X 1 2+(4374213993/10000000000 : ℝ)*X 2 0+(265259053/625000000 : ℝ)*X 2 1+(4508316213/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-219961609/1000000000 : ℝ)*X 0 0+(1315635803/2500000000 : ℝ)*X 0 1+(5396419237/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1327919839/2500000000 : ℝ)*X 1 0+(-533425073/2500000000 : ℝ)*X 1 1+(5396419219/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((331979959/625000000 : ℝ)*X 2 0+(2698209619/5000000000 : ℝ)*X 2 1+(-2133700283/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((136694537/312500000 : ℝ)*X 0 0+(4507629337/10000000000 : ℝ)*X 0 1+(4244834181/10000000000 : ℝ)*X 0 2+(136694537/312500000 : ℝ)*X 1 0+(4507629337/10000000000 : ℝ)*X 1 1+(4244834181/10000000000 : ℝ)*X 1 2+(136694537/312500000 : ℝ)*X 2 0+(4507629337/10000000000 : ℝ)*X 2 1+(4244834181/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1148198423222334315801423717/160150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (466398403/25000000000000 : ℝ)*(base19) + (870851813/50000000000000 : ℝ)*(base23) + (5346217/25000000000000 : ℝ)*(upper4) + (13718921/5000000000000 : ℝ)*(upper5) + (2804064444933701/50000000000000 : ℝ)*(major0) + (2804064444933701/50000000000000 : ℝ)*(major1) + (2804064444933701/50000000000000 : ℝ)*(major2) + (743073933072053/10000000000000 : ℝ)*(sp0) + (7430742530217871/100000000000000 : ℝ)*(sp1) + (7430782669306627/100000000000000 : ℝ)*(sp2) + (3785450161001981/100000000000000 : ℝ)*(sp3) + (45080289723/100000000000000 : ℝ)*(sp4) + (40015198771/100000000000000 : ℝ)*(sp5) + (114843693/500000000000 : ℝ)*(sp7) + (189273656487029/5000000000000 : ℝ)*(f.failure) + (3715392205505127/50000000000000 : ℝ)*(f.sum) + (39372143446443/16015000000000000000000000000 : ℝ)*base65 + (2412222158714778761/320300000000000000000000000000000 : ℝ)*base68 + (2589448335035778761/320300000000000000000000000000000 : ℝ)*base70 + (1489795436189678761/320300000000000000000000000000000 : ℝ)*base72 + (1790545017213/4003750000000000000000000000 : ℝ)*base74 + (3771581169917678761/320300000000000000000000000000000 : ℝ)*base76 + (309432515023021239/320300000000000000000000000000000 : ℝ)*base77 + (2656798448923821239/320300000000000000000000000000000 : ℝ)*base79 + (4844558617753/16015000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (5170961/500000000000000000000 : ℝ)*base90 + (5170961/500000000000000000000 : ℝ)*base92 + (5170961/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1730701197793530298440746853/160150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2031683849/100000000000000 : ℝ)*(base19) + (2202789233/100000000000000 : ℝ)*(base23) + (54491841/25000000000000 : ℝ)*(upper3) + (83360491/100000000000000 : ℝ)*(lower4) + (213873761/100000000000000 : ℝ)*(upper5) + (2818709954513509/50000000000000 : ℝ)*(major0) + (2818709954513509/50000000000000 : ℝ)*(major1) + (2818709954513509/50000000000000 : ℝ)*(major2) + (52440303781/100000000000000 : ℝ)*(sp1) + (28650971209/50000000000000 : ℝ)*(sp2) + (7469594962602893/100000000000000 : ℝ)*(sp4) + (1493908098123053/20000000000000 : ℝ)*(sp5) + (7469535457871243/100000000000000 : ℝ)*(sp6) + (237827780951631/6250000000000 : ℝ)*(sp7) + (237827780951631/6250000000000 : ℝ)*(f.failure) + (7469594962602893/100000000000000 : ℝ)*(f.sum) + (58083382967009/8007500000000000000000000000 : ℝ)*base66 + (1794086790690068951/320300000000000000000000000000000 : ℝ)*base67 + (1402600324205368951/320300000000000000000000000000000 : ℝ)*base69 + (4674775932394131049/320300000000000000000000000000000 : ℝ)*base72 + (3413779349803/4003750000000000000000000000 : ℝ)*base73 + (31621882627331049/320300000000000000000000000000000 : ℝ)*base76 + (2706827711839331049/320300000000000000000000000000000 : ℝ)*base78 + (623950743140131049/320300000000000000000000000000000 : ℝ)*base80 + (64222239369927/16015000000000000000000000000 : ℝ)*base81 + (1/50000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (4465021/625000000000000000000 : ℝ)*base89 + (4465021/625000000000000000000 : ℝ)*base91 + (4465021/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1074_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148148691/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7121/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11039/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11211/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7031/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1074_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1074_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148148691/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3343/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8751/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11211/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7031/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1074_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1074_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1074_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148148691/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3343/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8751/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11211/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7031/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1074_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
