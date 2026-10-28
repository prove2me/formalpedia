-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1193_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:00:13.622663+00:00
-- url     : https://prove2.me/submissions/38188656-9c58-4393-8f12-439ff305f449

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
theorem support_rectangle_w1193_s0_0 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1875773857/10000000000 : ℝ)*x 0 + (6042617387/10000000000 : ℝ)*x 1 + (957377713/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1875773857/10000000000 : ℝ)^4193 ≤ (2184505015919/20000000000000 : ℝ)^3169 := by
    have hnat : (1875773857 : ℕ)^4193*20000000000000^3169 ≤ 2184505015919^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1875773857 10000000000 2184505015919 20000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6042617387/10000000000 : ℝ)^4193 ≤ (10269807090241/20000000000000 : ℝ)^3169 := by
    have hnat : (6042617387 : ℕ)^4193*20000000000000^3169 ≤ 10269807090241^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6042617387 10000000000 10269807090241 20000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (957377713/2000000000 : ℝ)^4193 ≤ (37728439458599/100000000000000 : ℝ)^3169 := by
    have hnat : (957377713 : ℕ)^4193*100000000000000^3169 ≤ 37728439458599^3169*2000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      957377713 2000000000 37728439458599 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1875773857/10000000000 : ℝ), (6042617387/10000000000 : ℝ), (957377713/2000000000 : ℝ)] ![(2184505015919/20000000000000 : ℝ), (10269807090241/20000000000000 : ℝ), (37728439458599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1875773857/10000000000 : ℝ)|^4193 ≤ (2184505015919/20000000000000 : ℝ)^3169
        have hw : |(-1875773857/10000000000 : ℝ)|=(1875773857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6042617387/10000000000 : ℝ)|^4193 ≤ (10269807090241/20000000000000 : ℝ)^3169
        have hw : |(6042617387/10000000000 : ℝ)|=(6042617387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(957377713/2000000000 : ℝ)|^4193 ≤ (37728439458599/100000000000000 : ℝ)^3169
        have hw : |(957377713/2000000000 : ℝ)|=(957377713/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s0_1 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5513919949/10000000000 : ℝ)*x 0 + (-2594991243/10000000000 : ℝ)*x 1 + (957377701/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5513919949/10000000000 : ℝ)^4193 ≤ (11372566860211/25000000000000 : ℝ)^3169 := by
    have hnat : (5513919949 : ℕ)^4193*25000000000000^3169 ≤ 11372566860211^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5513919949 10000000000 11372566860211 25000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2594991243/10000000000 : ℝ)^4193 ≤ (4195323426551/25000000000000 : ℝ)^3169 := by
    have hnat : (2594991243 : ℕ)^4193*25000000000000^3169 ≤ 4195323426551^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2594991243 10000000000 4195323426551 25000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (957377701/2000000000 : ℝ)^4193 ≤ (18864219416447/50000000000000 : ℝ)^3169 := by
    have hnat : (957377701 : ℕ)^4193*50000000000000^3169 ≤ 18864219416447^3169*2000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      957377701 2000000000 18864219416447 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5513919949/10000000000 : ℝ), (-2594991243/10000000000 : ℝ), (957377701/2000000000 : ℝ)] ![(11372566860211/25000000000000 : ℝ), (4195323426551/25000000000000 : ℝ), (18864219416447/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5513919949/10000000000 : ℝ)|^4193 ≤ (11372566860211/25000000000000 : ℝ)^3169
        have hw : |(5513919949/10000000000 : ℝ)|=(5513919949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2594991243/10000000000 : ℝ)|^4193 ≤ (4195323426551/25000000000000 : ℝ)^3169
        have hw : |(-2594991243/10000000000 : ℝ)|=(2594991243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(957377701/2000000000 : ℝ)|^4193 ≤ (18864219416447/50000000000000 : ℝ)^3169
        have hw : |(957377701/2000000000 : ℝ)|=(957377701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s0_2 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1102784081/2000000000 : ℝ)*x 0 + (598361009/1250000000 : ℝ)*x 1 + (-2594991189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1102784081/2000000000 : ℝ)^4193 ≤ (45490272418507/100000000000000 : ℝ)^3169 := by
    have hnat : (1102784081 : ℕ)^4193*100000000000000^3169 ≤ 45490272418507^3169*2000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102784081 2000000000 45490272418507 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (598361009/1250000000 : ℝ)^4193 ≤ (2358027144837/6250000000000 : ℝ)^3169 := by
    have hnat : (598361009 : ℕ)^4193*6250000000000^3169 ≤ 2358027144837^3169*1250000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      598361009 1250000000 2358027144837 6250000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2594991189/10000000000 : ℝ)^4193 ≤ (16781293244157/100000000000000 : ℝ)^3169 := by
    have hnat : (2594991189 : ℕ)^4193*100000000000000^3169 ≤ 16781293244157^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2594991189 10000000000 16781293244157 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1102784081/2000000000 : ℝ), (598361009/1250000000 : ℝ), (-2594991189/10000000000 : ℝ)] ![(45490272418507/100000000000000 : ℝ), (2358027144837/6250000000000 : ℝ), (16781293244157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1102784081/2000000000 : ℝ)|^4193 ≤ (45490272418507/100000000000000 : ℝ)^3169
        have hw : |(1102784081/2000000000 : ℝ)|=(1102784081/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(598361009/1250000000 : ℝ)|^4193 ≤ (2358027144837/6250000000000 : ℝ)^3169
        have hw : |(598361009/1250000000 : ℝ)|=(598361009/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2594991189/10000000000 : ℝ)|^4193 ≤ (16781293244157/100000000000000 : ℝ)^3169
        have hw : |(-2594991189/10000000000 : ℝ)|=(2594991189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s0_3 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2098448703/5000000000 : ℝ)*x 0 + (3118833037/10000000000 : ℝ)*x 1 + (2821044331/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2098448703/5000000000 : ℝ)^4193 ≤ (15850941873419/50000000000000 : ℝ)^3169 := by
    have hnat : (2098448703 : ℕ)^4193*50000000000000^3169 ≤ 15850941873419^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098448703 5000000000 15850941873419 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3118833037/10000000000 : ℝ)^4193 ≤ (10701770702049/50000000000000 : ℝ)^3169 := by
    have hnat : (3118833037 : ℕ)^4193*50000000000000^3169 ≤ 10701770702049^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3118833037 10000000000 10701770702049 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2821044331/5000000000 : ℝ)^4193 ≤ (46894574838923/100000000000000 : ℝ)^3169 := by
    have hnat : (2821044331 : ℕ)^4193*100000000000000^3169 ≤ 46894574838923^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2821044331 5000000000 46894574838923 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2098448703/5000000000 : ℝ), (3118833037/10000000000 : ℝ), (2821044331/5000000000 : ℝ)] ![(15850941873419/50000000000000 : ℝ), (10701770702049/50000000000000 : ℝ), (46894574838923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2098448703/5000000000 : ℝ)|^4193 ≤ (15850941873419/50000000000000 : ℝ)^3169
        have hw : |(2098448703/5000000000 : ℝ)|=(2098448703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3118833037/10000000000 : ℝ)|^4193 ≤ (10701770702049/50000000000000 : ℝ)^3169
        have hw : |(3118833037/10000000000 : ℝ)|=(3118833037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2821044331/5000000000 : ℝ)|^4193 ≤ (46894574838923/100000000000000 : ℝ)^3169
        have hw : |(2821044331/5000000000 : ℝ)|=(2821044331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s0_4 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1880770951/10000000000 : ℝ)*x 0 + (4819255351/10000000000 : ℝ)*x 1 + (187784661/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1880770951/10000000000 : ℝ)^4193 ≤ (10961041816529/100000000000000 : ℝ)^3169 := by
    have hnat : (1880770951 : ℕ)^4193*100000000000000^3169 ≤ 10961041816529^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1880770951 10000000000 10961041816529 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4819255351/10000000000 : ℝ)^4193 ≤ (38066341784301/100000000000000 : ℝ)^3169 := by
    have hnat : (4819255351 : ℕ)^4193*100000000000000^3169 ≤ 38066341784301^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4819255351 10000000000 38066341784301 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (187784661/312500000 : ℝ)^4193 ≤ (25486308193969/50000000000000 : ℝ)^3169 := by
    have hnat : (187784661 : ℕ)^4193*50000000000000^3169 ≤ 25486308193969^3169*312500000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187784661 312500000 25486308193969 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1880770951/10000000000 : ℝ), (4819255351/10000000000 : ℝ), (187784661/312500000 : ℝ)] ![(10961041816529/100000000000000 : ℝ), (38066341784301/100000000000000 : ℝ), (25486308193969/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1880770951/10000000000 : ℝ)|^4193 ≤ (10961041816529/100000000000000 : ℝ)^3169
        have hw : |(-1880770951/10000000000 : ℝ)|=(1880770951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4819255351/10000000000 : ℝ)|^4193 ≤ (38066341784301/100000000000000 : ℝ)^3169
        have hw : |(4819255351/10000000000 : ℝ)|=(4819255351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(187784661/312500000 : ℝ)|^4193 ≤ (25486308193969/50000000000000 : ℝ)^3169
        have hw : |(187784661/312500000 : ℝ)|=(187784661/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s0_5 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (646558831/1250000000 : ℝ)*x 0 + (-1372770217/10000000000 : ℝ)*x 1 + (6009109201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (646558831/1250000000 : ℝ)^4193 ≤ (20900428599427/50000000000000 : ℝ)^3169 := by
    have hnat : (646558831 : ℕ)^4193*50000000000000^3169 ≤ 20900428599427^3169*1250000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646558831 1250000000 20900428599427 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1372770217/10000000000 : ℝ)^4193 ≤ (7226525854251/100000000000000 : ℝ)^3169 := by
    have hnat : (1372770217 : ℕ)^4193*100000000000000^3169 ≤ 7226525854251^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372770217 10000000000 7226525854251 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6009109201/10000000000 : ℝ)^4193 ≤ (50972616937891/100000000000000 : ℝ)^3169 := by
    have hnat : (6009109201 : ℕ)^4193*100000000000000^3169 ≤ 50972616937891^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6009109201 10000000000 50972616937891 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(646558831/1250000000 : ℝ), (-1372770217/10000000000 : ℝ), (6009109201/10000000000 : ℝ)] ![(20900428599427/50000000000000 : ℝ), (7226525854251/100000000000000 : ℝ), (50972616937891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(646558831/1250000000 : ℝ)|^4193 ≤ (20900428599427/50000000000000 : ℝ)^3169
        have hw : |(646558831/1250000000 : ℝ)|=(646558831/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1372770217/10000000000 : ℝ)|^4193 ≤ (7226525854251/100000000000000 : ℝ)^3169
        have hw : |(-1372770217/10000000000 : ℝ)|=(1372770217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6009109201/10000000000 : ℝ)|^4193 ≤ (50972616937891/100000000000000 : ℝ)^3169
        have hw : |(6009109201/10000000000 : ℝ)|=(6009109201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s0_6 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1293117667/2500000000 : ℝ)*x 0 + (3004554581/5000000000 : ℝ)*x 1 + (-1372770249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1293117667/2500000000 : ℝ)^4193 ≤ (4180085741271/10000000000000 : ℝ)^3169 := by
    have hnat : (1293117667 : ℕ)^4193*10000000000000^3169 ≤ 4180085741271^3169*2500000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293117667 2500000000 4180085741271 10000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3004554581/5000000000 : ℝ)^4193 ≤ (25486308250087/50000000000000 : ℝ)^3169 := by
    have hnat : (3004554581 : ℕ)^4193*50000000000000^3169 ≤ 25486308250087^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3004554581 5000000000 25486308250087 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1372770249/10000000000 : ℝ)^4193 ≤ (3613263038569/50000000000000 : ℝ)^3169 := by
    have hnat : (1372770249 : ℕ)^4193*50000000000000^3169 ≤ 3613263038569^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372770249 10000000000 3613263038569 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1293117667/2500000000 : ℝ), (3004554581/5000000000 : ℝ), (-1372770249/10000000000 : ℝ)] ![(4180085741271/10000000000000 : ℝ), (25486308250087/50000000000000 : ℝ), (3613263038569/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1293117667/2500000000 : ℝ)|^4193 ≤ (4180085741271/10000000000000 : ℝ)^3169
        have hw : |(1293117667/2500000000 : ℝ)|=(1293117667/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3004554581/5000000000 : ℝ)|^4193 ≤ (25486308250087/50000000000000 : ℝ)^3169
        have hw : |(3004554581/5000000000 : ℝ)|=(3004554581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1372770249/10000000000 : ℝ)|^4193 ≤ (3613263038569/50000000000000 : ℝ)^3169
        have hw : |(-1372770249/10000000000 : ℝ)|=(1372770249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s0_7 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4206938689/10000000000 : ℝ)*x 0 + (1394262729/2500000000 : ℝ)*x 1 + (398270569/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4206938689/10000000000 : ℝ)^4193 ≤ (3975284965217/12500000000000 : ℝ)^3169 := by
    have hnat : (4206938689 : ℕ)^4193*12500000000000^3169 ≤ 3975284965217^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4206938689 10000000000 3975284965217 12500000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1394262729/2500000000 : ℝ)^4193 ≤ (46180672017343/100000000000000 : ℝ)^3169 := by
    have hnat : (1394262729 : ℕ)^4193*100000000000000^3169 ≤ 46180672017343^3169*2500000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1394262729 2500000000 46180672017343 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (398270569/1250000000 : ℝ)^4193 ≤ (11008524121667/50000000000000 : ℝ)^3169 := by
    have hnat : (398270569 : ℕ)^4193*50000000000000^3169 ≤ 11008524121667^3169*1250000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398270569 1250000000 11008524121667 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4206938689/10000000000 : ℝ), (1394262729/2500000000 : ℝ), (398270569/1250000000 : ℝ)] ![(3975284965217/12500000000000 : ℝ), (46180672017343/100000000000000 : ℝ), (11008524121667/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4206938689/10000000000 : ℝ)|^4193 ≤ (3975284965217/12500000000000 : ℝ)^3169
        have hw : |(4206938689/10000000000 : ℝ)|=(4206938689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1394262729/2500000000 : ℝ)|^4193 ≤ (46180672017343/100000000000000 : ℝ)^3169
        have hw : |(1394262729/2500000000 : ℝ)|=(1394262729/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(398270569/1250000000 : ℝ)|^4193 ≤ (11008524121667/50000000000000 : ℝ)^3169
        have hw : |(398270569/1250000000 : ℝ)|=(398270569/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1193_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150469749/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (311/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27621/100000 : ℝ)*pair X 0 0 := by
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
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (8385/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8385 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8385*1^2048 ≤ 0^2048*1^8385 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8385 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8385 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8385/2048 : ℝ) ≤ (234822000106740911/10000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8385 ≤ (234822000106740911/10000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8385*10000000000000000000^2048 ≤ 234822000106740911^2048*5^8385 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 234822000106740911 10000000000000000000 8385 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (234822000106740911/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8385 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8385/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8385 := by
      have hnat : (1 : ℕ)^2048*1^8385 ≤ 1^8385*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8385 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10234822000106740911/10000000000000000000 : ℝ) ≤ (10056852214791143/10000000000000000 : ℝ) ^ (8385/2048 : ℝ) := by
    have hpowers : (10234822000106740911/10000000000000000000 : ℝ)^2048 ≤ (10056852214791143/10000000000000000 : ℝ)^8385 := by
      have hnat : (10234822000106740911 : ℕ)^2048*10000000000000000^8385 ≤ 10056852214791143^8385*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10234822000106740911 10000000000000000000 10056852214791143 10000000000000000 2048 8385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10056852214791143/10000000000000000 : ℝ)) (X := (10234822000106740911/10000000000000000000 : ℝ)) (by norm_num) 8385 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5234822000106740911/5000000000000000000 : ℝ) ≤ (5056852214791143/5000000000000000 : ℝ) ^ (8385/2048 : ℝ) := by
    have hpowers : (5234822000106740911/5000000000000000000 : ℝ)^2048 ≤ (5056852214791143/5000000000000000 : ℝ)^8385 := by
      have hnat : (5234822000106740911 : ℕ)^2048*5000000000000000^8385 ≤ 5056852214791143^8385*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5234822000106740911 5000000000000000000 5056852214791143 5000000000000000 2048 8385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5056852214791143/5000000000000000 : ℝ)) (X := (5234822000106740911/5000000000000000000 : ℝ)) (by norm_num) 8385 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(56852214791143/4000000000000000 : ℝ)*(0 : ℝ))^(8385/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(56852214791143/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(234822000106740911/10000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(56852214791143/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8385/2048 : ℝ) := by
    rw [show (1 : ℝ)+(56852214791143/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10056852214791143/10000000000000000 : ℝ) by norm_num, show 1+(234822000106740911/10000000000000000000 : ℝ)+(0 : ℝ)=(10234822000106740911/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(234822000106740911/10000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(56852214791143/4000000000000000 : ℝ)*(2/5 : ℝ))^(8385/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(56852214791143/4000000000000000 : ℝ)*(2/5 : ℝ)=(5056852214791143/5000000000000000 : ℝ) by norm_num, show 1+2*(234822000106740911/10000000000000000000 : ℝ)=(5234822000106740911/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(56852214791143/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8385/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (56852214791143/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(56852214791143/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8385/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (56852214791143/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(56852214791143/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8385/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (56852214791143/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1875773857/10000000000 : ℝ)*X 0 0+(6042617387/10000000000 : ℝ)*X 0 1+(957377713/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5513919949/10000000000 : ℝ)*X 1 0+(-2594991243/10000000000 : ℝ)*X 1 1+(957377701/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1102784081/2000000000 : ℝ)*X 2 0+(598361009/1250000000 : ℝ)*X 2 1+(-2594991189/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2098448703/5000000000 : ℝ)*X 0 0+(3118833037/10000000000 : ℝ)*X 0 1+(2821044331/5000000000 : ℝ)*X 0 2+(2098448703/5000000000 : ℝ)*X 1 0+(3118833037/10000000000 : ℝ)*X 1 1+(2821044331/5000000000 : ℝ)*X 1 2+(2098448703/5000000000 : ℝ)*X 2 0+(3118833037/10000000000 : ℝ)*X 2 1+(2821044331/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1880770951/10000000000 : ℝ)*X 0 0+(4819255351/10000000000 : ℝ)*X 0 1+(187784661/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((646558831/1250000000 : ℝ)*X 1 0+(-1372770217/10000000000 : ℝ)*X 1 1+(6009109201/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1293117667/2500000000 : ℝ)*X 2 0+(3004554581/5000000000 : ℝ)*X 2 1+(-1372770249/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4206938689/10000000000 : ℝ)*X 0 0+(1394262729/2500000000 : ℝ)*X 0 1+(398270569/1250000000 : ℝ)*X 0 2+(4206938689/10000000000 : ℝ)*X 1 0+(1394262729/2500000000 : ℝ)*X 1 1+(398270569/1250000000 : ℝ)*X 1 2+(4206938689/10000000000 : ℝ)*X 2 0+(1394262729/2500000000 : ℝ)*X 2 1+(398270569/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (80718751706164745568909/40000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7766761/50000000000000 : ℝ)*(base1) + (9240603/2000000000000 : ℝ)*(base19) + (479927787/100000000000000 : ℝ)*(base23) + (5995063/12500000000000 : ℝ)*(base24) + (124466727/100000000000000 : ℝ)*(upper3) + (119266721703879/20000000000000 : ℝ)*(major0) + (119266721703879/20000000000000 : ℝ)*(major1) + (119266721703879/20000000000000 : ℝ)*(major2) + (199087924133737/25000000000000 : ℝ)*(sp0) + (398176035680809/50000000000000 : ℝ)*(sp1) + (796352005503477/100000000000000 : ℝ)*(sp2) + (99078445454679/25000000000000 : ℝ)*(sp3) + (426195171/50000000000000 : ℝ)*(sp4) + (163805831/20000000000000 : ℝ)*(sp7) + (396314616381393/100000000000000 : ℝ)*(f.failure) + (99544066673971/12500000000000 : ℝ)*(f.sum) + (60025674576303/40000000000000000000000000000 : ℝ)*base66 + (102240086743697/80000000000000000000000000000 : ℝ)*base67 + (574251785463697/80000000000000000000000000000 : ℝ)*base69 + (59592599896303/80000000000000000000000000000 : ℝ)*base72 + (23767533976303/40000000000000000000000000000 : ℝ)*base74 + (493474066583697/80000000000000000000000000000 : ℝ)*base75 + (176756943863697/80000000000000000000000000000 : ℝ)*base77 + (10746852663697/80000000000000000000000000000 : ℝ)*base79 + (98561181983697/40000000000000000000000000000 : ℝ)*base81 + (7019643/10000000000000000000000 : ℝ)*base90 + (7019643/10000000000000000000000 : ℝ)*base92 + (7019643/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1503779624102113473862287/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (81350271/100000000000000 : ℝ)*(base1) + (918234697/50000000000000 : ℝ)*(base19) + (367819601/20000000000000 : ℝ)*(base23) + (213431363/100000000000000 : ℝ)*(upper3) + (20967069/10000000000000 : ℝ)*(upper5) + (629347276466001/100000000000000 : ℝ)*(major0) + (629347276466001/100000000000000 : ℝ)*(major1) + (629347276466001/100000000000000 : ℝ)*(major2) + (3884056337/100000000000000 : ℝ)*(sp1) + (193732173/5000000000000 : ℝ)*(sp2) + (52527460324133/6250000000000 : ℝ)*(sp4) + (420216781655063/50000000000000 : ℝ)*(sp5) + (840433570094391/100000000000000 : ℝ)*(sp6) + (418254937115933/100000000000000 : ℝ)*(sp7) + (104563754616551/25000000000000 : ℝ)*(f.failure) + (840439283835857/100000000000000 : ℝ)*(f.sum) + (128171466370857/200000000000000000000000000000 : ℝ)*base66 + (59404866970857/400000000000000000000000000000 : ℝ)*base68 + (769978833370857/400000000000000000000000000000 : ℝ)*base70 + (733630763770857/400000000000000000000000000000 : ℝ)*base72 + (14052723570857/200000000000000000000000000000 : ℝ)*base74 + (2598991655370857/400000000000000000000000000000 : ℝ)*base76 + (554541174570857/400000000000000000000000000000 : ℝ)*base78 + (1694695719429143/400000000000000000000000000000 : ℝ)*base79 + (37729412029143/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (4784301/2500000000000000000000 : ℝ)*base90 + (4784301/2500000000000000000000 : ℝ)*base92 + (4784301/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1193_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150469749/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (311/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27621/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1193_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1193_s1_0 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-8112273/39062500 : ℝ)*x 0 + (5688096013/10000000000 : ℝ)*x 1 + (1253191117/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8112273/39062500 : ℝ)^4193 ≤ (12497067496253/100000000000000 : ℝ)^3169 := by
    have hnat : (8112273 : ℕ)^4193*100000000000000^3169 ≤ 12497067496253^3169*39062500^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8112273 39062500 12497067496253 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5688096013/10000000000 : ℝ)^4193 ≤ (5925149494167/12500000000000 : ℝ)^3169 := by
    have hnat : (5688096013 : ℕ)^4193*12500000000000^3169 ≤ 5925149494167^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5688096013 10000000000 5925149494167 12500000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1253191117/2500000000 : ℝ)^4193 ≤ (10025434132389/25000000000000 : ℝ)^3169 := by
    have hnat : (1253191117 : ℕ)^4193*25000000000000^3169 ≤ 10025434132389^3169*2500000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1253191117 2500000000 10025434132389 25000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-8112273/39062500 : ℝ), (5688096013/10000000000 : ℝ), (1253191117/2500000000 : ℝ)] ![(12497067496253/100000000000000 : ℝ), (5925149494167/12500000000000 : ℝ), (10025434132389/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-8112273/39062500 : ℝ)|^4193 ≤ (12497067496253/100000000000000 : ℝ)^3169
        have hw : |(-8112273/39062500 : ℝ)|=(8112273/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5688096013/10000000000 : ℝ)|^4193 ≤ (5925149494167/12500000000000 : ℝ)^3169
        have hw : |(5688096013/10000000000 : ℝ)|=(5688096013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1253191117/2500000000 : ℝ)|^4193 ≤ (10025434132389/25000000000000 : ℝ)^3169
        have hw : |(1253191117/2500000000 : ℝ)|=(1253191117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s1_1 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (541633/1000000 : ℝ)*x 0 + (-1220126461/5000000000 : ℝ)*x 1 + (2506382393/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541633/1000000 : ℝ)^4193 ≤ (22214020525859/50000000000000 : ℝ)^3169 := by
    have hnat : (541633 : ℕ)^4193*50000000000000^3169 ≤ 22214020525859^3169*1000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541633 1000000 22214020525859 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1220126461/5000000000 : ℝ)^4193 ≤ (15470219035219/100000000000000 : ℝ)^3169 := by
    have hnat : (1220126461 : ℕ)^4193*100000000000000^3169 ≤ 15470219035219^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1220126461 5000000000 15470219035219 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2506382393/5000000000 : ℝ)^4193 ≤ (2506358743473/6250000000000 : ℝ)^3169 := by
    have hnat : (2506382393 : ℕ)^4193*6250000000000^3169 ≤ 2506358743473^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2506382393 5000000000 2506358743473 6250000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(541633/1000000 : ℝ), (-1220126461/5000000000 : ℝ), (2506382393/5000000000 : ℝ)] ![(22214020525859/50000000000000 : ℝ), (15470219035219/100000000000000 : ℝ), (2506358743473/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(541633/1000000 : ℝ)|^4193 ≤ (22214020525859/50000000000000 : ℝ)^3169
        have hw : |(541633/1000000 : ℝ)|=(541633/1000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1220126461/5000000000 : ℝ)|^4193 ≤ (15470219035219/100000000000000 : ℝ)^3169
        have hw : |(-1220126461/5000000000 : ℝ)|=(1220126461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2506382393/5000000000 : ℝ)|^4193 ≤ (2506358743473/6250000000000 : ℝ)^3169
        have hw : |(2506382393/5000000000 : ℝ)|=(2506382393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s1_2 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (216653161/400000000 : ℝ)*x 0 + (2506382711/5000000000 : ℝ)*x 1 + (-2440253381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216653161/400000000 : ℝ)^4193 ≤ (1777121218797/4000000000000 : ℝ)^3169 := by
    have hnat : (216653161 : ℕ)^4193*4000000000000^3169 ≤ 1777121218797^3169*400000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216653161 400000000 1777121218797 4000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2506382711/5000000000 : ℝ)^4193 ≤ (40101746627591/100000000000000 : ℝ)^3169 := by
    have hnat : (2506382711 : ℕ)^4193*100000000000000^3169 ≤ 40101746627591^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2506382711 5000000000 40101746627591 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2440253381/10000000000 : ℝ)^4193 ≤ (15470222885363/100000000000000 : ℝ)^3169 := by
    have hnat : (2440253381 : ℕ)^4193*100000000000000^3169 ≤ 15470222885363^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2440253381 10000000000 15470222885363 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(216653161/400000000 : ℝ), (2506382711/5000000000 : ℝ), (-2440253381/10000000000 : ℝ)] ![(1777121218797/4000000000000 : ℝ), (40101746627591/100000000000000 : ℝ), (15470222885363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(216653161/400000000 : ℝ)|^4193 ≤ (1777121218797/4000000000000 : ℝ)^3169
        have hw : |(216653161/400000000 : ℝ)|=(216653161/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2506382711/5000000000 : ℝ)|^4193 ≤ (40101746627591/100000000000000 : ℝ)^3169
        have hw : |(2506382711/5000000000 : ℝ)|=(2506382711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2440253381/10000000000 : ℝ)|^4193 ≤ (15470222885363/100000000000000 : ℝ)^3169
        have hw : |(-2440253381/10000000000 : ℝ)|=(2440253381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s1_3 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4313086559/10000000000 : ℝ)*x 0 + (1843258949/5000000000 : ℝ)*x 1 + (1260881497/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4313086559/10000000000 : ℝ)^4193 ≤ (6573658724981/20000000000000 : ℝ)^3169 := by
    have hnat : (4313086559 : ℕ)^4193*20000000000000^3169 ≤ 6573658724981^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4313086559 10000000000 6573658724981 20000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1843258949/5000000000 : ℝ)^4193 ≤ (26704038532569/100000000000000 : ℝ)^3169 := by
    have hnat : (1843258949 : ℕ)^4193*100000000000000^3169 ≤ 26704038532569^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1843258949 5000000000 26704038532569 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1260881497/2500000000 : ℝ)^4193 ≤ (10106916958693/25000000000000 : ℝ)^3169 := by
    have hnat : (1260881497 : ℕ)^4193*25000000000000^3169 ≤ 10106916958693^3169*2500000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1260881497 2500000000 10106916958693 25000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4313086559/10000000000 : ℝ), (1843258949/5000000000 : ℝ), (1260881497/2500000000 : ℝ)] ![(6573658724981/20000000000000 : ℝ), (26704038532569/100000000000000 : ℝ), (10106916958693/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4313086559/10000000000 : ℝ)|^4193 ≤ (6573658724981/20000000000000 : ℝ)^3169
        have hw : |(4313086559/10000000000 : ℝ)|=(4313086559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1843258949/5000000000 : ℝ)|^4193 ≤ (26704038532569/100000000000000 : ℝ)^3169
        have hw : |(1843258949/5000000000 : ℝ)|=(1843258949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1260881497/2500000000 : ℝ)|^4193 ≤ (10106916958693/25000000000000 : ℝ)^3169
        have hw : |(1260881497/2500000000 : ℝ)|=(1260881497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s1_4 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-103873953/500000000 : ℝ)*x 0 + (2510903407/5000000000 : ℝ)*x 1 + (5678878223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103873953/500000000 : ℝ)^4193 ≤ (12502937277969/100000000000000 : ℝ)^3169 := by
    have hnat : (103873953 : ℕ)^4193*100000000000000^3169 ≤ 12502937277969^3169*500000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103873953 500000000 12502937277969 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2510903407/5000000000 : ℝ)^4193 ≤ (10049369281351/25000000000000 : ℝ)^3169 := by
    have hnat : (2510903407 : ℕ)^4193*25000000000000^3169 ≤ 10049369281351^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2510903407 5000000000 10049369281351 25000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5678878223/10000000000 : ℝ)^4193 ≤ (23649792789771/50000000000000 : ℝ)^3169 := by
    have hnat : (5678878223 : ℕ)^4193*50000000000000^3169 ≤ 23649792789771^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5678878223 10000000000 23649792789771 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-103873953/500000000 : ℝ), (2510903407/5000000000 : ℝ), (5678878223/10000000000 : ℝ)] ![(12502937277969/100000000000000 : ℝ), (10049369281351/25000000000000 : ℝ), (23649792789771/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-103873953/500000000 : ℝ)|^4193 ≤ (12502937277969/100000000000000 : ℝ)^3169
        have hw : |(-103873953/500000000 : ℝ)|=(103873953/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2510903407/5000000000 : ℝ)|^4193 ≤ (10049369281351/25000000000000 : ℝ)^3169
        have hw : |(2510903407/5000000000 : ℝ)|=(2510903407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5678878223/10000000000 : ℝ)|^4193 ≤ (23649792789771/50000000000000 : ℝ)^3169
        have hw : |(5678878223/10000000000 : ℝ)|=(5678878223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s1_5 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5242750753/10000000000 : ℝ)*x 0 + (-1774139477/10000000000 : ℝ)*x 1 + (5678878413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5242750753/10000000000 : ℝ)^4193 ≤ (42553990088579/100000000000000 : ℝ)^3169 := by
    have hnat : (5242750753 : ℕ)^4193*100000000000000^3169 ≤ 42553990088579^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242750753 10000000000 42553990088579 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1774139477/10000000000 : ℝ)^4193 ≤ (1268302776893/12500000000000 : ℝ)^3169 := by
    have hnat : (1774139477 : ℕ)^4193*12500000000000^3169 ≤ 1268302776893^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1774139477 10000000000 1268302776893 12500000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5678878413/10000000000 : ℝ)^4193 ≤ (47299587673419/100000000000000 : ℝ)^3169 := by
    have hnat : (5678878413 : ℕ)^4193*100000000000000^3169 ≤ 47299587673419^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5678878413 10000000000 47299587673419 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5242750753/10000000000 : ℝ), (-1774139477/10000000000 : ℝ), (5678878413/10000000000 : ℝ)] ![(42553990088579/100000000000000 : ℝ), (1268302776893/12500000000000 : ℝ), (47299587673419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5242750753/10000000000 : ℝ)|^4193 ≤ (42553990088579/100000000000000 : ℝ)^3169
        have hw : |(5242750753/10000000000 : ℝ)|=(5242750753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1774139477/10000000000 : ℝ)|^4193 ≤ (1268302776893/12500000000000 : ℝ)^3169
        have hw : |(-1774139477/10000000000 : ℝ)|=(1774139477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5678878413/10000000000 : ℝ)|^4193 ≤ (47299587673419/100000000000000 : ℝ)^3169
        have hw : |(5678878413/10000000000 : ℝ)|=(5678878413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s1_6 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2621375339/5000000000 : ℝ)*x 0 + (2839439541/5000000000 : ℝ)*x 1 + (-1774138611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2621375339/5000000000 : ℝ)^4193 ≤ (42553989283117/100000000000000 : ℝ)^3169 := by
    have hnat : (2621375339 : ℕ)^4193*100000000000000^3169 ≤ 42553989283117^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621375339 5000000000 42553989283117 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2839439541/5000000000 : ℝ)^4193 ≤ (47299595046067/100000000000000 : ℝ)^3169 := by
    have hnat : (2839439541 : ℕ)^4193*100000000000000^3169 ≤ 47299595046067^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2839439541 5000000000 47299595046067 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1774138611/10000000000 : ℝ)^4193 ≤ (10146415662061/100000000000000 : ℝ)^3169 := by
    have hnat : (1774138611 : ℕ)^4193*100000000000000^3169 ≤ 10146415662061^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1774138611 10000000000 10146415662061 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2621375339/5000000000 : ℝ), (2839439541/5000000000 : ℝ), (-1774138611/10000000000 : ℝ)] ![(42553989283117/100000000000000 : ℝ), (47299595046067/100000000000000 : ℝ), (10146415662061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2621375339/5000000000 : ℝ)|^4193 ≤ (42553989283117/100000000000000 : ℝ)^3169
        have hw : |(2621375339/5000000000 : ℝ)|=(2621375339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2839439541/5000000000 : ℝ)|^4193 ≤ (47299595046067/100000000000000 : ℝ)^3169
        have hw : |(2839439541/5000000000 : ℝ)|=(2839439541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1774138611/10000000000 : ℝ)|^4193 ≤ (10146415662061/100000000000000 : ℝ)^3169
        have hw : |(-1774138611/10000000000 : ℝ)|=(1774138611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s1_7 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4314567177/10000000000 : ℝ)*x 0 + (502535643/1000000000 : ℝ)*x 1 + (3705039541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4314567177/10000000000 : ℝ)^4193 ≤ (32883223587399/100000000000000 : ℝ)^3169 := by
    have hnat : (4314567177 : ℕ)^4193*100000000000000^3169 ≤ 32883223587399^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4314567177 10000000000 32883223587399 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (502535643/1000000000 : ℝ)^4193 ≤ (8047015157263/20000000000000 : ℝ)^3169 := by
    have hnat : (502535643 : ℕ)^4193*20000000000000^3169 ≤ 8047015157263^3169*1000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502535643 1000000000 8047015157263 20000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3705039541/10000000000 : ℝ)^4193 ≤ (26881700603149/100000000000000 : ℝ)^3169 := by
    have hnat : (3705039541 : ℕ)^4193*100000000000000^3169 ≤ 26881700603149^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3705039541 10000000000 26881700603149 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4314567177/10000000000 : ℝ), (502535643/1000000000 : ℝ), (3705039541/10000000000 : ℝ)] ![(32883223587399/100000000000000 : ℝ), (8047015157263/20000000000000 : ℝ), (26881700603149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4314567177/10000000000 : ℝ)|^4193 ≤ (32883223587399/100000000000000 : ℝ)^3169
        have hw : |(4314567177/10000000000 : ℝ)|=(4314567177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(502535643/1000000000 : ℝ)|^4193 ≤ (8047015157263/20000000000000 : ℝ)^3169
        have hw : |(502535643/1000000000 : ℝ)|=(502535643/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3705039541/10000000000 : ℝ)|^4193 ≤ (26881700603149/100000000000000 : ℝ)^3169
        have hw : |(3705039541/10000000000 : ℝ)|=(3705039541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1193_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150469749/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27621/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (311/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (593/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2021/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27621/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (311/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27621/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (311/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27621/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (311/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27621/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (311/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27621/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (311/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27621/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (311/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (311/50000 : ℝ) ^ (8385/2048 : ℝ) ≤ (46368403267/50000000000000000000 : ℝ) := by
    have hpowers : (311/50000 : ℝ)^8385 ≤ (46368403267/50000000000000000000 : ℝ)^2048 := by
      have hnat : (311 : ℕ)^8385*50000000000000000000^2048 ≤ 46368403267^2048*50000^8385 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        311 50000 46368403267 50000000000000000000 8385 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (311/50000 : ℝ)) (X := (46368403267/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8385 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (27621/100000 : ℝ) ^ (8385/2048 : ℝ) ≤ (128896451477989913/25000000000000000000 : ℝ) := by
    have hpowers : (27621/100000 : ℝ)^8385 ≤ (128896451477989913/25000000000000000000 : ℝ)^2048 := by
      have hnat : (27621 : ℕ)^8385*25000000000000000000^2048 ≤ 128896451477989913^2048*100000^8385 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27621 100000 128896451477989913 25000000000000000000 8385 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27621/100000 : ℝ)) (X := (128896451477989913/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8385 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000046368403267/25000000000000000000 : ℝ) ≤ (10000000004530113/10000000000000000 : ℝ) ^ (8385/2048 : ℝ) := by
    have hpowers : (25000000046368403267/25000000000000000000 : ℝ)^2048 ≤ (10000000004530113/10000000000000000 : ℝ)^8385 := by
      have hnat : (25000000046368403267 : ℕ)^2048*10000000000000000^8385 ≤ 10000000004530113^8385*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000046368403267 25000000000000000000 10000000004530113 10000000000000000 2048 8385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000004530113/10000000000000000 : ℝ)) (X := (25000000046368403267/25000000000000000000 : ℝ)) (by norm_num) 8385 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50257792949324383093/50000000000000000000 : ℝ) ≤ (10012568501812819/10000000000000000 : ℝ) ^ (8385/2048 : ℝ) := by
    have hpowers : (50257792949324383093/50000000000000000000 : ℝ)^2048 ≤ (10012568501812819/10000000000000000 : ℝ)^8385 := by
      have hnat : (50257792949324383093 : ℕ)^2048*10000000000000000^8385 ≤ 10012568501812819^8385*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50257792949324383093 50000000000000000000 10012568501812819 10000000000000000 2048 8385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10012568501812819/10000000000000000 : ℝ)) (X := (50257792949324383093/50000000000000000000 : ℝ)) (by norm_num) 8385 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12628896451477989913/12500000000000000000 : ℝ) ≤ (401005479963821/400000000000000 : ℝ) ^ (8385/2048 : ℝ) := by
    have hpowers : (12628896451477989913/12500000000000000000 : ℝ)^2048 ≤ (401005479963821/400000000000000 : ℝ)^8385 := by
      have hnat : (12628896451477989913 : ℕ)^2048*400000000000000^8385 ≤ 401005479963821^8385*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12628896451477989913 12500000000000000000 401005479963821 400000000000000 2048 8385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (401005479963821/400000000000000 : ℝ)) (X := (12628896451477989913/12500000000000000000 : ℝ)) (by norm_num) 8385 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(46368403267/50000000000000000000 : ℝ) ≤ ((269974364911688834623/269990000000000000000 : ℝ)+2*(6284248641353/1349950000000000 : ℝ)*(311/50000 : ℝ))^(8385/2048 : ℝ) := by
    rw [show (269974364911688834623/269990000000000000000 : ℝ)+2*(6284248641353/1349950000000000 : ℝ)*(311/50000 : ℝ)=(10000000004530113/10000000000000000 : ℝ) by norm_num, show 1+2*(46368403267/50000000000000000000 : ℝ)=(25000000046368403267/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(128896451477989913/25000000000000000000 : ℝ)+(46368403267/50000000000000000000 : ℝ) ≤ ((269974364911688834623/269990000000000000000 : ℝ)+(6284248641353/1349950000000000 : ℝ)*((27621/100000 : ℝ)+(311/50000 : ℝ)))^(8385/2048 : ℝ) := by
    rw [show (269974364911688834623/269990000000000000000 : ℝ)+(6284248641353/1349950000000000 : ℝ)*((27621/100000 : ℝ)+(311/50000 : ℝ))=(10012568501812819/10000000000000000 : ℝ) by norm_num, show 1+(128896451477989913/25000000000000000000 : ℝ)+(46368403267/50000000000000000000 : ℝ)=(50257792949324383093/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(128896451477989913/25000000000000000000 : ℝ) ≤ ((269974364911688834623/269990000000000000000 : ℝ)+2*(6284248641353/1349950000000000 : ℝ)*(27621/100000 : ℝ))^(8385/2048 : ℝ) := by
    rw [show (269974364911688834623/269990000000000000000 : ℝ)+2*(6284248641353/1349950000000000 : ℝ)*(27621/100000 : ℝ)=(401005479963821/400000000000000 : ℝ) by norm_num, show 1+2*(128896451477989913/25000000000000000000 : ℝ)=(12628896451477989913/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (269974364911688834623/269990000000000000000 : ℝ)*(X 1 0+X 2 0)+(6284248641353/1349950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8385/2048 : ℝ)) (lo := (311/50000 : ℝ)) (hi := (27621/100000 : ℝ)) (c := (269974364911688834623/269990000000000000000 : ℝ)) (alpha := (6284248641353/1349950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (269974364911688834623/269990000000000000000 : ℝ)*(X 0 1+X 2 1)+(6284248641353/1349950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8385/2048 : ℝ)) (lo := (311/50000 : ℝ)) (hi := (27621/100000 : ℝ)) (c := (269974364911688834623/269990000000000000000 : ℝ)) (alpha := (6284248641353/1349950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (269974364911688834623/269990000000000000000 : ℝ)*(X 0 2+X 1 2)+(6284248641353/1349950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8385/2048 : ℝ)) (lo := (311/50000 : ℝ)) (hi := (27621/100000 : ℝ)) (c := (269974364911688834623/269990000000000000000 : ℝ)) (alpha := (6284248641353/1349950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-8112273/39062500 : ℝ)*X 0 0+(5688096013/10000000000 : ℝ)*X 0 1+(1253191117/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((541633/1000000 : ℝ)*X 1 0+(-1220126461/5000000000 : ℝ)*X 1 1+(2506382393/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((216653161/400000000 : ℝ)*X 2 0+(2506382711/5000000000 : ℝ)*X 2 1+(-2440253381/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4313086559/10000000000 : ℝ)*X 0 0+(1843258949/5000000000 : ℝ)*X 0 1+(1260881497/2500000000 : ℝ)*X 0 2+(4313086559/10000000000 : ℝ)*X 1 0+(1843258949/5000000000 : ℝ)*X 1 1+(1260881497/2500000000 : ℝ)*X 1 2+(4313086559/10000000000 : ℝ)*X 2 0+(1843258949/5000000000 : ℝ)*X 2 1+(1260881497/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-103873953/500000000 : ℝ)*X 0 0+(2510903407/5000000000 : ℝ)*X 0 1+(5678878223/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5242750753/10000000000 : ℝ)*X 1 0+(-1774139477/10000000000 : ℝ)*X 1 1+(5678878413/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2621375339/5000000000 : ℝ)*X 2 0+(2839439541/5000000000 : ℝ)*X 2 1+(-1774138611/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4314567177/10000000000 : ℝ)*X 0 0+(502535643/1000000000 : ℝ)*X 0 1+(3705039541/10000000000 : ℝ)*X 0 2+(4314567177/10000000000 : ℝ)*X 1 0+(502535643/1000000000 : ℝ)*X 1 1+(3705039541/10000000000 : ℝ)*X 1 2+(4314567177/10000000000 : ℝ)*X 2 0+(502535643/1000000000 : ℝ)*X 2 1+(3705039541/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3576864685897779279555680733/539980000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1636666339/100000000000000 : ℝ)*(base19) + (1365303251/100000000000000 : ℝ)*(base23) + (301601187/100000000000000 : ℝ)*(upper3) + (1301947/50000000000000 : ℝ)*(upper4) + (60335463/100000000000000 : ℝ)*(upper5) + (44353985708619/4000000000000 : ℝ)*(major0) + (44353985708619/4000000000000 : ℝ)*(major1) + (44353985708619/4000000000000 : ℝ)*(major2) + (740382667995569/50000000000000 : ℝ)*(sp0) + (185096516536263/12500000000000 : ℝ)*(sp1) + (185096550456649/12500000000000 : ℝ)*(sp2) + (736919820527767/100000000000000 : ℝ)*(sp3) + (1686593061/20000000000000 : ℝ)*(sp4) + (2737572219/50000000000000 : ℝ)*(sp7) + (147385059134441/20000000000000 : ℝ)*(f.failure) + (740386884478221/50000000000000 : ℝ)*(f.sum) + (3037026792701/5399800000000000000000000000 : ℝ)*base65 + (1379247566442154909/154280000000000000000000000000000 : ℝ)*base68 + (299046609315394909/154280000000000000000000000000000 : ℝ)*base70 + (978842230778674909/154280000000000000000000000000000 : ℝ)*base72 + (1363788394411/3374875000000000000000000000 : ℝ)*base73 + (740154750885994909/154280000000000000000000000000000 : ℝ)*base76 + (1112321861762674909/154280000000000000000000000000000 : ℝ)*base78 + (1225246189950954909/154280000000000000000000000000000 : ℝ)*base80 + (9134161678167/1687437500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (5474691/2000000000000000000000 : ℝ)*base90 + (5474691/2000000000000000000000 : ℝ)*base92 + (5474691/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (60630501014523072274645977/11637500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1580904071/100000000000000 : ℝ)*(base19) + (88554447/5000000000000 : ℝ)*(base23) + (1582033/2500000000000 : ℝ)*(upper2) + (103049297/50000000000000 : ℝ)*(upper3) + (9846529/6250000000000 : ℝ)*(upper5) + (56982454793743/5000000000000 : ℝ)*(major0) + (56982454793743/5000000000000 : ℝ)*(major1) + (56982454793743/5000000000000 : ℝ)*(major2) + (7595482661/100000000000000 : ℝ)*(sp1) + (1293968629/12500000000000 : ℝ)*(sp2) + (380475963793301/25000000000000 : ℝ)*(sp4) + (190236834848309/12500000000000 : ℝ)*(sp5) + (11889779158869/781250000000 : ℝ)*(sp6) + (757394162912347/100000000000000 : ℝ)*(sp7) + (757394162912347/100000000000000 : ℝ)*(f.failure) + (380475963793301/25000000000000 : ℝ)*(f.sum) + (5513259726641/931000000000000000000000000 : ℝ)*base66 + (5511515073503763/6650000000000000000000000000000 : ℝ)*base67 + (29680301986053763/6650000000000000000000000000000 : ℝ)*base69 + (15541546689653763/6650000000000000000000000000000 : ℝ)*base71 + (628336916867/116375000000000000000000000 : ℝ)*base74 + (52803229852553763/6650000000000000000000000000000 : ℝ)*base75 + (5540267882346237/6650000000000000000000000000000 : ℝ)*base78 + (59705181534703763/6650000000000000000000000000000 : ℝ)*base79 + (237318466993/186200000000000000000000000 : ℝ)*base82 + (37909097/10000000000000000000000 : ℝ)*base90 + (37909097/10000000000000000000000 : ℝ)*base92 + (37909097/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1193_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150469749/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27621/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (311/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (593/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2021/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1193_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1193_s2_0 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-265910571/1250000000 : ℝ)*x 0 + (5501373789/10000000000 : ℝ)*x 1 + (645912381/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265910571/1250000000 : ℝ)^4193 ≤ (3225266922277/25000000000000 : ℝ)^3169 := by
    have hnat : (265910571 : ℕ)^4193*25000000000000^3169 ≤ 3225266922277^3169*1250000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265910571 1250000000 3225266922277 25000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5501373789/10000000000 : ℝ)^4193 ≤ (4535336483587/10000000000000 : ℝ)^3169 := by
    have hnat : (5501373789 : ℕ)^4193*10000000000000^3169 ≤ 4535336483587^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5501373789 10000000000 4535336483587 10000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (645912381/1250000000 : ℝ)^4193 ≤ (41745567461563/100000000000000 : ℝ)^3169 := by
    have hnat : (645912381 : ℕ)^4193*100000000000000^3169 ≤ 41745567461563^3169*1250000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      645912381 1250000000 41745567461563 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-265910571/1250000000 : ℝ), (5501373789/10000000000 : ℝ), (645912381/1250000000 : ℝ)] ![(3225266922277/25000000000000 : ℝ), (4535336483587/10000000000000 : ℝ), (41745567461563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-265910571/1250000000 : ℝ)|^4193 ≤ (3225266922277/25000000000000 : ℝ)^3169
        have hw : |(-265910571/1250000000 : ℝ)|=(265910571/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5501373789/10000000000 : ℝ)|^4193 ≤ (4535336483587/10000000000000 : ℝ)^3169
        have hw : |(5501373789/10000000000 : ℝ)|=(5501373789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(645912381/1250000000 : ℝ)|^4193 ≤ (41745567461563/100000000000000 : ℝ)^3169
        have hw : |(645912381/1250000000 : ℝ)|=(645912381/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s2_1 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5371703083/10000000000 : ℝ)*x 0 + (-1150316607/5000000000 : ℝ)*x 1 + (6459129/12500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5371703083/10000000000 : ℝ)^4193 ≤ (10986086411213/25000000000000 : ℝ)^3169 := by
    have hnat : (5371703083 : ℕ)^4193*25000000000000^3169 ≤ 10986086411213^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5371703083 10000000000 10986086411213 25000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1150316607/5000000000 : ℝ)^4193 ≤ (111797207029/781250000000 : ℝ)^3169 := by
    have hnat : (1150316607 : ℕ)^4193*781250000000^3169 ≤ 111797207029^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1150316607 5000000000 111797207029 781250000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6459129/12500000 : ℝ)^4193 ≤ (10436402960889/25000000000000 : ℝ)^3169 := by
    have hnat : (6459129 : ℕ)^4193*25000000000000^3169 ≤ 10436402960889^3169*12500000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6459129 12500000 10436402960889 25000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5371703083/10000000000 : ℝ), (-1150316607/5000000000 : ℝ), (6459129/12500000 : ℝ)] ![(10986086411213/25000000000000 : ℝ), (111797207029/781250000000 : ℝ), (10436402960889/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5371703083/10000000000 : ℝ)|^4193 ≤ (10986086411213/25000000000000 : ℝ)^3169
        have hw : |(5371703083/10000000000 : ℝ)|=(5371703083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1150316607/5000000000 : ℝ)|^4193 ≤ (111797207029/781250000000 : ℝ)^3169
        have hw : |(-1150316607/5000000000 : ℝ)|=(1150316607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6459129/12500000 : ℝ)|^4193 ≤ (10436402960889/25000000000000 : ℝ)^3169
        have hw : |(6459129/12500000 : ℝ)|=(6459129/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s2_2 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5371704783/10000000000 : ℝ)*x 0 + (2583650409/5000000000 : ℝ)*x 1 + (-287579259/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5371704783/10000000000 : ℝ)^4193 ≤ (43944364045901/100000000000000 : ℝ)^3169 := by
    have hnat : (5371704783 : ℕ)^4193*100000000000000^3169 ≤ 43944364045901^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5371704783 10000000000 43944364045901 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2583650409/5000000000 : ℝ)^4193 ≤ (41745586381631/100000000000000 : ℝ)^3169 := by
    have hnat : (2583650409 : ℕ)^4193*100000000000000^3169 ≤ 41745586381631^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2583650409 5000000000 41745586381631 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (287579259/1250000000 : ℝ)^4193 ≤ (14310049560993/100000000000000 : ℝ)^3169 := by
    have hnat : (287579259 : ℕ)^4193*100000000000000^3169 ≤ 14310049560993^3169*1250000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287579259 1250000000 14310049560993 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5371704783/10000000000 : ℝ), (2583650409/5000000000 : ℝ), (-287579259/1250000000 : ℝ)] ![(43944364045901/100000000000000 : ℝ), (41745586381631/100000000000000 : ℝ), (14310049560993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5371704783/10000000000 : ℝ)|^4193 ≤ (43944364045901/100000000000000 : ℝ)^3169
        have hw : |(5371704783/10000000000 : ℝ)|=(5371704783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2583650409/5000000000 : ℝ)|^4193 ≤ (41745586381631/100000000000000 : ℝ)^3169
        have hw : |(2583650409/5000000000 : ℝ)|=(2583650409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-287579259/1250000000 : ℝ)|^4193 ≤ (14310049560993/100000000000000 : ℝ)^3169
        have hw : |(-287579259/1250000000 : ℝ)|=(287579259/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s2_3 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4347882611/10000000000 : ℝ)*x 0 + (4024929933/10000000000 : ℝ)*x 1 + (4696213879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4347882611/10000000000 : ℝ)^4193 ≤ (16609800092251/50000000000000 : ℝ)^3169 := by
    have hnat : (4347882611 : ℕ)^4193*50000000000000^3169 ≤ 16609800092251^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4347882611 10000000000 16609800092251 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4024929933/10000000000 : ℝ)^4193 ≤ (14997323437443/50000000000000 : ℝ)^3169 := by
    have hnat : (4024929933 : ℕ)^4193*50000000000000^3169 ≤ 14997323437443^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4024929933 10000000000 14997323437443 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4696213879/10000000000 : ℝ)^4193 ≤ (9196438230443/25000000000000 : ℝ)^3169 := by
    have hnat : (4696213879 : ℕ)^4193*25000000000000^3169 ≤ 9196438230443^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4696213879 10000000000 9196438230443 25000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4347882611/10000000000 : ℝ), (4024929933/10000000000 : ℝ), (4696213879/10000000000 : ℝ)] ![(16609800092251/50000000000000 : ℝ), (14997323437443/50000000000000 : ℝ), (9196438230443/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4347882611/10000000000 : ℝ)|^4193 ≤ (16609800092251/50000000000000 : ℝ)^3169
        have hw : |(4347882611/10000000000 : ℝ)|=(4347882611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4024929933/10000000000 : ℝ)|^4193 ≤ (14997323437443/50000000000000 : ℝ)^3169
        have hw : |(4024929933/10000000000 : ℝ)|=(4024929933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4696213879/10000000000 : ℝ)|^4193 ≤ (9196438230443/25000000000000 : ℝ)^3169
        have hw : |(4696213879/10000000000 : ℝ)|=(4696213879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s2_4 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-85094917/400000000 : ℝ)*x 0 + (646190369/1250000000 : ℝ)*x 1 + (5499129153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85094917/400000000 : ℝ)^4193 ≤ (3225444172411/25000000000000 : ℝ)^3169 := by
    have hnat : (85094917 : ℕ)^4193*25000000000000^3169 ≤ 3225444172411^3169*400000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85094917 400000000 3225444172411 25000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (646190369/1250000000 : ℝ)^4193 ≤ (10442335274629/25000000000000 : ℝ)^3169 := by
    have hnat : (646190369 : ℕ)^4193*25000000000000^3169 ≤ 10442335274629^3169*1250000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646190369 1250000000 10442335274629 25000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5499129153/10000000000 : ℝ)^4193 ≤ (45328882194317/100000000000000 : ℝ)^3169 := by
    have hnat : (5499129153 : ℕ)^4193*100000000000000^3169 ≤ 45328882194317^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5499129153 10000000000 45328882194317 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-85094917/400000000 : ℝ), (646190369/1250000000 : ℝ), (5499129153/10000000000 : ℝ)] ![(3225444172411/25000000000000 : ℝ), (10442335274629/25000000000000 : ℝ), (45328882194317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-85094917/400000000 : ℝ)|^4193 ≤ (3225444172411/25000000000000 : ℝ)^3169
        have hw : |(-85094917/400000000 : ℝ)|=(85094917/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(646190369/1250000000 : ℝ)|^4193 ≤ (10442335274629/25000000000000 : ℝ)^3169
        have hw : |(646190369/1250000000 : ℝ)|=(646190369/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5499129153/10000000000 : ℝ)|^4193 ≤ (45328882194317/100000000000000 : ℝ)^3169
        have hw : |(5499129153/10000000000 : ℝ)|=(5499129153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s2_5 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5286656049/10000000000 : ℝ)*x 0 + (-1968805647/10000000000 : ℝ)*x 1 + (343695573/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286656049/10000000000 : ℝ)^4193 ≤ (43026147398829/100000000000000 : ℝ)^3169 := by
    have hnat : (5286656049 : ℕ)^4193*100000000000000^3169 ≤ 43026147398829^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286656049 10000000000 43026147398829 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1968805647/10000000000 : ℝ)^4193 ≤ (5822485116153/50000000000000 : ℝ)^3169 := by
    have hnat : (1968805647 : ℕ)^4193*50000000000000^3169 ≤ 5822485116153^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1968805647 10000000000 5822485116153 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (343695573/625000000 : ℝ)^4193 ≤ (22664441178957/50000000000000 : ℝ)^3169 := by
    have hnat : (343695573 : ℕ)^4193*50000000000000^3169 ≤ 22664441178957^3169*625000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343695573 625000000 22664441178957 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286656049/10000000000 : ℝ), (-1968805647/10000000000 : ℝ), (343695573/625000000 : ℝ)] ![(43026147398829/100000000000000 : ℝ), (5822485116153/50000000000000 : ℝ), (22664441178957/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286656049/10000000000 : ℝ)|^4193 ≤ (43026147398829/100000000000000 : ℝ)^3169
        have hw : |(5286656049/10000000000 : ℝ)|=(5286656049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1968805647/10000000000 : ℝ)|^4193 ≤ (5822485116153/50000000000000 : ℝ)^3169
        have hw : |(-1968805647/10000000000 : ℝ)|=(1968805647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(343695573/625000000 : ℝ)|^4193 ≤ (22664441178957/50000000000000 : ℝ)^3169
        have hw : |(343695573/625000000 : ℝ)|=(343695573/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s2_6 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2643328107/5000000000 : ℝ)*x 0 + (274956459/500000000 : ℝ)*x 1 + (-1968805403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643328107/5000000000 : ℝ)^4193 ≤ (21513074587813/50000000000000 : ℝ)^3169 := by
    have hnat : (2643328107 : ℕ)^4193*50000000000000^3169 ≤ 21513074587813^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643328107 5000000000 21513074587813 50000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (274956459/500000000 : ℝ)^4193 ≤ (45328882488791/100000000000000 : ℝ)^3169 := by
    have hnat : (274956459 : ℕ)^4193*100000000000000^3169 ≤ 45328882488791^3169*500000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274956459 500000000 45328882488791 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1968805403/10000000000 : ℝ)^4193 ≤ (1164496832277/10000000000000 : ℝ)^3169 := by
    have hnat : (1968805403 : ℕ)^4193*10000000000000^3169 ≤ 1164496832277^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1968805403 10000000000 1164496832277 10000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643328107/5000000000 : ℝ), (274956459/500000000 : ℝ), (-1968805403/10000000000 : ℝ)] ![(21513074587813/50000000000000 : ℝ), (45328882488791/100000000000000 : ℝ), (1164496832277/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643328107/5000000000 : ℝ)|^4193 ≤ (21513074587813/50000000000000 : ℝ)^3169
        have hw : |(2643328107/5000000000 : ℝ)|=(2643328107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(274956459/500000000 : ℝ)|^4193 ≤ (45328882488791/100000000000000 : ℝ)^3169
        have hw : |(274956459/500000000 : ℝ)|=(274956459/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1968805403/10000000000 : ℝ)|^4193 ≤ (1164496832277/10000000000000 : ℝ)^3169
        have hw : |(-1968805403/10000000000 : ℝ)|=(1968805403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1193_s2_7 (p : ℝ) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (271753899/625000000 : ℝ)*x 0 + (2345873941/5000000000 : ℝ)*x 1 + (4029438317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271753899/625000000 : ℝ)^4193 ≤ (6644283513601/20000000000000 : ℝ)^3169 := by
    have hnat : (271753899 : ℕ)^4193*20000000000000^3169 ≤ 6644283513601^3169*625000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271753899 625000000 6644283513601 20000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2345873941/5000000000 : ℝ)^4193 ≤ (574054276499/1562500000000 : ℝ)^3169 := by
    have hnat : (2345873941 : ℕ)^4193*1562500000000^3169 ≤ 574054276499^3169*5000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2345873941 5000000000 574054276499 1562500000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4029438317/10000000000 : ℝ)^4193 ≤ (30039108723941/100000000000000 : ℝ)^3169 := by
    have hnat : (4029438317 : ℕ)^4193*100000000000000^3169 ≤ 30039108723941^3169*10000000000^4193 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4029438317 10000000000 30039108723941 100000000000000 4193 3169 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4193/1024 : ℝ)) 4193 3169 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(271753899/625000000 : ℝ), (2345873941/5000000000 : ℝ), (4029438317/10000000000 : ℝ)] ![(6644283513601/20000000000000 : ℝ), (574054276499/1562500000000 : ℝ), (30039108723941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(271753899/625000000 : ℝ)|^4193 ≤ (6644283513601/20000000000000 : ℝ)^3169
        have hw : |(271753899/625000000 : ℝ)|=(271753899/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2345873941/5000000000 : ℝ)|^4193 ≤ (574054276499/1562500000000 : ℝ)^3169
        have hw : |(2345873941/5000000000 : ℝ)|=(2345873941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4029438317/10000000000 : ℝ)|^4193 ≤ (30039108723941/100000000000000 : ℝ)^3169
        have hw : |(4029438317/10000000000 : ℝ)|=(4029438317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1193_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150469749/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2021/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (593/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (1859/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3271/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2021/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (593/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2021/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (593/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2021/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (593/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2021/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (593/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2021/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (593/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2021/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (593/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (593/10000 : ℝ) ^ (8385/2048 : ℝ) ≤ (473765640786649/50000000000000000000 : ℝ) := by
    have hpowers : (593/10000 : ℝ)^8385 ≤ (473765640786649/50000000000000000000 : ℝ)^2048 := by
      have hnat : (593 : ℕ)^8385*50000000000000000000^2048 ≤ 473765640786649^2048*10000^8385 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        593 10000 473765640786649 50000000000000000000 8385 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (593/10000 : ℝ)) (X := (473765640786649/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8385 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2021/10000 : ℝ) ^ (8385/2048 : ℝ) ≤ (143490456416784721/100000000000000000000 : ℝ) := by
    have hpowers : (2021/10000 : ℝ)^8385 ≤ (143490456416784721/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2021 : ℕ)^8385*100000000000000000000^2048 ≤ 143490456416784721^2048*10000^8385 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2021 10000 143490456416784721 100000000000000000000 8385 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2021/10000 : ℝ)) (X := (143490456416784721/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8385 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000473765640786649/25000000000000000000 : ℝ) ≤ (10000046285752381/10000000000000000 : ℝ) ^ (8385/2048 : ℝ) := by
    have hpowers : (25000473765640786649/25000000000000000000 : ℝ)^2048 ≤ (10000046285752381/10000000000000000 : ℝ)^8385 := by
      have hnat : (25000473765640786649 : ℕ)^2048*10000000000000000^8385 ≤ 10000046285752381^8385*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000473765640786649 25000000000000000000 10000046285752381 10000000000000000 2048 8385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000046285752381/10000000000000000 : ℝ)) (X := (25000473765640786649/25000000000000000000 : ℝ)) (by norm_num) 8385 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100144437987698358019/100000000000000000000 : ℝ) ≤ (10003525911546099/10000000000000000 : ℝ) ^ (8385/2048 : ℝ) := by
    have hpowers : (100144437987698358019/100000000000000000000 : ℝ)^2048 ≤ (10003525911546099/10000000000000000 : ℝ)^8385 := by
      have hnat : (100144437987698358019 : ℕ)^2048*10000000000000000^8385 ≤ 10003525911546099^8385*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100144437987698358019 100000000000000000000 10003525911546099 10000000000000000 2048 8385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003525911546099/10000000000000000 : ℝ)) (X := (100144437987698358019/100000000000000000000 : ℝ)) (by norm_num) 8385 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50143490456416784721/50000000000000000000 : ℝ) ≤ (10007005537339817/10000000000000000 : ℝ) ^ (8385/2048 : ℝ) := by
    have hpowers : (50143490456416784721/50000000000000000000 : ℝ)^2048 ≤ (10007005537339817/10000000000000000 : ℝ)^8385 := by
      have hnat : (50143490456416784721 : ℕ)^2048*10000000000000000^8385 ≤ 10007005537339817^8385*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50143490456416784721 50000000000000000000 10007005537339817 10000000000000000 2048 8385 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007005537339817/10000000000000000 : ℝ)) (X := (50143490456416784721/50000000000000000000 : ℝ)) (by norm_num) 8385 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(473765640786649/50000000000000000000 : ℝ) ≤ ((356898481496576263/357000000000000000 : ℝ)+2*(1739812896859/714000000000000 : ℝ)*(593/10000 : ℝ))^(8385/2048 : ℝ) := by
    rw [show (356898481496576263/357000000000000000 : ℝ)+2*(1739812896859/714000000000000 : ℝ)*(593/10000 : ℝ)=(10000046285752381/10000000000000000 : ℝ) by norm_num, show 1+2*(473765640786649/50000000000000000000 : ℝ)=(25000473765640786649/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(143490456416784721/100000000000000000000 : ℝ)+(473765640786649/50000000000000000000 : ℝ) ≤ ((356898481496576263/357000000000000000 : ℝ)+(1739812896859/714000000000000 : ℝ)*((2021/10000 : ℝ)+(593/10000 : ℝ)))^(8385/2048 : ℝ) := by
    rw [show (356898481496576263/357000000000000000 : ℝ)+(1739812896859/714000000000000 : ℝ)*((2021/10000 : ℝ)+(593/10000 : ℝ))=(10003525911546099/10000000000000000 : ℝ) by norm_num, show 1+(143490456416784721/100000000000000000000 : ℝ)+(473765640786649/50000000000000000000 : ℝ)=(100144437987698358019/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(143490456416784721/100000000000000000000 : ℝ) ≤ ((356898481496576263/357000000000000000 : ℝ)+2*(1739812896859/714000000000000 : ℝ)*(2021/10000 : ℝ))^(8385/2048 : ℝ) := by
    rw [show (356898481496576263/357000000000000000 : ℝ)+2*(1739812896859/714000000000000 : ℝ)*(2021/10000 : ℝ)=(10007005537339817/10000000000000000 : ℝ) by norm_num, show 1+2*(143490456416784721/100000000000000000000 : ℝ)=(50143490456416784721/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (356898481496576263/357000000000000000 : ℝ)*(X 1 0+X 2 0)+(1739812896859/714000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8385/2048 : ℝ)) (lo := (593/10000 : ℝ)) (hi := (2021/10000 : ℝ)) (c := (356898481496576263/357000000000000000 : ℝ)) (alpha := (1739812896859/714000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (356898481496576263/357000000000000000 : ℝ)*(X 0 1+X 2 1)+(1739812896859/714000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8385/2048 : ℝ)) (lo := (593/10000 : ℝ)) (hi := (2021/10000 : ℝ)) (c := (356898481496576263/357000000000000000 : ℝ)) (alpha := (1739812896859/714000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (356898481496576263/357000000000000000 : ℝ)*(X 0 2+X 1 2)+(1739812896859/714000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8385/2048 : ℝ)) (lo := (593/10000 : ℝ)) (hi := (2021/10000 : ℝ)) (c := (356898481496576263/357000000000000000 : ℝ)) (alpha := (1739812896859/714000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-265910571/1250000000 : ℝ)*X 0 0+(5501373789/10000000000 : ℝ)*X 0 1+(645912381/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5371703083/10000000000 : ℝ)*X 1 0+(-1150316607/5000000000 : ℝ)*X 1 1+(6459129/12500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5371704783/10000000000 : ℝ)*X 2 0+(2583650409/5000000000 : ℝ)*X 2 1+(-287579259/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4347882611/10000000000 : ℝ)*X 0 0+(4024929933/10000000000 : ℝ)*X 0 1+(4696213879/10000000000 : ℝ)*X 0 2+(4347882611/10000000000 : ℝ)*X 1 0+(4024929933/10000000000 : ℝ)*X 1 1+(4696213879/10000000000 : ℝ)*X 1 2+(4347882611/10000000000 : ℝ)*X 2 0+(4024929933/10000000000 : ℝ)*X 2 1+(4696213879/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-85094917/400000000 : ℝ)*X 0 0+(646190369/1250000000 : ℝ)*X 0 1+(5499129153/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5286656049/10000000000 : ℝ)*X 1 0+(-1968805647/10000000000 : ℝ)*X 1 1+(343695573/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2643328107/5000000000 : ℝ)*X 2 0+(274956459/500000000 : ℝ)*X 2 1+(-1968805403/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((271753899/625000000 : ℝ)*X 0 0+(2345873941/5000000000 : ℝ)*X 0 1+(4029438317/10000000000 : ℝ)*X 0 2+(271753899/625000000 : ℝ)*X 1 0+(2345873941/5000000000 : ℝ)*X 1 1+(4029438317/10000000000 : ℝ)*X 1 2+(271753899/625000000 : ℝ)*X 2 0+(2345873941/5000000000 : ℝ)*X 2 1+(4029438317/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1193_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9845672105486091307569791/2975000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (151486093/100000000000000 : ℝ)*(base19) + (1027351009/100000000000000 : ℝ)*(base23) + (16511293/10000000000000 : ℝ)*(upper2) + (422758923/100000000000000 : ℝ)*(upper3) + (10175103/5000000000000 : ℝ)*(upper4) + (2241550854342907/100000000000000 : ℝ)*(major0) + (2241550854342907/100000000000000 : ℝ)*(major1) + (2241550854342907/100000000000000 : ℝ)*(major2) + (374171585201749/12500000000000 : ℝ)*(sp0) + (748349862702121/25000000000000 : ℝ)*(sp1) + (187087410933973/6250000000000 : ℝ)*(sp2) + (1489689467080251/100000000000000 : ℝ)*(sp3) + (13460340293/50000000000000 : ℝ)*(sp4) + (3132248831/25000000000000 : ℝ)*(sp7) + (59588079843023/4000000000000 : ℝ)*(f.failure) + (187087475143411/6250000000000 : ℝ)*(f.sum) + (81422480954413/35700000000000000000000000000 : ℝ)*base65 + (138421737983175653/11900000000000000000000000000000 : ℝ)*base68 + (57073505773175653/11900000000000000000000000000000 : ℝ)*base70 + (13912048904624347/11900000000000000000000000000000 : ℝ)*base71 + (53090517458387/35700000000000000000000000000 : ℝ)*base74 + (115639897532575653/11900000000000000000000000000000 : ℝ)*base76 + (79328373002175653/11900000000000000000000000000000 : ℝ)*base78 + (50813617444775653/11900000000000000000000000000000 : ℝ)*base80 + (143623084685413/35700000000000000000000000000 : ℝ)*base81 + (1/50000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2211227/400000000000000000000 : ℝ)*base89 + (2211227/400000000000000000000 : ℝ)*base91 + (2211227/400000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (675355364587575137374971/425000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (299778699/50000000000000 : ℝ)*(base19) + (213978087/25000000000000 : ℝ)*(base23) + (49575971/100000000000000 : ℝ)*(upper2) + (94137887/100000000000000 : ℝ)*(upper3) + (7158139/20000000000000 : ℝ)*(upper5) + (1135947760527873/50000000000000 : ℝ)*(major0) + (1135947760527873/50000000000000 : ℝ)*(major1) + (1135947760527873/50000000000000 : ℝ)*(major2) + (43460381/800000000000 : ℝ)*(sp1) + (2413108669/25000000000000 : ℝ)*(sp2) + (189620148141517/6250000000000 : ℝ)*(sp4) + (12135665352637/400000000000 : ℝ)*(sp5) + (47404872842457/1562500000000 : ℝ)*(sp6) + (188733577359771/12500000000000 : ℝ)*(sp7) + (188733577359771/12500000000000 : ℝ)*(f.failure) + (189620148141517/6250000000000 : ℝ)*(f.sum) + (12465000409431/5950000000000000000000000000 : ℝ)*base66 + (11158041194955967/5950000000000000000000000000000 : ℝ)*base68 + (36426940019355967/5950000000000000000000000000000 : ℝ)*base70 + (8377323671105967/5950000000000000000000000000000 : ℝ)*base72 + (5260396094769/5950000000000000000000000000 : ℝ)*base73 + (45050765204155967/5950000000000000000000000000000 : ℝ)*base76 + (17079813038355967/5950000000000000000000000000000 : ℝ)*base78 + (9961440645755967/5950000000000000000000000000000 : ℝ)*base80 + (20323729041031/5950000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (67479/1250000000000000000000 : ℝ)*base89 + (67479/1250000000000000000000 : ℝ)*base91 + (67479/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1193_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150469749/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2021/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (593/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1859/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3271/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1193_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1193_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150469749/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1859/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3271/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1193_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1193_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1193_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8385/2048 : ℝ) ≤ p) (hpb : p ≤ (4193/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150469749/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1859/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3271/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1193_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
