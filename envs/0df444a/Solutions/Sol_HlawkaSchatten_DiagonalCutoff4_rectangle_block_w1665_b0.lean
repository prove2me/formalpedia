-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1665_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:19:02.978684+00:00
-- url     : https://prove2.me/submissions/824fb6e7-835c-4988-a82b-1eddeb56492c

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
theorem support_rectangle_w1665_s0_0 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-733347559/5000000000 : ℝ)*x 0 + (5767020831/10000000000 : ℝ)*x 1 + (4931560809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (733347559/5000000000 : ℝ)^4979 ≤ (4461332501549/50000000000000 : ℝ)^3955 := by
    have hnat : (733347559 : ℕ)^4979*50000000000000^3955 ≤ 4461332501549^3955*5000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      733347559 5000000000 4461332501549 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5767020831/10000000000 : ℝ)^4979 ≤ (25005112953789/50000000000000 : ℝ)^3955 := by
    have hnat : (5767020831 : ℕ)^4979*50000000000000^3955 ≤ 25005112953789^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5767020831 10000000000 25005112953789 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4931560809/10000000000 : ℝ)^4979 ≤ (20533554535431/50000000000000 : ℝ)^3955 := by
    have hnat : (4931560809 : ℕ)^4979*50000000000000^3955 ≤ 20533554535431^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4931560809 10000000000 20533554535431 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-733347559/5000000000 : ℝ), (5767020831/10000000000 : ℝ), (4931560809/10000000000 : ℝ)] ![(4461332501549/50000000000000 : ℝ), (25005112953789/50000000000000 : ℝ), (20533554535431/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-733347559/5000000000 : ℝ)|^4979 ≤ (4461332501549/50000000000000 : ℝ)^3955
        have hw : |(-733347559/5000000000 : ℝ)|=(733347559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5767020831/10000000000 : ℝ)|^4979 ≤ (25005112953789/50000000000000 : ℝ)^3955
        have hw : |(5767020831/10000000000 : ℝ)|=(5767020831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4931560809/10000000000 : ℝ)|^4979 ≤ (20533554535431/50000000000000 : ℝ)^3955
        have hw : |(4931560809/10000000000 : ℝ)|=(4931560809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_s0_1 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (339477223/625000000 : ℝ)*x 0 + (-1923920961/10000000000 : ℝ)*x 1 + (4931561631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (339477223/625000000 : ℝ)^4979 ≤ (23188399914513/50000000000000 : ℝ)^3955 := by
    have hnat : (339477223 : ℕ)^4979*50000000000000^3955 ≤ 23188399914513^3955*625000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339477223 625000000 23188399914513 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1923920961/10000000000 : ℝ)^4979 ≤ (12556082460031/100000000000000 : ℝ)^3955 := by
    have hnat : (1923920961 : ℕ)^4979*100000000000000^3955 ≤ 12556082460031^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1923920961 10000000000 12556082460031 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4931561631/10000000000 : ℝ)^4979 ≤ (41067117688281/100000000000000 : ℝ)^3955 := by
    have hnat : (4931561631 : ℕ)^4979*100000000000000^3955 ≤ 41067117688281^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4931561631 10000000000 41067117688281 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(339477223/625000000 : ℝ), (-1923920961/10000000000 : ℝ), (4931561631/10000000000 : ℝ)] ![(23188399914513/50000000000000 : ℝ), (12556082460031/100000000000000 : ℝ), (41067117688281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(339477223/625000000 : ℝ)|^4979 ≤ (23188399914513/50000000000000 : ℝ)^3955
        have hw : |(339477223/625000000 : ℝ)|=(339477223/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1923920961/10000000000 : ℝ)|^4979 ≤ (12556082460031/100000000000000 : ℝ)^3955
        have hw : |(-1923920961/10000000000 : ℝ)|=(1923920961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4931561631/10000000000 : ℝ)|^4979 ≤ (41067117688281/100000000000000 : ℝ)^3955
        have hw : |(4931561631/10000000000 : ℝ)|=(4931561631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_s0_2 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5431637389/10000000000 : ℝ)*x 0 + (246578023/500000000 : ℝ)*x 1 + (-1923920073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5431637389/10000000000 : ℝ)^4979 ≤ (23188409701427/50000000000000 : ℝ)^3955 := by
    have hnat : (5431637389 : ℕ)^4979*50000000000000^3955 ≤ 23188409701427^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431637389 10000000000 23188409701427 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (246578023/500000000 : ℝ)^4979 ≤ (1283347044129/3125000000000 : ℝ)^3955 := by
    have hnat : (246578023 : ℕ)^4979*3125000000000^3955 ≤ 1283347044129^3955*500000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246578023 500000000 1283347044129 3125000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1923920073/10000000000 : ℝ)^4979 ≤ (3139018791047/25000000000000 : ℝ)^3955 := by
    have hnat : (1923920073 : ℕ)^4979*25000000000000^3955 ≤ 3139018791047^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1923920073 10000000000 3139018791047 25000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5431637389/10000000000 : ℝ), (246578023/500000000 : ℝ), (-1923920073/10000000000 : ℝ)] ![(23188409701427/50000000000000 : ℝ), (1283347044129/3125000000000 : ℝ), (3139018791047/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5431637389/10000000000 : ℝ)|^4979 ≤ (23188409701427/50000000000000 : ℝ)^3955
        have hw : |(5431637389/10000000000 : ℝ)|=(5431637389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(246578023/500000000 : ℝ)|^4979 ≤ (1283347044129/3125000000000 : ℝ)^3955
        have hw : |(246578023/500000000 : ℝ)|=(246578023/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1923920073/10000000000 : ℝ)|^4979 ≤ (3139018791047/25000000000000 : ℝ)^3955
        have hw : |(-1923920073/10000000000 : ℝ)|=(1923920073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_s0_3 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4083649833/10000000000 : ℝ)*x 0 + (385818387/1250000000 : ℝ)*x 1 + (5288991527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4083649833/10000000000 : ℝ)^4979 ≤ (32385006148131/100000000000000 : ℝ)^3955 := by
    have hnat : (4083649833 : ℕ)^4979*100000000000000^3955 ≤ 32385006148131^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4083649833 10000000000 32385006148131 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (385818387/1250000000 : ℝ)^4979 ≤ (4553243967071/20000000000000 : ℝ)^3955 := by
    have hnat : (385818387 : ℕ)^4979*20000000000000^3955 ≤ 4553243967071^3955*1250000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385818387 1250000000 4553243967071 20000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5288991527/10000000000 : ℝ)^4979 ≤ (4484877399613/10000000000000 : ℝ)^3955 := by
    have hnat : (5288991527 : ℕ)^4979*10000000000000^3955 ≤ 4484877399613^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288991527 10000000000 4484877399613 10000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4083649833/10000000000 : ℝ), (385818387/1250000000 : ℝ), (5288991527/10000000000 : ℝ)] ![(32385006148131/100000000000000 : ℝ), (4553243967071/20000000000000 : ℝ), (4484877399613/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4083649833/10000000000 : ℝ)|^4979 ≤ (32385006148131/100000000000000 : ℝ)^3955
        have hw : |(4083649833/10000000000 : ℝ)|=(4083649833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(385818387/1250000000 : ℝ)|^4979 ≤ (4553243967071/20000000000000 : ℝ)^3955
        have hw : |(385818387/1250000000 : ℝ)|=(385818387/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5288991527/10000000000 : ℝ)|^4979 ≤ (4484877399613/10000000000000 : ℝ)^3955
        have hw : |(5288991527/10000000000 : ℝ)|=(5288991527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_s0_4 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1468827937/10000000000 : ℝ)*x 0 + (247605739/500000000 : ℝ)*x 1 + (2872882873/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1468827937/10000000000 : ℝ)^4979 ≤ (8939002521897/100000000000000 : ℝ)^3955 := by
    have hnat : (1468827937 : ℕ)^4979*100000000000000^3955 ≤ 8939002521897^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1468827937 10000000000 8939002521897 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (247605739/500000000 : ℝ)^4979 ≤ (10320675577599/25000000000000 : ℝ)^3955 := by
    have hnat : (247605739 : ℕ)^4979*25000000000000^3955 ≤ 10320675577599^3955*500000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      247605739 500000000 10320675577599 25000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2872882873/5000000000 : ℝ)^4979 ≤ (3111143447487/6250000000000 : ℝ)^3955 := by
    have hnat : (2872882873 : ℕ)^4979*6250000000000^3955 ≤ 3111143447487^3955*5000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2872882873 5000000000 3111143447487 6250000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1468827937/10000000000 : ℝ), (247605739/500000000 : ℝ), (2872882873/5000000000 : ℝ)] ![(8939002521897/100000000000000 : ℝ), (10320675577599/25000000000000 : ℝ), (3111143447487/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1468827937/10000000000 : ℝ)|^4979 ≤ (8939002521897/100000000000000 : ℝ)^3955
        have hw : |(-1468827937/10000000000 : ℝ)|=(1468827937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(247605739/500000000 : ℝ)|^4979 ≤ (10320675577599/25000000000000 : ℝ)^3955
        have hw : |(247605739/500000000 : ℝ)|=(247605739/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2872882873/5000000000 : ℝ)|^4979 ≤ (3111143447487/6250000000000 : ℝ)^3955
        have hw : |(2872882873/5000000000 : ℝ)|=(2872882873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_s0_5 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (260189139/500000000 : ℝ)*x 0 + (-1109716431/10000000000 : ℝ)*x 1 + (5745764087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (260189139/500000000 : ℝ)^4979 ≤ (2746316493809/6250000000000 : ℝ)^3955 := by
    have hnat : (260189139 : ℕ)^4979*6250000000000^3955 ≤ 2746316493809^3955*500000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260189139 500000000 2746316493809 6250000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1109716431/10000000000 : ℝ)^4979 ≤ (6280659022599/100000000000000 : ℝ)^3955 := by
    have hnat : (1109716431 : ℕ)^4979*100000000000000^3955 ≤ 6280659022599^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1109716431 10000000000 6280659022599 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5745764087/10000000000 : ℝ)^4979 ≤ (49778277065811/100000000000000 : ℝ)^3955 := by
    have hnat : (5745764087 : ℕ)^4979*100000000000000^3955 ≤ 49778277065811^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5745764087 10000000000 49778277065811 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(260189139/500000000 : ℝ), (-1109716431/10000000000 : ℝ), (5745764087/10000000000 : ℝ)] ![(2746316493809/6250000000000 : ℝ), (6280659022599/100000000000000 : ℝ), (49778277065811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(260189139/500000000 : ℝ)|^4979 ≤ (2746316493809/6250000000000 : ℝ)^3955
        have hw : |(260189139/500000000 : ℝ)|=(260189139/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1109716431/10000000000 : ℝ)|^4979 ≤ (6280659022599/100000000000000 : ℝ)^3955
        have hw : |(-1109716431/10000000000 : ℝ)|=(1109716431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5745764087/10000000000 : ℝ)|^4979 ≤ (49778277065811/100000000000000 : ℝ)^3955
        have hw : |(5745764087/10000000000 : ℝ)|=(5745764087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_s0_6 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5203784611/10000000000 : ℝ)*x 0 + (287288049/500000000 : ℝ)*x 1 + (-554859227/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5203784611/10000000000 : ℝ)^4979 ≤ (43941083365093/100000000000000 : ℝ)^3955 := by
    have hnat : (5203784611 : ℕ)^4979*100000000000000^3955 ≤ 43941083365093^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5203784611 10000000000 43941083365093 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (287288049/500000000 : ℝ)^4979 ≤ (24889121589569/50000000000000 : ℝ)^3955 := by
    have hnat : (287288049 : ℕ)^4979*50000000000000^3955 ≤ 24889121589569^3955*500000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287288049 500000000 24889121589569 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (554859227/5000000000 : ℝ)^4979 ≤ (6280673436609/100000000000000 : ℝ)^3955 := by
    have hnat : (554859227 : ℕ)^4979*100000000000000^3955 ≤ 6280673436609^3955*5000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554859227 5000000000 6280673436609 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5203784611/10000000000 : ℝ), (287288049/500000000 : ℝ), (-554859227/5000000000 : ℝ)] ![(43941083365093/100000000000000 : ℝ), (24889121589569/50000000000000 : ℝ), (6280673436609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5203784611/10000000000 : ℝ)|^4979 ≤ (43941083365093/100000000000000 : ℝ)^3955
        have hw : |(5203784611/10000000000 : ℝ)|=(5203784611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(287288049/500000000 : ℝ)|^4979 ≤ (24889121589569/50000000000000 : ℝ)^3955
        have hw : |(287288049/500000000 : ℝ)|=(287288049/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-554859227/5000000000 : ℝ)|^4979 ≤ (6280673436609/100000000000000 : ℝ)^3955
        have hw : |(-554859227/5000000000 : ℝ)|=(554859227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_s0_7 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4089273709/10000000000 : ℝ)*x 0 + (1046960773/2000000000 : ℝ)*x 1 + (3142581441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4089273709/10000000000 : ℝ)^4979 ≤ (32441163194557/100000000000000 : ℝ)^3955 := by
    have hnat : (4089273709 : ℕ)^4979*100000000000000^3955 ≤ 32441163194557^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4089273709 10000000000 32441163194557 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1046960773/2000000000 : ℝ)^4979 ≤ (44271082612301/100000000000000 : ℝ)^3955 := by
    have hnat : (1046960773 : ℕ)^4979*100000000000000^3955 ≤ 44271082612301^3955*2000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046960773 2000000000 44271082612301 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3142581441/10000000000 : ℝ)^4979 ≤ (23287754170973/100000000000000 : ℝ)^3955 := by
    have hnat : (3142581441 : ℕ)^4979*100000000000000^3955 ≤ 23287754170973^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3142581441 10000000000 23287754170973 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4089273709/10000000000 : ℝ), (1046960773/2000000000 : ℝ), (3142581441/10000000000 : ℝ)] ![(32441163194557/100000000000000 : ℝ), (44271082612301/100000000000000 : ℝ), (23287754170973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4089273709/10000000000 : ℝ)|^4979 ≤ (32441163194557/100000000000000 : ℝ)^3955
        have hw : |(4089273709/10000000000 : ℝ)|=(4089273709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1046960773/2000000000 : ℝ)|^4979 ≤ (44271082612301/100000000000000 : ℝ)^3955
        have hw : |(1046960773/2000000000 : ℝ)|=(1046960773/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3142581441/10000000000 : ℝ)|^4979 ≤ (23287754170973/100000000000000 : ℝ)^3955
        have hw : |(3142581441/10000000000 : ℝ)|=(3142581441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1665_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181810191/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (641/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (23043/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4975/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4975 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4975*1^1024 ≤ 0^1024*1^4975 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4975 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4975 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4975/1024 : ℝ) ≤ (1165866661563659269/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4975 ≤ (1165866661563659269/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4975*100000000000000000000^1024 ≤ 1165866661563659269^1024*5^4975 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1165866661563659269 100000000000000000000 4975 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1165866661563659269/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4975 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4975/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4975 := by
      have hnat : (1 : ℕ)^1024*1^4975 ≤ 1^4975*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4975 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4975 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101165866661563659269/100000000000000000000 : ℝ) ≤ (5011943304382719/5000000000000000 : ℝ) ^ (4975/1024 : ℝ) := by
    have hpowers : (101165866661563659269/100000000000000000000 : ℝ)^1024 ≤ (5011943304382719/5000000000000000 : ℝ)^4975 := by
      have hnat : (101165866661563659269 : ℕ)^1024*5000000000000000^4975 ≤ 5011943304382719^4975*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101165866661563659269 100000000000000000000 5011943304382719 5000000000000000 1024 4975 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5011943304382719/5000000000000000 : ℝ)) (X := (101165866661563659269/100000000000000000000 : ℝ)) (by norm_num) 4975 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51165866661563659269/50000000000000000000 : ℝ) ≤ (2511943304382719/2500000000000000 : ℝ) ^ (4975/1024 : ℝ) := by
    have hpowers : (51165866661563659269/50000000000000000000 : ℝ)^1024 ≤ (2511943304382719/2500000000000000 : ℝ)^4975 := by
      have hnat : (51165866661563659269 : ℕ)^1024*2500000000000000^4975 ≤ 2511943304382719^4975*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51165866661563659269 50000000000000000000 2511943304382719 2500000000000000 1024 4975 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2511943304382719/2500000000000000 : ℝ)) (X := (51165866661563659269/50000000000000000000 : ℝ)) (by norm_num) 4975 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(11943304382719/2000000000000000 : ℝ)*(0 : ℝ))^(4975/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(11943304382719/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1165866661563659269/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(11943304382719/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4975/1024 : ℝ) := by
    rw [show (1 : ℝ)+(11943304382719/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5011943304382719/5000000000000000 : ℝ) by norm_num, show 1+(1165866661563659269/100000000000000000000 : ℝ)+(0 : ℝ)=(101165866661563659269/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1165866661563659269/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(11943304382719/2000000000000000 : ℝ)*(2/5 : ℝ))^(4975/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(11943304382719/2000000000000000 : ℝ)*(2/5 : ℝ)=(2511943304382719/2500000000000000 : ℝ) by norm_num, show 1+2*(1165866661563659269/100000000000000000000 : ℝ)=(51165866661563659269/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(11943304382719/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4975/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11943304382719/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(11943304382719/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4975/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11943304382719/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(11943304382719/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4975/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11943304382719/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-733347559/5000000000 : ℝ)*X 0 0+(5767020831/10000000000 : ℝ)*X 0 1+(4931560809/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((339477223/625000000 : ℝ)*X 1 0+(-1923920961/10000000000 : ℝ)*X 1 1+(4931561631/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5431637389/10000000000 : ℝ)*X 2 0+(246578023/500000000 : ℝ)*X 2 1+(-1923920073/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4083649833/10000000000 : ℝ)*X 0 0+(385818387/1250000000 : ℝ)*X 0 1+(5288991527/10000000000 : ℝ)*X 0 2+(4083649833/10000000000 : ℝ)*X 1 0+(385818387/1250000000 : ℝ)*X 1 1+(5288991527/10000000000 : ℝ)*X 1 2+(4083649833/10000000000 : ℝ)*X 2 0+(385818387/1250000000 : ℝ)*X 2 1+(5288991527/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1468827937/10000000000 : ℝ)*X 0 0+(247605739/500000000 : ℝ)*X 0 1+(2872882873/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((260189139/500000000 : ℝ)*X 1 0+(-1109716431/10000000000 : ℝ)*X 1 1+(5745764087/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5203784611/10000000000 : ℝ)*X 2 0+(287288049/500000000 : ℝ)*X 2 1+(-554859227/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4089273709/10000000000 : ℝ)*X 0 0+(1046960773/2000000000 : ℝ)*X 0 1+(3142581441/10000000000 : ℝ)*X 0 2+(4089273709/10000000000 : ℝ)*X 1 0+(1046960773/2000000000 : ℝ)*X 1 1+(3142581441/10000000000 : ℝ)*X 1 2+(4089273709/10000000000 : ℝ)*X 2 0+(1046960773/2000000000 : ℝ)*X 2 1+(3142581441/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (342560069064663822763731/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2354767/1562500000000 : ℝ)*(base1) + (1190078987/100000000000000 : ℝ)*(base19) + (194419759/12500000000000 : ℝ)*(base23) + (36009977/100000000000000 : ℝ)*(base24) + (36396237/12500000000000 : ℝ)*(upper5) + (825501558231061/100000000000000 : ℝ)*(major0) + (825501558231061/100000000000000 : ℝ)*(major1) + (825501558231061/100000000000000 : ℝ)*(major2) + (1196949522809797/100000000000000 : ℝ)*(sp0) + (598477942948123/50000000000000 : ℝ)*(sp1) + (74809717787949/6250000000000 : ℝ)*(sp2) + (56755448589167/12500000000000 : ℝ)*(sp3) + (7703870523/100000000000000 : ℝ)*(sp4) + (51817377/2500000000000 : ℝ)*(sp7) + (454045812113503/100000000000000 : ℝ)*(f.failure) + (18702454312113/1562500000000 : ℝ)*(f.sum) + (259695073665141/100000000000000000000000000000 : ℝ)*base66 + (1697823363165141/200000000000000000000000000000 : ℝ)*base68 + (268342879165141/200000000000000000000000000000 : ℝ)*base70 + (2003410289765141/200000000000000000000000000000 : ℝ)*base72 + (546084227565141/100000000000000000000000000000 : ℝ)*base74 + (608660138165141/200000000000000000000000000000 : ℝ)*base76 + (1055635259365141/200000000000000000000000000000 : ℝ)*base78 + (1326190041765141/200000000000000000000000000000 : ℝ)*base80 + (43200814565141/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (5890927/10000000000000000000000 : ℝ)*base90 + (5890927/10000000000000000000000 : ℝ)*base92 + (5890927/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (48747141695132901057093/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (44849113/2000000000000 : ℝ)*(base19) + (257944261/10000000000000 : ℝ)*(base23) + (379212447/100000000000000 : ℝ)*(base32) + (135990927/50000000000000 : ℝ)*(upper3) + (155175121/100000000000000 : ℝ)*(upper5) + (108622427164833/12500000000000 : ℝ)*(major0) + (108622427164833/12500000000000 : ℝ)*(major1) + (108622427164833/12500000000000 : ℝ)*(major2) + (5809094081/100000000000000 : ℝ)*(sp1) + (676025973/20000000000000 : ℝ)*(sp2) + (251999777807619/20000000000000 : ℝ)*(sp4) + (251998167497673/20000000000000 : ℝ)*(sp5) + (62999646473281/5000000000000 : ℝ)*(sp6) + (238979653201011/50000000000000 : ℝ)*(sp7) + (119489921403617/25000000000000 : ℝ)*(f.failure) + (251999777807619/20000000000000 : ℝ)*(f.sum) + (11616915066573/12500000000000000000000000000 : ℝ)*base66 + (130718648529073/25000000000000000000000000000 : ℝ)*base68 + (273723859579073/25000000000000000000000000000 : ℝ)*base70 + (284776352929073/25000000000000000000000000000 : ℝ)*base72 + (21427893704073/12500000000000000000000000000 : ℝ)*base74 + (285875359479073/25000000000000000000000000000 : ℝ)*base76 + (178873067854073/25000000000000000000000000000 : ℝ)*base78 + (213571183529073/25000000000000000000000000000 : ℝ)*base80 + (66285196241573/12500000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (5139153/2500000000000000000000 : ℝ)*base90 + (5139153/2500000000000000000000 : ℝ)*base92 + (5139153/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1665_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181810191/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (641/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (23043/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1665_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1665_s1_0 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-783261447/5000000000 : ℝ)*x 0 + (342841467/625000000 : ℝ)*x 1 + (1029621377/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (783261447/5000000000 : ℝ)^4979 ≤ (9693834264503/100000000000000 : ℝ)^3955 := by
    have hnat : (783261447 : ℕ)^4979*100000000000000^3955 ≤ 9693834264503^3955*5000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      783261447 5000000000 9693834264503 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (342841467/625000000 : ℝ)^4979 ≤ (46956133424669/100000000000000 : ℝ)^3955 := by
    have hnat : (342841467 : ℕ)^4979*100000000000000^3955 ≤ 46956133424669^3955*625000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342841467 625000000 46956133424669 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1029621377/2000000000 : ℝ)^4979 ≤ (338672127267/781250000000 : ℝ)^3955 := by
    have hnat : (1029621377 : ℕ)^4979*781250000000^3955 ≤ 338672127267^3955*2000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029621377 2000000000 338672127267 781250000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-783261447/5000000000 : ℝ), (342841467/625000000 : ℝ), (1029621377/2000000000 : ℝ)] ![(9693834264503/100000000000000 : ℝ), (46956133424669/100000000000000 : ℝ), (338672127267/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-783261447/5000000000 : ℝ)|^4979 ≤ (9693834264503/100000000000000 : ℝ)^3955
        have hw : |(-783261447/5000000000 : ℝ)|=(783261447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(342841467/625000000 : ℝ)|^4979 ≤ (46956133424669/100000000000000 : ℝ)^3955
        have hw : |(342841467/625000000 : ℝ)|=(342841467/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1029621377/2000000000 : ℝ)|^4979 ≤ (338672127267/781250000000 : ℝ)^3955
        have hw : |(1029621377/2000000000 : ℝ)|=(1029621377/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_s1_1 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535673789/1000000000 : ℝ)*x 0 + (-217697621/1250000000 : ℝ)*x 1 + (5148106627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535673789/1000000000 : ℝ)^4979 ≤ (45573170949889/100000000000000 : ℝ)^3955 := by
    have hnat : (535673789 : ℕ)^4979*100000000000000^3955 ≤ 45573170949889^3955*1000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535673789 1000000000 45573170949889 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217697621/1250000000 : ℝ)^4979 ≤ (1384599935867/12500000000000 : ℝ)^3955 := by
    have hnat : (217697621 : ℕ)^4979*12500000000000^3955 ≤ 1384599935867^3955*1250000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217697621 1250000000 1384599935867 12500000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5148106627/10000000000 : ℝ)^4979 ≤ (43350029555177/100000000000000 : ℝ)^3955 := by
    have hnat : (5148106627 : ℕ)^4979*100000000000000^3955 ≤ 43350029555177^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5148106627 10000000000 43350029555177 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535673789/1000000000 : ℝ), (-217697621/1250000000 : ℝ), (5148106627/10000000000 : ℝ)] ![(45573170949889/100000000000000 : ℝ), (1384599935867/12500000000000 : ℝ), (43350029555177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535673789/1000000000 : ℝ)|^4979 ≤ (45573170949889/100000000000000 : ℝ)^3955
        have hw : |(535673789/1000000000 : ℝ)|=(535673789/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-217697621/1250000000 : ℝ)|^4979 ≤ (1384599935867/12500000000000 : ℝ)^3955
        have hw : |(-217697621/1250000000 : ℝ)|=(217697621/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5148106627/10000000000 : ℝ)|^4979 ≤ (43350029555177/100000000000000 : ℝ)^3955
        have hw : |(5148106627/10000000000 : ℝ)|=(5148106627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_s1_2 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071347467/2000000000 : ℝ)*x 0 + (1287026807/2500000000 : ℝ)*x 1 + (-870790457/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071347467/2000000000 : ℝ)^4979 ≤ (22786582502817/50000000000000 : ℝ)^3955 := by
    have hnat : (1071347467 : ℕ)^4979*50000000000000^3955 ≤ 22786582502817^3955*2000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071347467 2000000000 22786582502817 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1287026807/2500000000 : ℝ)^4979 ≤ (43350035926241/100000000000000 : ℝ)^3955 := by
    have hnat : (1287026807 : ℕ)^4979*100000000000000^3955 ≤ 43350035926241^3955*2500000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1287026807 2500000000 43350035926241 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (870790457/5000000000 : ℝ)^4979 ≤ (11076799054561/100000000000000 : ℝ)^3955 := by
    have hnat : (870790457 : ℕ)^4979*100000000000000^3955 ≤ 11076799054561^3955*5000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870790457 5000000000 11076799054561 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071347467/2000000000 : ℝ), (1287026807/2500000000 : ℝ), (-870790457/5000000000 : ℝ)] ![(22786582502817/50000000000000 : ℝ), (43350035926241/100000000000000 : ℝ), (11076799054561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071347467/2000000000 : ℝ)|^4979 ≤ (22786582502817/50000000000000 : ℝ)^3955
        have hw : |(1071347467/2000000000 : ℝ)|=(1071347467/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1287026807/2500000000 : ℝ)|^4979 ≤ (43350035926241/100000000000000 : ℝ)^3955
        have hw : |(1287026807/2500000000 : ℝ)|=(1287026807/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-870790457/5000000000 : ℝ)|^4979 ≤ (11076799054561/100000000000000 : ℝ)^3955
        have hw : |(-870790457/5000000000 : ℝ)|=(870790457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_s1_3 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2081525577/5000000000 : ℝ)*x 0 + (373520013/1000000000 : ℝ)*x 1 + (578067673/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2081525577/5000000000 : ℝ)^4979 ≤ (6635942050623/20000000000000 : ℝ)^3955 := by
    have hnat : (2081525577 : ℕ)^4979*20000000000000^3955 ≤ 6635942050623^3955*5000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081525577 5000000000 6635942050623 20000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (373520013/1000000000 : ℝ)^4979 ≤ (28945461454563/100000000000000 : ℝ)^3955 := by
    have hnat : (373520013 : ℕ)^4979*100000000000000^3955 ≤ 28945461454563^3955*1000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      373520013 1000000000 28945461454563 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (578067673/1250000000 : ℝ)^4979 ≤ (18937414132421/50000000000000 : ℝ)^3955 := by
    have hnat : (578067673 : ℕ)^4979*50000000000000^3955 ≤ 18937414132421^3955*1250000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      578067673 1250000000 18937414132421 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2081525577/5000000000 : ℝ), (373520013/1000000000 : ℝ), (578067673/1250000000 : ℝ)] ![(6635942050623/20000000000000 : ℝ), (28945461454563/100000000000000 : ℝ), (18937414132421/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2081525577/5000000000 : ℝ)|^4979 ≤ (6635942050623/20000000000000 : ℝ)^3955
        have hw : |(2081525577/5000000000 : ℝ)|=(2081525577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(373520013/1000000000 : ℝ)|^4979 ≤ (28945461454563/100000000000000 : ℝ)^3955
        have hw : |(373520013/1000000000 : ℝ)|=(373520013/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(578067673/1250000000 : ℝ)|^4979 ≤ (18937414132421/50000000000000 : ℝ)^3955
        have hw : |(578067673/1250000000 : ℝ)|=(578067673/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_s1_4 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-156666061/1000000000 : ℝ)*x 0 + (5151453541/10000000000 : ℝ)*x 1 + (274103563/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (156666061/1000000000 : ℝ)^4979 ≤ (1211863390801/12500000000000 : ℝ)^3955 := by
    have hnat : (156666061 : ℕ)^4979*12500000000000^3955 ≤ 1211863390801^3955*1000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156666061 1000000000 1211863390801 12500000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5151453541/10000000000 : ℝ)^4979 ≤ (43385512413747/100000000000000 : ℝ)^3955 := by
    have hnat : (5151453541 : ℕ)^4979*100000000000000^3955 ≤ 43385512413747^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5151453541 10000000000 43385512413747 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (274103563/500000000 : ℝ)^4979 ≤ (9383916087893/20000000000000 : ℝ)^3955 := by
    have hnat : (274103563 : ℕ)^4979*20000000000000^3955 ≤ 9383916087893^3955*500000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274103563 500000000 9383916087893 20000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-156666061/1000000000 : ℝ), (5151453541/10000000000 : ℝ), (274103563/500000000 : ℝ)] ![(1211863390801/12500000000000 : ℝ), (43385512413747/100000000000000 : ℝ), (9383916087893/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-156666061/1000000000 : ℝ)|^4979 ≤ (1211863390801/12500000000000 : ℝ)^3955
        have hw : |(-156666061/1000000000 : ℝ)|=(156666061/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5151453541/10000000000 : ℝ)|^4979 ≤ (43385512413747/100000000000000 : ℝ)^3955
        have hw : |(5151453541/10000000000 : ℝ)|=(5151453541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(274103563/500000000 : ℝ)|^4979 ≤ (9383916087893/20000000000000 : ℝ)^3955
        have hw : |(274103563/500000000 : ℝ)|=(274103563/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_s1_5 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5266408527/10000000000 : ℝ)*x 0 + (-1407616383/10000000000 : ℝ)*x 1 + (2741035717/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5266408527/10000000000 : ℝ)^4979 ≤ (22303915418917/50000000000000 : ℝ)^3955 := by
    have hnat : (5266408527 : ℕ)^4979*50000000000000^3955 ≤ 22303915418917^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266408527 10000000000 22303915418917 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1407616383/10000000000 : ℝ)^4979 ≤ (2118146709627/25000000000000 : ℝ)^3955 := by
    have hnat : (1407616383 : ℕ)^4979*25000000000000^3955 ≤ 2118146709627^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1407616383 10000000000 2118146709627 25000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2741035717/5000000000 : ℝ)^4979 ≤ (46919582314263/100000000000000 : ℝ)^3955 := by
    have hnat : (2741035717 : ℕ)^4979*100000000000000^3955 ≤ 46919582314263^3955*5000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2741035717 5000000000 46919582314263 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5266408527/10000000000 : ℝ), (-1407616383/10000000000 : ℝ), (2741035717/5000000000 : ℝ)] ![(22303915418917/50000000000000 : ℝ), (2118146709627/25000000000000 : ℝ), (46919582314263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5266408527/10000000000 : ℝ)|^4979 ≤ (22303915418917/50000000000000 : ℝ)^3955
        have hw : |(5266408527/10000000000 : ℝ)|=(5266408527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1407616383/10000000000 : ℝ)|^4979 ≤ (2118146709627/25000000000000 : ℝ)^3955
        have hw : |(-1407616383/10000000000 : ℝ)|=(1407616383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2741035717/5000000000 : ℝ)|^4979 ≤ (46919582314263/100000000000000 : ℝ)^3955
        have hw : |(2741035717/5000000000 : ℝ)|=(2741035717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_s1_6 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2633204203/5000000000 : ℝ)*x 0 + (2741035653/5000000000 : ℝ)*x 1 + (-281523347/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2633204203/5000000000 : ℝ)^4979 ≤ (44607829547573/100000000000000 : ℝ)^3955 := by
    have hnat : (2633204203 : ℕ)^4979*100000000000000^3955 ≤ 44607829547573^3955*5000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633204203 5000000000 44607829547573 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2741035653/5000000000 : ℝ)^4979 ≤ (23459790467551/50000000000000 : ℝ)^3955 := by
    have hnat : (2741035653 : ℕ)^4979*50000000000000^3955 ≤ 23459790467551^3955*5000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2741035653 5000000000 23459790467551 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (281523347/2000000000 : ℝ)^4979 ≤ (8472589505797/100000000000000 : ℝ)^3955 := by
    have hnat : (281523347 : ℕ)^4979*100000000000000^3955 ≤ 8472589505797^3955*2000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281523347 2000000000 8472589505797 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2633204203/5000000000 : ℝ), (2741035653/5000000000 : ℝ), (-281523347/2000000000 : ℝ)] ![(44607829547573/100000000000000 : ℝ), (23459790467551/50000000000000 : ℝ), (8472589505797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2633204203/5000000000 : ℝ)|^4979 ≤ (44607829547573/100000000000000 : ℝ)^3955
        have hw : |(2633204203/5000000000 : ℝ)|=(2633204203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2741035653/5000000000 : ℝ)|^4979 ≤ (23459790467551/50000000000000 : ℝ)^3955
        have hw : |(2741035653/5000000000 : ℝ)|=(2741035653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-281523347/2000000000 : ℝ)|^4979 ≤ (8472589505797/100000000000000 : ℝ)^3955
        have hw : |(-281523347/2000000000 : ℝ)|=(281523347/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_s1_7 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4163415903/10000000000 : ℝ)*x 0 + (1153929927/2500000000 : ℝ)*x 1 + (3744143149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4163415903/10000000000 : ℝ)^4979 ≤ (8295842509409/25000000000000 : ℝ)^3955 := by
    have hnat : (4163415903 : ℕ)^4979*25000000000000^3955 ≤ 8295842509409^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4163415903 10000000000 8295842509409 25000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1153929927/2500000000 : ℝ)^4979 ≤ (37783895283211/100000000000000 : ℝ)^3955 := by
    have hnat : (1153929927 : ℕ)^4979*100000000000000^3955 ≤ 37783895283211^3955*2500000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1153929927 2500000000 37783895283211 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3744143149/10000000000 : ℝ)^4979 ≤ (29032734655161/100000000000000 : ℝ)^3955 := by
    have hnat : (3744143149 : ℕ)^4979*100000000000000^3955 ≤ 29032734655161^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3744143149 10000000000 29032734655161 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4163415903/10000000000 : ℝ), (1153929927/2500000000 : ℝ), (3744143149/10000000000 : ℝ)] ![(8295842509409/25000000000000 : ℝ), (37783895283211/100000000000000 : ℝ), (29032734655161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4163415903/10000000000 : ℝ)|^4979 ≤ (8295842509409/25000000000000 : ℝ)^3955
        have hw : |(4163415903/10000000000 : ℝ)|=(4163415903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1153929927/2500000000 : ℝ)|^4979 ≤ (37783895283211/100000000000000 : ℝ)^3955
        have hw : |(1153929927/2500000000 : ℝ)|=(1153929927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3744143149/10000000000 : ℝ)|^4979 ≤ (29032734655161/100000000000000 : ℝ)^3955
        have hw : |(3744143149/10000000000 : ℝ)|=(3744143149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1665_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181810191/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (23043/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (641/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (9951/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8563/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (23043/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (641/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (23043/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (641/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (23043/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (641/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (23043/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (641/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (23043/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (641/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (23043/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (641/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (641/12500 : ℝ) ^ (4975/1024 : ℝ) ≤ (5400244945843/10000000000000000000 : ℝ) := by
    have hpowers : (641/12500 : ℝ)^4975 ≤ (5400244945843/10000000000000000000 : ℝ)^1024 := by
      have hnat : (641 : ℕ)^4975*10000000000000000000^1024 ≤ 5400244945843^1024*12500^4975 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        641 12500 5400244945843 10000000000000000000 4975 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (641/12500 : ℝ)) (X := (5400244945843/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4975 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (23043/100000 : ℝ) ^ (4975/1024 : ℝ) ≤ (9997020507080733/12500000000000000000 : ℝ) := by
    have hpowers : (23043/100000 : ℝ)^4975 ≤ (9997020507080733/12500000000000000000 : ℝ)^1024 := by
      have hnat : (23043 : ℕ)^4975*12500000000000000000^1024 ≤ 9997020507080733^1024*100000^4975 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23043 100000 9997020507080733 12500000000000000000 4975 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (23043/100000 : ℝ)) (X := (9997020507080733/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4975 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000005400244945843/5000000000000000000 : ℝ) ≤ (2000000444610931/2000000000000000 : ℝ) ^ (4975/1024 : ℝ) := by
    have hpowers : (5000005400244945843/5000000000000000000 : ℝ)^1024 ≤ (2000000444610931/2000000000000000 : ℝ)^4975 := by
      have hnat : (5000005400244945843 : ℕ)^1024*2000000000000000^4975 ≤ 2000000444610931^4975*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000005400244945843 5000000000000000000 2000000444610931 2000000000000000 1024 4975 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000444610931/2000000000000000 : ℝ)) (X := (5000005400244945843/5000000000000000000 : ℝ)) (by norm_num) 4975 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50040015083253052147/50000000000000000000 : ℝ) ≤ (5000823365426533/5000000000000000 : ℝ) ^ (4975/1024 : ℝ) := by
    have hpowers : (50040015083253052147/50000000000000000000 : ℝ)^1024 ≤ (5000823365426533/5000000000000000 : ℝ)^4975 := by
      have hnat : (50040015083253052147 : ℕ)^1024*5000000000000000^4975 ≤ 5000823365426533^4975*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50040015083253052147 50000000000000000000 5000823365426533 5000000000000000 1024 4975 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000823365426533/5000000000000000 : ℝ)) (X := (50040015083253052147/50000000000000000000 : ℝ)) (by norm_num) 4975 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6259997020507080733/6250000000000000000 : ℝ) ≤ (10003291238651477/10000000000000000 : ℝ) ^ (4975/1024 : ℝ) := by
    have hpowers : (6259997020507080733/6250000000000000000 : ℝ)^1024 ≤ (10003291238651477/10000000000000000 : ℝ)^4975 := by
      have hnat : (6259997020507080733 : ℕ)^1024*10000000000000000^4975 ≤ 10003291238651477^4975*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6259997020507080733 6250000000000000000 10003291238651477 10000000000000000 1024 4975 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003291238651477/10000000000000000 : ℝ)) (X := (6259997020507080733/6250000000000000000 : ℝ)) (by norm_num) 4975 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5400244945843/10000000000000000000 : ℝ) ≤ ((179133173754043641109/179150000000000000000 : ℝ)+2*(1644507798411/1791500000000000 : ℝ)*(641/12500 : ℝ))^(4975/1024 : ℝ) := by
    rw [show (179133173754043641109/179150000000000000000 : ℝ)+2*(1644507798411/1791500000000000 : ℝ)*(641/12500 : ℝ)=(2000000444610931/2000000000000000 : ℝ) by norm_num, show 1+2*(5400244945843/10000000000000000000 : ℝ)=(5000005400244945843/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9997020507080733/12500000000000000000 : ℝ)+(5400244945843/10000000000000000000 : ℝ) ≤ ((179133173754043641109/179150000000000000000 : ℝ)+(1644507798411/1791500000000000 : ℝ)*((23043/100000 : ℝ)+(641/12500 : ℝ)))^(4975/1024 : ℝ) := by
    rw [show (179133173754043641109/179150000000000000000 : ℝ)+(1644507798411/1791500000000000 : ℝ)*((23043/100000 : ℝ)+(641/12500 : ℝ))=(5000823365426533/5000000000000000 : ℝ) by norm_num, show 1+(9997020507080733/12500000000000000000 : ℝ)+(5400244945843/10000000000000000000 : ℝ)=(50040015083253052147/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9997020507080733/12500000000000000000 : ℝ) ≤ ((179133173754043641109/179150000000000000000 : ℝ)+2*(1644507798411/1791500000000000 : ℝ)*(23043/100000 : ℝ))^(4975/1024 : ℝ) := by
    rw [show (179133173754043641109/179150000000000000000 : ℝ)+2*(1644507798411/1791500000000000 : ℝ)*(23043/100000 : ℝ)=(10003291238651477/10000000000000000 : ℝ) by norm_num, show 1+2*(9997020507080733/12500000000000000000 : ℝ)=(6259997020507080733/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (179133173754043641109/179150000000000000000 : ℝ)*(X 1 0+X 2 0)+(1644507798411/1791500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4975/1024 : ℝ)) (lo := (641/12500 : ℝ)) (hi := (23043/100000 : ℝ)) (c := (179133173754043641109/179150000000000000000 : ℝ)) (alpha := (1644507798411/1791500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (179133173754043641109/179150000000000000000 : ℝ)*(X 0 1+X 2 1)+(1644507798411/1791500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4975/1024 : ℝ)) (lo := (641/12500 : ℝ)) (hi := (23043/100000 : ℝ)) (c := (179133173754043641109/179150000000000000000 : ℝ)) (alpha := (1644507798411/1791500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (179133173754043641109/179150000000000000000 : ℝ)*(X 0 2+X 1 2)+(1644507798411/1791500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4975/1024 : ℝ)) (lo := (641/12500 : ℝ)) (hi := (23043/100000 : ℝ)) (c := (179133173754043641109/179150000000000000000 : ℝ)) (alpha := (1644507798411/1791500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-783261447/5000000000 : ℝ)*X 0 0+(342841467/625000000 : ℝ)*X 0 1+(1029621377/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((535673789/1000000000 : ℝ)*X 1 0+(-217697621/1250000000 : ℝ)*X 1 1+(5148106627/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1071347467/2000000000 : ℝ)*X 2 0+(1287026807/2500000000 : ℝ)*X 2 1+(-870790457/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2081525577/5000000000 : ℝ)*X 0 0+(373520013/1000000000 : ℝ)*X 0 1+(578067673/1250000000 : ℝ)*X 0 2+(2081525577/5000000000 : ℝ)*X 1 0+(373520013/1000000000 : ℝ)*X 1 1+(578067673/1250000000 : ℝ)*X 1 2+(2081525577/5000000000 : ℝ)*X 2 0+(373520013/1000000000 : ℝ)*X 2 1+(578067673/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-156666061/1000000000 : ℝ)*X 0 0+(5151453541/10000000000 : ℝ)*X 0 1+(274103563/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5266408527/10000000000 : ℝ)*X 1 0+(-1407616383/10000000000 : ℝ)*X 1 1+(2741035717/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2633204203/5000000000 : ℝ)*X 2 0+(2741035653/5000000000 : ℝ)*X 2 1+(-281523347/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4163415903/10000000000 : ℝ)*X 0 0+(1153929927/2500000000 : ℝ)*X 0 1+(3744143149/10000000000 : ℝ)*X 0 2+(4163415903/10000000000 : ℝ)*X 1 0+(1153929927/2500000000 : ℝ)*X 1 1+(3744143149/10000000000 : ℝ)*X 1 2+(4163415903/10000000000 : ℝ)*X 2 0+(1153929927/2500000000 : ℝ)*X 2 1+(3744143149/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9306525821041020870733996731/4478750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1312400207/100000000000000 : ℝ)*(base19) + (32428423/4000000000000 : ℝ)*(base23) + (28140511/12500000000000 : ℝ)*(upper3) + (26056611/25000000000000 : ℝ)*(upper4) + (9848983/12500000000000 : ℝ)*(upper5) + (1022170449764747/50000000000000 : ℝ)*(major0) + (1022170449764747/50000000000000 : ℝ)*(major1) + (1022170449764747/50000000000000 : ℝ)*(major2) + (296423478078297/10000000000000 : ℝ)*(sp0) + (2964243504213127/100000000000000 : ℝ)*(sp1) + (2964244005902759/100000000000000 : ℝ)*(sp2) + (1124431868044753/100000000000000 : ℝ)*(sp3) + (10035830363/100000000000000 : ℝ)*(sp4) + (630642073/12500000000000 : ℝ)*(sp7) + (562218456590669/50000000000000 : ℝ)*(f.failure) + (1482122408306667/50000000000000 : ℝ)*(f.sum) + (10937894350883/44787500000000000000000000000 : ℝ)*base66 + (48677174761912384423/8957500000000000000000000000000000 : ℝ)*base67 + (90002740632464884423/8957500000000000000000000000000000 : ℝ)*base69 + (4522793020669884423/8957500000000000000000000000000000 : ℝ)*base71 + (94306972018771/22393750000000000000000000000 : ℝ)*base73 + (42063744294577615577/8957500000000000000000000000000000 : ℝ)*base76 + (27108903228157384423/8957500000000000000000000000000000 : ℝ)*base77 + (26805033743855115577/8957500000000000000000000000000000 : ℝ)*base80 + (72405189954221/22393750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (39707779/5000000000000000000000 : ℝ)*base89 + (39707779/5000000000000000000000 : ℝ)*base91 + (39707779/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17829524800032250576198047/2239375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (706247559/50000000000000 : ℝ)*(base19) + (392820013/25000000000000 : ℝ)*(base23) + (109035763/50000000000000 : ℝ)*(upper3) + (59668669/50000000000000 : ℝ)*(lower4) + (135234949/100000000000000 : ℝ)*(upper5) + (1042996056139/50000000000 : ℝ)*(major0) + (1042996056139/50000000000 : ℝ)*(major1) + (1042996056139/50000000000 : ℝ)*(major2) + (113236453/800000000000 : ℝ)*(sp1) + (14252422173/100000000000000 : ℝ)*(sp2) + (75615946803047/2500000000000 : ℝ)*(sp4) + (1512311152535069/50000000000000 : ℝ)*(sp5) + (378077756052457/12500000000000 : ℝ)*(sp6) + (143418260879969/12500000000000 : ℝ)*(sp7) + (143418260879969/12500000000000 : ℝ)*(f.failure) + (75615946803047/2500000000000 : ℝ)*(f.sum) + (412540798259/447875000000000000000000000 : ℝ)*base65 + (91930420984698151/8957500000000000000000000000000 : ℝ)*base67 + (7562251346658151/8957500000000000000000000000000 : ℝ)*base69 + (75621907978478151/8957500000000000000000000000000 : ℝ)*base71 + (3907776906337/1791500000000000000000000000 : ℝ)*base73 + (52814191630244349/8957500000000000000000000000000 : ℝ)*base76 + (37277812589365651/8957500000000000000000000000000 : ℝ)*base77 + (356285238948151/8957500000000000000000000000000 : ℝ)*base79 + (3958809240629/1791500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (8035921/1250000000000000000000 : ℝ)*base90 + (8035921/1250000000000000000000 : ℝ)*base92 + (8035921/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1665_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181810191/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (23043/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (641/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9951/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8563/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1665_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1665_s2_0 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-393624837/2500000000 : ℝ)*x 0 + (5445888073/10000000000 : ℝ)*x 1 + (5182405257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (393624837/2500000000 : ℝ)^4979 ≤ (4878007092859/50000000000000 : ℝ)^3955 := by
    have hnat : (393624837 : ℕ)^4979*50000000000000^3955 ≤ 4878007092859^3955*2500000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393624837 2500000000 4878007092859 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5445888073/10000000000 : ℝ)^4979 ≤ (23265025605533/50000000000000 : ℝ)^3955 := by
    have hnat : (5445888073 : ℕ)^4979*50000000000000^3955 ≤ 23265025605533^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5445888073 10000000000 23265025605533 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5182405257/10000000000 : ℝ)^4979 ≤ (43713934598173/100000000000000 : ℝ)^3955 := by
    have hnat : (5182405257 : ℕ)^4979*100000000000000^3955 ≤ 43713934598173^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182405257 10000000000 43713934598173 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-393624837/2500000000 : ℝ), (5445888073/10000000000 : ℝ), (5182405257/10000000000 : ℝ)] ![(4878007092859/50000000000000 : ℝ), (23265025605533/50000000000000 : ℝ), (43713934598173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-393624837/2500000000 : ℝ)|^4979 ≤ (4878007092859/50000000000000 : ℝ)^3955
        have hw : |(-393624837/2500000000 : ℝ)|=(393624837/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5445888073/10000000000 : ℝ)|^4979 ≤ (23265025605533/50000000000000 : ℝ)^3955
        have hw : |(5445888073/10000000000 : ℝ)|=(5445888073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5182405257/10000000000 : ℝ)|^4979 ≤ (43713934598173/100000000000000 : ℝ)^3955
        have hw : |(5182405257/10000000000 : ℝ)|=(5182405257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_s2_1 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673106101/5000000000 : ℝ)*x 0 + (-42753353/250000000 : ℝ)*x 1 + (1295601359/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673106101/5000000000 : ℝ)^4979 ≤ (45460465623523/100000000000000 : ℝ)^3955 := by
    have hnat : (2673106101 : ℕ)^4979*100000000000000^3955 ≤ 45460465623523^3955*5000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673106101 5000000000 45460465623523 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42753353/250000000 : ℝ)^4979 ≤ (5412798930803/50000000000000 : ℝ)^3955 := by
    have hnat : (42753353 : ℕ)^4979*50000000000000^3955 ≤ 5412798930803^3955*250000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42753353 250000000 5412798930803 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1295601359/2500000000 : ℝ)^4979 ≤ (1366060515593/3125000000000 : ℝ)^3955 := by
    have hnat : (1295601359 : ℕ)^4979*3125000000000^3955 ≤ 1366060515593^3955*2500000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295601359 2500000000 1366060515593 3125000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673106101/5000000000 : ℝ), (-42753353/250000000 : ℝ), (1295601359/2500000000 : ℝ)] ![(45460465623523/100000000000000 : ℝ), (5412798930803/50000000000000 : ℝ), (1366060515593/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673106101/5000000000 : ℝ)|^4979 ≤ (45460465623523/100000000000000 : ℝ)^3955
        have hw : |(2673106101/5000000000 : ℝ)|=(2673106101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-42753353/250000000 : ℝ)|^4979 ≤ (5412798930803/50000000000000 : ℝ)^3955
        have hw : |(-42753353/250000000 : ℝ)|=(42753353/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1295601359/2500000000 : ℝ)|^4979 ≤ (1366060515593/3125000000000 : ℝ)^3955
        have hw : |(1295601359/2500000000 : ℝ)|=(1295601359/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_s2_2 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346212253/10000000000 : ℝ)*x 0 + (1036481057/2000000000 : ℝ)*x 1 + (-1710134253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346212253/10000000000 : ℝ)^4979 ≤ (22730233084737/50000000000000 : ℝ)^3955 := by
    have hnat : (5346212253 : ℕ)^4979*50000000000000^3955 ≤ 22730233084737^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346212253 10000000000 22730233084737 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036481057/2000000000 : ℝ)^4979 ≤ (8742786979101/20000000000000 : ℝ)^3955 := by
    have hnat : (1036481057 : ℕ)^4979*20000000000000^3955 ≤ 8742786979101^3955*2000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036481057 2000000000 8742786979101 20000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1710134253/10000000000 : ℝ)^4979 ≤ (2706399730379/25000000000000 : ℝ)^3955 := by
    have hnat : (1710134253 : ℕ)^4979*25000000000000^3955 ≤ 2706399730379^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1710134253 10000000000 2706399730379 25000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346212253/10000000000 : ℝ), (1036481057/2000000000 : ℝ), (-1710134253/10000000000 : ℝ)] ![(22730233084737/50000000000000 : ℝ), (8742786979101/20000000000000 : ℝ), (2706399730379/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346212253/10000000000 : ℝ)|^4979 ≤ (22730233084737/50000000000000 : ℝ)^3955
        have hw : |(5346212253/10000000000 : ℝ)|=(5346212253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036481057/2000000000 : ℝ)|^4979 ≤ (8742786979101/20000000000000 : ℝ)^3955
        have hw : |(1036481057/2000000000 : ℝ)|=(1036481057/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1710134253/10000000000 : ℝ)|^4979 ≤ (2706399730379/25000000000000 : ℝ)^3955
        have hw : |(-1710134253/10000000000 : ℝ)|=(1710134253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_s2_3 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (83380367/200000000 : ℝ)*x 0 + (119749543/312500000 : ℝ)*x 1 + (4526579487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83380367/200000000 : ℝ)^4979 ≤ (8309898443759/25000000000000 : ℝ)^3955 := by
    have hnat : (83380367 : ℕ)^4979*25000000000000^3955 ≤ 8309898443759^3955*200000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83380367 200000000 8309898443759 25000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (119749543/312500000 : ℝ)^4979 ≤ (14946412403179/50000000000000 : ℝ)^3955 := by
    have hnat : (119749543 : ℕ)^4979*50000000000000^3955 ≤ 14946412403179^3955*312500000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119749543 312500000 14946412403179 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4526579487/10000000000 : ℝ)^4979 ≤ (36867581396191/100000000000000 : ℝ)^3955 := by
    have hnat : (4526579487 : ℕ)^4979*100000000000000^3955 ≤ 36867581396191^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4526579487 10000000000 36867581396191 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83380367/200000000 : ℝ), (119749543/312500000 : ℝ), (4526579487/10000000000 : ℝ)] ![(8309898443759/25000000000000 : ℝ), (14946412403179/50000000000000 : ℝ), (36867581396191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83380367/200000000 : ℝ)|^4979 ≤ (8309898443759/25000000000000 : ℝ)^3955
        have hw : |(83380367/200000000 : ℝ)|=(83380367/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(119749543/312500000 : ℝ)|^4979 ≤ (14946412403179/50000000000000 : ℝ)^3955
        have hw : |(119749543/312500000 : ℝ)|=(119749543/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4526579487/10000000000 : ℝ)|^4979 ≤ (36867581396191/100000000000000 : ℝ)^3955
        have hw : |(4526579487/10000000000 : ℝ)|=(4526579487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_s2_4 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1574565317/10000000000 : ℝ)*x 0 + (5184451721/10000000000 : ℝ)*x 1 + (544381967/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1574565317/10000000000 : ℝ)^4979 ≤ (609783048963/6250000000000 : ℝ)^3955 := by
    have hnat : (1574565317 : ℕ)^4979*6250000000000^3955 ≤ 609783048963^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1574565317 10000000000 609783048963 6250000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184451721/10000000000 : ℝ)^4979 ≤ (2733479196091/6250000000000 : ℝ)^3955 := by
    have hnat : (5184451721 : ℕ)^4979*6250000000000^3955 ≤ 2733479196091^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184451721 10000000000 2733479196091 6250000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (544381967/1000000000 : ℝ)^4979 ≤ (9301560813469/20000000000000 : ℝ)^3955 := by
    have hnat : (544381967 : ℕ)^4979*20000000000000^3955 ≤ 9301560813469^3955*1000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544381967 1000000000 9301560813469 20000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1574565317/10000000000 : ℝ), (5184451721/10000000000 : ℝ), (544381967/1000000000 : ℝ)] ![(609783048963/6250000000000 : ℝ), (2733479196091/6250000000000 : ℝ), (9301560813469/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1574565317/10000000000 : ℝ)|^4979 ≤ (609783048963/6250000000000 : ℝ)^3955
        have hw : |(-1574565317/10000000000 : ℝ)|=(1574565317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184451721/10000000000 : ℝ)|^4979 ≤ (2733479196091/6250000000000 : ℝ)^3955
        have hw : |(5184451721/10000000000 : ℝ)|=(5184451721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(544381967/1000000000 : ℝ)|^4979 ≤ (9301560813469/20000000000000 : ℝ)^3955
        have hw : |(544381967/1000000000 : ℝ)|=(544381967/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_s2_5 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275704279/10000000000 : ℝ)*x 0 + (-289743943/2000000000 : ℝ)*x 1 + (680477477/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275704279/10000000000 : ℝ)^4979 ≤ (22353488500297/50000000000000 : ℝ)^3955 := by
    have hnat : (5275704279 : ℕ)^4979*50000000000000^3955 ≤ 22353488500297^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275704279 10000000000 22353488500297 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (289743943/2000000000 : ℝ)^4979 ≤ (2196304337827/25000000000000 : ℝ)^3955 := by
    have hnat : (289743943 : ℕ)^4979*25000000000000^3955 ≤ 2196304337827^3955*2000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      289743943 2000000000 2196304337827 25000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (680477477/1250000000 : ℝ)^4979 ≤ (23253902818801/50000000000000 : ℝ)^3955 := by
    have hnat : (680477477 : ℕ)^4979*50000000000000^3955 ≤ 23253902818801^3955*1250000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680477477 1250000000 23253902818801 50000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275704279/10000000000 : ℝ), (-289743943/2000000000 : ℝ), (680477477/1250000000 : ℝ)] ![(22353488500297/50000000000000 : ℝ), (2196304337827/25000000000000 : ℝ), (23253902818801/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275704279/10000000000 : ℝ)|^4979 ≤ (22353488500297/50000000000000 : ℝ)^3955
        have hw : |(5275704279/10000000000 : ℝ)|=(5275704279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-289743943/2000000000 : ℝ)|^4979 ≤ (2196304337827/25000000000000 : ℝ)^3955
        have hw : |(-289743943/2000000000 : ℝ)|=(289743943/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(680477477/1250000000 : ℝ)|^4979 ≤ (23253902818801/50000000000000 : ℝ)^3955
        have hw : |(680477477/1250000000 : ℝ)|=(680477477/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_s2_6 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1318926109/2500000000 : ℝ)*x 0 + (2721909791/5000000000 : ℝ)*x 1 + (-724359913/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1318926109/2500000000 : ℝ)^4979 ≤ (44706978675499/100000000000000 : ℝ)^3955 := by
    have hnat : (1318926109 : ℕ)^4979*100000000000000^3955 ≤ 44706978675499^3955*2500000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318926109 2500000000 44706978675499 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2721909791/5000000000 : ℝ)^4979 ≤ (46507803120889/100000000000000 : ℝ)^3955 := by
    have hnat : (2721909791 : ℕ)^4979*100000000000000^3955 ≤ 46507803120889^3955*5000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721909791 5000000000 46507803120889 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (724359913/5000000000 : ℝ)^4979 ≤ (1757043639741/20000000000000 : ℝ)^3955 := by
    have hnat : (724359913 : ℕ)^4979*20000000000000^3955 ≤ 1757043639741^3955*5000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      724359913 5000000000 1757043639741 20000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1318926109/2500000000 : ℝ), (2721909791/5000000000 : ℝ), (-724359913/5000000000 : ℝ)] ![(44706978675499/100000000000000 : ℝ), (46507803120889/100000000000000 : ℝ), (1757043639741/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1318926109/2500000000 : ℝ)|^4979 ≤ (44706978675499/100000000000000 : ℝ)^3955
        have hw : |(1318926109/2500000000 : ℝ)|=(1318926109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2721909791/5000000000 : ℝ)|^4979 ≤ (46507803120889/100000000000000 : ℝ)^3955
        have hw : |(2721909791/5000000000 : ℝ)|=(2721909791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-724359913/5000000000 : ℝ)|^4979 ≤ (1757043639741/20000000000000 : ℝ)^3955
        have hw : |(-724359913/5000000000 : ℝ)|=(724359913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1665_s2_7 (p : ℝ) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1042298123/2500000000 : ℝ)*x 0 + (4521184977/10000000000 : ℝ)*x 1 + (1918718893/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1042298123/2500000000 : ℝ)^4979 ≤ (33241341702539/100000000000000 : ℝ)^3955 := by
    have hnat : (1042298123 : ℕ)^4979*100000000000000^3955 ≤ 33241341702539^3955*2500000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042298123 2500000000 33241341702539 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4521184977/10000000000 : ℝ)^4979 ≤ (230076734867/625000000000 : ℝ)^3955 := by
    have hnat : (4521184977 : ℕ)^4979*625000000000^3955 ≤ 230076734867^3955*10000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4521184977 10000000000 230076734867 625000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1918718893/5000000000 : ℝ)^4979 ≤ (29946380693689/100000000000000 : ℝ)^3955 := by
    have hnat : (1918718893 : ℕ)^4979*100000000000000^3955 ≤ 29946380693689^3955*5000000000^4979 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1918718893 5000000000 29946380693689 100000000000000 4979 3955 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4979/1024 : ℝ)) 4979 3955 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1042298123/2500000000 : ℝ), (4521184977/10000000000 : ℝ), (1918718893/5000000000 : ℝ)] ![(33241341702539/100000000000000 : ℝ), (230076734867/625000000000 : ℝ), (29946380693689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1042298123/2500000000 : ℝ)|^4979 ≤ (33241341702539/100000000000000 : ℝ)^3955
        have hw : |(1042298123/2500000000 : ℝ)|=(1042298123/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4521184977/10000000000 : ℝ)|^4979 ≤ (230076734867/625000000000 : ℝ)^3955
        have hw : |(4521184977/10000000000 : ℝ)|=(4521184977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1918718893/5000000000 : ℝ)|^4979 ≤ (29946380693689/100000000000000 : ℝ)^3955
        have hw : |(1918718893/5000000000 : ℝ)|=(1918718893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1665_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181810191/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8563/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9951/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10691/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8149/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8563/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9951/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8563/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9951/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8563/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9951/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8563/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9951/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8563/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9951/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8563/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9951/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9951/100000 : ℝ) ^ (4975/1024 : ℝ) ≤ (5411245777357/400000000000000000 : ℝ) := by
    have hpowers : (9951/100000 : ℝ)^4975 ≤ (5411245777357/400000000000000000 : ℝ)^1024 := by
      have hnat : (9951 : ℕ)^4975*400000000000000000^1024 ≤ 5411245777357^1024*100000^4975 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9951 100000 5411245777357 400000000000000000 4975 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9951/100000 : ℝ)) (X := (5411245777357/400000000000000000 : ℝ)) (by norm_num) (by norm_num) 4975 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8563/50000 : ℝ) ^ (4975/1024 : ℝ) ≤ (18914515220019981/100000000000000000000 : ℝ) := by
    have hpowers : (8563/50000 : ℝ)^4975 ≤ (18914515220019981/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8563 : ℕ)^4975*100000000000000000000^1024 ≤ 18914515220019981^1024*50000^4975 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8563 50000 18914515220019981 100000000000000000000 4975 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8563/50000 : ℝ)) (X := (18914515220019981/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4975 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (200005411245777357/200000000000000000 : ℝ) ≤ (2000011137801297/2000000000000000 : ℝ) ^ (4975/1024 : ℝ) := by
    have hpowers : (200005411245777357/200000000000000000 : ℝ)^1024 ≤ (2000011137801297/2000000000000000 : ℝ)^4975 := by
      have hnat : (200005411245777357 : ℕ)^1024*2000000000000000^4975 ≤ 2000011137801297^4975*200000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        200005411245777357 200000000000000000 2000011137801297 2000000000000000 1024 4975 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000011137801297/2000000000000000 : ℝ)) (X := (200005411245777357/200000000000000000 : ℝ)) (by norm_num) 4975 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100020267326664359231/100000000000000000000 : ℝ) ≤ (2500104281771229/2500000000000000 : ℝ) ^ (4975/1024 : ℝ) := by
    have hpowers : (100020267326664359231/100000000000000000000 : ℝ)^1024 ≤ (2500104281771229/2500000000000000 : ℝ)^4975 := by
      have hnat : (100020267326664359231 : ℕ)^1024*2500000000000000^4975 ≤ 2500104281771229^4975*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100020267326664359231 100000000000000000000 2500104281771229 2500000000000000 1024 4975 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500104281771229/2500000000000000 : ℝ)) (X := (100020267326664359231/100000000000000000000 : ℝ)) (by norm_num) 4975 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50018914515220019981/50000000000000000000 : ℝ) ≤ (10000778565163347/10000000000000000 : ℝ) ^ (4975/1024 : ℝ) := by
    have hpowers : (50018914515220019981/50000000000000000000 : ℝ)^1024 ≤ (10000778565163347/10000000000000000 : ℝ)^4975 := by
      have hnat : (50018914515220019981 : ℕ)^1024*10000000000000000^4975 ≤ 10000778565163347^4975*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018914515220019981 50000000000000000000 10000778565163347 10000000000000000 1024 4975 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000778565163347/10000000000000000 : ℝ)) (X := (50018914515220019981/50000000000000000000 : ℝ)) (by norm_num) 4975 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5411245777357/400000000000000000 : ℝ) ≤ ((71743206227984596113/71750000000000000000 : ℝ)+2*(361438078431/717500000000000 : ℝ)*(9951/100000 : ℝ))^(4975/1024 : ℝ) := by
    rw [show (71743206227984596113/71750000000000000000 : ℝ)+2*(361438078431/717500000000000 : ℝ)*(9951/100000 : ℝ)=(2000011137801297/2000000000000000 : ℝ) by norm_num, show 1+2*(5411245777357/400000000000000000 : ℝ)=(200005411245777357/200000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18914515220019981/100000000000000000000 : ℝ)+(5411245777357/400000000000000000 : ℝ) ≤ ((71743206227984596113/71750000000000000000 : ℝ)+(361438078431/717500000000000 : ℝ)*((8563/50000 : ℝ)+(9951/100000 : ℝ)))^(4975/1024 : ℝ) := by
    rw [show (71743206227984596113/71750000000000000000 : ℝ)+(361438078431/717500000000000 : ℝ)*((8563/50000 : ℝ)+(9951/100000 : ℝ))=(2500104281771229/2500000000000000 : ℝ) by norm_num, show 1+(18914515220019981/100000000000000000000 : ℝ)+(5411245777357/400000000000000000 : ℝ)=(100020267326664359231/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18914515220019981/100000000000000000000 : ℝ) ≤ ((71743206227984596113/71750000000000000000 : ℝ)+2*(361438078431/717500000000000 : ℝ)*(8563/50000 : ℝ))^(4975/1024 : ℝ) := by
    rw [show (71743206227984596113/71750000000000000000 : ℝ)+2*(361438078431/717500000000000 : ℝ)*(8563/50000 : ℝ)=(10000778565163347/10000000000000000 : ℝ) by norm_num, show 1+2*(18914515220019981/100000000000000000000 : ℝ)=(50018914515220019981/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (71743206227984596113/71750000000000000000 : ℝ)*(X 1 0+X 2 0)+(361438078431/717500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4975/1024 : ℝ)) (lo := (9951/100000 : ℝ)) (hi := (8563/50000 : ℝ)) (c := (71743206227984596113/71750000000000000000 : ℝ)) (alpha := (361438078431/717500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (71743206227984596113/71750000000000000000 : ℝ)*(X 0 1+X 2 1)+(361438078431/717500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4975/1024 : ℝ)) (lo := (9951/100000 : ℝ)) (hi := (8563/50000 : ℝ)) (c := (71743206227984596113/71750000000000000000 : ℝ)) (alpha := (361438078431/717500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (71743206227984596113/71750000000000000000 : ℝ)*(X 0 2+X 1 2)+(361438078431/717500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4975/1024 : ℝ)) (lo := (9951/100000 : ℝ)) (hi := (8563/50000 : ℝ)) (c := (71743206227984596113/71750000000000000000 : ℝ)) (alpha := (361438078431/717500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-393624837/2500000000 : ℝ)*X 0 0+(5445888073/10000000000 : ℝ)*X 0 1+(5182405257/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673106101/5000000000 : ℝ)*X 1 0+(-42753353/250000000 : ℝ)*X 1 1+(1295601359/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346212253/10000000000 : ℝ)*X 2 0+(1036481057/2000000000 : ℝ)*X 2 1+(-1710134253/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((83380367/200000000 : ℝ)*X 0 0+(119749543/312500000 : ℝ)*X 0 1+(4526579487/10000000000 : ℝ)*X 0 2+(83380367/200000000 : ℝ)*X 1 0+(119749543/312500000 : ℝ)*X 1 1+(4526579487/10000000000 : ℝ)*X 1 2+(83380367/200000000 : ℝ)*X 2 0+(119749543/312500000 : ℝ)*X 2 1+(4526579487/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1574565317/10000000000 : ℝ)*X 0 0+(5184451721/10000000000 : ℝ)*X 0 1+(544381967/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5275704279/10000000000 : ℝ)*X 1 0+(-289743943/2000000000 : ℝ)*X 1 1+(680477477/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1318926109/2500000000 : ℝ)*X 2 0+(2721909791/5000000000 : ℝ)*X 2 1+(-724359913/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1042298123/2500000000 : ℝ)*X 0 0+(4521184977/10000000000 : ℝ)*X 0 1+(1918718893/5000000000 : ℝ)*X 0 2+(1042298123/2500000000 : ℝ)*X 1 0+(4521184977/10000000000 : ℝ)*X 1 1+(1918718893/5000000000 : ℝ)*X 1 2+(1042298123/2500000000 : ℝ)*X 2 0+(4521184977/10000000000 : ℝ)*X 2 1+(1918718893/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1665_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11761415028288681340589517591/896875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2022939803/100000000000000 : ℝ)*(base19) + (1955539483/100000000000000 : ℝ)*(base23) + (55390007/100000000000000 : ℝ)*(lower2) + (37442747/10000000000000 : ℝ)*(upper3) + (39585247/20000000000000 : ℝ)*(upper5) + (1308769530834869/50000000000000 : ℝ)*(major0) + (1308769530834869/50000000000000 : ℝ)*(major1) + (1308769530834869/50000000000000 : ℝ)*(major2) + (948835592853683/25000000000000 : ℝ)*(sp0) + (3795365904831521/100000000000000 : ℝ)*(sp1) + (1897682986115921/50000000000000 : ℝ)*(sp2) + (1439698828835627/100000000000000 : ℝ)*(sp3) + (1597272287/6250000000000 : ℝ)*(sp4) + (5464803379/50000000000000 : ℝ)*(sp7) + (287941951688477/20000000000000 : ℝ)*(f.failure) + (948841981942831/25000000000000 : ℝ)*(f.sum) + (1083828404583/2242187500000000000000000000 : ℝ)*base65 + (19201613545058835803/3587500000000000000000000000000000 : ℝ)*base68 + (431097175121335803/3587500000000000000000000000000000 : ℝ)*base70 + (9623647454266164197/3587500000000000000000000000000000 : ℝ)*base71 + (45905532476793/8968750000000000000000000000 : ℝ)*base74 + (1818517568921335803/3587500000000000000000000000000000 : ℝ)*base76 + (37490060108333835803/3587500000000000000000000000000000 : ℝ)*base78 + (19943145138483835803/3587500000000000000000000000000000 : ℝ)*base80 + (137954614363953/35875000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (15869107/2000000000000000000000 : ℝ)*base89 + (15869107/2000000000000000000000 : ℝ)*base91 + (15869107/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1528949074436144551364517339/179375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1224382093/100000000000000 : ℝ)*(base19) + (1477172669/100000000000000 : ℝ)*(base23) + (104052527/50000000000000 : ℝ)*(upper3) + (16332407/25000000000000 : ℝ)*(lower4) + (155785613/100000000000000 : ℝ)*(upper5) + (265902700163999/10000000000000 : ℝ)*(major0) + (265902700163999/10000000000000 : ℝ)*(major1) + (265902700163999/10000000000000 : ℝ)*(major2) + (15532280509/100000000000000 : ℝ)*(sp1) + (16596510863/100000000000000 : ℝ)*(sp2) + (3855524590828793/100000000000000 : ℝ)*(sp4) + (3855507834166191/100000000000000 : ℝ)*(sp5) + (192775325857263/5000000000000 : ℝ)*(sp6) + (9140807052037/625000000000 : ℝ)*(sp7) + (9140807052037/625000000000 : ℝ)*(f.failure) + (3855524590828793/100000000000000 : ℝ)*(f.sum) + (2736081147187/7175000000000000000000000000 : ℝ)*base66 + (1197098430957335887/717500000000000000000000000000000 : ℝ)*base67 + (1629417410409835887/717500000000000000000000000000000 : ℝ)*base69 + (727873819537664113/717500000000000000000000000000000 : ℝ)*base72 + (19696836637013/7175000000000000000000000000 : ℝ)*base73 + (1065656515684835887/717500000000000000000000000000000 : ℝ)*base75 + (4511185193202335887/717500000000000000000000000000000 : ℝ)*base77 + (3053708948922335887/717500000000000000000000000000000 : ℝ)*base79 + (13808193410463/7175000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (159067/62500000000000000000 : ℝ)*base89 + (159067/62500000000000000000 : ℝ)*base91 + (159067/62500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1665_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181810191/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8563/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9951/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10691/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8149/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1665_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1665_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181810191/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10691/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8149/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1665_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1665_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1665_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4975/1024 : ℝ) ≤ p) (hpb : p ≤ (4979/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (181810191/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10691/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8149/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1665_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
