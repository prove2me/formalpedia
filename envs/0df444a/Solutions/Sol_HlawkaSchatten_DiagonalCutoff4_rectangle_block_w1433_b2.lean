-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1433_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:55:07.701426+00:00
-- url     : https://prove2.me/submissions/9dc3c61e-9544-4af3-85ec-edc7e435b00b

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
theorem support_rectangle_w1433_s6_0 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-245985909/1250000000 : ℝ)*x 0 + (1081603261/2000000000 : ℝ)*x 1 + (1049398657/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (245985909/1250000000 : ℝ)^4393 ≤ (375200308257/3125000000000 : ℝ)^3369 := by
    have hnat : (245985909 : ℕ)^4393*3125000000000^3369 ≤ 375200308257^3369*1250000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245985909 1250000000 375200308257 3125000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081603261/2000000000 : ℝ)^4393 ≤ (44863741371157/100000000000000 : ℝ)^3369 := by
    have hnat : (1081603261 : ℕ)^4393*100000000000000^3369 ≤ 44863741371157^3369*2000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081603261 2000000000 44863741371157 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049398657/2000000000 : ℝ)^4393 ≤ (43129848746891/100000000000000 : ℝ)^3369 := by
    have hnat : (1049398657 : ℕ)^4393*100000000000000^3369 ≤ 43129848746891^3369*2000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049398657 2000000000 43129848746891 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-245985909/1250000000 : ℝ), (1081603261/2000000000 : ℝ), (1049398657/2000000000 : ℝ)] ![(375200308257/3125000000000 : ℝ), (44863741371157/100000000000000 : ℝ), (43129848746891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-245985909/1250000000 : ℝ)|^4393 ≤ (375200308257/3125000000000 : ℝ)^3369
        have hw : |(-245985909/1250000000 : ℝ)|=(245985909/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081603261/2000000000 : ℝ)|^4393 ≤ (44863741371157/100000000000000 : ℝ)^3369
        have hw : |(1081603261/2000000000 : ℝ)|=(1081603261/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049398657/2000000000 : ℝ)|^4393 ≤ (43129848746891/100000000000000 : ℝ)^3369
        have hw : |(1049398657/2000000000 : ℝ)|=(1049398657/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s6_1 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267362207/500000000 : ℝ)*x 0 + (-512465981/2500000000 : ℝ)*x 1 + (1049398657/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267362207/500000000 : ℝ)^4393 ≤ (22103739026249/50000000000000 : ℝ)^3369 := by
    have hnat : (267362207 : ℕ)^4393*50000000000000^3369 ≤ 22103739026249^3369*500000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267362207 500000000 22103739026249 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (512465981/2500000000 : ℝ)^4393 ≤ (6331336593813/50000000000000 : ℝ)^3369 := by
    have hnat : (512465981 : ℕ)^4393*50000000000000^3369 ≤ 6331336593813^3369*2500000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512465981 2500000000 6331336593813 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049398657/2000000000 : ℝ)^4393 ≤ (43129848746891/100000000000000 : ℝ)^3369 := by
    have hnat : (1049398657 : ℕ)^4393*100000000000000^3369 ≤ 43129848746891^3369*2000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049398657 2000000000 43129848746891 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267362207/500000000 : ℝ), (-512465981/2500000000 : ℝ), (1049398657/2000000000 : ℝ)] ![(22103739026249/50000000000000 : ℝ), (6331336593813/50000000000000 : ℝ), (43129848746891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267362207/500000000 : ℝ)|^4393 ≤ (22103739026249/50000000000000 : ℝ)^3369
        have hw : |(267362207/500000000 : ℝ)|=(267362207/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-512465981/2500000000 : ℝ)|^4393 ≤ (6331336593813/50000000000000 : ℝ)^3369
        have hw : |(-512465981/2500000000 : ℝ)|=(512465981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049398657/2000000000 : ℝ)|^4393 ≤ (43129848746891/100000000000000 : ℝ)^3369
        have hw : |(1049398657/2000000000 : ℝ)|=(1049398657/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s6_2 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267362207/500000000 : ℝ)*x 0 + (1049398657/2000000000 : ℝ)*x 1 + (-512465981/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267362207/500000000 : ℝ)^4393 ≤ (22103739026249/50000000000000 : ℝ)^3369 := by
    have hnat : (267362207 : ℕ)^4393*50000000000000^3369 ≤ 22103739026249^3369*500000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267362207 500000000 22103739026249 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049398657/2000000000 : ℝ)^4393 ≤ (43129848746891/100000000000000 : ℝ)^3369 := by
    have hnat : (1049398657 : ℕ)^4393*100000000000000^3369 ≤ 43129848746891^3369*2000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049398657 2000000000 43129848746891 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (512465981/2500000000 : ℝ)^4393 ≤ (6331336593813/50000000000000 : ℝ)^3369 := by
    have hnat : (512465981 : ℕ)^4393*50000000000000^3369 ≤ 6331336593813^3369*2500000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512465981 2500000000 6331336593813 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267362207/500000000 : ℝ), (1049398657/2000000000 : ℝ), (-512465981/2500000000 : ℝ)] ![(22103739026249/50000000000000 : ℝ), (43129848746891/100000000000000 : ℝ), (6331336593813/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267362207/500000000 : ℝ)|^4393 ≤ (22103739026249/50000000000000 : ℝ)^3369
        have hw : |(267362207/500000000 : ℝ)|=(267362207/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049398657/2000000000 : ℝ)|^4393 ≤ (43129848746891/100000000000000 : ℝ)^3369
        have hw : |(1049398657/2000000000 : ℝ)|=(1049398657/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-512465981/2500000000 : ℝ)|^4393 ≤ (6331336593813/50000000000000 : ℝ)^3369
        have hw : |(-512465981/2500000000 : ℝ)|=(512465981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s6_3 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4303373889/10000000000 : ℝ)*x 0 + (4132119511/10000000000 : ℝ)*x 1 + (4480976743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4303373889/10000000000 : ℝ)^4393 ≤ (8326187366961/25000000000000 : ℝ)^3369 := by
    have hnat : (4303373889 : ℕ)^4393*25000000000000^3369 ≤ 8326187366961^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4303373889 10000000000 8326187366961 25000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4132119511/10000000000 : ℝ)^4393 ≤ (31587079907883/100000000000000 : ℝ)^3369 := by
    have hnat : (4132119511 : ℕ)^4393*100000000000000^3369 ≤ 31587079907883^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4132119511 10000000000 31587079907883 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4480976743/10000000000 : ℝ)^4393 ≤ (35108170614623/100000000000000 : ℝ)^3369 := by
    have hnat : (4480976743 : ℕ)^4393*100000000000000^3369 ≤ 35108170614623^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4480976743 10000000000 35108170614623 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4303373889/10000000000 : ℝ), (4132119511/10000000000 : ℝ), (4480976743/10000000000 : ℝ)] ![(8326187366961/25000000000000 : ℝ), (31587079907883/100000000000000 : ℝ), (35108170614623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4303373889/10000000000 : ℝ)|^4393 ≤ (8326187366961/25000000000000 : ℝ)^3369
        have hw : |(4303373889/10000000000 : ℝ)|=(4303373889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4132119511/10000000000 : ℝ)|^4393 ≤ (31587079907883/100000000000000 : ℝ)^3369
        have hw : |(4132119511/10000000000 : ℝ)|=(4132119511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4480976743/10000000000 : ℝ)|^4393 ≤ (35108170614623/100000000000000 : ℝ)^3369
        have hw : |(4480976743/10000000000 : ℝ)|=(4480976743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s6_4 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1967898523/10000000000 : ℝ)*x 0 + (1049514863/2000000000 : ℝ)*x 1 + (1081486459/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1967898523/10000000000 : ℝ)^4393 ≤ (12006499372799/100000000000000 : ℝ)^3369 := by
    have hnat : (1967898523 : ℕ)^4393*100000000000000^3369 ≤ 12006499372799^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1967898523 10000000000 12006499372799 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049514863/2000000000 : ℝ)^4393 ≤ (43136076530069/100000000000000 : ℝ)^3369 := by
    have hnat : (1049514863 : ℕ)^4393*100000000000000^3369 ≤ 43136076530069^3369*2000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049514863 2000000000 43136076530069 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081486459/2000000000 : ℝ)^4393 ≤ (44857424080717/100000000000000 : ℝ)^3369 := by
    have hnat : (1081486459 : ℕ)^4393*100000000000000^3369 ≤ 44857424080717^3369*2000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081486459 2000000000 44857424080717 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1967898523/10000000000 : ℝ), (1049514863/2000000000 : ℝ), (1081486459/2000000000 : ℝ)] ![(12006499372799/100000000000000 : ℝ), (43136076530069/100000000000000 : ℝ), (44857424080717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1967898523/10000000000 : ℝ)|^4393 ≤ (12006499372799/100000000000000 : ℝ)^3369
        have hw : |(-1967898523/10000000000 : ℝ)|=(1967898523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049514863/2000000000 : ℝ)|^4393 ≤ (43136076530069/100000000000000 : ℝ)^3369
        have hw : |(1049514863/2000000000 : ℝ)|=(1049514863/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081486459/2000000000 : ℝ)|^4393 ≤ (44857424080717/100000000000000 : ℝ)^3369
        have hw : |(1081486459/2000000000 : ℝ)|=(1081486459/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s6_5 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652683031/5000000000 : ℝ)*x 0 + (-377884977/2000000000 : ℝ)*x 1 + (5407432339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652683031/5000000000 : ℝ)^4393 ≤ (43756563236917/100000000000000 : ℝ)^3369 := by
    have hnat : (2652683031 : ℕ)^4393*100000000000000^3369 ≤ 43756563236917^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652683031 5000000000 43756563236917 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (377884977/2000000000 : ℝ)^4393 ≤ (2846503045391/25000000000000 : ℝ)^3369 := by
    have hnat : (377884977 : ℕ)^4393*25000000000000^3369 ≤ 2846503045391^3369*2000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      377884977 2000000000 2846503045391 25000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407432339/10000000000 : ℝ)^4393 ≤ (44857424556661/100000000000000 : ℝ)^3369 := by
    have hnat : (5407432339 : ℕ)^4393*100000000000000^3369 ≤ 44857424556661^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407432339 10000000000 44857424556661 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652683031/5000000000 : ℝ), (-377884977/2000000000 : ℝ), (5407432339/10000000000 : ℝ)] ![(43756563236917/100000000000000 : ℝ), (2846503045391/25000000000000 : ℝ), (44857424556661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652683031/5000000000 : ℝ)|^4393 ≤ (43756563236917/100000000000000 : ℝ)^3369
        have hw : |(2652683031/5000000000 : ℝ)|=(2652683031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-377884977/2000000000 : ℝ)|^4393 ≤ (2846503045391/25000000000000 : ℝ)^3369
        have hw : |(-377884977/2000000000 : ℝ)|=(377884977/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407432339/10000000000 : ℝ)|^4393 ≤ (44857424556661/100000000000000 : ℝ)^3369
        have hw : |(5407432339/10000000000 : ℝ)|=(5407432339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s6_6 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305366249/10000000000 : ℝ)*x 0 + (675929021/1250000000 : ℝ)*x 1 + (-944712433/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305366249/10000000000 : ℝ)^4393 ≤ (21878282623999/50000000000000 : ℝ)^3369 := by
    have hnat : (5305366249 : ℕ)^4393*50000000000000^3369 ≤ 21878282623999^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305366249 10000000000 21878282623999 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (675929021/1250000000 : ℝ)^4393 ≤ (44857422706969/100000000000000 : ℝ)^3369 := by
    have hnat : (675929021 : ℕ)^4393*100000000000000^3369 ≤ 44857422706969^3369*1250000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675929021 1250000000 44857422706969 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (944712433/5000000000 : ℝ)^4393 ≤ (5693006016133/50000000000000 : ℝ)^3369 := by
    have hnat : (944712433 : ℕ)^4393*50000000000000^3369 ≤ 5693006016133^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      944712433 5000000000 5693006016133 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305366249/10000000000 : ℝ), (675929021/1250000000 : ℝ), (-944712433/5000000000 : ℝ)] ![(21878282623999/50000000000000 : ℝ), (44857422706969/100000000000000 : ℝ), (5693006016133/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305366249/10000000000 : ℝ)|^4393 ≤ (21878282623999/50000000000000 : ℝ)^3369
        have hw : |(5305366249/10000000000 : ℝ)|=(5305366249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(675929021/1250000000 : ℝ)|^4393 ≤ (44857422706969/100000000000000 : ℝ)^3369
        have hw : |(675929021/1250000000 : ℝ)|=(675929021/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-944712433/5000000000 : ℝ)|^4393 ≤ (5693006016133/50000000000000 : ℝ)^3369
        have hw : |(-944712433/5000000000 : ℝ)|=(944712433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s6_7 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4303398219/10000000000 : ℝ)*x 0 + (895943633/2000000000 : ℝ)*x 1 + (4133384733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4303398219/10000000000 : ℝ)^4393 ≤ (33304994995131/100000000000000 : ℝ)^3369 := by
    have hnat : (4303398219 : ℕ)^4393*100000000000000^3369 ≤ 33304994995131^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4303398219 10000000000 33304994995131 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (895943633/2000000000 : ℝ)^4393 ≤ (35095313091941/100000000000000 : ℝ)^3369 := by
    have hnat : (895943633 : ℕ)^4393*100000000000000^3369 ≤ 35095313091941^3369*2000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895943633 2000000000 35095313091941 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4133384733/10000000000 : ℝ)^4393 ≤ (15799845950711/50000000000000 : ℝ)^3369 := by
    have hnat : (4133384733 : ℕ)^4393*50000000000000^3369 ≤ 15799845950711^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4133384733 10000000000 15799845950711 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4303398219/10000000000 : ℝ), (895943633/2000000000 : ℝ), (4133384733/10000000000 : ℝ)] ![(33304994995131/100000000000000 : ℝ), (35095313091941/100000000000000 : ℝ), (15799845950711/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4303398219/10000000000 : ℝ)|^4393 ≤ (33304994995131/100000000000000 : ℝ)^3369
        have hw : |(4303398219/10000000000 : ℝ)|=(4303398219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(895943633/2000000000 : ℝ)|^4393 ≤ (35095313091941/100000000000000 : ℝ)^3369
        have hw : |(895943633/2000000000 : ℝ)|=(895943633/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4133384733/10000000000 : ℝ)|^4393 ≤ (15799845950711/50000000000000 : ℝ)^3369
        have hw : |(4133384733/10000000000 : ℝ)|=(4133384733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1433_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158325267/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14763/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2269/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2837/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14759/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14763/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2269/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14763/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2269/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14763/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2269/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14763/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2269/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14763/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2269/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14763/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2269/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2269/20000 : ℝ) ^ (549/128 : ℝ) ≤ (8830746680305981/100000000000000000000 : ℝ) := by
    have hpowers : (2269/20000 : ℝ)^549 ≤ (8830746680305981/100000000000000000000 : ℝ)^128 := by
      have hnat : (2269 : ℕ)^549*100000000000000000000^128 ≤ 8830746680305981^128*20000^549 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2269 20000 8830746680305981 100000000000000000000 549 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2269/20000 : ℝ)) (X := (8830746680305981/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have hpowhi : (14763/100000 : ℝ) ^ (549/128 : ℝ) ≤ (27323606204747113/100000000000000000000 : ℝ) := by
    have hpowers : (14763/100000 : ℝ)^549 ≤ (27323606204747113/100000000000000000000 : ℝ)^128 := by
      have hnat : (14763 : ℕ)^549*100000000000000000000^128 ≤ 27323606204747113^128*100000^549 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14763 100000 27323606204747113 100000000000000000000 549 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14763/100000 : ℝ)) (X := (27323606204747113/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008830746680305981/50000000000000000000 : ℝ) ≤ (10000411751926571/10000000000000000 : ℝ) ^ (549/128 : ℝ) := by
    have hpowers : (50008830746680305981/50000000000000000000 : ℝ)^128 ≤ (10000411751926571/10000000000000000 : ℝ)^549 := by
      have hnat : (50008830746680305981 : ℕ)^128*10000000000000000^549 ≤ 10000411751926571^549*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008830746680305981 50000000000000000000 10000411751926571 10000000000000000 128 549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000411751926571/10000000000000000 : ℝ)) (X := (50008830746680305981/50000000000000000000 : ℝ)) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018077176442526547/50000000000000000000 : ℝ) ≤ (10000842826190311/10000000000000000 : ℝ) ^ (549/128 : ℝ) := by
    have hpowers : (50018077176442526547/50000000000000000000 : ℝ)^128 ≤ (10000842826190311/10000000000000000 : ℝ)^549 := by
      have hnat : (50018077176442526547 : ℕ)^128*10000000000000000^549 ≤ 10000842826190311^549*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018077176442526547 50000000000000000000 10000842826190311 10000000000000000 128 549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000842826190311/10000000000000000 : ℝ)) (X := (50018077176442526547/50000000000000000000 : ℝ)) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027323606204747113/50000000000000000000 : ℝ) ≤ (10001273900454051/10000000000000000 : ℝ) ^ (549/128 : ℝ) := by
    have hpowers : (50027323606204747113/50000000000000000000 : ℝ)^128 ≤ (10001273900454051/10000000000000000 : ℝ)^549 := by
      have hnat : (50027323606204747113 : ℕ)^128*10000000000000000^549 ≤ 10001273900454051^549*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027323606204747113 50000000000000000000 10001273900454051 10000000000000000 128 549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001273900454051/10000000000000000 : ℝ)) (X := (50027323606204747113/50000000000000000000 : ℝ)) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8830746680305981/100000000000000000000 : ℝ) ≤ ((17085813146520379539/17090000000000000000 : ℝ)+2*(21553713187/17090000000000 : ℝ)*(2269/20000 : ℝ))^(549/128 : ℝ) := by
    rw [show (17085813146520379539/17090000000000000000 : ℝ)+2*(21553713187/17090000000000 : ℝ)*(2269/20000 : ℝ)=(10000411751926571/10000000000000000 : ℝ) by norm_num, show 1+2*(8830746680305981/100000000000000000000 : ℝ)=(50008830746680305981/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27323606204747113/100000000000000000000 : ℝ)+(8830746680305981/100000000000000000000 : ℝ) ≤ ((17085813146520379539/17090000000000000000 : ℝ)+(21553713187/17090000000000 : ℝ)*((14763/100000 : ℝ)+(2269/20000 : ℝ)))^(549/128 : ℝ) := by
    rw [show (17085813146520379539/17090000000000000000 : ℝ)+(21553713187/17090000000000 : ℝ)*((14763/100000 : ℝ)+(2269/20000 : ℝ))=(10000842826190311/10000000000000000 : ℝ) by norm_num, show 1+(27323606204747113/100000000000000000000 : ℝ)+(8830746680305981/100000000000000000000 : ℝ)=(50018077176442526547/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27323606204747113/100000000000000000000 : ℝ) ≤ ((17085813146520379539/17090000000000000000 : ℝ)+2*(21553713187/17090000000000 : ℝ)*(14763/100000 : ℝ))^(549/128 : ℝ) := by
    rw [show (17085813146520379539/17090000000000000000 : ℝ)+2*(21553713187/17090000000000 : ℝ)*(14763/100000 : ℝ)=(10001273900454051/10000000000000000 : ℝ) by norm_num, show 1+2*(27323606204747113/100000000000000000000 : ℝ)=(50027323606204747113/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17085813146520379539/17090000000000000000 : ℝ)*(X 1 0+X 2 0)+(21553713187/17090000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (549/128 : ℝ)) (lo := (2269/20000 : ℝ)) (hi := (14763/100000 : ℝ)) (c := (17085813146520379539/17090000000000000000 : ℝ)) (alpha := (21553713187/17090000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17085813146520379539/17090000000000000000 : ℝ)*(X 0 1+X 2 1)+(21553713187/17090000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (549/128 : ℝ)) (lo := (2269/20000 : ℝ)) (hi := (14763/100000 : ℝ)) (c := (17085813146520379539/17090000000000000000 : ℝ)) (alpha := (21553713187/17090000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17085813146520379539/17090000000000000000 : ℝ)*(X 0 2+X 1 2)+(21553713187/17090000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (549/128 : ℝ)) (lo := (2269/20000 : ℝ)) (hi := (14763/100000 : ℝ)) (c := (17085813146520379539/17090000000000000000 : ℝ)) (alpha := (21553713187/17090000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-245985909/1250000000 : ℝ)*X 0 0+(1081603261/2000000000 : ℝ)*X 0 1+(1049398657/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267362207/500000000 : ℝ)*X 1 0+(-512465981/2500000000 : ℝ)*X 1 1+(1049398657/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267362207/500000000 : ℝ)*X 2 0+(1049398657/2000000000 : ℝ)*X 2 1+(-512465981/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4303373889/10000000000 : ℝ)*X 0 0+(4132119511/10000000000 : ℝ)*X 0 1+(4480976743/10000000000 : ℝ)*X 0 2+(4303373889/10000000000 : ℝ)*X 1 0+(4132119511/10000000000 : ℝ)*X 1 1+(4480976743/10000000000 : ℝ)*X 1 2+(4303373889/10000000000 : ℝ)*X 2 0+(4132119511/10000000000 : ℝ)*X 2 1+(4480976743/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1967898523/10000000000 : ℝ)*X 0 0+(1049514863/2000000000 : ℝ)*X 0 1+(1081486459/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652683031/5000000000 : ℝ)*X 1 0+(-377884977/2000000000 : ℝ)*X 1 1+(5407432339/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305366249/10000000000 : ℝ)*X 2 0+(675929021/1250000000 : ℝ)*X 2 1+(-944712433/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4303398219/10000000000 : ℝ)*X 0 0+(895943633/2000000000 : ℝ)*X 0 1+(4133384733/10000000000 : ℝ)*X 0 2+(4303398219/10000000000 : ℝ)*X 1 0+(895943633/2000000000 : ℝ)*X 1 1+(4133384733/10000000000 : ℝ)*X 1 2+(4303398219/10000000000 : ℝ)*X 2 0+(895943633/2000000000 : ℝ)*X 2 1+(4133384733/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6906290851248299016848311701/854500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (734799777/50000000000000 : ℝ)*(base19) + (342437031/25000000000000 : ℝ)*(base23) + (53392997/100000000000000 : ℝ)*(lower2) + (201452241/100000000000000 : ℝ)*(upper3) + (64433079/50000000000000 : ℝ)*(upper5) + (4538443602048351/100000000000000 : ℝ)*(major0) + (4538443602048351/100000000000000 : ℝ)*(major1) + (4538443602048351/100000000000000 : ℝ)*(major2) + (388145280314501/6250000000000 : ℝ)*(sp0) + (6210353996015801/100000000000000 : ℝ)*(sp1) + (621035409586723/10000000000000 : ℝ)*(sp2) + (2866515998610933/100000000000000 : ℝ)*(sp3) + (30980583339/100000000000000 : ℝ)*(sp4) + (1933807719/12500000000000 : ℝ)*(sp7) + (573306293814537/20000000000000 : ℝ)*(f.failure) + (1242071093123071/20000000000000 : ℝ)*(f.sum) + (755301675521/170900000000000000000000000 : ℝ)*base66 + (12012934870185909811/1709000000000000000000000000000000 : ℝ)*base68 + (1338540510013909811/1709000000000000000000000000000000 : ℝ)*base70 + (16448314117898909811/1709000000000000000000000000000000 : ℝ)*base72 + (10213172605503/1709000000000000000000000000 : ℝ)*base73 + (32769358890493909811/1709000000000000000000000000000000 : ℝ)*base76 + (14040121304438909811/1709000000000000000000000000000000 : ℝ)*base78 + (7968059801650909811/1709000000000000000000000000000000 : ℝ)*base80 + (9069036077539/1709000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (993621/2000000000000000000000 : ℝ)*base90 + (993621/2000000000000000000000 : ℝ)*base92 + (993621/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (292421934741637610137868121/53406250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (434150097/50000000000000 : ℝ)*(base19) + (1170717371/100000000000000 : ℝ)*(base23) + (311825607/100000000000000 : ℝ)*(lower1) + (57235741/50000000000000 : ℝ)*(upper3) + (11599273/50000000000000 : ℝ)*(lower4) + (47628119/100000000000000 : ℝ)*(upper5) + (571432219856687/12500000000000 : ℝ)*(major0) + (571432219856687/12500000000000 : ℝ)*(major1) + (571432219856687/12500000000000 : ℝ)*(major2) + (2419703843/50000000000000 : ℝ)*(sp2) + (390970734837543/6250000000000 : ℝ)*(sp4) + (3127765444550247/50000000000000 : ℝ)*(sp5) + (625552574727563/10000000000000 : ℝ)*(sp6) + (28873835777921/1000000000000 : ℝ)*(sp7) + (28873835777921/1000000000000 : ℝ)*(f.failure) + (390970734837543/6250000000000 : ℝ)*(f.sum) + (262932740019/85450000000000000000000000 : ℝ)*base66 + (2400253659726372707/213625000000000000000000000000000 : ℝ)*base68 + (955217653353627293/213625000000000000000000000000000 : ℝ)*base69 + (9304307235602127293/213625000000000000000000000000000 : ℝ)*base71 + (2181755026643/854500000000000000000000000 : ℝ)*base74 + (22674459332259377293/213625000000000000000000000000000 : ℝ)*base75 + (1921077471234877293/213625000000000000000000000000000 : ℝ)*base77 + (3937631452564877293/213625000000000000000000000000000 : ℝ)*base79 + (8247531709/4272500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (970093/100000000000000000000 : ℝ)*base90 + (970093/100000000000000000000 : ℝ)*base92 + (970093/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1433_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158325267/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14763/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2269/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2837/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14759/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1433_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1433_s7_0 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1967891993/10000000000 : ℝ)*x 0 + (5407990043/10000000000 : ℝ)*x 1 + (2623508143/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1967891993/10000000000 : ℝ)^4393 ≤ (12006447422643/100000000000000 : ℝ)^3369 := by
    have hnat : (1967891993 : ℕ)^4393*100000000000000^3369 ≤ 12006447422643^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1967891993 10000000000 12006447422643 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407990043/10000000000 : ℝ)^4393 ≤ (4486345728821/10000000000000 : ℝ)^3369 := by
    have hnat : (5407990043 : ℕ)^4393*10000000000000^3369 ≤ 4486345728821^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407990043 10000000000 4486345728821 10000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623508143/5000000000 : ℝ)^4393 ≤ (10782523819911/25000000000000 : ℝ)^3369 := by
    have hnat : (2623508143 : ℕ)^4393*25000000000000^3369 ≤ 10782523819911^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623508143 5000000000 10782523819911 25000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1967891993/10000000000 : ℝ), (5407990043/10000000000 : ℝ), (2623508143/5000000000 : ℝ)] ![(12006447422643/100000000000000 : ℝ), (4486345728821/10000000000000 : ℝ), (10782523819911/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1967891993/10000000000 : ℝ)|^4393 ≤ (12006447422643/100000000000000 : ℝ)^3369
        have hw : |(-1967891993/10000000000 : ℝ)|=(1967891993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407990043/10000000000 : ℝ)|^4393 ≤ (4486345728821/10000000000000 : ℝ)^3369
        have hw : |(5407990043/10000000000 : ℝ)|=(5407990043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623508143/5000000000 : ℝ)|^4393 ≤ (10782523819911/25000000000000 : ℝ)^3369
        have hw : |(2623508143/5000000000 : ℝ)|=(2623508143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s7_1 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534723687/1000000000 : ℝ)*x 0 + (-256230397/1250000000 : ℝ)*x 1 + (5247016189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534723687/1000000000 : ℝ)^4393 ≤ (44207399680623/100000000000000 : ℝ)^3369 := by
    have hnat : (534723687 : ℕ)^4393*100000000000000^3369 ≤ 44207399680623^3369*1000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534723687 1000000000 44207399680623 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (256230397/1250000000 : ℝ)^4393 ≤ (6331253032331/50000000000000 : ℝ)^3369 := by
    have hnat : (256230397 : ℕ)^4393*50000000000000^3369 ≤ 6331253032331^3369*1250000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256230397 1250000000 6331253032331 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247016189/10000000000 : ℝ)^4393 ≤ (10782523559991/25000000000000 : ℝ)^3369 := by
    have hnat : (5247016189 : ℕ)^4393*25000000000000^3369 ≤ 10782523559991^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247016189 10000000000 10782523559991 25000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534723687/1000000000 : ℝ), (-256230397/1250000000 : ℝ), (5247016189/10000000000 : ℝ)] ![(44207399680623/100000000000000 : ℝ), (6331253032331/50000000000000 : ℝ), (10782523559991/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534723687/1000000000 : ℝ)|^4393 ≤ (44207399680623/100000000000000 : ℝ)^3369
        have hw : |(534723687/1000000000 : ℝ)|=(534723687/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-256230397/1250000000 : ℝ)|^4393 ≤ (6331253032331/50000000000000 : ℝ)^3369
        have hw : |(-256230397/1250000000 : ℝ)|=(256230397/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247016189/10000000000 : ℝ)|^4393 ≤ (10782523559991/25000000000000 : ℝ)^3369
        have hw : |(5247016189/10000000000 : ℝ)|=(5247016189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s7_2 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673618393/5000000000 : ℝ)*x 0 + (209880653/400000000 : ℝ)*x 1 + (-512460777/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673618393/5000000000 : ℝ)^4393 ≤ (2762962423443/6250000000000 : ℝ)^3369 := by
    have hnat : (2673618393 : ℕ)^4393*6250000000000^3369 ≤ 2762962423443^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673618393 5000000000 2762962423443 6250000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209880653/400000000 : ℝ)^4393 ≤ (2156504784883/5000000000000 : ℝ)^3369 := by
    have hnat : (209880653 : ℕ)^4393*5000000000000^3369 ≤ 2156504784883^3369*400000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209880653 400000000 2156504784883 5000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (512460777/2500000000 : ℝ)^4393 ≤ (1266250551693/10000000000000 : ℝ)^3369 := by
    have hnat : (512460777 : ℕ)^4393*10000000000000^3369 ≤ 1266250551693^3369*2500000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512460777 2500000000 1266250551693 10000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673618393/5000000000 : ℝ), (209880653/400000000 : ℝ), (-512460777/2500000000 : ℝ)] ![(2762962423443/6250000000000 : ℝ), (2156504784883/5000000000000 : ℝ), (1266250551693/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673618393/5000000000 : ℝ)|^4393 ≤ (2762962423443/6250000000000 : ℝ)^3369
        have hw : |(2673618393/5000000000 : ℝ)|=(2673618393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209880653/400000000 : ℝ)|^4393 ≤ (2156504784883/5000000000000 : ℝ)^3369
        have hw : |(209880653/400000000 : ℝ)|=(209880653/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-512460777/2500000000 : ℝ)|^4393 ≤ (1266250551693/10000000000000 : ℝ)^3369
        have hw : |(-512460777/2500000000 : ℝ)|=(512460777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s7_3 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4303375621/10000000000 : ℝ)*x 0 + (4132172537/10000000000 : ℝ)*x 1 + (140028853/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4303375621/10000000000 : ℝ)^4393 ≤ (6660953389277/20000000000000 : ℝ)^3369 := by
    have hnat : (4303375621 : ℕ)^4393*20000000000000^3369 ≤ 6660953389277^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4303375621 10000000000 6660953389277 20000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4132172537/10000000000 : ℝ)^4393 ≤ (7896902114603/25000000000000 : ℝ)^3369 := by
    have hnat : (4132172537 : ℕ)^4393*25000000000000^3369 ≤ 7896902114603^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4132172537 10000000000 7896902114603 25000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (140028853/312500000 : ℝ)^4393 ≤ (3510762458243/10000000000000 : ℝ)^3369 := by
    have hnat : (140028853 : ℕ)^4393*10000000000000^3369 ≤ 3510762458243^3369*312500000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140028853 312500000 3510762458243 10000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4303375621/10000000000 : ℝ), (4132172537/10000000000 : ℝ), (140028853/312500000 : ℝ)] ![(6660953389277/20000000000000 : ℝ), (7896902114603/25000000000000 : ℝ), (3510762458243/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4303375621/10000000000 : ℝ)|^4393 ≤ (6660953389277/20000000000000 : ℝ)^3369
        have hw : |(4303375621/10000000000 : ℝ)|=(4303375621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4132172537/10000000000 : ℝ)|^4393 ≤ (7896902114603/25000000000000 : ℝ)^3369
        have hw : |(4132172537/10000000000 : ℝ)|=(4132172537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(140028853/312500000 : ℝ)|^4393 ≤ (3510762458243/10000000000000 : ℝ)^3369
        have hw : |(140028853/312500000 : ℝ)|=(140028853/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s7_4 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-491975741/2500000000 : ℝ)*x 0 + (5247596793/10000000000 : ℝ)*x 1 + (1081481351/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (491975741/2500000000 : ℝ)^4393 ≤ (12006534703709/100000000000000 : ℝ)^3369 := by
    have hnat : (491975741 : ℕ)^4393*100000000000000^3369 ≤ 12006534703709^3369*2500000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491975741 2500000000 12006534703709 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247596793/10000000000 : ℝ)^4393 ≤ (43136317465231/100000000000000 : ℝ)^3369 := by
    have hnat : (5247596793 : ℕ)^4393*100000000000000^3369 ≤ 43136317465231^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247596793 10000000000 43136317465231 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081481351/2000000000 : ℝ)^4393 ≤ (700892934639/1562500000000 : ℝ)^3369 := by
    have hnat : (1081481351 : ℕ)^4393*1562500000000^3369 ≤ 700892934639^3369*2000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081481351 2000000000 700892934639 1562500000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-491975741/2500000000 : ℝ), (5247596793/10000000000 : ℝ), (1081481351/2000000000 : ℝ)] ![(12006534703709/100000000000000 : ℝ), (43136317465231/100000000000000 : ℝ), (700892934639/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-491975741/2500000000 : ℝ)|^4393 ≤ (12006534703709/100000000000000 : ℝ)^3369
        have hw : |(-491975741/2500000000 : ℝ)|=(491975741/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247596793/10000000000 : ℝ)|^4393 ≤ (43136317465231/100000000000000 : ℝ)^3369
        have hw : |(5247596793/10000000000 : ℝ)|=(5247596793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081481351/2000000000 : ℝ)|^4393 ≤ (700892934639/1562500000000 : ℝ)^3369
        have hw : |(1081481351/2000000000 : ℝ)|=(1081481351/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_s7_5 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (67240619/156250000 : ℝ)*x 0 + (4479666029/10000000000 : ℝ)*x 1 + (826687349/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67240619/156250000 : ℝ)^4393 ≤ (4163126136629/12500000000000 : ℝ)^3369 := by
    have hnat : (67240619 : ℕ)^4393*12500000000000^3369 ≤ 4163126136629^3369*156250000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67240619 156250000 4163126136629 12500000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4479666029/10000000000 : ℝ)^4393 ≤ (3509478049881/10000000000000 : ℝ)^3369 := by
    have hnat : (4479666029 : ℕ)^4393*10000000000000^3369 ≤ 3509478049881^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4479666029 10000000000 3509478049881 10000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (826687349/2000000000 : ℝ)^4393 ≤ (15800105196433/50000000000000 : ℝ)^3369 := by
    have hnat : (826687349 : ℕ)^4393*50000000000000^3369 ≤ 15800105196433^3369*2000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      826687349 2000000000 15800105196433 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(67240619/156250000 : ℝ), (4479666029/10000000000 : ℝ), (826687349/2000000000 : ℝ)] ![(4163126136629/12500000000000 : ℝ), (3509478049881/10000000000000 : ℝ), (15800105196433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(67240619/156250000 : ℝ)|^4393 ≤ (4163126136629/12500000000000 : ℝ)^3369
        have hw : |(67240619/156250000 : ℝ)|=(67240619/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4479666029/10000000000 : ℝ)|^4393 ≤ (3509478049881/10000000000000 : ℝ)^3369
        have hw : |(4479666029/10000000000 : ℝ)|=(4479666029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(826687349/2000000000 : ℝ)|^4393 ≤ (15800105196433/50000000000000 : ℝ)^3369
        have hw : |(826687349/2000000000 : ℝ)|=(826687349/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1433_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158325267/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14759/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2837/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11349/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14759/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14759/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2837/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14759/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2837/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14759/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2837/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14759/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2837/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14759/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2837/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14759/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2837/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2837/25000 : ℝ) ^ (549/128 : ℝ) ≤ (8840766627077739/100000000000000000000 : ℝ) := by
    have hpowers : (2837/25000 : ℝ)^549 ≤ (8840766627077739/100000000000000000000 : ℝ)^128 := by
      have hnat : (2837 : ℕ)^549*100000000000000000000^128 ≤ 8840766627077739^128*25000^549 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2837 25000 8840766627077739 100000000000000000000 549 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2837/25000 : ℝ)) (X := (8840766627077739/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have hpowhi : (14759/100000 : ℝ) ^ (549/128 : ℝ) ≤ (1705741704828951/6250000000000000000 : ℝ) := by
    have hpowers : (14759/100000 : ℝ)^549 ≤ (1705741704828951/6250000000000000000 : ℝ)^128 := by
      have hnat : (14759 : ℕ)^549*6250000000000000000^128 ≤ 1705741704828951^128*100000^549 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14759 100000 1705741704828951 6250000000000000000 549 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14759/100000 : ℝ)) (X := (1705741704828951/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008840766627077739/50000000000000000000 : ℝ) ≤ (2500103054773939/2500000000000000 : ℝ) ^ (549/128 : ℝ) := by
    have hpowers : (50008840766627077739/50000000000000000000 : ℝ)^128 ≤ (2500103054773939/2500000000000000 : ℝ)^549 := by
      have hnat : (50008840766627077739 : ℕ)^128*2500000000000000^549 ≤ 2500103054773939^549*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008840766627077739 50000000000000000000 2500103054773939 2500000000000000 128 549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500103054773939/2500000000000000 : ℝ)) (X := (50008840766627077739/50000000000000000000 : ℝ)) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007226526780868191/20000000000000000000 : ℝ) ≤ (10000842319950011/10000000000000000 : ℝ) ^ (549/128 : ℝ) := by
    have hpowers : (20007226526780868191/20000000000000000000 : ℝ)^128 ≤ (10000842319950011/10000000000000000 : ℝ)^549 := by
      have hnat : (20007226526780868191 : ℕ)^128*10000000000000000^549 ≤ 10000842319950011^549*20000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007226526780868191 20000000000000000000 10000842319950011 10000000000000000 128 549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000842319950011/10000000000000000 : ℝ)) (X := (20007226526780868191/20000000000000000000 : ℝ)) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (3126705741704828951/3125000000000000000 : ℝ) ≤ (5000636210402133/5000000000000000 : ℝ) ^ (549/128 : ℝ) := by
    have hpowers : (3126705741704828951/3125000000000000000 : ℝ)^128 ≤ (5000636210402133/5000000000000000 : ℝ)^549 := by
      have hnat : (3126705741704828951 : ℕ)^128*5000000000000000^549 ≤ 5000636210402133^549*3125000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126705741704828951 3125000000000000000 5000636210402133 5000000000000000 128 549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000636210402133/5000000000000000 : ℝ)) (X := (3126705741704828951/3125000000000000000 : ℝ)) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8840766627077739/100000000000000000000 : ℝ) ≤ ((8525411127586863059/8527500000000000000 : ℝ)+2*(86020170851/68220000000000 : ℝ)*(2837/25000 : ℝ))^(549/128 : ℝ) := by
    rw [show (8525411127586863059/8527500000000000000 : ℝ)+2*(86020170851/68220000000000 : ℝ)*(2837/25000 : ℝ)=(2500103054773939/2500000000000000 : ℝ) by norm_num, show 1+2*(8840766627077739/100000000000000000000 : ℝ)=(50008840766627077739/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1705741704828951/6250000000000000000 : ℝ)+(8840766627077739/100000000000000000000 : ℝ) ≤ ((8525411127586863059/8527500000000000000 : ℝ)+(86020170851/68220000000000 : ℝ)*((14759/100000 : ℝ)+(2837/25000 : ℝ)))^(549/128 : ℝ) := by
    rw [show (8525411127586863059/8527500000000000000 : ℝ)+(86020170851/68220000000000 : ℝ)*((14759/100000 : ℝ)+(2837/25000 : ℝ))=(10000842319950011/10000000000000000 : ℝ) by norm_num, show 1+(1705741704828951/6250000000000000000 : ℝ)+(8840766627077739/100000000000000000000 : ℝ)=(20007226526780868191/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1705741704828951/6250000000000000000 : ℝ) ≤ ((8525411127586863059/8527500000000000000 : ℝ)+2*(86020170851/68220000000000 : ℝ)*(14759/100000 : ℝ))^(549/128 : ℝ) := by
    rw [show (8525411127586863059/8527500000000000000 : ℝ)+2*(86020170851/68220000000000 : ℝ)*(14759/100000 : ℝ)=(5000636210402133/5000000000000000 : ℝ) by norm_num, show 1+2*(1705741704828951/6250000000000000000 : ℝ)=(3126705741704828951/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8525411127586863059/8527500000000000000 : ℝ)*(X 1 0+X 2 0)+(86020170851/68220000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (549/128 : ℝ)) (lo := (2837/25000 : ℝ)) (hi := (14759/100000 : ℝ)) (c := (8525411127586863059/8527500000000000000 : ℝ)) (alpha := (86020170851/68220000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8525411127586863059/8527500000000000000 : ℝ)*(X 0 1+X 2 1)+(86020170851/68220000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (549/128 : ℝ)) (lo := (2837/25000 : ℝ)) (hi := (14759/100000 : ℝ)) (c := (8525411127586863059/8527500000000000000 : ℝ)) (alpha := (86020170851/68220000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8525411127586863059/8527500000000000000 : ℝ)*(X 0 2+X 1 2)+(86020170851/68220000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (549/128 : ℝ)) (lo := (2837/25000 : ℝ)) (hi := (14759/100000 : ℝ)) (c := (8525411127586863059/8527500000000000000 : ℝ)) (alpha := (86020170851/68220000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1967891993/10000000000 : ℝ)*X 0 0+(5407990043/10000000000 : ℝ)*X 0 1+(2623508143/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534723687/1000000000 : ℝ)*X 1 0+(-256230397/1250000000 : ℝ)*X 1 1+(5247016189/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673618393/5000000000 : ℝ)*X 2 0+(209880653/400000000 : ℝ)*X 2 1+(-512460777/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4303375621/10000000000 : ℝ)*X 0 0+(4132172537/10000000000 : ℝ)*X 0 1+(140028853/312500000 : ℝ)*X 0 2+(4303375621/10000000000 : ℝ)*X 1 0+(4132172537/10000000000 : ℝ)*X 1 1+(140028853/312500000 : ℝ)*X 1 2+(4303375621/10000000000 : ℝ)*X 2 0+(4132172537/10000000000 : ℝ)*X 2 1+(140028853/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-491975741/2500000000 : ℝ)*X 0 0+(5247596793/10000000000 : ℝ)*X 0 1+(1081481351/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((67240619/156250000 : ℝ)*X 0 0+(4479666029/10000000000 : ℝ)*X 0 1+(826687349/2000000000 : ℝ)*X 0 2+(67240619/156250000 : ℝ)*X 1 0+(4479666029/10000000000 : ℝ)*X 1 1+(826687349/2000000000 : ℝ)*X 1 2+(67240619/156250000 : ℝ)*X 2 0+(4479666029/10000000000 : ℝ)*X 2 1+(826687349/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_s7_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14224592062240808131111341/4737500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (299126299/50000000000000 : ℝ)*(base19) + (1535123/312500000000 : ℝ)*(base23) + (42854227/100000000000000 : ℝ)*(upper3) + (5039927/100000000000000 : ℝ)*(upper4) + (106994407/100000000000000 : ℝ)*(upper5) + (453980118289797/10000000000000 : ℝ)*(major0) + (453980118289797/10000000000000 : ℝ)*(major1) + (453980118289797/10000000000000 : ℝ)*(major2) + (48532828389137/781250000000 : ℝ)*(sp0) + (6212212735217911/100000000000000 : ℝ)*(sp1) + (6212212842231149/100000000000000 : ℝ)*(sp2) + (2867383711751817/100000000000000 : ℝ)*(sp3) + (11299660973/100000000000000 : ℝ)*(sp4) + (1305122131/25000000000000 : ℝ)*(sp5) + (1433694466120171/50000000000000 : ℝ)*(f.failure) + (6212213333470509/100000000000000 : ℝ)*(f.sum) + (665441226771/379000000000000000000000000 : ℝ)*base65 + (22236269572529553/9475000000000000000000000000000 : ℝ)*base68 + (88071599311995447/9475000000000000000000000000000 : ℝ)*base69 + (48237831284304553/9475000000000000000000000000000 : ℝ)*base72 + (465676137599/379000000000000000000000000 : ℝ)*base73 + (166195571102304553/9475000000000000000000000000000 : ℝ)*base76 + (112228224261295447/9475000000000000000000000000000 : ℝ)*base77 + (157520298613829553/9475000000000000000000000000000 : ℝ)*base80 + (30390497047/7580000000000000000000000 : ℝ)*base81 + (27660657/5000000000000000000000 : ℝ)*base89 + (27660657/5000000000000000000000 : ℝ)*base91 + (27660657/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1433_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158325267/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14759/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2837/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11349/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14759/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1433_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1433_box_0 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-225939653/1250000000 : ℝ)*x 0 + (2693042969/5000000000 : ℝ)*x 1 + (21544343/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (225939653/1250000000 : ℝ)^4393 ≤ (67166750163/625000000000 : ℝ)^3369 := by
    have hnat : (225939653 : ℕ)^4393*625000000000^3369 ≤ 67166750163^3369*1250000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225939653 1250000000 67166750163 625000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2693042969/5000000000 : ℝ)^4393 ≤ (89253321991/200000000000 : ℝ)^3369 := by
    have hnat : (2693042969 : ℕ)^4393*200000000000^3369 ≤ 89253321991^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693042969 5000000000 89253321991 200000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21544343/40000000 : ℝ)^4393 ≤ (11156664741091/25000000000000 : ℝ)^3369 := by
    have hnat : (21544343 : ℕ)^4393*25000000000000^3369 ≤ 11156664741091^3369*40000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21544343 40000000 11156664741091 25000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-225939653/1250000000 : ℝ), (2693042969/5000000000 : ℝ), (21544343/40000000 : ℝ)] ![(67166750163/625000000000 : ℝ), (89253321991/200000000000 : ℝ), (11156664741091/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-225939653/1250000000 : ℝ)|^4393 ≤ (67166750163/625000000000 : ℝ)^3369
        have hw : |(-225939653/1250000000 : ℝ)|=(225939653/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2693042969/5000000000 : ℝ)|^4393 ≤ (89253321991/200000000000 : ℝ)^3369
        have hw : |(2693042969/5000000000 : ℝ)|=(2693042969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21544343/40000000 : ℝ)|^4393 ≤ (11156664741091/25000000000000 : ℝ)^3369
        have hw : |(21544343/40000000 : ℝ)|=(21544343/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_box_1 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5286093021/10000000000 : ℝ)*x 0 + (-972454781/5000000000 : ℝ)*x 1 + (2693042901/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286093021/10000000000 : ℝ)^4393 ≤ (21774703443161/50000000000000 : ℝ)^3369 := by
    have hnat : (5286093021 : ℕ)^4393*50000000000000^3369 ≤ 21774703443161^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286093021 10000000000 21774703443161 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (972454781/5000000000 : ℝ)^4393 ≤ (738995848373/6250000000000 : ℝ)^3369 := by
    have hnat : (972454781 : ℕ)^4393*6250000000000^3369 ≤ 738995848373^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      972454781 5000000000 738995848373 6250000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693042901/5000000000 : ℝ)^4393 ≤ (44626659526167/100000000000000 : ℝ)^3369 := by
    have hnat : (2693042901 : ℕ)^4393*100000000000000^3369 ≤ 44626659526167^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693042901 5000000000 44626659526167 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286093021/10000000000 : ℝ), (-972454781/5000000000 : ℝ), (2693042901/5000000000 : ℝ)] ![(21774703443161/50000000000000 : ℝ), (738995848373/6250000000000 : ℝ), (44626659526167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286093021/10000000000 : ℝ)|^4393 ≤ (21774703443161/50000000000000 : ℝ)^3369
        have hw : |(5286093021/10000000000 : ℝ)|=(5286093021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-972454781/5000000000 : ℝ)|^4393 ≤ (738995848373/6250000000000 : ℝ)^3369
        have hw : |(-972454781/5000000000 : ℝ)|=(972454781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693042901/5000000000 : ℝ)|^4393 ≤ (44626659526167/100000000000000 : ℝ)^3369
        have hw : |(2693042901/5000000000 : ℝ)|=(2693042901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_box_2 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5286092967/10000000000 : ℝ)*x 0 + (2693042941/5000000000 : ℝ)*x 1 + (-972454763/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286092967/10000000000 : ℝ)^4393 ≤ (2721837894139/6250000000000 : ℝ)^3369 := by
    have hnat : (5286092967 : ℕ)^4393*6250000000000^3369 ≤ 2721837894139^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286092967 10000000000 2721837894139 6250000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2693042941/5000000000 : ℝ)^4393 ≤ (44626660390481/100000000000000 : ℝ)^3369 := by
    have hnat : (2693042941 : ℕ)^4393*100000000000000^3369 ≤ 44626660390481^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693042941 5000000000 44626660390481 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (972454763/5000000000 : ℝ)^4393 ≤ (11823933288587/100000000000000 : ℝ)^3369 := by
    have hnat : (972454763 : ℕ)^4393*100000000000000^3369 ≤ 11823933288587^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      972454763 5000000000 11823933288587 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286092967/10000000000 : ℝ), (2693042941/5000000000 : ℝ), (-972454763/5000000000 : ℝ)] ![(2721837894139/6250000000000 : ℝ), (44626660390481/100000000000000 : ℝ), (11823933288587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286092967/10000000000 : ℝ)|^4393 ≤ (2721837894139/6250000000000 : ℝ)^3369
        have hw : |(5286092967/10000000000 : ℝ)|=(5286092967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2693042941/5000000000 : ℝ)|^4393 ≤ (44626660390481/100000000000000 : ℝ)^3369
        have hw : |(2693042941/5000000000 : ℝ)|=(2693042941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-972454763/5000000000 : ℝ)|^4393 ≤ (11823933288587/100000000000000 : ℝ)^3369
        have hw : |(-972454763/5000000000 : ℝ)|=(972454763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_box_3 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4449593657/10000000000 : ℝ)*x 0 + (4233967359/10000000000 : ℝ)*x 1 + (169358693/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4449593657/10000000000 : ℝ)^4393 ≤ (34787891882977/100000000000000 : ℝ)^3369 := by
    have hnat : (4449593657 : ℕ)^4393*100000000000000^3369 ≤ 34787891882977^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4449593657 10000000000 34787891882977 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4233967359/10000000000 : ℝ)^4393 ≤ (32606054218257/100000000000000 : ℝ)^3369 := by
    have hnat : (4233967359 : ℕ)^4393*100000000000000^3369 ≤ 32606054218257^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4233967359 10000000000 32606054218257 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169358693/400000000 : ℝ)^4393 ≤ (8151513469209/25000000000000 : ℝ)^3369 := by
    have hnat : (169358693 : ℕ)^4393*25000000000000^3369 ≤ 8151513469209^3369*400000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169358693 400000000 8151513469209 25000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4449593657/10000000000 : ℝ), (4233967359/10000000000 : ℝ), (169358693/400000000 : ℝ)] ![(34787891882977/100000000000000 : ℝ), (32606054218257/100000000000000 : ℝ), (8151513469209/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4449593657/10000000000 : ℝ)|^4393 ≤ (34787891882977/100000000000000 : ℝ)^3369
        have hw : |(4449593657/10000000000 : ℝ)|=(4449593657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4233967359/10000000000 : ℝ)|^4393 ≤ (32606054218257/100000000000000 : ℝ)^3369
        have hw : |(4233967359/10000000000 : ℝ)|=(4233967359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169358693/400000000 : ℝ)|^4393 ≤ (8151513469209/25000000000000 : ℝ)^3369
        have hw : |(169358693/400000000 : ℝ)|=(169358693/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_box_4 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-532749041/2500000000 : ℝ)*x 0 + (5266585043/10000000000 : ℝ)*x 1 + (1053317023/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (532749041/2500000000 : ℝ)^4393 ≤ (3330020316847/25000000000000 : ℝ)^3369 := by
    have hnat : (532749041 : ℕ)^4393*25000000000000^3369 ≤ 3330020316847^3369*2500000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532749041 2500000000 3330020316847 25000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266585043/10000000000 : ℝ)^4393 ≤ (10834989742819/25000000000000 : ℝ)^3369 := by
    have hnat : (5266585043 : ℕ)^4393*25000000000000^3369 ≤ 10834989742819^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266585043 10000000000 10834989742819 25000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053317023/2000000000 : ℝ)^4393 ≤ (43339959743871/100000000000000 : ℝ)^3369 := by
    have hnat : (1053317023 : ℕ)^4393*100000000000000^3369 ≤ 43339959743871^3369*2000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053317023 2000000000 43339959743871 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-532749041/2500000000 : ℝ), (5266585043/10000000000 : ℝ), (1053317023/2000000000 : ℝ)] ![(3330020316847/25000000000000 : ℝ), (10834989742819/25000000000000 : ℝ), (43339959743871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-532749041/2500000000 : ℝ)|^4393 ≤ (3330020316847/25000000000000 : ℝ)^3369
        have hw : |(-532749041/2500000000 : ℝ)|=(532749041/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266585043/10000000000 : ℝ)|^4393 ≤ (10834989742819/25000000000000 : ℝ)^3369
        have hw : |(5266585043/10000000000 : ℝ)|=(5266585043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053317023/2000000000 : ℝ)|^4393 ≤ (43339959743871/100000000000000 : ℝ)^3369
        have hw : |(1053317023/2000000000 : ℝ)|=(1053317023/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_box_5 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5369711973/10000000000 : ℝ)*x 0 + (-1993452953/10000000000 : ℝ)*x 1 + (658323137/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369711973/10000000000 : ℝ)^4393 ≤ (2778114987321/6250000000000 : ℝ)^3369 := by
    have hnat : (5369711973 : ℕ)^4393*6250000000000^3369 ≤ 2778114987321^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369711973 10000000000 2778114987321 6250000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1993452953/10000000000 : ℝ)^4393 ≤ (6105100326069/50000000000000 : ℝ)^3369 := by
    have hnat : (1993452953 : ℕ)^4393*50000000000000^3369 ≤ 6105100326069^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1993452953 10000000000 6105100326069 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658323137/1250000000 : ℝ)^4393 ≤ (5417494942499/12500000000000 : ℝ)^3369 := by
    have hnat : (658323137 : ℕ)^4393*12500000000000^3369 ≤ 5417494942499^3369*1250000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658323137 1250000000 5417494942499 12500000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369711973/10000000000 : ℝ), (-1993452953/10000000000 : ℝ), (658323137/1250000000 : ℝ)] ![(2778114987321/6250000000000 : ℝ), (6105100326069/50000000000000 : ℝ), (5417494942499/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369711973/10000000000 : ℝ)|^4393 ≤ (2778114987321/6250000000000 : ℝ)^3369
        have hw : |(5369711973/10000000000 : ℝ)|=(5369711973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1993452953/10000000000 : ℝ)|^4393 ≤ (6105100326069/50000000000000 : ℝ)^3369
        have hw : |(-1993452953/10000000000 : ℝ)|=(1993452953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658323137/1250000000 : ℝ)|^4393 ≤ (5417494942499/12500000000000 : ℝ)^3369
        have hw : |(658323137/1250000000 : ℝ)|=(658323137/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_box_6 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2684855929/5000000000 : ℝ)*x 0 + (1053317019/2000000000 : ℝ)*x 1 + (-199345311/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684855929/5000000000 : ℝ)^4393 ≤ (8889967711167/20000000000000 : ℝ)^3369 := by
    have hnat : (2684855929 : ℕ)^4393*20000000000000^3369 ≤ 8889967711167^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684855929 5000000000 8889967711167 20000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053317019/2000000000 : ℝ)^4393 ≤ (43339959529261/100000000000000 : ℝ)^3369 := by
    have hnat : (1053317019 : ℕ)^4393*100000000000000^3369 ≤ 43339959529261^3369*2000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053317019 2000000000 43339959529261 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (199345311/1000000000 : ℝ)^4393 ≤ (6105100953039/50000000000000 : ℝ)^3369 := by
    have hnat : (199345311 : ℕ)^4393*50000000000000^3369 ≤ 6105100953039^3369*1000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199345311 1000000000 6105100953039 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684855929/5000000000 : ℝ), (1053317019/2000000000 : ℝ), (-199345311/1000000000 : ℝ)] ![(8889967711167/20000000000000 : ℝ), (43339959529261/100000000000000 : ℝ), (6105100953039/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684855929/5000000000 : ℝ)|^4393 ≤ (8889967711167/20000000000000 : ℝ)^3369
        have hw : |(2684855929/5000000000 : ℝ)|=(2684855929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053317019/2000000000 : ℝ)|^4393 ≤ (43339959529261/100000000000000 : ℝ)^3369
        have hw : |(1053317019/2000000000 : ℝ)|=(1053317019/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-199345311/1000000000 : ℝ)|^4393 ≤ (6105100953039/50000000000000 : ℝ)^3369
        have hw : |(-199345311/1000000000 : ℝ)|=(199345311/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_box_7 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2078051783/5000000000 : ℝ)*x 0 + (8761323/20000000 : ℝ)*x 1 + (2190330859/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2078051783/5000000000 : ℝ)^4393 ≤ (31826357383243/100000000000000 : ℝ)^3369 := by
    have hnat : (2078051783 : ℕ)^4393*100000000000000^3369 ≤ 31826357383243^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078051783 5000000000 31826357383243 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8761323/20000000 : ℝ)^4393 ≤ (34086820199223/100000000000000 : ℝ)^3369 := by
    have hnat : (8761323 : ℕ)^4393*100000000000000^3369 ≤ 34086820199223^3369*20000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8761323 20000000 34086820199223 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2190330859/5000000000 : ℝ)^4393 ≤ (4260852801389/12500000000000 : ℝ)^3369 := by
    have hnat : (2190330859 : ℕ)^4393*12500000000000^3369 ≤ 4260852801389^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190330859 5000000000 4260852801389 12500000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2078051783/5000000000 : ℝ), (8761323/20000000 : ℝ), (2190330859/5000000000 : ℝ)] ![(31826357383243/100000000000000 : ℝ), (34086820199223/100000000000000 : ℝ), (4260852801389/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2078051783/5000000000 : ℝ)|^4393 ≤ (31826357383243/100000000000000 : ℝ)^3369
        have hw : |(2078051783/5000000000 : ℝ)|=(2078051783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8761323/20000000 : ℝ)|^4393 ≤ (34086820199223/100000000000000 : ℝ)^3369
        have hw : |(8761323/20000000 : ℝ)|=(8761323/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2190330859/5000000000 : ℝ)|^4393 ≤ (4260852801389/12500000000000 : ℝ)^3369
        have hw : |(2190330859/5000000000 : ℝ)|=(2190330859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_box_8 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2062853433/10000000000 : ℝ)*x 0 + (5183908681/10000000000 : ℝ)*x 1 + (5400057823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2062853433/10000000000 : ℝ)^4393 ≤ (12767403093953/100000000000000 : ℝ)^3369 := by
    have hnat : (2062853433 : ℕ)^4393*100000000000000^3369 ≤ 12767403093953^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062853433 10000000000 12767403093953 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183908681/10000000000 : ℝ)^4393 ≤ (2653432831793/6250000000000 : ℝ)^3369 := by
    have hnat : (5183908681 : ℕ)^4393*6250000000000^3369 ≤ 2653432831793^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183908681 10000000000 2653432831793 6250000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5400057823/10000000000 : ℝ)^4393 ≤ (44777671578969/100000000000000 : ℝ)^3369 := by
    have hnat : (5400057823 : ℕ)^4393*100000000000000^3369 ≤ 44777671578969^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400057823 10000000000 44777671578969 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2062853433/10000000000 : ℝ), (5183908681/10000000000 : ℝ), (5400057823/10000000000 : ℝ)] ![(12767403093953/100000000000000 : ℝ), (2653432831793/6250000000000 : ℝ), (44777671578969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2062853433/10000000000 : ℝ)|^4393 ≤ (12767403093953/100000000000000 : ℝ)^3369
        have hw : |(-2062853433/10000000000 : ℝ)|=(2062853433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183908681/10000000000 : ℝ)|^4393 ≤ (2653432831793/6250000000000 : ℝ)^3369
        have hw : |(5183908681/10000000000 : ℝ)|=(5183908681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5400057823/10000000000 : ℝ)|^4393 ≤ (44777671578969/100000000000000 : ℝ)^3369
        have hw : |(5400057823/10000000000 : ℝ)|=(5400057823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_box_9 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055262573/2000000000 : ℝ)*x 0 + (-969553927/5000000000 : ℝ)*x 1 + (5400057177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055262573/2000000000 : ℝ)^4393 ≤ (43444372564801/100000000000000 : ℝ)^3369 := by
    have hnat : (1055262573 : ℕ)^4393*100000000000000^3369 ≤ 43444372564801^3369*2000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055262573 2000000000 43444372564801 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (969553927/5000000000 : ℝ)^4393 ≤ (11777962826619/100000000000000 : ℝ)^3369 := by
    have hnat : (969553927 : ℕ)^4393*100000000000000^3369 ≤ 11777962826619^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      969553927 5000000000 11777962826619 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5400057177/10000000000 : ℝ)^4393 ≤ (2238883229707/5000000000000 : ℝ)^3369 := by
    have hnat : (5400057177 : ℕ)^4393*5000000000000^3369 ≤ 2238883229707^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400057177 10000000000 2238883229707 5000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055262573/2000000000 : ℝ), (-969553927/5000000000 : ℝ), (5400057177/10000000000 : ℝ)] ![(43444372564801/100000000000000 : ℝ), (11777962826619/100000000000000 : ℝ), (2238883229707/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055262573/2000000000 : ℝ)|^4393 ≤ (43444372564801/100000000000000 : ℝ)^3369
        have hw : |(1055262573/2000000000 : ℝ)|=(1055262573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-969553927/5000000000 : ℝ)|^4393 ≤ (11777962826619/100000000000000 : ℝ)^3369
        have hw : |(-969553927/5000000000 : ℝ)|=(969553927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5400057177/10000000000 : ℝ)|^4393 ≤ (2238883229707/5000000000000 : ℝ)^3369
        have hw : |(5400057177/10000000000 : ℝ)|=(5400057177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_box_10 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638156243/5000000000 : ℝ)*x 0 + (5400057157/10000000000 : ℝ)*x 1 + (-484777099/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638156243/5000000000 : ℝ)^4393 ≤ (2715273030979/6250000000000 : ℝ)^3369 := by
    have hnat : (2638156243 : ℕ)^4393*6250000000000^3369 ≤ 2715273030979^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638156243 5000000000 2715273030979 6250000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5400057157/10000000000 : ℝ)^4393 ≤ (44777664377891/100000000000000 : ℝ)^3369 := by
    have hnat : (5400057157 : ℕ)^4393*100000000000000^3369 ≤ 44777664377891^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400057157 10000000000 44777664377891 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (484777099/2500000000 : ℝ)^4393 ≤ (11777967119291/100000000000000 : ℝ)^3369 := by
    have hnat : (484777099 : ℕ)^4393*100000000000000^3369 ≤ 11777967119291^3369*2500000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      484777099 2500000000 11777967119291 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638156243/5000000000 : ℝ), (5400057157/10000000000 : ℝ), (-484777099/2500000000 : ℝ)] ![(2715273030979/6250000000000 : ℝ), (44777664377891/100000000000000 : ℝ), (11777967119291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638156243/5000000000 : ℝ)|^4393 ≤ (2715273030979/6250000000000 : ℝ)^3369
        have hw : |(2638156243/5000000000 : ℝ)|=(2638156243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5400057157/10000000000 : ℝ)|^4393 ≤ (44777664377891/100000000000000 : ℝ)^3369
        have hw : |(5400057157/10000000000 : ℝ)|=(5400057157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-484777099/2500000000 : ℝ)|^4393 ≤ (11777967119291/100000000000000 : ℝ)^3369
        have hw : |(-484777099/2500000000 : ℝ)|=(484777099/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_box_11 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4483350309/10000000000 : ℝ)*x 0 + (4216801491/10000000000 : ℝ)*x 1 + (4216802399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4483350309/10000000000 : ℝ)^4393 ≤ (4391552718011/12500000000000 : ℝ)^3369 := by
    have hnat : (4483350309 : ℕ)^4393*12500000000000^3369 ≤ 4391552718011^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483350309 10000000000 4391552718011 12500000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4216801491/10000000000 : ℝ)^4393 ≤ (16216892283229/50000000000000 : ℝ)^3369 := by
    have hnat : (4216801491 : ℕ)^4393*50000000000000^3369 ≤ 16216892283229^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4216801491 10000000000 16216892283229 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4216802399/10000000000 : ℝ)^4393 ≤ (32433793673147/100000000000000 : ℝ)^3369 := by
    have hnat : (4216802399 : ℕ)^4393*100000000000000^3369 ≤ 32433793673147^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4216802399 10000000000 32433793673147 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4483350309/10000000000 : ℝ), (4216801491/10000000000 : ℝ), (4216802399/10000000000 : ℝ)] ![(4391552718011/12500000000000 : ℝ), (16216892283229/50000000000000 : ℝ), (32433793673147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4483350309/10000000000 : ℝ)|^4393 ≤ (4391552718011/12500000000000 : ℝ)^3369
        have hw : |(4483350309/10000000000 : ℝ)|=(4483350309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4216801491/10000000000 : ℝ)|^4393 ≤ (16216892283229/50000000000000 : ℝ)^3369
        have hw : |(4216801491/10000000000 : ℝ)|=(4216801491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4216802399/10000000000 : ℝ)|^4393 ≤ (32433793673147/100000000000000 : ℝ)^3369
        have hw : |(4216802399/10000000000 : ℝ)|=(4216802399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_box_12 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-937917067/5000000000 : ℝ)*x 0 + (546674551/1000000000 : ℝ)*x 1 + (1313864243/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (937917067/5000000000 : ℝ)^4393 ≤ (11279335412543/100000000000000 : ℝ)^3369 := by
    have hnat : (937917067 : ℕ)^4393*100000000000000^3369 ≤ 11279335412543^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      937917067 5000000000 11279335412543 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (546674551/1000000000 : ℝ)^4393 ≤ (45500076907971/100000000000000 : ℝ)^3369 := by
    have hnat : (546674551 : ℕ)^4393*100000000000000^3369 ≤ 45500076907971^3369*1000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546674551 1000000000 45500076907971 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313864243/2500000000 : ℝ)^4393 ≤ (5402573458839/12500000000000 : ℝ)^3369 := by
    have hnat : (1313864243 : ℕ)^4393*12500000000000^3369 ≤ 5402573458839^3369*2500000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313864243 2500000000 5402573458839 12500000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-937917067/5000000000 : ℝ), (546674551/1000000000 : ℝ), (1313864243/2500000000 : ℝ)] ![(11279335412543/100000000000000 : ℝ), (45500076907971/100000000000000 : ℝ), (5402573458839/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-937917067/5000000000 : ℝ)|^4393 ≤ (11279335412543/100000000000000 : ℝ)^3369
        have hw : |(-937917067/5000000000 : ℝ)|=(937917067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(546674551/1000000000 : ℝ)|^4393 ≤ (45500076907971/100000000000000 : ℝ)^3369
        have hw : |(546674551/1000000000 : ℝ)|=(546674551/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313864243/2500000000 : ℝ)|^4393 ≤ (5402573458839/12500000000000 : ℝ)^3369
        have hw : |(1313864243/2500000000 : ℝ)|=(1313864243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_box_13 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5377497823/10000000000 : ℝ)*x 0 + (-399574759/2000000000 : ℝ)*x 1 + (2627728153/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5377497823/10000000000 : ℝ)^4393 ≤ (8906779638303/20000000000000 : ℝ)^3369 := by
    have hnat : (5377497823 : ℕ)^4393*20000000000000^3369 ≤ 8906779638303^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377497823 10000000000 8906779638303 20000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (399574759/2000000000 : ℝ)^4393 ≤ (12245521267917/100000000000000 : ℝ)^3369 := by
    have hnat : (399574759 : ℕ)^4393*100000000000000^3369 ≤ 12245521267917^3369*2000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399574759 2000000000 12245521267917 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627728153/5000000000 : ℝ)^4393 ≤ (21610290264399/50000000000000 : ℝ)^3369 := by
    have hnat : (2627728153 : ℕ)^4393*50000000000000^3369 ≤ 21610290264399^3369*5000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627728153 5000000000 21610290264399 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5377497823/10000000000 : ℝ), (-399574759/2000000000 : ℝ), (2627728153/5000000000 : ℝ)] ![(8906779638303/20000000000000 : ℝ), (12245521267917/100000000000000 : ℝ), (21610290264399/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5377497823/10000000000 : ℝ)|^4393 ≤ (8906779638303/20000000000000 : ℝ)^3369
        have hw : |(5377497823/10000000000 : ℝ)|=(5377497823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-399574759/2000000000 : ℝ)|^4393 ≤ (12245521267917/100000000000000 : ℝ)^3369
        have hw : |(-399574759/2000000000 : ℝ)|=(399574759/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627728153/5000000000 : ℝ)|^4393 ≤ (21610290264399/50000000000000 : ℝ)^3369
        have hw : |(2627728153/5000000000 : ℝ)|=(2627728153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_box_14 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5377497153/10000000000 : ℝ)*x 0 + (105109131/200000000 : ℝ)*x 1 + (-499468593/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5377497153/10000000000 : ℝ)^4393 ≤ (44533890956399/100000000000000 : ℝ)^3369 := by
    have hnat : (5377497153 : ℕ)^4393*100000000000000^3369 ≤ 44533890956399^3369*10000000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377497153 10000000000 44533890956399 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105109131/200000000 : ℝ)^4393 ≤ (8644116629071/20000000000000 : ℝ)^3369 := by
    have hnat : (105109131 : ℕ)^4393*20000000000000^3369 ≤ 8644116629071^3369*200000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105109131 200000000 8644116629071 20000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (499468593/2500000000 : ℝ)^4393 ≤ (12245525879449/100000000000000 : ℝ)^3369 := by
    have hnat : (499468593 : ℕ)^4393*100000000000000^3369 ≤ 12245525879449^3369*2500000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499468593 2500000000 12245525879449 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5377497153/10000000000 : ℝ), (105109131/200000000 : ℝ), (-499468593/2500000000 : ℝ)] ![(44533890956399/100000000000000 : ℝ), (8644116629071/20000000000000 : ℝ), (12245525879449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5377497153/10000000000 : ℝ)|^4393 ≤ (44533890956399/100000000000000 : ℝ)^3369
        have hw : |(5377497153/10000000000 : ℝ)|=(5377497153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(105109131/200000000 : ℝ)|^4393 ≤ (8644116629071/20000000000000 : ℝ)^3369
        have hw : |(105109131/200000000 : ℝ)|=(105109131/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-499468593/2500000000 : ℝ)|^4393 ≤ (12245525879449/100000000000000 : ℝ)^3369
        have hw : |(-499468593/2500000000 : ℝ)|=(499468593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1433_box_15 (p : ℝ) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1032081001/2500000000 : ℝ)*x 0 + (175772449/400000000 : ℝ)*x 1 + (1098577511/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1032081001/2500000000 : ℝ)^4393 ≤ (15774626277441/50000000000000 : ℝ)^3369 := by
    have hnat : (1032081001 : ℕ)^4393*50000000000000^3369 ≤ 15774626277441^3369*2500000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032081001 2500000000 15774626277441 50000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (175772449/400000000 : ℝ)^4393 ≤ (34225379711187/100000000000000 : ℝ)^3369 := by
    have hnat : (175772449 : ℕ)^4393*100000000000000^3369 ≤ 34225379711187^3369*400000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175772449 400000000 34225379711187 100000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1098577511/2500000000 : ℝ)^4393 ≤ (3422536771709/10000000000000 : ℝ)^3369 := by
    have hnat : (1098577511 : ℕ)^4393*10000000000000^3369 ≤ 3422536771709^3369*2500000000^4393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098577511 2500000000 3422536771709 10000000000000 4393 3369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4393/1024 : ℝ)) 4393 3369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1032081001/2500000000 : ℝ), (175772449/400000000 : ℝ), (1098577511/2500000000 : ℝ)] ![(15774626277441/50000000000000 : ℝ), (34225379711187/100000000000000 : ℝ), (3422536771709/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1032081001/2500000000 : ℝ)|^4393 ≤ (15774626277441/50000000000000 : ℝ)^3369
        have hw : |(1032081001/2500000000 : ℝ)|=(1032081001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(175772449/400000000 : ℝ)|^4393 ≤ (34225379711187/100000000000000 : ℝ)^3369
        have hw : |(175772449/400000000 : ℝ)|=(175772449/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1098577511/2500000000 : ℝ)|^4393 ≤ (3422536771709/10000000000000 : ℝ)^3369
        have hw : |(1098577511/2500000000 : ℝ)|=(1098577511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1433_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158325267/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14759/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11349/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31451/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59121/100000 : ℝ) ∧ (80471/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (847/1000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14759/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11349/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14759/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11349/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14759/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11349/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14759/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11349/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14759/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11349/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14759/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11349/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11349/100000 : ℝ) ^ (549/128 : ℝ) ≤ (1768821709202553/20000000000000000000 : ℝ) := by
    have hpowers : (11349/100000 : ℝ)^549 ≤ (1768821709202553/20000000000000000000 : ℝ)^128 := by
      have hnat : (11349 : ℕ)^549*20000000000000000000^128 ≤ 1768821709202553^128*100000^549 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11349 100000 1768821709202553 20000000000000000000 549 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11349/100000 : ℝ)) (X := (1768821709202553/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have hpowhi : (14759/100000 : ℝ) ^ (549/128 : ℝ) ≤ (1705741704828951/6250000000000000000 : ℝ) := by
    have hpowers : (14759/100000 : ℝ)^549 ≤ (1705741704828951/6250000000000000000 : ℝ)^128 := by
      have hnat : (14759 : ℕ)^549*6250000000000000000^128 ≤ 1705741704828951^128*100000^549 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14759 100000 1705741704828951 6250000000000000000 549 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14759/100000 : ℝ)) (X := (1705741704828951/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001768821709202553/10000000000000000000 : ℝ) ≤ (1250051546863637/1250000000000000 : ℝ) ^ (549/128 : ℝ) := by
    have hpowers : (10001768821709202553/10000000000000000000 : ℝ)^128 ≤ (1250051546863637/1250000000000000 : ℝ)^549 := by
      have hnat : (10001768821709202553 : ℕ)^128*1250000000000000^549 ≤ 1250051546863637^549*10000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001768821709202553 10000000000000000000 1250051546863637 1250000000000000 128 549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250051546863637/1250000000000000 : ℝ)) (X := (10001768821709202553/10000000000000000000 : ℝ)) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100036135975823275981/100000000000000000000 : ℝ) ≤ (10000842397845663/10000000000000000 : ℝ) ^ (549/128 : ℝ) := by
    have hpowers : (100036135975823275981/100000000000000000000 : ℝ)^128 ≤ (10000842397845663/10000000000000000 : ℝ)^549 := by
      have hnat : (100036135975823275981 : ℕ)^128*10000000000000000^549 ≤ 10000842397845663^549*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100036135975823275981 100000000000000000000 10000842397845663 10000000000000000 128 549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000842397845663/10000000000000000 : ℝ)) (X := (100036135975823275981/100000000000000000000 : ℝ)) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (3126705741704828951/3125000000000000000 : ℝ) ≤ (1000127242078223/1000000000000000 : ℝ) ^ (549/128 : ℝ) := by
    have hpowers : (3126705741704828951/3125000000000000000 : ℝ)^128 ≤ (1000127242078223/1000000000000000 : ℝ)^549 := by
      have hnat : (3126705741704828951 : ℕ)^128*1000000000000000^549 ≤ 1000127242078223^549*3125000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126705741704828951 3125000000000000000 1000127242078223 1000000000000000 128 549 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000127242078223/1000000000000000 : ℝ)) (X := (3126705741704828951/3125000000000000000 : ℝ)) (by norm_num) 549 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1768821709202553/20000000000000000000 : ℝ) ≤ ((17045822768912909797/17050000000000000000 : ℝ)+2*(430022936567/341000000000000 : ℝ)*(11349/100000 : ℝ))^(549/128 : ℝ) := by
    rw [show (17045822768912909797/17050000000000000000 : ℝ)+2*(430022936567/341000000000000 : ℝ)*(11349/100000 : ℝ)=(1250051546863637/1250000000000000 : ℝ) by norm_num, show 1+2*(1768821709202553/20000000000000000000 : ℝ)=(10001768821709202553/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1705741704828951/6250000000000000000 : ℝ)+(1768821709202553/20000000000000000000 : ℝ) ≤ ((17045822768912909797/17050000000000000000 : ℝ)+(430022936567/341000000000000 : ℝ)*((14759/100000 : ℝ)+(11349/100000 : ℝ)))^(549/128 : ℝ) := by
    rw [show (17045822768912909797/17050000000000000000 : ℝ)+(430022936567/341000000000000 : ℝ)*((14759/100000 : ℝ)+(11349/100000 : ℝ))=(10000842397845663/10000000000000000 : ℝ) by norm_num, show 1+(1705741704828951/6250000000000000000 : ℝ)+(1768821709202553/20000000000000000000 : ℝ)=(100036135975823275981/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1705741704828951/6250000000000000000 : ℝ) ≤ ((17045822768912909797/17050000000000000000 : ℝ)+2*(430022936567/341000000000000 : ℝ)*(14759/100000 : ℝ))^(549/128 : ℝ) := by
    rw [show (17045822768912909797/17050000000000000000 : ℝ)+2*(430022936567/341000000000000 : ℝ)*(14759/100000 : ℝ)=(1000127242078223/1000000000000000 : ℝ) by norm_num, show 1+2*(1705741704828951/6250000000000000000 : ℝ)=(3126705741704828951/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17045822768912909797/17050000000000000000 : ℝ)*(X 1 0+X 2 0)+(430022936567/341000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (549/128 : ℝ)) (lo := (11349/100000 : ℝ)) (hi := (14759/100000 : ℝ)) (c := (17045822768912909797/17050000000000000000 : ℝ)) (alpha := (430022936567/341000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17045822768912909797/17050000000000000000 : ℝ)*(X 0 1+X 2 1)+(430022936567/341000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (549/128 : ℝ)) (lo := (11349/100000 : ℝ)) (hi := (14759/100000 : ℝ)) (c := (17045822768912909797/17050000000000000000 : ℝ)) (alpha := (430022936567/341000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17045822768912909797/17050000000000000000 : ℝ)*(X 0 2+X 1 2)+(430022936567/341000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (549/128 : ℝ)) (lo := (11349/100000 : ℝ)) (hi := (14759/100000 : ℝ)) (c := (17045822768912909797/17050000000000000000 : ℝ)) (alpha := (430022936567/341000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-225939653/1250000000 : ℝ)*X 0 0+(2693042969/5000000000 : ℝ)*X 0 1+(21544343/40000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5286093021/10000000000 : ℝ)*X 1 0+(-972454781/5000000000 : ℝ)*X 1 1+(2693042901/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5286092967/10000000000 : ℝ)*X 2 0+(2693042941/5000000000 : ℝ)*X 2 1+(-972454763/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4449593657/10000000000 : ℝ)*X 0 0+(4233967359/10000000000 : ℝ)*X 0 1+(169358693/400000000 : ℝ)*X 0 2+(4449593657/10000000000 : ℝ)*X 1 0+(4233967359/10000000000 : ℝ)*X 1 1+(169358693/400000000 : ℝ)*X 1 2+(4449593657/10000000000 : ℝ)*X 2 0+(4233967359/10000000000 : ℝ)*X 2 1+(169358693/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-532749041/2500000000 : ℝ)*X 0 0+(5266585043/10000000000 : ℝ)*X 0 1+(1053317023/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5369711973/10000000000 : ℝ)*X 1 0+(-1993452953/10000000000 : ℝ)*X 1 1+(658323137/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2684855929/5000000000 : ℝ)*X 2 0+(1053317019/2000000000 : ℝ)*X 2 1+(-199345311/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2078051783/5000000000 : ℝ)*X 0 0+(8761323/20000000 : ℝ)*X 0 1+(2190330859/5000000000 : ℝ)*X 0 2+(2078051783/5000000000 : ℝ)*X 1 0+(8761323/20000000 : ℝ)*X 1 1+(2190330859/5000000000 : ℝ)*X 1 2+(2078051783/5000000000 : ℝ)*X 2 0+(8761323/20000000 : ℝ)*X 2 1+(2190330859/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2062853433/10000000000 : ℝ)*X 0 0+(5183908681/10000000000 : ℝ)*X 0 1+(5400057823/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1055262573/2000000000 : ℝ)*X 1 0+(-969553927/5000000000 : ℝ)*X 1 1+(5400057177/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2638156243/5000000000 : ℝ)*X 2 0+(5400057157/10000000000 : ℝ)*X 2 1+(-484777099/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4483350309/10000000000 : ℝ)*X 0 0+(4216801491/10000000000 : ℝ)*X 0 1+(4216802399/10000000000 : ℝ)*X 0 2+(4483350309/10000000000 : ℝ)*X 1 0+(4216801491/10000000000 : ℝ)*X 1 1+(4216802399/10000000000 : ℝ)*X 1 2+(4483350309/10000000000 : ℝ)*X 2 0+(4216801491/10000000000 : ℝ)*X 2 1+(4216802399/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-937917067/5000000000 : ℝ)*X 0 0+(546674551/1000000000 : ℝ)*X 0 1+(1313864243/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5377497823/10000000000 : ℝ)*X 1 0+(-399574759/2000000000 : ℝ)*X 1 1+(2627728153/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5377497153/10000000000 : ℝ)*X 2 0+(105109131/200000000 : ℝ)*X 2 1+(-499468593/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1032081001/2500000000 : ℝ)*X 0 0+(175772449/400000000 : ℝ)*X 0 1+(1098577511/2500000000 : ℝ)*X 0 2+(1032081001/2500000000 : ℝ)*X 1 0+(175772449/400000000 : ℝ)*X 1 1+(1098577511/2500000000 : ℝ)*X 1 2+(1032081001/2500000000 : ℝ)*X 2 0+(175772449/400000000 : ℝ)*X 2 1+(1098577511/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1433_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31451/50000 : ℝ) ≤ (-268108727462867843207519226640647/426250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17202637/50000000000000 : ℝ)*(upper1) + (52538169/50000000000000 : ℝ)*(lower4) + (10944513/25000000000000 : ℝ)*(upper5) + (3021144869576017/100000000000000 : ℝ)*(major0) + (3021144869576017/100000000000000 : ℝ)*(major1) + (3021144869576017/100000000000000 : ℝ)*(major2) + (2243661869/50000000000000 : ℝ)*(sp2) + (2761089669/100000000000000 : ℝ)*(sp3) + (4155065927454737/100000000000000 : ℝ)*(sp4) + (259690131616691/6250000000000 : ℝ)*(sp5) + (10387657528697/250000000000 : ℝ)*(sp6) + (190818594866063/10000000000000 : ℝ)*(sp7) + (785673901/50000000000000 : ℝ)*(sp12) + (12696467741/50000000000000 : ℝ)*(sp13) + (19081887097503/1000000000000 : ℝ)*(f.failure) + (2077533749401269/50000000000000 : ℝ)*(f.sum) + (133775434615789/17050000000000000000000000000 : ℝ)*base65 + (565451768972511451/1705000000000000000000000000000000 : ℝ)*base68 + (1168505640717488549/1705000000000000000000000000000000 : ℝ)*base69 + (8395471710502488549/1705000000000000000000000000000000 : ℝ)*base71 + (12060288338011/17050000000000000000000000000 : ℝ)*base74 + (20201707815572488549/1705000000000000000000000000000000 : ℝ)*base75 + (14557948908742488549/1705000000000000000000000000000000 : ℝ)*base77 + (11338542456502488549/1705000000000000000000000000000000 : ℝ)*base79 + (20132107125789/17050000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (508301/100000000000000000000 : ℝ)*base89 + (508301/100000000000000000000 : ℝ)*base91 + (508301/100000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (59121/100000 : ℝ) ≤ (25201469279753763861294010350573/42625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3964357/100000000000000 : ℝ)*(upper3) + (5318759/100000000000000 : ℝ)*(upper4) + (1902959/50000000000000 : ℝ)*(lower5) + (309289022666403/10000000000000 : ℝ)*(major0) + (309289022666403/10000000000000 : ℝ)*(major1) + (309289022666403/10000000000000 : ℝ)*(major2) + (842513016597901/20000000000000 : ℝ)*(sp0) + (1053141900928659/25000000000000 : ℝ)*(sp1) + (1053141061804969/25000000000000 : ℝ)*(sp2) + (976751149997729/50000000000000 : ℝ)*(sp3) + (540148473/50000000000000 : ℝ)*(sp5) + (2218395853/50000000000000 : ℝ)*(sp6) + (1575456103/100000000000000 : ℝ)*(sp7) + (3601022077/100000000000000 : ℝ)*(sp8) + (1953503875451561/100000000000000 : ℝ)*(f.failure) + (2106284342005791/50000000000000 : ℝ)*(f.sum) + (807286899157/852500000000000000000000000 : ℝ)*base66 + (1564002367567999809/170500000000000000000000000000000 : ℝ)*base68 + (764931150574000191/170500000000000000000000000000000 : ℝ)*base69 + (1218900473282499809/170500000000000000000000000000000 : ℝ)*base72 + (11371709454659/1705000000000000000000000000 : ℝ)*base74 + (1024893071199499809/170500000000000000000000000000000 : ℝ)*base76 + (2010663603715499809/170500000000000000000000000000000 : ℝ)*base78 + (1393090026105499809/170500000000000000000000000000000 : ℝ)*base80 + (1225376218939/1705000000000000000000000000 : ℝ)*base82 + (140891787/10000000000000000000000 : ℝ)*base89 + (140891787/10000000000000000000000 : ℝ)*base91 + (140891787/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (80471/100000 : ℝ) ≤ (137206477145242368133375408769517/170500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (190937029/100000000000000 : ℝ)*(upper0) + (9007607/4000000000000 : ℝ)*(upper2) + (217101799/100000000000000 : ℝ)*(lower5) + (680110486462529/20000000000000 : ℝ)*(major0) + (680110486462529/20000000000000 : ℝ)*(major1) + (680110486462529/20000000000000 : ℝ)*(major2) + (25484039311/50000000000000 : ℝ)*(sp1) + (40703653363/100000000000000 : ℝ)*(sp3) + (12467313133/100000000000000 : ℝ)*(sp4) + (578303403637191/12500000000000 : ℝ)*(sp8) + (4626402813568891/100000000000000 : ℝ)*(sp9) + (4626453781647513/100000000000000 : ℝ)*(sp10) + (2147786043616639/100000000000000 : ℝ)*(sp11) + (3521309213/25000000000000 : ℝ)*(sp12) + (1073913373635001/50000000000000 : ℝ)*(f.failure) + (4626453781647513/100000000000000 : ℝ)*(f.sum) + (18614072634637/3410000000000000000000000000 : ℝ)*base66 + (204684348198353387/341000000000000000000000000000000 : ℝ)*base68 + (3124516641884353387/341000000000000000000000000000000 : ℝ)*base70 + (669759873684353387/341000000000000000000000000000000 : ℝ)*base72 + (4984950862863/3410000000000000000000000000 : ℝ)*base73 + (2537824971572353387/341000000000000000000000000000000 : ℝ)*base76 + (2992709005165353387/341000000000000000000000000000000 : ℝ)*base78 + (2257250553492353387/341000000000000000000000000000000 : ℝ)*base80 + (6993111299137/3410000000000000000000000000 : ℝ)*base82 + (43870267/5000000000000000000000 : ℝ)*base89 + (43870267/5000000000000000000000 : ℝ)*base91 + (43870267/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-847/1000 : ℝ) ≤ (-361022206393678755498763415004303/426250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (61477631/25000000000000 : ℝ)*(lower0) + (303131613/100000000000000 : ℝ)*(upper3) + (282664317/100000000000000 : ℝ)*(lower4) + (1719043919258433/50000000000000 : ℝ)*(major0) + (1719043919258433/50000000000000 : ℝ)*(major1) + (1719043919258433/50000000000000 : ℝ)*(major2) + (333297429/10000000000000 : ℝ)*(sp0) + (7434312597/1250000000000 : ℝ)*(sp5) + (550552457687/100000000000000 : ℝ)*(sp6) + (59330934717/50000000000000 : ℝ)*(sp7) + (4732870247258351/100000000000000 : ℝ)*(sp12) + (4732278835224881/100000000000000 : ℝ)*(sp13) + (2366161513887477/50000000000000 : ℝ)*(sp14) + (2171415865539173/100000000000000 : ℝ)*(sp15) + (67860453981519/3125000000000 : ℝ)*(f.failure) + (4732873580232641/100000000000000 : ℝ)*(f.sum) + (27483867753961/8525000000000000000000000000 : ℝ)*base65 + (1540625233798618101/852500000000000000000000000000000 : ℝ)*base67 + (1552964369096118101/852500000000000000000000000000000 : ℝ)*base69 + (463356001088618101/852500000000000000000000000000000 : ℝ)*base71 + (24982502286739/8525000000000000000000000000 : ℝ)*base74 + (38102308488881899/852500000000000000000000000000000 : ℝ)*base76 + (5711334181176118101/852500000000000000000000000000000 : ℝ)*base77 + (5853819900788881899/852500000000000000000000000000000 : ℝ)*base80 + (10192103664361/8525000000000000000000000000 : ℝ)*base81 + (2490573/312500000000000000000 : ℝ)*base89 + (2490573/312500000000000000000 : ℝ)*base91 + (2490573/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1433_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158325267/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14759/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11349/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31451/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59121/100000 : ℝ) else (80471/100000 : ℝ) ≤ X j i ∧ X j i ≤ (847/1000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1433_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1433_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158325267/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14763/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2269/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31451/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59121/100000 : ℝ) else (80471/100000 : ℝ) ≤ X j i ∧ X j i ≤ (847/1000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1433_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1433_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1433_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (549/128 : ℝ) ≤ p) (hpb : p ≤ (4393/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158325267/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14763/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2269/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31451/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59121/100000 : ℝ) else (80471/100000 : ℝ) ≤ X j i ∧ X j i ≤ (847/1000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1433_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
