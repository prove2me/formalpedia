-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1370_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:20:34.46799+00:00
-- url     : https://prove2.me/submissions/a0fbdc4a-92d1-4700-a4fe-0b0f0ec1a8ec

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
theorem support_rectangle_w1370_s0_0 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-448177141/2500000000 : ℝ)*x 0 + (5984911161/10000000000 : ℝ)*x 1 + (4817545479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (448177141/2500000000 : ℝ)^2165 ≤ (657918202679/6250000000000 : ℝ)^1653 := by
    have hnat : (448177141 : ℕ)^2165*6250000000000^1653 ≤ 657918202679^1653*2500000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448177141 2500000000 657918202679 6250000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5984911161/10000000000 : ℝ)^2165 ≤ (51050922279831/100000000000000 : ℝ)^1653 := by
    have hnat : (5984911161 : ℕ)^2165*100000000000000^1653 ≤ 51050922279831^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5984911161 10000000000 51050922279831 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4817545479/10000000000 : ℝ)^2165 ≤ (19211193229813/50000000000000 : ℝ)^1653 := by
    have hnat : (4817545479 : ℕ)^2165*50000000000000^1653 ≤ 19211193229813^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4817545479 10000000000 19211193229813 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-448177141/2500000000 : ℝ), (5984911161/10000000000 : ℝ), (4817545479/10000000000 : ℝ)] ![(657918202679/6250000000000 : ℝ), (51050922279831/100000000000000 : ℝ), (19211193229813/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-448177141/2500000000 : ℝ)|^2165 ≤ (657918202679/6250000000000 : ℝ)^1653
        have hw : |(-448177141/2500000000 : ℝ)|=(448177141/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5984911161/10000000000 : ℝ)|^2165 ≤ (51050922279831/100000000000000 : ℝ)^1653
        have hw : |(5984911161/10000000000 : ℝ)|=(5984911161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4817545479/10000000000 : ℝ)|^2165 ≤ (19211193229813/50000000000000 : ℝ)^1653
        have hw : |(4817545479/10000000000 : ℝ)|=(4817545479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s0_1 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1374669923/2500000000 : ℝ)*x 0 + (-1227447509/5000000000 : ℝ)*x 1 + (4817546053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1374669923/2500000000 : ℝ)^2165 ≤ (9137683172323/20000000000000 : ℝ)^1653 := by
    have hnat : (1374669923 : ℕ)^2165*20000000000000^1653 ≤ 9137683172323^1653*2500000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1374669923 2500000000 9137683172323 20000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1227447509/5000000000 : ℝ)^2165 ≤ (7944595831889/50000000000000 : ℝ)^1653 := by
    have hnat : (1227447509 : ℕ)^2165*50000000000000^1653 ≤ 7944595831889^1653*5000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1227447509 5000000000 7944595831889 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4817546053/10000000000 : ℝ)^2165 ≤ (38422392455541/100000000000000 : ℝ)^1653 := by
    have hnat : (4817546053 : ℕ)^2165*100000000000000^1653 ≤ 38422392455541^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4817546053 10000000000 38422392455541 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1374669923/2500000000 : ℝ), (-1227447509/5000000000 : ℝ), (4817546053/10000000000 : ℝ)] ![(9137683172323/20000000000000 : ℝ), (7944595831889/50000000000000 : ℝ), (38422392455541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1374669923/2500000000 : ℝ)|^2165 ≤ (9137683172323/20000000000000 : ℝ)^1653
        have hw : |(1374669923/2500000000 : ℝ)|=(1374669923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1227447509/5000000000 : ℝ)|^2165 ≤ (7944595831889/50000000000000 : ℝ)^1653
        have hw : |(-1227447509/5000000000 : ℝ)|=(1227447509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4817546053/10000000000 : ℝ)|^2165 ≤ (38422392455541/100000000000000 : ℝ)^1653
        have hw : |(4817546053/10000000000 : ℝ)|=(4817546053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s0_2 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2749339791/5000000000 : ℝ)*x 0 + (1204386353/2500000000 : ℝ)*x 1 + (-49097919/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2749339791/5000000000 : ℝ)^2165 ≤ (2855525916533/6250000000000 : ℝ)^1653 := by
    have hnat : (2749339791 : ℕ)^2165*6250000000000^1653 ≤ 2855525916533^1653*5000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2749339791 5000000000 2855525916533 6250000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1204386353/2500000000 : ℝ)^2165 ≤ (19211192879877/50000000000000 : ℝ)^1653 := by
    have hnat : (1204386353 : ℕ)^2165*50000000000000^1653 ≤ 19211192879877^1653*2500000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1204386353 2500000000 19211192879877 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (49097919/200000000 : ℝ)^2165 ≤ (3972299891139/25000000000000 : ℝ)^1653 := by
    have hnat : (49097919 : ℕ)^2165*25000000000000^1653 ≤ 3972299891139^1653*200000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49097919 200000000 3972299891139 25000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2749339791/5000000000 : ℝ), (1204386353/2500000000 : ℝ), (-49097919/200000000 : ℝ)] ![(2855525916533/6250000000000 : ℝ), (19211192879877/50000000000000 : ℝ), (3972299891139/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2749339791/5000000000 : ℝ)|^2165 ≤ (2855525916533/6250000000000 : ℝ)^1653
        have hw : |(2749339791/5000000000 : ℝ)|=(2749339791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1204386353/2500000000 : ℝ)|^2165 ≤ (19211192879877/50000000000000 : ℝ)^1653
        have hw : |(1204386353/2500000000 : ℝ)|=(1204386353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-49097919/200000000 : ℝ)|^2165 ≤ (3972299891139/25000000000000 : ℝ)^1653
        have hw : |(-49097919/200000000 : ℝ)|=(49097919/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s0_3 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (208729263/500000000 : ℝ)*x 0 + (3105293843/10000000000 : ℝ)*x 1 + (1394052179/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (208729263/500000000 : ℝ)^2165 ≤ (31849466375471/100000000000000 : ℝ)^1653 := by
    have hnat : (208729263 : ℕ)^2165*100000000000000^1653 ≤ 31849466375471^1653*500000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208729263 500000000 31849466375471 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3105293843/10000000000 : ℝ)^2165 ≤ (5404140971921/25000000000000 : ℝ)^1653 := by
    have hnat : (3105293843 : ℕ)^2165*25000000000000^1653 ≤ 5404140971921^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3105293843 10000000000 5404140971921 25000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1394052179/2500000000 : ℝ)^2165 ≤ (46533969732007/100000000000000 : ℝ)^1653 := by
    have hnat : (1394052179 : ℕ)^2165*100000000000000^1653 ≤ 46533969732007^1653*2500000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1394052179 2500000000 46533969732007 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(208729263/500000000 : ℝ), (3105293843/10000000000 : ℝ), (1394052179/2500000000 : ℝ)] ![(31849466375471/100000000000000 : ℝ), (5404140971921/25000000000000 : ℝ), (46533969732007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(208729263/500000000 : ℝ)|^2165 ≤ (31849466375471/100000000000000 : ℝ)^1653
        have hw : |(208729263/500000000 : ℝ)|=(208729263/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3105293843/10000000000 : ℝ)|^2165 ≤ (5404140971921/25000000000000 : ℝ)^1653
        have hw : |(3105293843/10000000000 : ℝ)|=(3105293843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1394052179/2500000000 : ℝ)|^2165 ≤ (46533969732007/100000000000000 : ℝ)^1653
        have hw : |(1394052179/2500000000 : ℝ)|=(1394052179/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s0_4 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1797020401/10000000000 : ℝ)*x 0 + (4847538319/10000000000 : ℝ)*x 1 + (2976923223/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1797020401/10000000000 : ℝ)^2165 ≤ (5279932368831/50000000000000 : ℝ)^1653 := by
    have hnat : (1797020401 : ℕ)^2165*50000000000000^1653 ≤ 5279932368831^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1797020401 10000000000 5279932368831 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4847538319/10000000000 : ℝ)^2165 ≤ (9683997162957/25000000000000 : ℝ)^1653 := by
    have hnat : (4847538319 : ℕ)^2165*25000000000000^1653 ≤ 9683997162957^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4847538319 10000000000 9683997162957 25000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2976923223/5000000000 : ℝ)^2165 ≤ (2535207329781/5000000000000 : ℝ)^1653 := by
    have hnat : (2976923223 : ℕ)^2165*5000000000000^1653 ≤ 2535207329781^1653*5000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2976923223 5000000000 2535207329781 5000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1797020401/10000000000 : ℝ), (4847538319/10000000000 : ℝ), (2976923223/5000000000 : ℝ)] ![(5279932368831/50000000000000 : ℝ), (9683997162957/25000000000000 : ℝ), (2535207329781/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1797020401/10000000000 : ℝ)|^2165 ≤ (5279932368831/50000000000000 : ℝ)^1653
        have hw : |(-1797020401/10000000000 : ℝ)|=(1797020401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4847538319/10000000000 : ℝ)|^2165 ≤ (9683997162957/25000000000000 : ℝ)^1653
        have hw : |(4847538319/10000000000 : ℝ)|=(4847538319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2976923223/5000000000 : ℝ)|^2165 ≤ (2535207329781/5000000000000 : ℝ)^1653
        have hw : |(2976923223/5000000000 : ℝ)|=(2976923223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s0_5 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5180366023/10000000000 : ℝ)*x 0 + (-329649291/2500000000 : ℝ)*x 1 + (1190769057/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5180366023/10000000000 : ℝ)^2165 ≤ (10563953906119/25000000000000 : ℝ)^1653 := by
    have hnat : (5180366023 : ℕ)^2165*25000000000000^1653 ≤ 10563953906119^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180366023 10000000000 10563953906119 25000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329649291/2500000000 : ℝ)^2165 ≤ (281602028697/4000000000000 : ℝ)^1653 := by
    have hnat : (329649291 : ℕ)^2165*4000000000000^1653 ≤ 281602028697^1653*2500000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329649291 2500000000 281602028697 4000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1190769057/2000000000 : ℝ)^2165 ≤ (50704133645819/100000000000000 : ℝ)^1653 := by
    have hnat : (1190769057 : ℕ)^2165*100000000000000^1653 ≤ 50704133645819^1653*2000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1190769057 2000000000 50704133645819 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5180366023/10000000000 : ℝ), (-329649291/2500000000 : ℝ), (1190769057/2000000000 : ℝ)] ![(10563953906119/25000000000000 : ℝ), (281602028697/4000000000000 : ℝ), (50704133645819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5180366023/10000000000 : ℝ)|^2165 ≤ (10563953906119/25000000000000 : ℝ)^1653
        have hw : |(5180366023/10000000000 : ℝ)|=(5180366023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-329649291/2500000000 : ℝ)|^2165 ≤ (281602028697/4000000000000 : ℝ)^1653
        have hw : |(-329649291/2500000000 : ℝ)|=(329649291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1190769057/2000000000 : ℝ)|^2165 ≤ (50704133645819/100000000000000 : ℝ)^1653
        have hw : |(1190769057/2000000000 : ℝ)|=(1190769057/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s0_6 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (647545653/1250000000 : ℝ)*x 0 + (5953847301/10000000000 : ℝ)*x 1 + (-1318595167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (647545653/1250000000 : ℝ)^2165 ≤ (5281975886051/12500000000000 : ℝ)^1653 := by
    have hnat : (647545653 : ℕ)^2165*12500000000000^1653 ≤ 5281975886051^1653*1250000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647545653 1250000000 5281975886051 12500000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5953847301/10000000000 : ℝ)^2165 ≤ (6338019516537/12500000000000 : ℝ)^1653 := by
    have hnat : (5953847301 : ℕ)^2165*12500000000000^1653 ≤ 6338019516537^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5953847301 10000000000 6338019516537 12500000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1318595167/10000000000 : ℝ)^2165 ≤ (1408007350577/20000000000000 : ℝ)^1653 := by
    have hnat : (1318595167 : ℕ)^2165*20000000000000^1653 ≤ 1408007350577^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318595167 10000000000 1408007350577 20000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(647545653/1250000000 : ℝ), (5953847301/10000000000 : ℝ), (-1318595167/10000000000 : ℝ)] ![(5281975886051/12500000000000 : ℝ), (6338019516537/12500000000000 : ℝ), (1408007350577/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(647545653/1250000000 : ℝ)|^2165 ≤ (5281975886051/12500000000000 : ℝ)^1653
        have hw : |(647545653/1250000000 : ℝ)|=(647545653/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5953847301/10000000000 : ℝ)|^2165 ≤ (6338019516537/12500000000000 : ℝ)^1653
        have hw : |(5953847301/10000000000 : ℝ)|=(5953847301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1318595167/10000000000 : ℝ)|^2165 ≤ (1408007350577/20000000000000 : ℝ)^1653
        have hw : |(-1318595167/10000000000 : ℝ)|=(1318595167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s0_7 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4183705039/10000000000 : ℝ)*x 0 + (2756363371/5000000000 : ℝ)*x 1 + (3171048451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4183705039/10000000000 : ℝ)^2165 ≤ (31940626523493/100000000000000 : ℝ)^1653 := by
    have hnat : (4183705039 : ℕ)^2165*100000000000000^1653 ≤ 31940626523493^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4183705039 10000000000 31940626523493 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2756363371/5000000000 : ℝ)^2165 ≤ (9168268950619/20000000000000 : ℝ)^1653 := by
    have hnat : (2756363371 : ℕ)^2165*20000000000000^1653 ≤ 9168268950619^1653*5000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2756363371 5000000000 9168268950619 20000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3171048451/10000000000 : ℝ)^2165 ≤ (22218028702267/100000000000000 : ℝ)^1653 := by
    have hnat : (3171048451 : ℕ)^2165*100000000000000^1653 ≤ 22218028702267^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3171048451 10000000000 22218028702267 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4183705039/10000000000 : ℝ), (2756363371/5000000000 : ℝ), (3171048451/10000000000 : ℝ)] ![(31940626523493/100000000000000 : ℝ), (9168268950619/20000000000000 : ℝ), (22218028702267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4183705039/10000000000 : ℝ)|^2165 ≤ (31940626523493/100000000000000 : ℝ)^1653
        have hw : |(4183705039/10000000000 : ℝ)|=(4183705039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2756363371/5000000000 : ℝ)|^2165 ≤ (9168268950619/20000000000000 : ℝ)^1653
        have hw : |(2756363371/5000000000 : ℝ)|=(2756363371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3171048451/10000000000 : ℝ)|^2165 ≤ (22218028702267/100000000000000 : ℝ)^1653
        have hw : |(3171048451/10000000000 : ℝ)|=(3171048451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1370_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155832971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (811/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26671/100000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4329/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4329 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4329*1^1024 ≤ 0^1024*1^4329 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4329 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4329/1024 : ℝ) ≤ (1039113705764293481/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4329 ≤ (1039113705764293481/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4329*50000000000000000000^1024 ≤ 1039113705764293481^1024*5^4329 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1039113705764293481 50000000000000000000 4329 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1039113705764293481/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4329/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4329 := by
      have hnat : (1 : ℕ)^1024*1^4329 ≤ 1^4329*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (51039113705764293481/50000000000000000000 : ℝ) ≤ (2512193494862289/2500000000000000 : ℝ) ^ (4329/1024 : ℝ) := by
    have hpowers : (51039113705764293481/50000000000000000000 : ℝ)^1024 ≤ (2512193494862289/2500000000000000 : ℝ)^4329 := by
      have hnat : (51039113705764293481 : ℕ)^1024*2500000000000000^4329 ≤ 2512193494862289^4329*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51039113705764293481 50000000000000000000 2512193494862289 2500000000000000 1024 4329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2512193494862289/2500000000000000 : ℝ)) (X := (51039113705764293481/50000000000000000000 : ℝ)) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (26039113705764293481/25000000000000000000 : ℝ) ≤ (1262193494862289/1250000000000000 : ℝ) ^ (4329/1024 : ℝ) := by
    have hpowers : (26039113705764293481/25000000000000000000 : ℝ)^1024 ≤ (1262193494862289/1250000000000000 : ℝ)^4329 := by
      have hnat : (26039113705764293481 : ℕ)^1024*1250000000000000^4329 ≤ 1262193494862289^4329*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26039113705764293481 25000000000000000000 1262193494862289 1250000000000000 1024 4329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1262193494862289/1250000000000000 : ℝ)) (X := (26039113705764293481/25000000000000000000 : ℝ)) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(12193494862289/1000000000000000 : ℝ)*(0 : ℝ))^(4329/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(12193494862289/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1039113705764293481/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(12193494862289/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4329/1024 : ℝ) := by
    rw [show (1 : ℝ)+(12193494862289/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2512193494862289/2500000000000000 : ℝ) by norm_num, show 1+(1039113705764293481/50000000000000000000 : ℝ)+(0 : ℝ)=(51039113705764293481/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1039113705764293481/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(12193494862289/1000000000000000 : ℝ)*(2/5 : ℝ))^(4329/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(12193494862289/1000000000000000 : ℝ)*(2/5 : ℝ)=(1262193494862289/1250000000000000 : ℝ) by norm_num, show 1+2*(1039113705764293481/50000000000000000000 : ℝ)=(26039113705764293481/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(12193494862289/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4329/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12193494862289/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(12193494862289/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4329/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12193494862289/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(12193494862289/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4329/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12193494862289/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-448177141/2500000000 : ℝ)*X 0 0+(5984911161/10000000000 : ℝ)*X 0 1+(4817545479/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1374669923/2500000000 : ℝ)*X 1 0+(-1227447509/5000000000 : ℝ)*X 1 1+(4817546053/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2749339791/5000000000 : ℝ)*X 2 0+(1204386353/2500000000 : ℝ)*X 2 1+(-49097919/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((208729263/500000000 : ℝ)*X 0 0+(3105293843/10000000000 : ℝ)*X 0 1+(1394052179/2500000000 : ℝ)*X 0 2+(208729263/500000000 : ℝ)*X 1 0+(3105293843/10000000000 : ℝ)*X 1 1+(1394052179/2500000000 : ℝ)*X 1 2+(208729263/500000000 : ℝ)*X 2 0+(3105293843/10000000000 : ℝ)*X 2 1+(1394052179/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1797020401/10000000000 : ℝ)*X 0 0+(4847538319/10000000000 : ℝ)*X 0 1+(2976923223/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5180366023/10000000000 : ℝ)*X 1 0+(-329649291/2500000000 : ℝ)*X 1 1+(1190769057/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((647545653/1250000000 : ℝ)*X 2 0+(5953847301/10000000000 : ℝ)*X 2 1+(-1318595167/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4183705039/10000000000 : ℝ)*X 0 0+(2756363371/5000000000 : ℝ)*X 0 1+(3171048451/10000000000 : ℝ)*X 0 2+(4183705039/10000000000 : ℝ)*X 1 0+(2756363371/5000000000 : ℝ)*X 1 1+(3171048451/10000000000 : ℝ)*X 1 2+(4183705039/10000000000 : ℝ)*X 2 0+(2756363371/5000000000 : ℝ)*X 2 1+(3171048451/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (177194102100501411397179/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (106596619/50000000000000 : ℝ)*(base1) + (411406013/25000000000000 : ℝ)*(base19) + (203560897/12500000000000 : ℝ)*(base23) + (144679489/50000000000000 : ℝ)*(upper3) + (42963649/100000000000000 : ℝ)*(upper5) + (630676547089779/100000000000000 : ℝ)*(major0) + (630676547089779/100000000000000 : ℝ)*(major1) + (630676547089779/100000000000000 : ℝ)*(major2) + (856635419629617/100000000000000 : ℝ)*(sp0) + (214159512138269/25000000000000 : ℝ)*(sp1) + (26769939552811/3125000000000 : ℝ)*(sp2) + (50588784479607/12500000000000 : ℝ)*(sp3) + (4487740749/100000000000000 : ℝ)*(sp4) + (334339191/12500000000000 : ℝ)*(sp7) + (404713163743621/100000000000000 : ℝ)*(f.failure) + (107079961772141/12500000000000 : ℝ)*(f.sum) + (100261166305869/50000000000000000000000000000 : ℝ)*base66 + (752064640755869/100000000000000000000000000000 : ℝ)*base68 + (882214837655869/100000000000000000000000000000 : ℝ)*base70 + (331462949955869/100000000000000000000000000000 : ℝ)*base72 + (374342076355869/50000000000000000000000000000 : ℝ)*base74 + (423107780755869/100000000000000000000000000000 : ℝ)*base76 + (813425697155869/100000000000000000000000000000 : ℝ)*base78 + (60803036355869/100000000000000000000000000000 : ℝ)*base80 + (279883056755869/50000000000000000000000000000 : ℝ)*base82 + (42727991/10000000000000000000000 : ℝ)*base89 + (42727991/10000000000000000000000 : ℝ)*base91 + (42727991/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (34452546444778396441119/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (117563827/20000000000000 : ℝ)*(base19) + (42555959/4000000000000 : ℝ)*(base23) + (77176219/20000000000000 : ℝ)*(base39) + (90808767/100000000000000 : ℝ)*(upper2) + (2260051/1000000000000 : ℝ)*(upper5) + (16636863525849/2500000000000 : ℝ)*(major0) + (16636863525849/2500000000000 : ℝ)*(major1) + (133094831030573/20000000000000 : ℝ)*(major2) + (1169562943/100000000000000 : ℝ)*(sp1) + (27517399/1250000000000 : ℝ)*(sp2) + (451952493672497/50000000000000 : ℝ)*(sp4) + (225975807490729/25000000000000 : ℝ)*(sp5) + (180780421587039/20000000000000 : ℝ)*(sp6) + (213521739579091/50000000000000 : ℝ)*(sp7) + (213521739579091/50000000000000 : ℝ)*(f.failure) + (903905373226089/100000000000000 : ℝ)*(f.sum) + (14120914370303/4000000000000000000000000000 : ℝ)*base66 + (86499978838403/20000000000000000000000000000 : ℝ)*base68 + (10255421706639/2500000000000000000000000000 : ℝ)*base70 + (11508130678403/20000000000000000000000000000 : ℝ)*base72 + (15002347738303/4000000000000000000000000000 : ℝ)*base74 + (11338855994139/2500000000000000000000000000 : ℝ)*base76 + (28508041236639/2500000000000000000000000000 : ℝ)*base78 + (24968335139139/2500000000000000000000000000 : ℝ)*base80 + (170940087889/1250000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (40009361/5000000000000000000000 : ℝ)*base89 + (40009361/5000000000000000000000 : ℝ)*base91 + (40009361/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1370_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155832971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (811/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26671/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1370_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1370_s1_0 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-246686487/1250000000 : ℝ)*x 0 + (5629799191/10000000000 : ℝ)*x 1 + (5056850563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (246686487/1250000000 : ℝ)^2165 ≤ (11938276619311/100000000000000 : ℝ)^1653 := by
    have hnat : (246686487 : ℕ)^2165*100000000000000^1653 ≤ 11938276619311^1653*1250000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246686487 1250000000 11938276619311 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5629799191/10000000000 : ℝ)^2165 ≤ (4712057806989/10000000000000 : ℝ)^1653 := by
    have hnat : (5629799191 : ℕ)^2165*10000000000000^1653 ≤ 4712057806989^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5629799191 10000000000 4712057806989 10000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5056850563/10000000000 : ℝ)^2165 ≤ (65505832473/160000000000 : ℝ)^1653 := by
    have hnat : (5056850563 : ℕ)^2165*160000000000^1653 ≤ 65505832473^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5056850563 10000000000 65505832473 160000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-246686487/1250000000 : ℝ), (5629799191/10000000000 : ℝ), (5056850563/10000000000 : ℝ)] ![(11938276619311/100000000000000 : ℝ), (4712057806989/10000000000000 : ℝ), (65505832473/160000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-246686487/1250000000 : ℝ)|^2165 ≤ (11938276619311/100000000000000 : ℝ)^1653
        have hw : |(-246686487/1250000000 : ℝ)|=(246686487/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5629799191/10000000000 : ℝ)|^2165 ≤ (4712057806989/10000000000000 : ℝ)^1653
        have hw : |(5629799191/10000000000 : ℝ)|=(5629799191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5056850563/10000000000 : ℝ)|^2165 ≤ (65505832473/160000000000 : ℝ)^1653
        have hw : |(5056850563/10000000000 : ℝ)|=(5056850563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s1_1 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5402813183/10000000000 : ℝ)*x 0 + (-1139256007/5000000000 : ℝ)*x 1 + (2528425907/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5402813183/10000000000 : ℝ)^2165 ≤ (22323983579167/50000000000000 : ℝ)^1653 := by
    have hnat : (5402813183 : ℕ)^2165*50000000000000^1653 ≤ 22323983579167^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402813183 10000000000 22323983579167 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1139256007/5000000000 : ℝ)^2165 ≤ (14410874268457/100000000000000 : ℝ)^1653 := by
    have hnat : (1139256007 : ℕ)^2165*100000000000000^1653 ≤ 14410874268457^1653*5000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1139256007 5000000000 14410874268457 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2528425907/5000000000 : ℝ)^2165 ≤ (40941158561083/100000000000000 : ℝ)^1653 := by
    have hnat : (2528425907 : ℕ)^2165*100000000000000^1653 ≤ 40941158561083^1653*5000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2528425907 5000000000 40941158561083 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5402813183/10000000000 : ℝ), (-1139256007/5000000000 : ℝ), (2528425907/5000000000 : ℝ)] ![(22323983579167/50000000000000 : ℝ), (14410874268457/100000000000000 : ℝ), (40941158561083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5402813183/10000000000 : ℝ)|^2165 ≤ (22323983579167/50000000000000 : ℝ)^1653
        have hw : |(5402813183/10000000000 : ℝ)|=(5402813183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1139256007/5000000000 : ℝ)|^2165 ≤ (14410874268457/100000000000000 : ℝ)^1653
        have hw : |(-1139256007/5000000000 : ℝ)|=(1139256007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2528425907/5000000000 : ℝ)|^2165 ≤ (40941158561083/100000000000000 : ℝ)^1653
        have hw : |(2528425907/5000000000 : ℝ)|=(2528425907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s1_2 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5402813609/10000000000 : ℝ)*x 0 + (126421269/250000000 : ℝ)*x 1 + (-2278512807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5402813609/10000000000 : ℝ)^2165 ≤ (2790498235571/6250000000000 : ℝ)^1653 := by
    have hnat : (5402813609 : ℕ)^2165*6250000000000^1653 ≤ 2790498235571^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402813609 10000000000 2790498235571 6250000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (126421269/250000000 : ℝ)^2165 ≤ (4094114738459/10000000000000 : ℝ)^1653 := by
    have hnat : (126421269 : ℕ)^2165*10000000000000^1653 ≤ 4094114738459^1653*250000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126421269 250000000 4094114738459 10000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2278512807/10000000000 : ℝ)^2165 ≤ (14410880837427/100000000000000 : ℝ)^1653 := by
    have hnat : (2278512807 : ℕ)^2165*100000000000000^1653 ≤ 14410880837427^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2278512807 10000000000 14410880837427 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5402813609/10000000000 : ℝ), (126421269/250000000 : ℝ), (-2278512807/10000000000 : ℝ)] ![(2790498235571/6250000000000 : ℝ), (4094114738459/10000000000000 : ℝ), (14410880837427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5402813609/10000000000 : ℝ)|^2165 ≤ (2790498235571/6250000000000 : ℝ)^1653
        have hw : |(5402813609/10000000000 : ℝ)|=(5402813609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(126421269/250000000 : ℝ)|^2165 ≤ (4094114738459/10000000000000 : ℝ)^1653
        have hw : |(126421269/250000000 : ℝ)|=(126421269/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2278512807/10000000000 : ℝ)|^2165 ≤ (14410880837427/100000000000000 : ℝ)^1653
        have hw : |(-2278512807/10000000000 : ℝ)|=(2278512807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s1_3 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4287299191/10000000000 : ℝ)*x 0 + (148807687/400000000 : ℝ)*x 1 + (4932924357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4287299191/10000000000 : ℝ)^2165 ≤ (3298044025093/10000000000000 : ℝ)^1653 := by
    have hnat : (4287299191 : ℕ)^2165*10000000000000^1653 ≤ 3298044025093^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4287299191 10000000000 3298044025093 10000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (148807687/400000000 : ℝ)^2165 ≤ (27387497524733/100000000000000 : ℝ)^1653 := by
    have hnat : (148807687 : ℕ)^2165*100000000000000^1653 ≤ 27387497524733^1653*400000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      148807687 400000000 27387497524733 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4932924357/10000000000 : ℝ)^2165 ≤ (39632062207657/100000000000000 : ℝ)^1653 := by
    have hnat : (4932924357 : ℕ)^2165*100000000000000^1653 ≤ 39632062207657^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4932924357 10000000000 39632062207657 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4287299191/10000000000 : ℝ), (148807687/400000000 : ℝ), (4932924357/10000000000 : ℝ)] ![(3298044025093/10000000000000 : ℝ), (27387497524733/100000000000000 : ℝ), (39632062207657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4287299191/10000000000 : ℝ)|^2165 ≤ (3298044025093/10000000000000 : ℝ)^1653
        have hw : |(4287299191/10000000000 : ℝ)|=(4287299191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(148807687/400000000 : ℝ)|^2165 ≤ (27387497524733/100000000000000 : ℝ)^1653
        have hw : |(148807687/400000000 : ℝ)|=(148807687/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4932924357/10000000000 : ℝ)|^2165 ≤ (39632062207657/100000000000000 : ℝ)^1653
        have hw : |(4932924357/10000000000 : ℝ)|=(4932924357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s1_4 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1973979453/10000000000 : ℝ)*x 0 + (158246453/312500000 : ℝ)*x 1 + (1405659511/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1973979453/10000000000 : ℝ)^2165 ≤ (1194213969617/10000000000000 : ℝ)^1653 := by
    have hnat : (1973979453 : ℕ)^2165*10000000000000^1653 ≤ 1194213969617^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1973979453 10000000000 1194213969617 10000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (158246453/312500000 : ℝ)^2165 ≤ (10253942393831/25000000000000 : ℝ)^1653 := by
    have hnat : (158246453 : ℕ)^2165*25000000000000^1653 ≤ 10253942393831^1653*312500000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158246453 312500000 10253942393831 25000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1405659511/2500000000 : ℝ)^2165 ≤ (23521045352033/50000000000000 : ℝ)^1653 := by
    have hnat : (1405659511 : ℕ)^2165*50000000000000^1653 ≤ 23521045352033^1653*2500000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1405659511 2500000000 23521045352033 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1973979453/10000000000 : ℝ), (158246453/312500000 : ℝ), (1405659511/2500000000 : ℝ)] ![(1194213969617/10000000000000 : ℝ), (10253942393831/25000000000000 : ℝ), (23521045352033/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1973979453/10000000000 : ℝ)|^2165 ≤ (1194213969617/10000000000000 : ℝ)^1653
        have hw : |(-1973979453/10000000000 : ℝ)|=(1973979453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(158246453/312500000 : ℝ)|^2165 ≤ (10253942393831/25000000000000 : ℝ)^1653
        have hw : |(158246453/312500000 : ℝ)|=(158246453/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1405659511/2500000000 : ℝ)|^2165 ≤ (23521045352033/50000000000000 : ℝ)^1653
        have hw : |(1405659511/2500000000 : ℝ)|=(1405659511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s1_5 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2626899513/5000000000 : ℝ)*x 0 + (-342545117/2000000000 : ℝ)*x 1 + (5622638131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2626899513/5000000000 : ℝ)^2165 ≤ (43042049342511/100000000000000 : ℝ)^1653 := by
    have hnat : (2626899513 : ℕ)^2165*100000000000000^1653 ≤ 43042049342511^1653*5000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626899513 5000000000 43042049342511 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (342545117/2000000000 : ℝ)^2165 ≤ (9915858984903/100000000000000 : ℝ)^1653 := by
    have hnat : (342545117 : ℕ)^2165*100000000000000^1653 ≤ 9915858984903^1653*2000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342545117 2000000000 9915858984903 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5622638131/10000000000 : ℝ)^2165 ≤ (11760522914353/25000000000000 : ℝ)^1653 := by
    have hnat : (5622638131 : ℕ)^2165*25000000000000^1653 ≤ 11760522914353^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5622638131 10000000000 11760522914353 25000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2626899513/5000000000 : ℝ), (-342545117/2000000000 : ℝ), (5622638131/10000000000 : ℝ)] ![(43042049342511/100000000000000 : ℝ), (9915858984903/100000000000000 : ℝ), (11760522914353/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2626899513/5000000000 : ℝ)|^2165 ≤ (43042049342511/100000000000000 : ℝ)^1653
        have hw : |(2626899513/5000000000 : ℝ)|=(2626899513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-342545117/2000000000 : ℝ)|^2165 ≤ (9915858984903/100000000000000 : ℝ)^1653
        have hw : |(-342545117/2000000000 : ℝ)|=(342545117/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5622638131/10000000000 : ℝ)|^2165 ≤ (11760522914353/25000000000000 : ℝ)^1653
        have hw : |(5622638131/10000000000 : ℝ)|=(5622638131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s1_6 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5253798919/10000000000 : ℝ)*x 0 + (702829779/1250000000 : ℝ)*x 1 + (-1712725591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5253798919/10000000000 : ℝ)^2165 ≤ (10760512048597/25000000000000 : ℝ)^1653 := by
    have hnat : (5253798919 : ℕ)^2165*25000000000000^1653 ≤ 10760512048597^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253798919 10000000000 10760512048597 25000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (702829779/1250000000 : ℝ)^2165 ≤ (47042092764171/100000000000000 : ℝ)^1653 := by
    have hnat : (702829779 : ℕ)^2165*100000000000000^1653 ≤ 47042092764171^1653*1250000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      702829779 1250000000 47042092764171 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1712725591/10000000000 : ℝ)^2165 ≤ (3098705947/31250000000 : ℝ)^1653 := by
    have hnat : (1712725591 : ℕ)^2165*31250000000^1653 ≤ 3098705947^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1712725591 10000000000 3098705947 31250000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5253798919/10000000000 : ℝ), (702829779/1250000000 : ℝ), (-1712725591/10000000000 : ℝ)] ![(10760512048597/25000000000000 : ℝ), (47042092764171/100000000000000 : ℝ), (3098705947/31250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5253798919/10000000000 : ℝ)|^2165 ≤ (10760512048597/25000000000000 : ℝ)^1653
        have hw : |(5253798919/10000000000 : ℝ)|=(5253798919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(702829779/1250000000 : ℝ)|^2165 ≤ (47042092764171/100000000000000 : ℝ)^1653
        have hw : |(702829779/1250000000 : ℝ)|=(702829779/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1712725591/10000000000 : ℝ)|^2165 ≤ (3098705947/31250000000 : ℝ)^1653
        have hw : |(-1712725591/10000000000 : ℝ)|=(1712725591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s1_7 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2144165959/5000000000 : ℝ)*x 0 + (4918033531/10000000000 : ℝ)*x 1 + (3735346629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2144165959/5000000000 : ℝ)^2165 ≤ (32990845666641/100000000000000 : ℝ)^1653 := by
    have hnat : (2144165959 : ℕ)^2165*100000000000000^1653 ≤ 32990845666641^1653*5000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144165959 5000000000 32990845666641 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4918033531/10000000000 : ℝ)^2165 ≤ (9868860947697/25000000000000 : ℝ)^1653 := by
    have hnat : (4918033531 : ℕ)^2165*25000000000000^1653 ≤ 9868860947697^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4918033531 10000000000 9868860947697 25000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3735346629/10000000000 : ℝ)^2165 ≤ (27533710515091/100000000000000 : ℝ)^1653 := by
    have hnat : (3735346629 : ℕ)^2165*100000000000000^1653 ≤ 27533710515091^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3735346629 10000000000 27533710515091 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2144165959/5000000000 : ℝ), (4918033531/10000000000 : ℝ), (3735346629/10000000000 : ℝ)] ![(32990845666641/100000000000000 : ℝ), (9868860947697/25000000000000 : ℝ), (27533710515091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2144165959/5000000000 : ℝ)|^2165 ≤ (32990845666641/100000000000000 : ℝ)^1653
        have hw : |(2144165959/5000000000 : ℝ)|=(2144165959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4918033531/10000000000 : ℝ)|^2165 ≤ (9868860947697/25000000000000 : ℝ)^1653
        have hw : |(4918033531/10000000000 : ℝ)|=(4918033531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3735346629/10000000000 : ℝ)|^2165 ≤ (27533710515091/100000000000000 : ℝ)^1653
        have hw : |(3735346629/10000000000 : ℝ)|=(3735346629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1370_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155832971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26671/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (811/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1429/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3851/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26671/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (811/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26671/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (811/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26671/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (811/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26671/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (811/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26671/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (811/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26671/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (811/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
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
  have hpowlo : (811/50000 : ℝ) ^ (4329/1024 : ℝ) ≤ (2709692741349/100000000000000000000 : ℝ) := by
    have hpowers : (811/50000 : ℝ)^4329 ≤ (2709692741349/100000000000000000000 : ℝ)^1024 := by
      have hnat : (811 : ℕ)^4329*100000000000000000000^1024 ≤ 2709692741349^1024*50000^4329 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        811 50000 2709692741349 100000000000000000000 4329 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (811/50000 : ℝ)) (X := (2709692741349/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (26671/100000 : ℝ) ^ (4329/1024 : ℝ) ≤ (374592189534494961/100000000000000000000 : ℝ) := by
    have hpowers : (26671/100000 : ℝ)^4329 ≤ (374592189534494961/100000000000000000000 : ℝ)^1024 := by
      have hnat : (26671 : ℕ)^4329*100000000000000000000^1024 ≤ 374592189534494961^1024*100000^4329 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26671 100000 374592189534494961 100000000000000000000 4329 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26671/100000 : ℝ)) (X := (374592189534494961/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000002709692741349/50000000000000000000 : ℝ) ≤ (5000000064096219/5000000000000000 : ℝ) ^ (4329/1024 : ℝ) := by
    have hpowers : (50000002709692741349/50000000000000000000 : ℝ)^1024 ≤ (5000000064096219/5000000000000000 : ℝ)^4329 := by
      have hnat : (50000002709692741349 : ℕ)^1024*5000000000000000^4329 ≤ 5000000064096219^4329*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000002709692741349 50000000000000000000 5000000064096219 5000000000000000 1024 4329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000064096219/5000000000000000 : ℝ)) (X := (50000002709692741349/50000000000000000000 : ℝ)) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10037459489922723631/10000000000000000000 : ℝ) ≤ (2001769636776569/2000000000000000 : ℝ) ^ (4329/1024 : ℝ) := by
    have hpowers : (10037459489922723631/10000000000000000000 : ℝ)^1024 ≤ (2001769636776569/2000000000000000 : ℝ)^4329 := by
      have hnat : (10037459489922723631 : ℕ)^1024*2000000000000000^4329 ≤ 2001769636776569^4329*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10037459489922723631 10000000000000000000 2001769636776569 2000000000000000 1024 4329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2001769636776569/2000000000000000 : ℝ)) (X := (10037459489922723631/10000000000000000000 : ℝ)) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50374592189534494961/50000000000000000000 : ℝ) ≤ (2504424059893313/2500000000000000 : ℝ) ^ (4329/1024 : ℝ) := by
    have hpowers : (50374592189534494961/50000000000000000000 : ℝ)^1024 ≤ (2504424059893313/2500000000000000 : ℝ)^4329 := by
      have hnat : (50374592189534494961 : ℕ)^1024*2500000000000000^4329 ≤ 2504424059893313^4329*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50374592189534494961 50000000000000000000 2504424059893313 2500000000000000 1024 4329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2504424059893313/2500000000000000 : ℝ)) (X := (50374592189534494961/50000000000000000000 : ℝ)) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2709692741349/100000000000000000000 : ℝ) ≤ ((125230650059216349577/125245000000000000000 : ℝ)+2*(8848055690407/2504900000000000 : ℝ)*(811/50000 : ℝ))^(4329/1024 : ℝ) := by
    rw [show (125230650059216349577/125245000000000000000 : ℝ)+2*(8848055690407/2504900000000000 : ℝ)*(811/50000 : ℝ)=(5000000064096219/5000000000000000 : ℝ) by norm_num, show 1+2*(2709692741349/100000000000000000000 : ℝ)=(50000002709692741349/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(374592189534494961/100000000000000000000 : ℝ)+(2709692741349/100000000000000000000 : ℝ) ≤ ((125230650059216349577/125245000000000000000 : ℝ)+(8848055690407/2504900000000000 : ℝ)*((26671/100000 : ℝ)+(811/50000 : ℝ)))^(4329/1024 : ℝ) := by
    rw [show (125230650059216349577/125245000000000000000 : ℝ)+(8848055690407/2504900000000000 : ℝ)*((26671/100000 : ℝ)+(811/50000 : ℝ))=(2001769636776569/2000000000000000 : ℝ) by norm_num, show 1+(374592189534494961/100000000000000000000 : ℝ)+(2709692741349/100000000000000000000 : ℝ)=(10037459489922723631/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(374592189534494961/100000000000000000000 : ℝ) ≤ ((125230650059216349577/125245000000000000000 : ℝ)+2*(8848055690407/2504900000000000 : ℝ)*(26671/100000 : ℝ))^(4329/1024 : ℝ) := by
    rw [show (125230650059216349577/125245000000000000000 : ℝ)+2*(8848055690407/2504900000000000 : ℝ)*(26671/100000 : ℝ)=(2504424059893313/2500000000000000 : ℝ) by norm_num, show 1+2*(374592189534494961/100000000000000000000 : ℝ)=(50374592189534494961/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (125230650059216349577/125245000000000000000 : ℝ)*(X 1 0+X 2 0)+(8848055690407/2504900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4329/1024 : ℝ)) (lo := (811/50000 : ℝ)) (hi := (26671/100000 : ℝ)) (c := (125230650059216349577/125245000000000000000 : ℝ)) (alpha := (8848055690407/2504900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (125230650059216349577/125245000000000000000 : ℝ)*(X 0 1+X 2 1)+(8848055690407/2504900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4329/1024 : ℝ)) (lo := (811/50000 : ℝ)) (hi := (26671/100000 : ℝ)) (c := (125230650059216349577/125245000000000000000 : ℝ)) (alpha := (8848055690407/2504900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (125230650059216349577/125245000000000000000 : ℝ)*(X 0 2+X 1 2)+(8848055690407/2504900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4329/1024 : ℝ)) (lo := (811/50000 : ℝ)) (hi := (26671/100000 : ℝ)) (c := (125230650059216349577/125245000000000000000 : ℝ)) (alpha := (8848055690407/2504900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-246686487/1250000000 : ℝ)*X 0 0+(5629799191/10000000000 : ℝ)*X 0 1+(5056850563/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5402813183/10000000000 : ℝ)*X 1 0+(-1139256007/5000000000 : ℝ)*X 1 1+(2528425907/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5402813609/10000000000 : ℝ)*X 2 0+(126421269/250000000 : ℝ)*X 2 1+(-2278512807/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4287299191/10000000000 : ℝ)*X 0 0+(148807687/400000000 : ℝ)*X 0 1+(4932924357/10000000000 : ℝ)*X 0 2+(4287299191/10000000000 : ℝ)*X 1 0+(148807687/400000000 : ℝ)*X 1 1+(4932924357/10000000000 : ℝ)*X 1 2+(4287299191/10000000000 : ℝ)*X 2 0+(148807687/400000000 : ℝ)*X 2 1+(4932924357/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1973979453/10000000000 : ℝ)*X 0 0+(158246453/312500000 : ℝ)*X 0 1+(1405659511/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2626899513/5000000000 : ℝ)*X 1 0+(-342545117/2000000000 : ℝ)*X 1 1+(5622638131/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5253798919/10000000000 : ℝ)*X 2 0+(702829779/1250000000 : ℝ)*X 2 1+(-1712725591/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2144165959/5000000000 : ℝ)*X 0 0+(4918033531/10000000000 : ℝ)*X 0 1+(3735346629/10000000000 : ℝ)*X 0 2+(2144165959/5000000000 : ℝ)*X 1 0+(4918033531/10000000000 : ℝ)*X 1 1+(3735346629/10000000000 : ℝ)*X 1 2+(2144165959/5000000000 : ℝ)*X 2 0+(4918033531/10000000000 : ℝ)*X 2 1+(3735346629/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (931808589931272664192902339/125245000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6857873/25000000000000 : ℝ)*(base16) + (557679551/50000000000000 : ℝ)*(base19) + (260864077/20000000000000 : ℝ)*(base23) + (12918457/100000000000000 : ℝ)*(upper2) + (210424729/100000000000000 : ℝ)*(upper3) + (25699700317031/2000000000000 : ℝ)*(major0) + (25699700317031/2000000000000 : ℝ)*(major1) + (25699700317031/2000000000000 : ℝ)*(major2) + (872684455985161/50000000000000 : ℝ)*(sp0) + (69815096345859/4000000000000 : ℝ)*(sp1) + (436344311779171/25000000000000 : ℝ)*(sp2) + (412293594172583/50000000000000 : ℝ)*(sp3) + (9639466747/100000000000000 : ℝ)*(sp4) + (25274529/625000000000 : ℝ)*(sp7) + (824591232269807/100000000000000 : ℝ)*(f.failure) + (1745378551437069/100000000000000 : ℝ)*(f.sum) + (175488803085343/25049000000000000000000000000 : ℝ)*base65 + (1006114981069364113/250490000000000000000000000000000 : ℝ)*base68 + (716248479625355887/250490000000000000000000000000000 : ℝ)*base69 + (165937185679605887/250490000000000000000000000000000 : ℝ)*base71 + (4678280988341/2504900000000000000000000000 : ℝ)*base73 + (568874818292315887/250490000000000000000000000000000 : ℝ)*base75 + (1916944288340415887/250490000000000000000000000000000 : ℝ)*base77 + (1884864417264104113/250490000000000000000000000000000 : ℝ)*base80 + (17814555112413/3131125000000000000000000000 : ℝ)*base81 + (98406597/10000000000000000000000 : ℝ)*base89 + (98406597/10000000000000000000000 : ℝ)*base91 + (98406597/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5847467342030683182185079627/1565562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (37263493/100000000000000 : ℝ)*(base1) + (760097767/100000000000000 : ℝ)*(base19) + (724717981/100000000000000 : ℝ)*(base23) + (46435261/50000000000000 : ℝ)*(upper3) + (16170913/20000000000000 : ℝ)*(upper5) + (329404557301739/25000000000000 : ℝ)*(major0) + (329404557301739/25000000000000 : ℝ)*(major1) + (329404557301739/25000000000000 : ℝ)*(major2) + (2072074563/50000000000000 : ℝ)*(sp1) + (1045462107/25000000000000 : ℝ)*(sp2) + (178970399073527/10000000000000 : ℝ)*(sp4) + (447424762306221/25000000000000 : ℝ)*(sp5) + (1789699046905369/100000000000000 : ℝ)*(sp6) + (52845771448543/6250000000000 : ℝ)*(sp7) + (42276619022009/5000000000000 : ℝ)*(f.failure) + (1789703953471777/100000000000000 : ℝ)*(f.sum) + (100569923019/62622500000000000000000000000 : ℝ)*base66 + (12261762950011335597/3131125000000000000000000000000000 : ℝ)*base68 + (14503828126488335597/3131125000000000000000000000000000 : ℝ)*base70 + (6843599679951585597/3131125000000000000000000000000000 : ℝ)*base72 + (21215066473197/31311250000000000000000000000 : ℝ)*base74 + (19004677810227335597/3131125000000000000000000000000000 : ℝ)*base76 + (18229189661117710597/3131125000000000000000000000000000 : ℝ)*base78 + (35739435948690335597/3131125000000000000000000000000000 : ℝ)*base80 + (298064936226773/125245000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (3141261/500000000000000000000 : ℝ)*base90 + (3141261/500000000000000000000 : ℝ)*base92 + (3141261/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1370_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155832971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26671/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (811/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1429/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3851/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1370_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1370_s2_0 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1005633837/5000000000 : ℝ)*x 0 + (5472325019/10000000000 : ℝ)*x 1 + (5190088917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1005633837/5000000000 : ℝ)^2165 ≤ (2447691729767/20000000000000 : ℝ)^1653 := by
    have hnat : (1005633837 : ℕ)^2165*20000000000000^1653 ≤ 2447691729767^1653*5000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005633837 5000000000 2447691729767 20000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5472325019/10000000000 : ℝ)^2165 ≤ (5675227698047/12500000000000 : ℝ)^1653 := by
    have hnat : (5472325019 : ℕ)^2165*12500000000000^1653 ≤ 5675227698047^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5472325019 10000000000 5675227698047 12500000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5190088917/10000000000 : ℝ)^2165 ≤ (21179859876599/50000000000000 : ℝ)^1653 := by
    have hnat : (5190088917 : ℕ)^2165*50000000000000^1653 ≤ 21179859876599^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5190088917 10000000000 21179859876599 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1005633837/5000000000 : ℝ), (5472325019/10000000000 : ℝ), (5190088917/10000000000 : ℝ)] ![(2447691729767/20000000000000 : ℝ), (5675227698047/12500000000000 : ℝ), (21179859876599/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1005633837/5000000000 : ℝ)|^2165 ≤ (2447691729767/20000000000000 : ℝ)^1653
        have hw : |(-1005633837/5000000000 : ℝ)|=(1005633837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5472325019/10000000000 : ℝ)|^2165 ≤ (5675227698047/12500000000000 : ℝ)^1653
        have hw : |(5472325019/10000000000 : ℝ)|=(5472325019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5190088917/10000000000 : ℝ)|^2165 ≤ (21179859876599/50000000000000 : ℝ)^1653
        have hw : |(5190088917/10000000000 : ℝ)|=(5190088917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s2_1 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5364014137/10000000000 : ℝ)*x 0 + (-269610571/1250000000 : ℝ)*x 1 + (2595044563/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364014137/10000000000 : ℝ)^2165 ≤ (110571236011/250000000000 : ℝ)^1653 := by
    have hnat : (5364014137 : ℕ)^2165*250000000000^1653 ≤ 110571236011^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364014137 10000000000 110571236011 250000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269610571/1250000000 : ℝ)^2165 ≤ (1341178358123/10000000000000 : ℝ)^1653 := by
    have hnat : (269610571 : ℕ)^2165*10000000000000^1653 ≤ 1341178358123^1653*1250000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269610571 1250000000 1341178358123 10000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2595044563/5000000000 : ℝ)^2165 ≤ (8471944397467/20000000000000 : ℝ)^1653 := by
    have hnat : (2595044563 : ℕ)^2165*20000000000000^1653 ≤ 8471944397467^1653*5000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2595044563 5000000000 8471944397467 20000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364014137/10000000000 : ℝ), (-269610571/1250000000 : ℝ), (2595044563/5000000000 : ℝ)] ![(110571236011/250000000000 : ℝ), (1341178358123/10000000000000 : ℝ), (8471944397467/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364014137/10000000000 : ℝ)|^2165 ≤ (110571236011/250000000000 : ℝ)^1653
        have hw : |(5364014137/10000000000 : ℝ)|=(5364014137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-269610571/1250000000 : ℝ)|^2165 ≤ (1341178358123/10000000000000 : ℝ)^1653
        have hw : |(-269610571/1250000000 : ℝ)|=(269610571/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2595044563/5000000000 : ℝ)|^2165 ≤ (8471944397467/20000000000000 : ℝ)^1653
        have hw : |(2595044563/5000000000 : ℝ)|=(2595044563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s2_2 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (536401413/1000000000 : ℝ)*x 0 + (5190089119/10000000000 : ℝ)*x 1 + (-539221147/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536401413/1000000000 : ℝ)^2165 ≤ (11057123582201/25000000000000 : ℝ)^1653 := by
    have hnat : (536401413 : ℕ)^2165*25000000000000^1653 ≤ 11057123582201^1653*1000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536401413 1000000000 11057123582201 25000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5190089119/10000000000 : ℝ)^2165 ≤ (42359721912507/100000000000000 : ℝ)^1653 := by
    have hnat : (5190089119 : ℕ)^2165*100000000000000^1653 ≤ 42359721912507^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5190089119 10000000000 42359721912507 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539221147/2500000000 : ℝ)^2165 ≤ (838236484007/6250000000000 : ℝ)^1653 := by
    have hnat : (539221147 : ℕ)^2165*6250000000000^1653 ≤ 838236484007^1653*2500000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539221147 2500000000 838236484007 6250000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536401413/1000000000 : ℝ), (5190089119/10000000000 : ℝ), (-539221147/2500000000 : ℝ)] ![(11057123582201/25000000000000 : ℝ), (42359721912507/100000000000000 : ℝ), (838236484007/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536401413/1000000000 : ℝ)|^2165 ≤ (11057123582201/25000000000000 : ℝ)^1653
        have hw : |(536401413/1000000000 : ℝ)|=(536401413/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5190089119/10000000000 : ℝ)|^2165 ≤ (42359721912507/100000000000000 : ℝ)^1653
        have hw : |(5190089119/10000000000 : ℝ)|=(5190089119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-539221147/2500000000 : ℝ)|^2165 ≤ (838236484007/6250000000000 : ℝ)^1653
        have hw : |(-539221147/2500000000 : ℝ)|=(539221147/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s2_3 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4313799307/10000000000 : ℝ)*x 0 + (4024623649/10000000000 : ℝ)*x 1 + (4622020781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4313799307/10000000000 : ℝ)^2165 ≤ (16623845959529/50000000000000 : ℝ)^1653 := by
    have hnat : (4313799307 : ℕ)^2165*50000000000000^1653 ≤ 16623845959529^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4313799307 10000000000 16623845959529 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4024623649/10000000000 : ℝ)^2165 ≤ (15179691254859/50000000000000 : ℝ)^1653 := by
    have hnat : (4024623649 : ℕ)^2165*50000000000000^1653 ≤ 15179691254859^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4024623649 10000000000 15179691254859 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4622020781/10000000000 : ℝ)^2165 ≤ (2274557847697/6250000000000 : ℝ)^1653 := by
    have hnat : (4622020781 : ℕ)^2165*6250000000000^1653 ≤ 2274557847697^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4622020781 10000000000 2274557847697 6250000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4313799307/10000000000 : ℝ), (4024623649/10000000000 : ℝ), (4622020781/10000000000 : ℝ)] ![(16623845959529/50000000000000 : ℝ), (15179691254859/50000000000000 : ℝ), (2274557847697/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4313799307/10000000000 : ℝ)|^2165 ≤ (16623845959529/50000000000000 : ℝ)^1653
        have hw : |(4313799307/10000000000 : ℝ)|=(4313799307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4024623649/10000000000 : ℝ)|^2165 ≤ (15179691254859/50000000000000 : ℝ)^1653
        have hw : |(4024623649/10000000000 : ℝ)|=(4024623649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4622020781/10000000000 : ℝ)|^2165 ≤ (2274557847697/6250000000000 : ℝ)^1653
        have hw : |(4622020781/10000000000 : ℝ)|=(4622020781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s2_4 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-251415753/1250000000 : ℝ)*x 0 + (81121967/156250000 : ℝ)*x 1 + (5470593013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (251415753/1250000000 : ℝ)^2165 ≤ (12238923682839/100000000000000 : ℝ)^1653 := by
    have hnat : (251415753 : ℕ)^2165*100000000000000^1653 ≤ 12238923682839^1653*1250000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251415753 1250000000 12238923682839 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81121967/156250000 : ℝ)^2165 ≤ (42378074505801/100000000000000 : ℝ)^1653 := by
    have hnat : (81121967 : ℕ)^2165*100000000000000^1653 ≤ 42378074505801^1653*156250000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81121967 156250000 42378074505801 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5470593013/10000000000 : ℝ)^2165 ≤ (45383001804321/100000000000000 : ℝ)^1653 := by
    have hnat : (5470593013 : ℕ)^2165*100000000000000^1653 ≤ 45383001804321^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470593013 10000000000 45383001804321 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-251415753/1250000000 : ℝ), (81121967/156250000 : ℝ), (5470593013/10000000000 : ℝ)] ![(12238923682839/100000000000000 : ℝ), (42378074505801/100000000000000 : ℝ), (45383001804321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-251415753/1250000000 : ℝ)|^2165 ≤ (12238923682839/100000000000000 : ℝ)^1653
        have hw : |(-251415753/1250000000 : ℝ)|=(251415753/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(81121967/156250000 : ℝ)|^2165 ≤ (42378074505801/100000000000000 : ℝ)^1653
        have hw : |(81121967/156250000 : ℝ)|=(81121967/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5470593013/10000000000 : ℝ)|^2165 ≤ (45383001804321/100000000000000 : ℝ)^1653
        have hw : |(5470593013/10000000000 : ℝ)|=(5470593013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s2_5 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2645525609/5000000000 : ℝ)*x 0 + (-469095107/2500000000 : ℝ)*x 1 + (5470592947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2645525609/5000000000 : ℝ)^2165 ≤ (1357569000403/3125000000000 : ℝ)^1653 := by
    have hnat : (2645525609 : ℕ)^2165*3125000000000^1653 ≤ 1357569000403^1653*5000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2645525609 5000000000 1357569000403 3125000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (469095107/2500000000 : ℝ)^2165 ≤ (11174790883061/100000000000000 : ℝ)^1653 := by
    have hnat : (469095107 : ℕ)^2165*100000000000000^1653 ≤ 11174790883061^1653*2500000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469095107 2500000000 11174790883061 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5470592947/10000000000 : ℝ)^2165 ≤ (45383001087207/100000000000000 : ℝ)^1653 := by
    have hnat : (5470592947 : ℕ)^2165*100000000000000^1653 ≤ 45383001087207^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470592947 10000000000 45383001087207 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2645525609/5000000000 : ℝ), (-469095107/2500000000 : ℝ), (5470592947/10000000000 : ℝ)] ![(1357569000403/3125000000000 : ℝ), (11174790883061/100000000000000 : ℝ), (45383001087207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2645525609/5000000000 : ℝ)|^2165 ≤ (1357569000403/3125000000000 : ℝ)^1653
        have hw : |(2645525609/5000000000 : ℝ)|=(2645525609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-469095107/2500000000 : ℝ)|^2165 ≤ (11174790883061/100000000000000 : ℝ)^1653
        have hw : |(-469095107/2500000000 : ℝ)|=(469095107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5470592947/10000000000 : ℝ)|^2165 ≤ (45383001087207/100000000000000 : ℝ)^1653
        have hw : |(5470592947/10000000000 : ℝ)|=(5470592947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s2_6 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5291051169/10000000000 : ℝ)*x 0 + (2735296507/5000000000 : ℝ)*x 1 + (-1876380403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5291051169/10000000000 : ℝ)^2165 ≤ (2715137967873/6250000000000 : ℝ)^1653 := by
    have hnat : (5291051169 : ℕ)^2165*6250000000000^1653 ≤ 2715137967873^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5291051169 10000000000 2715137967873 6250000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2735296507/5000000000 : ℝ)^2165 ≤ (22691500907593/50000000000000 : ℝ)^1653 := by
    have hnat : (2735296507 : ℕ)^2165*50000000000000^1653 ≤ 22691500907593^1653*5000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2735296507 5000000000 22691500907593 50000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1876380403/10000000000 : ℝ)^2165 ≤ (11174790688057/100000000000000 : ℝ)^1653 := by
    have hnat : (1876380403 : ℕ)^2165*100000000000000^1653 ≤ 11174790688057^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1876380403 10000000000 11174790688057 100000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5291051169/10000000000 : ℝ), (2735296507/5000000000 : ℝ), (-1876380403/10000000000 : ℝ)] ![(2715137967873/6250000000000 : ℝ), (22691500907593/50000000000000 : ℝ), (11174790688057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5291051169/10000000000 : ℝ)|^2165 ≤ (2715137967873/6250000000000 : ℝ)^1653
        have hw : |(5291051169/10000000000 : ℝ)|=(5291051169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2735296507/5000000000 : ℝ)|^2165 ≤ (22691500907593/50000000000000 : ℝ)^1653
        have hw : |(2735296507/5000000000 : ℝ)|=(2735296507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1876380403/10000000000 : ℝ)|^2165 ≤ (11174790688057/100000000000000 : ℝ)^1653
        have hw : |(-1876380403/10000000000 : ℝ)|=(1876380403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1370_s2_7 (p : ℝ) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4313922999/10000000000 : ℝ)*x 0 + (2309193479/5000000000 : ℝ)*x 1 + (2014144637/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4313922999/10000000000 : ℝ)^2165 ≤ (2078058783667/6250000000000 : ℝ)^1653 := by
    have hnat : (4313922999 : ℕ)^2165*6250000000000^1653 ≤ 2078058783667^1653*10000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4313922999 10000000000 2078058783667 6250000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2309193479/5000000000 : ℝ)^2165 ≤ (7271091159099/20000000000000 : ℝ)^1653 := by
    have hnat : (2309193479 : ℕ)^2165*20000000000000^1653 ≤ 7271091159099^1653*5000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2309193479 5000000000 7271091159099 20000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2014144637/5000000000 : ℝ)^2165 ≤ (6079120727737/20000000000000 : ℝ)^1653 := by
    have hnat : (2014144637 : ℕ)^2165*20000000000000^1653 ≤ 6079120727737^1653*5000000000^2165 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014144637 5000000000 6079120727737 20000000000000 2165 1653 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2165/512 : ℝ)) 2165 1653 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4313922999/10000000000 : ℝ), (2309193479/5000000000 : ℝ), (2014144637/5000000000 : ℝ)] ![(2078058783667/6250000000000 : ℝ), (7271091159099/20000000000000 : ℝ), (6079120727737/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4313922999/10000000000 : ℝ)|^2165 ≤ (2078058783667/6250000000000 : ℝ)^1653
        have hw : |(4313922999/10000000000 : ℝ)|=(4313922999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2309193479/5000000000 : ℝ)|^2165 ≤ (7271091159099/20000000000000 : ℝ)^1653
        have hw : |(2309193479/5000000000 : ℝ)|=(2309193479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2014144637/5000000000 : ℝ)|^2165 ≤ (6079120727737/20000000000000 : ℝ)^1653
        have hw : |(2014144637/5000000000 : ℝ)|=(2014144637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1370_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155832971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3851/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1429/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (10029/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15997/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3851/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1429/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3851/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1429/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3851/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1429/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3851/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1429/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3851/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1429/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3851/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1429/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1429/20000 : ℝ) ^ (4329/1024 : ℝ) ≤ (44678614465361/3125000000000000000 : ℝ) := by
    have hpowers : (1429/20000 : ℝ)^4329 ≤ (44678614465361/3125000000000000000 : ℝ)^1024 := by
      have hnat : (1429 : ℕ)^4329*3125000000000000000^1024 ≤ 44678614465361^1024*20000^4329 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1429 20000 44678614465361 3125000000000000000 4329 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1429/20000 : ℝ)) (X := (44678614465361/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3851/20000 : ℝ) ^ (4329/1024 : ℝ) ≤ (4724434150339857/5000000000000000000 : ℝ) := by
    have hpowers : (3851/20000 : ℝ)^4329 ≤ (4724434150339857/5000000000000000000 : ℝ)^1024 := by
      have hnat : (3851 : ℕ)^4329*5000000000000000000^1024 ≤ 4724434150339857^1024*20000^4329 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3851 20000 4724434150339857 5000000000000000000 4329 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3851/20000 : ℝ)) (X := (4724434150339857/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562544678614465361/1562500000000000000 : ℝ) ≤ (2500016909365429/2500000000000000 : ℝ) ^ (4329/1024 : ℝ) := by
    have hpowers : (1562544678614465361/1562500000000000000 : ℝ)^1024 ≤ (2500016909365429/2500000000000000 : ℝ)^4329 := by
      have hnat : (1562544678614465361 : ℕ)^1024*2500000000000000^4329 ≤ 2500016909365429^4329*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562544678614465361 1562500000000000000 2500016909365429 2500000000000000 1024 4329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500016909365429/2500000000000000 : ℝ)) (X := (1562544678614465361/1562500000000000000 : ℝ)) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25023979599667422173/25000000000000000000 : ℝ) ≤ (1250283508019621/1250000000000000 : ℝ) ^ (4329/1024 : ℝ) := by
    have hpowers : (25023979599667422173/25000000000000000000 : ℝ)^1024 ≤ (1250283508019621/1250000000000000 : ℝ)^4329 := by
      have hnat : (25023979599667422173 : ℕ)^1024*1250000000000000^4329 ≤ 1250283508019621^4329*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25023979599667422173 25000000000000000000 1250283508019621 1250000000000000 1024 4329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250283508019621/1250000000000000 : ℝ)) (X := (25023979599667422173/25000000000000000000 : ℝ)) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2504724434150339857/2500000000000000000 : ℝ) ≤ (500223424542611/500000000000000 : ℝ) ^ (4329/1024 : ℝ) := by
    have hpowers : (2504724434150339857/2500000000000000000 : ℝ)^1024 ≤ (500223424542611/500000000000000 : ℝ)^4329 := by
      have hnat : (2504724434150339857 : ℕ)^1024*500000000000000^4329 ≤ 500223424542611^4329*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2504724434150339857 2500000000000000000 500223424542611 500000000000000 1024 4329 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500223424542611/500000000000000 : ℝ)) (X := (2504724434150339857/2500000000000000000 : ℝ)) (by norm_num) 4329 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(44678614465361/3125000000000000000 : ℝ) ≤ ((1513367187402327871/1513750000000000000 : ℝ)+2*(550106673813/302750000000000 : ℝ)*(1429/20000 : ℝ))^(4329/1024 : ℝ) := by
    rw [show (1513367187402327871/1513750000000000000 : ℝ)+2*(550106673813/302750000000000 : ℝ)*(1429/20000 : ℝ)=(2500016909365429/2500000000000000 : ℝ) by norm_num, show 1+2*(44678614465361/3125000000000000000 : ℝ)=(1562544678614465361/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4724434150339857/5000000000000000000 : ℝ)+(44678614465361/3125000000000000000 : ℝ) ≤ ((1513367187402327871/1513750000000000000 : ℝ)+(550106673813/302750000000000 : ℝ)*((3851/20000 : ℝ)+(1429/20000 : ℝ)))^(4329/1024 : ℝ) := by
    rw [show (1513367187402327871/1513750000000000000 : ℝ)+(550106673813/302750000000000 : ℝ)*((3851/20000 : ℝ)+(1429/20000 : ℝ))=(1250283508019621/1250000000000000 : ℝ) by norm_num, show 1+(4724434150339857/5000000000000000000 : ℝ)+(44678614465361/3125000000000000000 : ℝ)=(25023979599667422173/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4724434150339857/5000000000000000000 : ℝ) ≤ ((1513367187402327871/1513750000000000000 : ℝ)+2*(550106673813/302750000000000 : ℝ)*(3851/20000 : ℝ))^(4329/1024 : ℝ) := by
    rw [show (1513367187402327871/1513750000000000000 : ℝ)+2*(550106673813/302750000000000 : ℝ)*(3851/20000 : ℝ)=(500223424542611/500000000000000 : ℝ) by norm_num, show 1+2*(4724434150339857/5000000000000000000 : ℝ)=(2504724434150339857/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1513367187402327871/1513750000000000000 : ℝ)*(X 1 0+X 2 0)+(550106673813/302750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4329/1024 : ℝ)) (lo := (1429/20000 : ℝ)) (hi := (3851/20000 : ℝ)) (c := (1513367187402327871/1513750000000000000 : ℝ)) (alpha := (550106673813/302750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1513367187402327871/1513750000000000000 : ℝ)*(X 0 1+X 2 1)+(550106673813/302750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4329/1024 : ℝ)) (lo := (1429/20000 : ℝ)) (hi := (3851/20000 : ℝ)) (c := (1513367187402327871/1513750000000000000 : ℝ)) (alpha := (550106673813/302750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1513367187402327871/1513750000000000000 : ℝ)*(X 0 2+X 1 2)+(550106673813/302750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4329/1024 : ℝ)) (lo := (1429/20000 : ℝ)) (hi := (3851/20000 : ℝ)) (c := (1513367187402327871/1513750000000000000 : ℝ)) (alpha := (550106673813/302750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1005633837/5000000000 : ℝ)*X 0 0+(5472325019/10000000000 : ℝ)*X 0 1+(5190088917/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5364014137/10000000000 : ℝ)*X 1 0+(-269610571/1250000000 : ℝ)*X 1 1+(2595044563/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((536401413/1000000000 : ℝ)*X 2 0+(5190089119/10000000000 : ℝ)*X 2 1+(-539221147/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4313799307/10000000000 : ℝ)*X 0 0+(4024623649/10000000000 : ℝ)*X 0 1+(4622020781/10000000000 : ℝ)*X 0 2+(4313799307/10000000000 : ℝ)*X 1 0+(4024623649/10000000000 : ℝ)*X 1 1+(4622020781/10000000000 : ℝ)*X 1 2+(4313799307/10000000000 : ℝ)*X 2 0+(4024623649/10000000000 : ℝ)*X 2 1+(4622020781/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-251415753/1250000000 : ℝ)*X 0 0+(81121967/156250000 : ℝ)*X 0 1+(5470593013/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2645525609/5000000000 : ℝ)*X 1 0+(-469095107/2500000000 : ℝ)*X 1 1+(5470592947/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5291051169/10000000000 : ℝ)*X 2 0+(2735296507/5000000000 : ℝ)*X 2 1+(-1876380403/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4313922999/10000000000 : ℝ)*X 0 0+(2309193479/5000000000 : ℝ)*X 0 1+(2014144637/5000000000 : ℝ)*X 0 2+(4313922999/10000000000 : ℝ)*X 1 0+(2309193479/5000000000 : ℝ)*X 1 1+(2014144637/5000000000 : ℝ)*X 1 2+(4313922999/10000000000 : ℝ)*X 2 0+(2309193479/5000000000 : ℝ)*X 2 1+(2014144637/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1370_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (53252365383350277330640491/5406250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (859398253/50000000000000 : ℝ)*(base19) + (1617451031/100000000000000 : ℝ)*(base23) + (51881631/100000000000000 : ℝ)*(lower2) + (248185431/100000000000000 : ℝ)*(upper3) + (153486117/100000000000000 : ℝ)*(upper5) + (1304282608690901/50000000000000 : ℝ)*(major0) + (1304282608690901/50000000000000 : ℝ)*(major1) + (1304282608690901/50000000000000 : ℝ)*(major2) + (3543157355224831/100000000000000 : ℝ)*(sp0) + (1771589450715333/50000000000000 : ℝ)*(sp1) + (1771589501388071/50000000000000 : ℝ)*(sp2) + (167393830323841/10000000000000 : ℝ)*(sp3) + (23265002341/100000000000000 : ℝ)*(sp4) + (5591479867/50000000000000 : ℝ)*(sp7) + (13077730360923/781250000000 : ℝ)*(f.failure) + (885795155056793/25000000000000 : ℝ)*(f.sum) + (3368224473293/2162500000000000000000000000 : ℝ)*base65 + (26156776531557753/10812500000000000000000000000000 : ℝ)*base67 + (49916674866629747/10812500000000000000000000000000 : ℝ)*base70 + (32722218232370253/10812500000000000000000000000000 : ℝ)*base71 + (1080567372443/2162500000000000000000000000 : ℝ)*base73 + (15715238452870253/10812500000000000000000000000000 : ℝ)*base75 + (657087562745253/10812500000000000000000000000000 : ℝ)*base77 + (125197336973004747/10812500000000000000000000000000 : ℝ)*base80 + (1359428546343/2162500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (579733/78125000000000000000 : ℝ)*base89 + (579733/78125000000000000000 : ℝ)*base91 + (579733/78125000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9057355146202686671986161/2703125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (815092207/100000000000000 : ℝ)*(base19) + (220690389/25000000000000 : ℝ)*(base23) + (81186049/100000000000000 : ℝ)*(upper3) + (9867159/25000000000000 : ℝ)*(lower4) + (39773699/100000000000000 : ℝ)*(upper5) + (1320399911540479/50000000000000 : ℝ)*(major0) + (1320399911540479/50000000000000 : ℝ)*(major1) + (1320399911540479/50000000000000 : ℝ)*(major2) + (1884668963/20000000000000 : ℝ)*(sp1) + (11330017381/100000000000000 : ℝ)*(sp2) + (358696469170757/10000000000000 : ℝ)*(sp4) + (896738613317637/25000000000000 : ℝ)*(sp5) + (3586952478928633/100000000000000 : ℝ)*(sp6) + (169463484276441/10000000000000 : ℝ)*(sp7) + (169463484276441/10000000000000 : ℝ)*(f.failure) + (358696469170757/10000000000000 : ℝ)*(f.sum) + (5938520730747/2162500000000000000000000000 : ℝ)*base65 + (103135269252532113/10812500000000000000000000000000 : ℝ)*base68 + (131565762823157113/10812500000000000000000000000000 : ℝ)*base70 + (21846355870155387/10812500000000000000000000000000 : ℝ)*base71 + (1971447085591/270312500000000000000000000 : ℝ)*base74 + (178820693749907113/10812500000000000000000000000000 : ℝ)*base76 + (127011909200094613/10812500000000000000000000000000 : ℝ)*base78 + (20994599383344613/10812500000000000000000000000000 : ℝ)*base80 + (16517756923981/4325000000000000000000000000 : ℝ)*base82 + (6336211/1000000000000000000000 : ℝ)*base89 + (6336211/1000000000000000000000 : ℝ)*base91 + (6336211/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1370_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155832971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3851/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1429/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10029/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15997/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1370_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1370_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155832971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10029/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15997/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1370_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1370_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1370_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4329/1024 : ℝ) ≤ p) (hpb : p ≤ (2165/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155832971/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10029/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15997/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1370_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
