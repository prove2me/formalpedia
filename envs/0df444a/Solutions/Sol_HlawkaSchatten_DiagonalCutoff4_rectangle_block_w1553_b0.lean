-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1553_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:10:43.78949+00:00
-- url     : https://prove2.me/submissions/645a31a2-240d-4ab9-b5cd-c36f3b320baa

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
theorem support_rectangle_w1553_s0_0 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-821599721/5000000000 : ℝ)*x 0 + (5881951119/10000000000 : ℝ)*x 1 + (2436233459/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (821599721/5000000000 : ℝ)^4603 ≤ (2450353461259/25000000000000 : ℝ)^3579 := by
    have hnat : (821599721 : ℕ)^4603*25000000000000^3579 ≤ 2450353461259^3579*5000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      821599721 5000000000 2450353461259 25000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5881951119/10000000000 : ℝ)^4603 ≤ (5053338483997/10000000000000 : ℝ)^3579 := by
    have hnat : (5881951119 : ℕ)^4603*10000000000000^3579 ≤ 5053338483997^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5881951119 10000000000 5053338483997 10000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2436233459/5000000000 : ℝ)^4603 ≤ (61976877031/156250000000 : ℝ)^3579 := by
    have hnat : (2436233459 : ℕ)^4603*156250000000^3579 ≤ 61976877031^3579*5000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2436233459 5000000000 61976877031 156250000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-821599721/5000000000 : ℝ), (5881951119/10000000000 : ℝ), (2436233459/5000000000 : ℝ)] ![(2450353461259/25000000000000 : ℝ), (5053338483997/10000000000000 : ℝ), (61976877031/156250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-821599721/5000000000 : ℝ)|^4603 ≤ (2450353461259/25000000000000 : ℝ)^3579
        have hw : |(-821599721/5000000000 : ℝ)|=(821599721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5881951119/10000000000 : ℝ)|^4603 ≤ (5053338483997/10000000000000 : ℝ)^3579
        have hw : |(5881951119/10000000000 : ℝ)|=(5881951119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2436233459/5000000000 : ℝ)|^4603 ≤ (61976877031/156250000000 : ℝ)^3579
        have hw : |(2436233459/5000000000 : ℝ)|=(2436233459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1553_s0_1 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5469116497/10000000000 : ℝ)*x 0 + (-2206121601/10000000000 : ℝ)*x 1 + (1218116729/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5469116497/10000000000 : ℝ)^4603 ≤ (46018425526001/100000000000000 : ℝ)^3579 := by
    have hnat : (5469116497 : ℕ)^4603*100000000000000^3579 ≤ 46018425526001^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5469116497 10000000000 46018425526001 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2206121601/10000000000 : ℝ)^4603 ≤ (7158186590141/50000000000000 : ℝ)^3579 := by
    have hnat : (2206121601 : ℕ)^4603*50000000000000^3579 ≤ 7158186590141^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2206121601 10000000000 7158186590141 50000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1218116729/2500000000 : ℝ)^4603 ≤ (396652012789/1000000000000 : ℝ)^3579 := by
    have hnat : (1218116729 : ℕ)^4603*1000000000000^3579 ≤ 396652012789^3579*2500000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1218116729 2500000000 396652012789 1000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5469116497/10000000000 : ℝ), (-2206121601/10000000000 : ℝ), (1218116729/2500000000 : ℝ)] ![(46018425526001/100000000000000 : ℝ), (7158186590141/50000000000000 : ℝ), (396652012789/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5469116497/10000000000 : ℝ)|^4603 ≤ (46018425526001/100000000000000 : ℝ)^3579
        have hw : |(5469116497/10000000000 : ℝ)|=(5469116497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2206121601/10000000000 : ℝ)|^4603 ≤ (7158186590141/50000000000000 : ℝ)^3579
        have hw : |(-2206121601/10000000000 : ℝ)|=(2206121601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1218116729/2500000000 : ℝ)|^4603 ≤ (396652012789/1000000000000 : ℝ)^3579
        have hw : |(1218116729/2500000000 : ℝ)|=(1218116729/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1553_s0_2 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2734558267/5000000000 : ℝ)*x 0 + (2436233437/5000000000 : ℝ)*x 1 + (-1103060803/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2734558267/5000000000 : ℝ)^4603 ≤ (46018425926403/100000000000000 : ℝ)^3579 := by
    have hnat : (2734558267 : ℕ)^4603*100000000000000^3579 ≤ 46018425926403^3579*5000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734558267 5000000000 46018425926403 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2436233437/5000000000 : ℝ)^4603 ≤ (39665200839167/100000000000000 : ℝ)^3579 := by
    have hnat : (2436233437 : ℕ)^4603*100000000000000^3579 ≤ 39665200839167^3579*5000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2436233437 5000000000 39665200839167 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1103060803/5000000000 : ℝ)^4603 ≤ (14316373222013/100000000000000 : ℝ)^3579 := by
    have hnat : (1103060803 : ℕ)^4603*100000000000000^3579 ≤ 14316373222013^3579*5000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103060803 5000000000 14316373222013 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2734558267/5000000000 : ℝ), (2436233437/5000000000 : ℝ), (-1103060803/5000000000 : ℝ)] ![(46018425926403/100000000000000 : ℝ), (39665200839167/100000000000000 : ℝ), (14316373222013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2734558267/5000000000 : ℝ)|^4603 ≤ (46018425926403/100000000000000 : ℝ)^3579
        have hw : |(2734558267/5000000000 : ℝ)|=(2734558267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2436233437/5000000000 : ℝ)|^4603 ≤ (39665200839167/100000000000000 : ℝ)^3579
        have hw : |(2436233437/5000000000 : ℝ)|=(2436233437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1103060803/5000000000 : ℝ)|^4603 ≤ (14316373222013/100000000000000 : ℝ)^3579
        have hw : |(-1103060803/5000000000 : ℝ)|=(1103060803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1553_s0_3 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (516783031/1250000000 : ℝ)*x 0 + (773080947/2500000000 : ℝ)*x 1 + (1089540367/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (516783031/1250000000 : ℝ)^4603 ≤ (32110318290433/100000000000000 : ℝ)^3579 := by
    have hnat : (516783031 : ℕ)^4603*100000000000000^3579 ≤ 32110318290433^3579*1250000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516783031 1250000000 32110318290433 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (773080947/2500000000 : ℝ)^4603 ≤ (35364589481/160000000000 : ℝ)^3579 := by
    have hnat : (773080947 : ℕ)^4603*160000000000^3579 ≤ 35364589481^3579*2500000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      773080947 2500000000 35364589481 160000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1089540367/2000000000 : ℝ)^4603 ≤ (22893406640113/50000000000000 : ℝ)^3579 := by
    have hnat : (1089540367 : ℕ)^4603*50000000000000^3579 ≤ 22893406640113^3579*2000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089540367 2000000000 22893406640113 50000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(516783031/1250000000 : ℝ), (773080947/2500000000 : ℝ), (1089540367/2000000000 : ℝ)] ![(32110318290433/100000000000000 : ℝ), (35364589481/160000000000 : ℝ), (22893406640113/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(516783031/1250000000 : ℝ)|^4603 ≤ (32110318290433/100000000000000 : ℝ)^3579
        have hw : |(516783031/1250000000 : ℝ)|=(516783031/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(773080947/2500000000 : ℝ)|^4603 ≤ (35364589481/160000000000 : ℝ)^3579
        have hw : |(773080947/2500000000 : ℝ)|=(773080947/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1089540367/2000000000 : ℝ)|^4603 ≤ (22893406640113/50000000000000 : ℝ)^3579
        have hw : |(1089540367/2000000000 : ℝ)|=(1089540367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1553_s0_4 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-102899043/625000000 : ℝ)*x 0 + (4898002769/10000000000 : ℝ)*x 1 + (731938411/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (102899043/625000000 : ℝ)^4603 ≤ (491292804421/5000000000000 : ℝ)^3579 := by
    have hnat : (102899043 : ℕ)^4603*5000000000000^3579 ≤ 491292804421^3579*625000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102899043 625000000 491292804421 5000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4898002769/10000000000 : ℝ)^4603 ≤ (39932757768931/100000000000000 : ℝ)^3579 := by
    have hnat : (4898002769 : ℕ)^4603*100000000000000^3579 ≤ 39932757768931^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4898002769 10000000000 39932757768931 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (731938411/1250000000 : ℝ)^4603 ≤ (6280173267123/12500000000000 : ℝ)^3579 := by
    have hnat : (731938411 : ℕ)^4603*12500000000000^3579 ≤ 6280173267123^3579*1250000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      731938411 1250000000 6280173267123 12500000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-102899043/625000000 : ℝ), (4898002769/10000000000 : ℝ), (731938411/1250000000 : ℝ)] ![(491292804421/5000000000000 : ℝ), (39932757768931/100000000000000 : ℝ), (6280173267123/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-102899043/625000000 : ℝ)|^4603 ≤ (491292804421/5000000000000 : ℝ)^3579
        have hw : |(-102899043/625000000 : ℝ)|=(102899043/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4898002769/10000000000 : ℝ)|^4603 ≤ (39932757768931/100000000000000 : ℝ)^3579
        have hw : |(4898002769/10000000000 : ℝ)|=(4898002769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(731938411/1250000000 : ℝ)|^4603 ≤ (6280173267123/12500000000000 : ℝ)^3579
        have hw : |(731938411/1250000000 : ℝ)|=(731938411/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1553_s0_5 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2596589933/5000000000 : ℝ)*x 0 + (-152885203/1250000000 : ℝ)*x 1 + (365969191/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2596589933/5000000000 : ℝ)^4603 ≤ (10763537656119/25000000000000 : ℝ)^3579 := by
    have hnat : (2596589933 : ℕ)^4603*25000000000000^3579 ≤ 10763537656119^3579*5000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596589933 5000000000 10763537656119 25000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (152885203/1250000000 : ℝ)^4603 ≤ (6704465785619/100000000000000 : ℝ)^3579 := by
    have hnat : (152885203 : ℕ)^4603*100000000000000^3579 ≤ 6704465785619^3579*1250000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      152885203 1250000000 6704465785619 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (365969191/625000000 : ℝ)^4603 ≤ (1256034589421/2500000000000 : ℝ)^3579 := by
    have hnat : (365969191 : ℕ)^4603*2500000000000^3579 ≤ 1256034589421^3579*625000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      365969191 625000000 1256034589421 2500000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2596589933/5000000000 : ℝ), (-152885203/1250000000 : ℝ), (365969191/625000000 : ℝ)] ![(10763537656119/25000000000000 : ℝ), (6704465785619/100000000000000 : ℝ), (1256034589421/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2596589933/5000000000 : ℝ)|^4603 ≤ (10763537656119/25000000000000 : ℝ)^3579
        have hw : |(2596589933/5000000000 : ℝ)|=(2596589933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-152885203/1250000000 : ℝ)|^4603 ≤ (6704465785619/100000000000000 : ℝ)^3579
        have hw : |(-152885203/1250000000 : ℝ)|=(152885203/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(365969191/625000000 : ℝ)|^4603 ≤ (1256034589421/2500000000000 : ℝ)^3579
        have hw : |(365969191/625000000 : ℝ)|=(365969191/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1553_s0_6 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5193179543/10000000000 : ℝ)*x 0 + (5855507709/10000000000 : ℝ)*x 1 + (-122308109/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5193179543/10000000000 : ℝ)^4603 ≤ (43054147180473/100000000000000 : ℝ)^3579 := by
    have hnat : (5193179543 : ℕ)^4603*100000000000000^3579 ≤ 43054147180473^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5193179543 10000000000 43054147180473 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5855507709/10000000000 : ℝ)^4603 ≤ (25120695391381/50000000000000 : ℝ)^3579 := by
    have hnat : (5855507709 : ℕ)^4603*50000000000000^3579 ≤ 25120695391381^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5855507709 10000000000 25120695391381 50000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (122308109/1000000000 : ℝ)^4603 ≤ (104757219077/1562500000000 : ℝ)^3579 := by
    have hnat : (122308109 : ℕ)^4603*1562500000000^3579 ≤ 104757219077^3579*1000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122308109 1000000000 104757219077 1562500000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5193179543/10000000000 : ℝ), (5855507709/10000000000 : ℝ), (-122308109/1000000000 : ℝ)] ![(43054147180473/100000000000000 : ℝ), (25120695391381/50000000000000 : ℝ), (104757219077/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5193179543/10000000000 : ℝ)|^4603 ≤ (43054147180473/100000000000000 : ℝ)^3579
        have hw : |(5193179543/10000000000 : ℝ)|=(5193179543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5855507709/10000000000 : ℝ)|^4603 ≤ (25120695391381/50000000000000 : ℝ)^3579
        have hw : |(5855507709/10000000000 : ℝ)|=(5855507709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-122308109/1000000000 : ℝ)|^4603 ≤ (104757219077/1562500000000 : ℝ)^3579
        have hw : |(-122308109/1000000000 : ℝ)|=(122308109/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1553_s0_7 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (33133559/80000000 : ℝ)*x 0 + (673514977/1250000000 : ℝ)*x 1 + (3154023531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33133559/80000000 : ℝ)^4603 ≤ (16092281261299/50000000000000 : ℝ)^3579 := by
    have hnat : (33133559 : ℕ)^4603*50000000000000^3579 ≤ 16092281261299^3579*80000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33133559 80000000 16092281261299 50000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (673514977/1250000000 : ℝ)^4603 ≤ (22571885328121/50000000000000 : ℝ)^3579 := by
    have hnat : (673514977 : ℕ)^4603*50000000000000^3579 ≤ 22571885328121^3579*1250000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673514977 1250000000 22571885328121 50000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3154023531/10000000000 : ℝ)^4603 ≤ (22671666805041/100000000000000 : ℝ)^3579 := by
    have hnat : (3154023531 : ℕ)^4603*100000000000000^3579 ≤ 22671666805041^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3154023531 10000000000 22671666805041 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33133559/80000000 : ℝ), (673514977/1250000000 : ℝ), (3154023531/10000000000 : ℝ)] ![(16092281261299/50000000000000 : ℝ), (22571885328121/50000000000000 : ℝ), (22671666805041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33133559/80000000 : ℝ)|^4603 ≤ (16092281261299/50000000000000 : ℝ)^3579
        have hw : |(33133559/80000000 : ℝ)|=(33133559/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(673514977/1250000000 : ℝ)|^4603 ≤ (22571885328121/50000000000000 : ℝ)^3579
        have hw : |(673514977/1250000000 : ℝ)|=(673514977/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3154023531/10000000000 : ℝ)|^4603 ≤ (22671666805041/100000000000000 : ℝ)^3579
        have hw : |(3154023531/10000000000 : ℝ)|=(3154023531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1553_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (166662453/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (167/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6241/25000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4601/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4601 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4601*1^1024 ≤ 0^1024*1^4601 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4601 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4601 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4601/1024 : ℝ) ≤ (13034075760331647/800000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4601 ≤ (13034075760331647/800000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4601*800000000000000000^1024 ≤ 13034075760331647^1024*5^4601 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 13034075760331647 800000000000000000 4601 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (13034075760331647/800000000000000000 : ℝ)) (by norm_num) (by norm_num) 4601 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4601/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4601 := by
      have hnat : (1 : ℕ)^1024*1^4601 ≤ 1^4601*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4601 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4601 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (813034075760331647/800000000000000000 : ℝ) ≤ (1003603339259189/1000000000000000 : ℝ) ^ (4601/1024 : ℝ) := by
    have hpowers : (813034075760331647/800000000000000000 : ℝ)^1024 ≤ (1003603339259189/1000000000000000 : ℝ)^4601 := by
      have hnat : (813034075760331647 : ℕ)^1024*1000000000000000^4601 ≤ 1003603339259189^4601*800000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        813034075760331647 800000000000000000 1003603339259189 1000000000000000 1024 4601 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1003603339259189/1000000000000000 : ℝ)) (X := (813034075760331647/800000000000000000 : ℝ)) (by norm_num) 4601 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (413034075760331647/400000000000000000 : ℝ) ≤ (503603339259189/500000000000000 : ℝ) ^ (4601/1024 : ℝ) := by
    have hpowers : (413034075760331647/400000000000000000 : ℝ)^1024 ≤ (503603339259189/500000000000000 : ℝ)^4601 := by
      have hnat : (413034075760331647 : ℕ)^1024*500000000000000^4601 ≤ 503603339259189^4601*400000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        413034075760331647 400000000000000000 503603339259189 500000000000000 1024 4601 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (503603339259189/500000000000000 : ℝ)) (X := (413034075760331647/400000000000000000 : ℝ)) (by norm_num) 4601 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(3603339259189/400000000000000 : ℝ)*(0 : ℝ))^(4601/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(3603339259189/400000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13034075760331647/800000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(3603339259189/400000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4601/1024 : ℝ) := by
    rw [show (1 : ℝ)+(3603339259189/400000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1003603339259189/1000000000000000 : ℝ) by norm_num, show 1+(13034075760331647/800000000000000000 : ℝ)+(0 : ℝ)=(813034075760331647/800000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13034075760331647/800000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(3603339259189/400000000000000 : ℝ)*(2/5 : ℝ))^(4601/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(3603339259189/400000000000000 : ℝ)*(2/5 : ℝ)=(503603339259189/500000000000000 : ℝ) by norm_num, show 1+2*(13034075760331647/800000000000000000 : ℝ)=(413034075760331647/400000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(3603339259189/400000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4601/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3603339259189/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(3603339259189/400000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4601/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3603339259189/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(3603339259189/400000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4601/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3603339259189/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-821599721/5000000000 : ℝ)*X 0 0+(5881951119/10000000000 : ℝ)*X 0 1+(2436233459/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5469116497/10000000000 : ℝ)*X 1 0+(-2206121601/10000000000 : ℝ)*X 1 1+(1218116729/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2734558267/5000000000 : ℝ)*X 2 0+(2436233437/5000000000 : ℝ)*X 2 1+(-1103060803/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((516783031/1250000000 : ℝ)*X 0 0+(773080947/2500000000 : ℝ)*X 0 1+(1089540367/2000000000 : ℝ)*X 0 2+(516783031/1250000000 : ℝ)*X 1 0+(773080947/2500000000 : ℝ)*X 1 1+(1089540367/2000000000 : ℝ)*X 1 2+(516783031/1250000000 : ℝ)*X 2 0+(773080947/2500000000 : ℝ)*X 2 1+(1089540367/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-102899043/625000000 : ℝ)*X 0 0+(4898002769/10000000000 : ℝ)*X 0 1+(731938411/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2596589933/5000000000 : ℝ)*X 1 0+(-152885203/1250000000 : ℝ)*X 1 1+(365969191/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5193179543/10000000000 : ℝ)*X 2 0+(5855507709/10000000000 : ℝ)*X 2 1+(-122308109/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((33133559/80000000 : ℝ)*X 0 0+(673514977/1250000000 : ℝ)*X 0 1+(3154023531/10000000000 : ℝ)*X 0 2+(33133559/80000000 : ℝ)*X 1 0+(673514977/1250000000 : ℝ)*X 1 1+(3154023531/10000000000 : ℝ)*X 1 2+(33133559/80000000 : ℝ)*X 2 0+(673514977/1250000000 : ℝ)*X 2 1+(3154023531/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (79532063000626192169727/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (76471829/100000000000000 : ℝ)*(base1) + (844896861/50000000000000 : ℝ)*(base19) + (1696495493/100000000000000 : ℝ)*(base23) + (219061981/100000000000000 : ℝ)*(upper3) + (219493573/100000000000000 : ℝ)*(upper5) + (707591360383173/100000000000000 : ℝ)*(major0) + (707591360383173/100000000000000 : ℝ)*(major1) + (707591360383173/100000000000000 : ℝ)*(major2) + (990610777543547/100000000000000 : ℝ)*(sp0) + (495307607884799/50000000000000 : ℝ)*(sp1) + (247653802266957/25000000000000 : ℝ)*(sp2) + (21228140750907/5000000000000 : ℝ)*(sp3) + (3102245801/50000000000000 : ℝ)*(sp4) + (664651543/25000000000000 : ℝ)*(sp7) + (424565550096141/100000000000000 : ℝ)*(f.failure) + (24765422639083/2500000000000 : ℝ)*(f.sum) + (79906275826697/20000000000000000000000000000 : ℝ)*base65 + (221411253106697/40000000000000000000000000000 : ℝ)*base67 + (243569251066697/40000000000000000000000000000 : ℝ)*base69 + (284837584186697/40000000000000000000000000000 : ℝ)*base71 + (33726355746697/20000000000000000000000000000 : ℝ)*base73 + (490531401226697/40000000000000000000000000000 : ℝ)*base75 + (210061186346697/40000000000000000000000000000 : ℝ)*base77 + (94691067466697/40000000000000000000000000000 : ℝ)*base79 + (29004431946697/20000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (55106127/10000000000000000000000 : ℝ)*base90 + (55106127/10000000000000000000000 : ℝ)*base92 + (55106127/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (115579523082936119727249/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1247101139/100000000000000 : ℝ)*(base19) + (337147401/25000000000000 : ℝ)*(base23) + (160358261/100000000000000 : ℝ)*(base39) + (79602317/50000000000000 : ℝ)*(upper3) + (128025293/50000000000000 : ℝ)*(upper5) + (745994449327123/100000000000000 : ℝ)*(major0) + (745994449327123/100000000000000 : ℝ)*(major1) + (372997144484431/50000000000000 : ℝ)*(major2) + (339178341/10000000000000 : ℝ)*(sp1) + (3558696527/100000000000000 : ℝ)*(sp2) + (522190279821031/50000000000000 : ℝ)*(sp4) + (522187960378757/50000000000000 : ℝ)*(sp5) + (1044375812714193/100000000000000 : ℝ)*(sp6) + (447607986021377/100000000000000 : ℝ)*(sp7) + (447607986021377/100000000000000 : ℝ)*(f.failure) + (261095180000081/25000000000000 : ℝ)*(f.sum) + (19913547140767/8000000000000000000000000000 : ℝ)*base66 + (172766642013541/20000000000000000000000000000 : ℝ)*base68 + (267815542963247/40000000000000000000000000000 : ℝ)*base69 + (134328531193541/20000000000000000000000000000 : ℝ)*base72 + (44247533276767/8000000000000000000000000000 : ℝ)*base74 + (85877836556753/40000000000000000000000000000 : ℝ)*base76 + (116960618996753/40000000000000000000000000000 : ℝ)*base78 + (345204337996753/40000000000000000000000000000 : ℝ)*base80 + (27745355583247/20000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (101257781/10000000000000000000000 : ℝ)*base89 + (101257781/10000000000000000000000 : ℝ)*base91 + (101257781/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1553_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (166662453/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (167/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6241/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1553_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1553_s1_0 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-89306879/500000000 : ℝ)*x 0 + (1108942993/2000000000 : ℝ)*x 1 + (5117653701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (89306879/500000000 : ℝ)^4603 ≤ (68195815429/625000000000 : ℝ)^3579 := by
    have hnat : (89306879 : ℕ)^4603*625000000000^3579 ≤ 68195815429^3579*500000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89306879 500000000 68195815429 625000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1108942993/2000000000 : ℝ)^4603 ≤ (46838138850373/100000000000000 : ℝ)^3579 := by
    have hnat : (1108942993 : ℕ)^4603*100000000000000^3579 ≤ 46838138850373^3579*2000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108942993 2000000000 46838138850373 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5117653701/10000000000 : ℝ)^4603 ≤ (8450106132167/20000000000000 : ℝ)^3579 := by
    have hnat : (5117653701 : ℕ)^4603*20000000000000^3579 ≤ 8450106132167^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5117653701 10000000000 8450106132167 20000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-89306879/500000000 : ℝ), (1108942993/2000000000 : ℝ), (5117653701/10000000000 : ℝ)] ![(68195815429/625000000000 : ℝ), (46838138850373/100000000000000 : ℝ), (8450106132167/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-89306879/500000000 : ℝ)|^4603 ≤ (68195815429/625000000000 : ℝ)^3579
        have hw : |(-89306879/500000000 : ℝ)|=(89306879/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1108942993/2000000000 : ℝ)|^4603 ≤ (46838138850373/100000000000000 : ℝ)^3579
        have hw : |(1108942993/2000000000 : ℝ)|=(1108942993/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5117653701/10000000000 : ℝ)|^4603 ≤ (8450106132167/20000000000000 : ℝ)^3579
        have hw : |(5117653701/10000000000 : ℝ)|=(5117653701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1553_s1_1 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2689672063/5000000000 : ℝ)*x 0 + (-1256207/6250000 : ℝ)*x 1 + (5117653559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2689672063/5000000000 : ℝ)^4603 ≤ (45049229720731/100000000000000 : ℝ)^3579 := by
    have hnat : (2689672063 : ℕ)^4603*100000000000000^3579 ≤ 45049229720731^3579*5000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689672063 5000000000 45049229720731 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1256207/6250000 : ℝ)^4603 ≤ (6350120552787/50000000000000 : ℝ)^3579 := by
    have hnat : (1256207 : ℕ)^4603*50000000000000^3579 ≤ 6350120552787^3579*6250000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1256207 6250000 6350120552787 50000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5117653559/10000000000 : ℝ)^4603 ≤ (42250529153087/100000000000000 : ℝ)^3579 := by
    have hnat : (5117653559 : ℕ)^4603*100000000000000^3579 ≤ 42250529153087^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5117653559 10000000000 42250529153087 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2689672063/5000000000 : ℝ), (-1256207/6250000 : ℝ), (5117653559/10000000000 : ℝ)] ![(45049229720731/100000000000000 : ℝ), (6350120552787/50000000000000 : ℝ), (42250529153087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2689672063/5000000000 : ℝ)|^4603 ≤ (45049229720731/100000000000000 : ℝ)^3579
        have hw : |(2689672063/5000000000 : ℝ)|=(2689672063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1256207/6250000 : ℝ)|^4603 ≤ (6350120552787/50000000000000 : ℝ)^3579
        have hw : |(-1256207/6250000 : ℝ)|=(1256207/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5117653559/10000000000 : ℝ)|^4603 ≤ (42250529153087/100000000000000 : ℝ)^3579
        have hw : |(5117653559/10000000000 : ℝ)|=(5117653559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1553_s1_2 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5379343989/10000000000 : ℝ)*x 0 + (2558826729/5000000000 : ℝ)*x 1 + (-1004965757/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5379343989/10000000000 : ℝ)^4603 ≤ (45049228245167/100000000000000 : ℝ)^3579 := by
    have hnat : (5379343989 : ℕ)^4603*100000000000000^3579 ≤ 45049228245167^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5379343989 10000000000 45049228245167 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2558826729/5000000000 : ℝ)^4603 ≤ (21125264040337/50000000000000 : ℝ)^3579 := by
    have hnat : (2558826729 : ℕ)^4603*50000000000000^3579 ≤ 21125264040337^3579*5000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2558826729 5000000000 21125264040337 50000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1004965757/5000000000 : ℝ)^4603 ≤ (12700243657333/100000000000000 : ℝ)^3579 := by
    have hnat : (1004965757 : ℕ)^4603*100000000000000^3579 ≤ 12700243657333^3579*5000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004965757 5000000000 12700243657333 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5379343989/10000000000 : ℝ), (2558826729/5000000000 : ℝ), (-1004965757/5000000000 : ℝ)] ![(45049228245167/100000000000000 : ℝ), (21125264040337/50000000000000 : ℝ), (12700243657333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5379343989/10000000000 : ℝ)|^4603 ≤ (45049228245167/100000000000000 : ℝ)^3579
        have hw : |(5379343989/10000000000 : ℝ)|=(5379343989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2558826729/5000000000 : ℝ)|^4603 ≤ (21125264040337/50000000000000 : ℝ)^3579
        have hw : |(2558826729/5000000000 : ℝ)|=(2558826729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1004965757/5000000000 : ℝ)|^4603 ≤ (12700243657333/100000000000000 : ℝ)^3579
        have hw : |(-1004965757/5000000000 : ℝ)|=(1004965757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1553_s1_3 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2117325817/5000000000 : ℝ)*x 0 + (1880188649/5000000000 : ℝ)*x 1 + (4756817863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2117325817/5000000000 : ℝ)^4603 ≤ (33116559702983/100000000000000 : ℝ)^3579 := by
    have hnat : (2117325817 : ℕ)^4603*100000000000000^3579 ≤ 33116559702983^3579*5000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117325817 5000000000 33116559702983 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1880188649/5000000000 : ℝ)^4603 ≤ (142124656363/500000000000 : ℝ)^3579 := by
    have hnat : (1880188649 : ℕ)^4603*500000000000^3579 ≤ 142124656363^3579*5000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1880188649 5000000000 142124656363 500000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4756817863/10000000000 : ℝ)^4603 ≤ (7691701802689/20000000000000 : ℝ)^3579 := by
    have hnat : (4756817863 : ℕ)^4603*20000000000000^3579 ≤ 7691701802689^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4756817863 10000000000 7691701802689 20000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2117325817/5000000000 : ℝ), (1880188649/5000000000 : ℝ), (4756817863/10000000000 : ℝ)] ![(33116559702983/100000000000000 : ℝ), (142124656363/500000000000 : ℝ), (7691701802689/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2117325817/5000000000 : ℝ)|^4603 ≤ (33116559702983/100000000000000 : ℝ)^3579
        have hw : |(2117325817/5000000000 : ℝ)|=(2117325817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1880188649/5000000000 : ℝ)|^4603 ≤ (142124656363/500000000000 : ℝ)^3579
        have hw : |(1880188649/5000000000 : ℝ)|=(1880188649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4756817863/10000000000 : ℝ)|^4603 ≤ (7691701802689/20000000000000 : ℝ)^3579
        have hw : |(4756817863/10000000000 : ℝ)|=(4756817863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1553_s1_4 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-446592967/2500000000 : ℝ)*x 0 + (5122162833/10000000000 : ℝ)*x 1 + (5540137529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (446592967/2500000000 : ℝ)^4603 ≤ (5456585620897/50000000000000 : ℝ)^3579 := by
    have hnat : (446592967 : ℕ)^4603*50000000000000^3579 ≤ 5456585620897^3579*2500000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      446592967 2500000000 5456585620897 50000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5122162833/10000000000 : ℝ)^4603 ≤ (42298414418577/100000000000000 : ℝ)^3579 := by
    have hnat : (5122162833 : ℕ)^4603*100000000000000^3579 ≤ 42298414418577^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5122162833 10000000000 42298414418577 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5540137529/10000000000 : ℝ)^4603 ≤ (11697103580913/25000000000000 : ℝ)^3579 := by
    have hnat : (5540137529 : ℕ)^4603*25000000000000^3579 ≤ 11697103580913^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5540137529 10000000000 11697103580913 25000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-446592967/2500000000 : ℝ), (5122162833/10000000000 : ℝ), (5540137529/10000000000 : ℝ)] ![(5456585620897/50000000000000 : ℝ), (42298414418577/100000000000000 : ℝ), (11697103580913/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-446592967/2500000000 : ℝ)|^4603 ≤ (5456585620897/50000000000000 : ℝ)^3579
        have hw : |(-446592967/2500000000 : ℝ)|=(446592967/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5122162833/10000000000 : ℝ)|^4603 ≤ (42298414418577/100000000000000 : ℝ)^3579
        have hw : |(5122162833/10000000000 : ℝ)|=(5122162833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5540137529/10000000000 : ℝ)|^4603 ≤ (11697103580913/25000000000000 : ℝ)^3579
        have hw : |(5540137529/10000000000 : ℝ)|=(5540137529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1553_s1_5 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5266338249/10000000000 : ℝ)*x 0 + (-317489873/2000000000 : ℝ)*x 1 + (554013671/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5266338249/10000000000 : ℝ)^4603 ≤ (8767154417499/20000000000000 : ℝ)^3579 := by
    have hnat : (5266338249 : ℕ)^4603*20000000000000^3579 ≤ 8767154417499^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266338249 10000000000 8767154417499 20000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (317489873/2000000000 : ℝ)^4603 ≤ (4687911233947/50000000000000 : ℝ)^3579 := by
    have hnat : (317489873 : ℕ)^4603*50000000000000^3579 ≤ 4687911233947^3579*2000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317489873 2000000000 4687911233947 50000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (554013671/1000000000 : ℝ)^4603 ≤ (1462137669623/3125000000000 : ℝ)^3579 := by
    have hnat : (554013671 : ℕ)^4603*3125000000000^3579 ≤ 1462137669623^3579*1000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554013671 1000000000 1462137669623 3125000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5266338249/10000000000 : ℝ), (-317489873/2000000000 : ℝ), (554013671/1000000000 : ℝ)] ![(8767154417499/20000000000000 : ℝ), (4687911233947/50000000000000 : ℝ), (1462137669623/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5266338249/10000000000 : ℝ)|^4603 ≤ (8767154417499/20000000000000 : ℝ)^3579
        have hw : |(5266338249/10000000000 : ℝ)|=(5266338249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-317489873/2000000000 : ℝ)|^4603 ≤ (4687911233947/50000000000000 : ℝ)^3579
        have hw : |(-317489873/2000000000 : ℝ)|=(317489873/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(554013671/1000000000 : ℝ)|^4603 ≤ (1462137669623/3125000000000 : ℝ)^3579
        have hw : |(554013671/1000000000 : ℝ)|=(554013671/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1553_s1_6 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (263316999/500000000 : ℝ)*x 0 + (1108027247/2000000000 : ℝ)*x 1 + (-793723803/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263316999/500000000 : ℝ)^4603 ≤ (8767158123677/20000000000000 : ℝ)^3579 := by
    have hnat : (263316999 : ℕ)^4603*20000000000000^3579 ≤ 8767158123677^3579*500000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263316999 500000000 8767158123677 20000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1108027247/2000000000 : ℝ)^4603 ≤ (46788400268637/100000000000000 : ℝ)^3579 := by
    have hnat : (1108027247 : ℕ)^4603*100000000000000^3579 ≤ 46788400268637^3579*2000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108027247 2000000000 46788400268637 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (793723803/5000000000 : ℝ)^4603 ≤ (1875161821283/20000000000000 : ℝ)^3579 := by
    have hnat : (793723803 : ℕ)^4603*20000000000000^3579 ≤ 1875161821283^3579*5000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      793723803 5000000000 1875161821283 20000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(263316999/500000000 : ℝ), (1108027247/2000000000 : ℝ), (-793723803/5000000000 : ℝ)] ![(8767158123677/20000000000000 : ℝ), (46788400268637/100000000000000 : ℝ), (1875161821283/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(263316999/500000000 : ℝ)|^4603 ≤ (8767158123677/20000000000000 : ℝ)^3579
        have hw : |(263316999/500000000 : ℝ)|=(263316999/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1108027247/2000000000 : ℝ)|^4603 ≤ (46788400268637/100000000000000 : ℝ)^3579
        have hw : |(1108027247/2000000000 : ℝ)|=(1108027247/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-793723803/5000000000 : ℝ)|^4603 ≤ (1875161821283/20000000000000 : ℝ)^3579
        have hw : |(-793723803/5000000000 : ℝ)|=(793723803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1553_s1_7 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2117599377/5000000000 : ℝ)*x 0 + (2373147463/5000000000 : ℝ)*x 1 + (3771058337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2117599377/5000000000 : ℝ)^4603 ≤ (33122062676457/100000000000000 : ℝ)^3579 := by
    have hnat : (2117599377 : ℕ)^4603*100000000000000^3579 ≤ 33122062676457^3579*5000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117599377 5000000000 33122062676457 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2373147463/5000000000 : ℝ)^4603 ≤ (38349124803811/100000000000000 : ℝ)^3579 := by
    have hnat : (2373147463 : ℕ)^4603*100000000000000^3579 ≤ 38349124803811^3579*5000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2373147463 5000000000 38349124803811 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3771058337/10000000000 : ℝ)^4603 ≤ (28528812505443/100000000000000 : ℝ)^3579 := by
    have hnat : (3771058337 : ℕ)^4603*100000000000000^3579 ≤ 28528812505443^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3771058337 10000000000 28528812505443 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2117599377/5000000000 : ℝ), (2373147463/5000000000 : ℝ), (3771058337/10000000000 : ℝ)] ![(33122062676457/100000000000000 : ℝ), (38349124803811/100000000000000 : ℝ), (28528812505443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2117599377/5000000000 : ℝ)|^4603 ≤ (33122062676457/100000000000000 : ℝ)^3579
        have hw : |(2117599377/5000000000 : ℝ)|=(2117599377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2373147463/5000000000 : ℝ)|^4603 ≤ (38349124803811/100000000000000 : ℝ)^3579
        have hw : |(2373147463/5000000000 : ℝ)|=(2373147463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3771058337/10000000000 : ℝ)|^4603 ≤ (28528812505443/100000000000000 : ℝ)^3579
        have hw : |(3771058337/10000000000 : ℝ)|=(3771058337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1553_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (166662453/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6241/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (167/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (8873/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8957/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6241/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (167/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6241/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (167/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6241/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (167/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6241/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (167/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6241/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (167/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6241/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (167/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (167/5000 : ℝ) ^ (4601/1024 : ℝ) ≤ (23278268733021/100000000000000000000 : ℝ) := by
    have hpowers : (167/5000 : ℝ)^4601 ≤ (23278268733021/100000000000000000000 : ℝ)^1024 := by
      have hnat : (167 : ℕ)^4601*100000000000000000000^1024 ≤ 23278268733021^1024*5000^4601 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        167 5000 23278268733021 100000000000000000000 4601 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (167/5000 : ℝ)) (X := (23278268733021/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4601 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (6241/25000 : ℝ) ^ (4601/1024 : ℝ) ≤ (979498351845649/500000000000000000 : ℝ) := by
    have hpowers : (6241/25000 : ℝ)^4601 ≤ (979498351845649/500000000000000000 : ℝ)^1024 := by
      have hnat : (6241 : ℕ)^4601*500000000000000000^1024 ≤ 979498351845649^1024*25000^4601 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6241 25000 979498351845649 500000000000000000 4601 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6241/25000 : ℝ)) (X := (979498351845649/500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4601 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000023278268733021/50000000000000000000 : ℝ) ≤ (625000064760223/625000000000000 : ℝ) ^ (4601/1024 : ℝ) := by
    have hpowers : (50000023278268733021/50000000000000000000 : ℝ)^1024 ≤ (625000064760223/625000000000000 : ℝ)^4601 := by
      have hnat : (50000023278268733021 : ℕ)^1024*625000000000000^4601 ≤ 625000064760223^4601*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000023278268733021 50000000000000000000 625000064760223 625000000000000 1024 4601 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625000064760223/625000000000000 : ℝ)) (X := (50000023278268733021/50000000000000000000 : ℝ)) (by norm_num) 4601 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100195922948637862821/100000000000000000000 : ℝ) ≤ (400174286009287/400000000000000 : ℝ) ^ (4601/1024 : ℝ) := by
    have hpowers : (100195922948637862821/100000000000000000000 : ℝ)^1024 ≤ (400174286009287/400000000000000 : ℝ)^4601 := by
      have hnat : (100195922948637862821 : ℕ)^1024*400000000000000^4601 ≤ 400174286009287^4601*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100195922948637862821 100000000000000000000 400174286009287 400000000000000 1024 4601 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400174286009287/400000000000000 : ℝ)) (X := (100195922948637862821/100000000000000000000 : ℝ)) (by norm_num) 4601 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (250979498351845649/250000000000000000 : ℝ) ≤ (5004356632150391/5000000000000000 : ℝ) ^ (4601/1024 : ℝ) := by
    have hpowers : (250979498351845649/250000000000000000 : ℝ)^1024 ≤ (5004356632150391/5000000000000000 : ℝ)^4601 := by
      have hnat : (250979498351845649 : ℕ)^1024*5000000000000000^4601 ≤ 5004356632150391^4601*250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        250979498351845649 250000000000000000 5004356632150391 5000000000000000 1024 4601 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004356632150391/5000000000000000 : ℝ)) (X := (250979498351845649/250000000000000000 : ℝ)) (by norm_num) 4601 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(23278268733021/100000000000000000000 : ℝ) ≤ ((9008788481834279153/9010000000000000000 : ℝ)+2*(1452038022869/720800000000000 : ℝ)*(167/5000 : ℝ))^(4601/1024 : ℝ) := by
    rw [show (9008788481834279153/9010000000000000000 : ℝ)+2*(1452038022869/720800000000000 : ℝ)*(167/5000 : ℝ)=(625000064760223/625000000000000 : ℝ) by norm_num, show 1+2*(23278268733021/100000000000000000000 : ℝ)=(50000023278268733021/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(979498351845649/500000000000000000 : ℝ)+(23278268733021/100000000000000000000 : ℝ) ≤ ((9008788481834279153/9010000000000000000 : ℝ)+(1452038022869/720800000000000 : ℝ)*((6241/25000 : ℝ)+(167/5000 : ℝ)))^(4601/1024 : ℝ) := by
    rw [show (9008788481834279153/9010000000000000000 : ℝ)+(1452038022869/720800000000000 : ℝ)*((6241/25000 : ℝ)+(167/5000 : ℝ))=(400174286009287/400000000000000 : ℝ) by norm_num, show 1+(979498351845649/500000000000000000 : ℝ)+(23278268733021/100000000000000000000 : ℝ)=(100195922948637862821/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(979498351845649/500000000000000000 : ℝ) ≤ ((9008788481834279153/9010000000000000000 : ℝ)+2*(1452038022869/720800000000000 : ℝ)*(6241/25000 : ℝ))^(4601/1024 : ℝ) := by
    rw [show (9008788481834279153/9010000000000000000 : ℝ)+2*(1452038022869/720800000000000 : ℝ)*(6241/25000 : ℝ)=(5004356632150391/5000000000000000 : ℝ) by norm_num, show 1+2*(979498351845649/500000000000000000 : ℝ)=(250979498351845649/250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9008788481834279153/9010000000000000000 : ℝ)*(X 1 0+X 2 0)+(1452038022869/720800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4601/1024 : ℝ)) (lo := (167/5000 : ℝ)) (hi := (6241/25000 : ℝ)) (c := (9008788481834279153/9010000000000000000 : ℝ)) (alpha := (1452038022869/720800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9008788481834279153/9010000000000000000 : ℝ)*(X 0 1+X 2 1)+(1452038022869/720800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4601/1024 : ℝ)) (lo := (167/5000 : ℝ)) (hi := (6241/25000 : ℝ)) (c := (9008788481834279153/9010000000000000000 : ℝ)) (alpha := (1452038022869/720800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9008788481834279153/9010000000000000000 : ℝ)*(X 0 2+X 1 2)+(1452038022869/720800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4601/1024 : ℝ)) (lo := (167/5000 : ℝ)) (hi := (6241/25000 : ℝ)) (c := (9008788481834279153/9010000000000000000 : ℝ)) (alpha := (1452038022869/720800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-89306879/500000000 : ℝ)*X 0 0+(1108942993/2000000000 : ℝ)*X 0 1+(5117653701/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2689672063/5000000000 : ℝ)*X 1 0+(-1256207/6250000 : ℝ)*X 1 1+(5117653559/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5379343989/10000000000 : ℝ)*X 2 0+(2558826729/5000000000 : ℝ)*X 2 1+(-1004965757/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2117325817/5000000000 : ℝ)*X 0 0+(1880188649/5000000000 : ℝ)*X 0 1+(4756817863/10000000000 : ℝ)*X 0 2+(2117325817/5000000000 : ℝ)*X 1 0+(1880188649/5000000000 : ℝ)*X 1 1+(4756817863/10000000000 : ℝ)*X 1 2+(2117325817/5000000000 : ℝ)*X 2 0+(1880188649/5000000000 : ℝ)*X 2 1+(4756817863/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-446592967/2500000000 : ℝ)*X 0 0+(5122162833/10000000000 : ℝ)*X 0 1+(5540137529/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5266338249/10000000000 : ℝ)*X 1 0+(-317489873/2000000000 : ℝ)*X 1 1+(554013671/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((263316999/500000000 : ℝ)*X 2 0+(1108027247/2000000000 : ℝ)*X 2 1+(-793723803/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2117599377/5000000000 : ℝ)*X 0 0+(2373147463/5000000000 : ℝ)*X 0 1+(3771058337/10000000000 : ℝ)*X 0 2+(2117599377/5000000000 : ℝ)*X 1 0+(2373147463/5000000000 : ℝ)*X 1 1+(3771058337/10000000000 : ℝ)*X 1 2+(2117599377/5000000000 : ℝ)*X 2 0+(2373147463/5000000000 : ℝ)*X 2 1+(3771058337/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (330593139056007818264511/36040000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22498383/20000000000000 : ℝ)*(base1) + (354730291/25000000000000 : ℝ)*(base19) + (1359285733/100000000000000 : ℝ)*(base23) + (15970283/6250000000000 : ℝ)*(upper3) + (35620567/50000000000000 : ℝ)*(upper5) + (1672592346525247/100000000000000 : ℝ)*(major0) + (1672592346525247/100000000000000 : ℝ)*(major1) + (1672592346525247/100000000000000 : ℝ)*(major2) + (1170797759844409/50000000000000 : ℝ)*(sp0) + (1170801093959931/50000000000000 : ℝ)*(sp1) + (585400561888823/25000000000000 : ℝ)*(sp2) + (125446982767839/12500000000000 : ℝ)*(sp3) + (4099822061/50000000000000 : ℝ)*(sp4) + (2402904907/50000000000000 : ℝ)*(sp7) + (1003580780444439/100000000000000 : ℝ)*(f.failure) + (1170801803420513/50000000000000 : ℝ)*(f.sum) + (51403062847477/36040000000000000000000000000 : ℝ)*base66 + (1289471406355186709/901000000000000000000000000000000 : ℝ)*base68 + (2180442860250813291/901000000000000000000000000000000 : ℝ)*base69 + (6371254521195186709/901000000000000000000000000000000 : ℝ)*base72 + (14231589972043/36040000000000000000000000000 : ℝ)*base73 + (3251342770451186709/901000000000000000000000000000000 : ℝ)*base76 + (695370311228813291/901000000000000000000000000000000 : ℝ)*base77 + (2938993006904813291/901000000000000000000000000000000 : ℝ)*base79 + (66379662710203/36040000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (66051133/10000000000000000000000 : ℝ)*base90 + (66051133/10000000000000000000000 : ℝ)*base92 + (66051133/10000000000000000000000 : ℝ)*base94 + (1/50000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (981324921754934213597357913/225250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (231789913/50000000000000 : ℝ)*(base19) + (38365581/3125000000000 : ℝ)*(base23) + (87203683/100000000000000 : ℝ)*(lower2) + (5402369/50000000000000 : ℝ)*(upper3) + (28781457/10000000000000 : ℝ)*(upper5) + (854472622212307/50000000000000 : ℝ)*(major0) + (854472622212307/50000000000000 : ℝ)*(major1) + (854472622212307/50000000000000 : ℝ)*(major2) + (6678825527/100000000000000 : ℝ)*(sp2) + (256378623/50000000000000 : ℝ)*(sp3) + (1196248636493363/50000000000000 : ℝ)*(sp4) + (2392496809406901/100000000000000 : ℝ)*(sp5) + (149530585403913/6250000000000 : ℝ)*(sp6) + (205078511577027/20000000000000 : ℝ)*(sp7) + (51269653532119/5000000000000 : ℝ)*(f.failure) + (1196248636493363/50000000000000 : ℝ)*(f.sum) + (3708288050937/18020000000000000000000000000 : ℝ)*base66 + (230858394658076529/450500000000000000000000000000000 : ℝ)*base68 + (1172014476006423471/450500000000000000000000000000000 : ℝ)*base69 + (1223822125321576529/450500000000000000000000000000000 : ℝ)*base72 + (25028126074277/18020000000000000000000000000 : ℝ)*base74 + (1948146567021576529/450500000000000000000000000000000 : ℝ)*base76 + (1310236446968576529/450500000000000000000000000000000 : ℝ)*base78 + (145728751497923471/450500000000000000000000000000000 : ℝ)*base79 + (22088577786557/18020000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (3172093/500000000000000000000 : ℝ)*base90 + (3172093/500000000000000000000 : ℝ)*base92 + (3172093/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1553_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (166662453/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6241/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (167/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8873/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8957/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1553_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1553_s2_0 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-36126469/200000000 : ℝ)*x 0 + (1089175371/2000000000 : ℝ)*x 1 + (2601680211/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (36126469/200000000 : ℝ)^4603 ≤ (5535090605537/50000000000000 : ℝ)^3579 := by
    have hnat : (36126469 : ℕ)^4603*50000000000000^3579 ≤ 5535090605537^3579*200000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36126469 200000000 5535090605537 50000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1089175371/2000000000 : ℝ)^4603 ≤ (9153417413983/20000000000000 : ℝ)^3579 := by
    have hnat : (1089175371 : ℕ)^4603*20000000000000^3579 ≤ 9153417413983^3579*2000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089175371 2000000000 9153417413983 20000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2601680211/5000000000 : ℝ)^4603 ≤ (5395341463039/12500000000000 : ℝ)^3579 := by
    have hnat : (2601680211 : ℕ)^4603*12500000000000^3579 ≤ 5395341463039^3579*5000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2601680211 5000000000 5395341463039 12500000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-36126469/200000000 : ℝ), (1089175371/2000000000 : ℝ), (2601680211/5000000000 : ℝ)] ![(5535090605537/50000000000000 : ℝ), (9153417413983/20000000000000 : ℝ), (5395341463039/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-36126469/200000000 : ℝ)|^4603 ≤ (5535090605537/50000000000000 : ℝ)^3579
        have hw : |(-36126469/200000000 : ℝ)|=(36126469/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1089175371/2000000000 : ℝ)|^4603 ≤ (9153417413983/20000000000000 : ℝ)^3579
        have hw : |(1089175371/2000000000 : ℝ)|=(1089175371/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2601680211/5000000000 : ℝ)|^4603 ≤ (5395341463039/12500000000000 : ℝ)^3579
        have hw : |(2601680211/5000000000 : ℝ)|=(2601680211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1553_s2_1 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070786039/2000000000 : ℝ)*x 0 + (-96544647/500000000 : ℝ)*x 1 + (5203360441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070786039/2000000000 : ℝ)^4603 ≤ (22387846632171/50000000000000 : ℝ)^3579 := by
    have hnat : (1070786039 : ℕ)^4603*50000000000000^3579 ≤ 22387846632171^3579*2000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070786039 2000000000 22387846632171 50000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (96544647/500000000 : ℝ)^4603 ≤ (12061574816109/100000000000000 : ℝ)^3579 := by
    have hnat : (96544647 : ℕ)^4603*100000000000000^3579 ≤ 12061574816109^3579*500000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96544647 500000000 12061574816109 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5203360441/10000000000 : ℝ)^4603 ≤ (21581365953507/50000000000000 : ℝ)^3579 := by
    have hnat : (5203360441 : ℕ)^4603*50000000000000^3579 ≤ 21581365953507^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5203360441 10000000000 21581365953507 50000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070786039/2000000000 : ℝ), (-96544647/500000000 : ℝ), (5203360441/10000000000 : ℝ)] ![(22387846632171/50000000000000 : ℝ), (12061574816109/100000000000000 : ℝ), (21581365953507/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070786039/2000000000 : ℝ)|^4603 ≤ (22387846632171/50000000000000 : ℝ)^3579
        have hw : |(1070786039/2000000000 : ℝ)|=(1070786039/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-96544647/500000000 : ℝ)|^4603 ≤ (12061574816109/100000000000000 : ℝ)^3579
        have hw : |(-96544647/500000000 : ℝ)|=(96544647/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5203360441/10000000000 : ℝ)|^4603 ≤ (21581365953507/50000000000000 : ℝ)^3579
        have hw : |(5203360441/10000000000 : ℝ)|=(5203360441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1553_s2_2 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353930789/10000000000 : ℝ)*x 0 + (650419967/1250000000 : ℝ)*x 1 + (-1930893081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353930789/10000000000 : ℝ)^4603 ≤ (22387849826689/50000000000000 : ℝ)^3579 := by
    have hnat : (5353930789 : ℕ)^4603*50000000000000^3579 ≤ 22387849826689^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353930789 10000000000 22387849826689 50000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (650419967/1250000000 : ℝ)^4603 ≤ (21581362192853/50000000000000 : ℝ)^3579 := by
    have hnat : (650419967 : ℕ)^4603*50000000000000^3579 ≤ 21581362192853^3579*1250000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      650419967 1250000000 21581362192853 50000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1930893081/10000000000 : ℝ)^4603 ≤ (6030787974443/50000000000000 : ℝ)^3579 := by
    have hnat : (1930893081 : ℕ)^4603*50000000000000^3579 ≤ 6030787974443^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1930893081 10000000000 6030787974443 50000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353930789/10000000000 : ℝ), (650419967/1250000000 : ℝ), (-1930893081/10000000000 : ℝ)] ![(22387849826689/50000000000000 : ℝ), (21581362192853/50000000000000 : ℝ), (6030787974443/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353930789/10000000000 : ℝ)|^4603 ≤ (22387849826689/50000000000000 : ℝ)^3579
        have hw : |(5353930789/10000000000 : ℝ)|=(5353930789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(650419967/1250000000 : ℝ)|^4603 ≤ (21581362192853/50000000000000 : ℝ)^3579
        have hw : |(650419967/1250000000 : ℝ)|=(650419967/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1930893081/10000000000 : ℝ)|^4603 ≤ (6030787974443/50000000000000 : ℝ)^3579
        have hw : |(-1930893081/10000000000 : ℝ)|=(1930893081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1553_s2_3 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2124621273/5000000000 : ℝ)*x 0 + (1987021067/5000000000 : ℝ)*x 1 + (567487079/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2124621273/5000000000 : ℝ)^4603 ≤ (4157923217751/12500000000000 : ℝ)^3579 := by
    have hnat : (2124621273 : ℕ)^4603*12500000000000^3579 ≤ 4157923217751^3579*5000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124621273 5000000000 4157923217751 12500000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1987021067/5000000000 : ℝ)^4603 ≤ (30518802596791/100000000000000 : ℝ)^3579 := by
    have hnat : (1987021067 : ℕ)^4603*100000000000000^3579 ≤ 30518802596791^3579*5000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1987021067 5000000000 30518802596791 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (567487079/1250000000 : ℝ)^4603 ≤ (36217811657037/100000000000000 : ℝ)^3579 := by
    have hnat : (567487079 : ℕ)^4603*100000000000000^3579 ≤ 36217811657037^3579*1250000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      567487079 1250000000 36217811657037 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2124621273/5000000000 : ℝ), (1987021067/5000000000 : ℝ), (567487079/1250000000 : ℝ)] ![(4157923217751/12500000000000 : ℝ), (30518802596791/100000000000000 : ℝ), (36217811657037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2124621273/5000000000 : ℝ)|^4603 ≤ (4157923217751/12500000000000 : ℝ)^3579
        have hw : |(2124621273/5000000000 : ℝ)|=(2124621273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1987021067/5000000000 : ℝ)|^4603 ≤ (30518802596791/100000000000000 : ℝ)^3579
        have hw : |(1987021067/5000000000 : ℝ)|=(1987021067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(567487079/1250000000 : ℝ)|^4603 ≤ (36217811657037/100000000000000 : ℝ)^3579
        have hw : |(567487079/1250000000 : ℝ)|=(567487079/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1553_s2_4 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-903182453/5000000000 : ℝ)*x 0 + (5204822949/10000000000 : ℝ)*x 1 + (5444402919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (903182453/5000000000 : ℝ)^4603 ≤ (2214101593977/20000000000000 : ℝ)^3579 := by
    have hnat : (903182453 : ℕ)^4603*20000000000000^3579 ≤ 2214101593977^3579*5000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903182453 5000000000 2214101593977 20000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5204822949/10000000000 : ℝ)^4603 ≤ (43178335334313/100000000000000 : ℝ)^3579 := by
    have hnat : (5204822949 : ℕ)^4603*100000000000000^3579 ≤ 43178335334313^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5204822949 10000000000 43178335334313 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5444402919/10000000000 : ℝ)^4603 ≤ (1830046267001/4000000000000 : ℝ)^3579 := by
    have hnat : (5444402919 : ℕ)^4603*4000000000000^3579 ≤ 1830046267001^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5444402919 10000000000 1830046267001 4000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-903182453/5000000000 : ℝ), (5204822949/10000000000 : ℝ), (5444402919/10000000000 : ℝ)] ![(2214101593977/20000000000000 : ℝ), (43178335334313/100000000000000 : ℝ), (1830046267001/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-903182453/5000000000 : ℝ)|^4603 ≤ (2214101593977/20000000000000 : ℝ)^3579
        have hw : |(-903182453/5000000000 : ℝ)|=(903182453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5204822949/10000000000 : ℝ)|^4603 ≤ (43178335334313/100000000000000 : ℝ)^3579
        have hw : |(5204822949/10000000000 : ℝ)|=(5204822949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5444402919/10000000000 : ℝ)|^4603 ≤ (1830046267001/4000000000000 : ℝ)^3579
        have hw : |(5444402919/10000000000 : ℝ)|=(5444402919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1553_s2_5 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289893503/10000000000 : ℝ)*x 0 + (-1689851411/10000000000 : ℝ)*x 1 + (2722201349/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289893503/10000000000 : ℝ)^4603 ≤ (11022024882223/25000000000000 : ℝ)^3579 := by
    have hnat : (5289893503 : ℕ)^4603*25000000000000^3579 ≤ 11022024882223^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289893503 10000000000 11022024882223 25000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1689851411/10000000000 : ℝ)^4603 ≤ (5080373089013/50000000000000 : ℝ)^3579 := by
    have hnat : (1689851411 : ℕ)^4603*50000000000000^3579 ≤ 5080373089013^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1689851411 10000000000 5080373089013 50000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2722201349/5000000000 : ℝ)^4603 ≤ (5718894285817/12500000000000 : ℝ)^3579 := by
    have hnat : (2722201349 : ℕ)^4603*12500000000000^3579 ≤ 5718894285817^3579*5000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2722201349 5000000000 5718894285817 12500000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289893503/10000000000 : ℝ), (-1689851411/10000000000 : ℝ), (2722201349/5000000000 : ℝ)] ![(11022024882223/25000000000000 : ℝ), (5080373089013/50000000000000 : ℝ), (5718894285817/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289893503/10000000000 : ℝ)|^4603 ≤ (11022024882223/25000000000000 : ℝ)^3579
        have hw : |(5289893503/10000000000 : ℝ)|=(5289893503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1689851411/10000000000 : ℝ)|^4603 ≤ (5080373089013/50000000000000 : ℝ)^3579
        have hw : |(-1689851411/10000000000 : ℝ)|=(1689851411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2722201349/5000000000 : ℝ)|^4603 ≤ (5718894285817/12500000000000 : ℝ)^3579
        have hw : |(2722201349/5000000000 : ℝ)|=(2722201349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1553_s2_6 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289892509/10000000000 : ℝ)*x 0 + (5444404867/10000000000 : ℝ)*x 1 + (-422462439/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289892509/10000000000 : ℝ)^4603 ≤ (2204404443711/5000000000000 : ℝ)^3579 := by
    have hnat : (5289892509 : ℕ)^4603*5000000000000^3579 ≤ 2204404443711^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289892509 10000000000 2204404443711 5000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5444404867/10000000000 : ℝ)^4603 ≤ (142972430401/312500000000 : ℝ)^3579 := by
    have hnat : (5444404867 : ℕ)^4603*312500000000^3579 ≤ 142972430401^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5444404867 10000000000 142972430401 312500000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (422462439/2500000000 : ℝ)^4603 ≤ (5080366689833/50000000000000 : ℝ)^3579 := by
    have hnat : (422462439 : ℕ)^4603*50000000000000^3579 ≤ 5080366689833^3579*2500000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422462439 2500000000 5080366689833 50000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289892509/10000000000 : ℝ), (5444404867/10000000000 : ℝ), (-422462439/2500000000 : ℝ)] ![(2204404443711/5000000000000 : ℝ), (142972430401/312500000000 : ℝ), (5080366689833/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289892509/10000000000 : ℝ)|^4603 ≤ (2204404443711/5000000000000 : ℝ)^3579
        have hw : |(5289892509/10000000000 : ℝ)|=(5289892509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5444404867/10000000000 : ℝ)|^4603 ≤ (142972430401/312500000000 : ℝ)^3579
        have hw : |(5444404867/10000000000 : ℝ)|=(5444404867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-422462439/2500000000 : ℝ)|^4603 ≤ (5080366689833/50000000000000 : ℝ)^3579
        have hw : |(-422462439/2500000000 : ℝ)|=(422462439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1553_s2_7 (p : ℝ) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4249342483/10000000000 : ℝ)*x 0 + (4536483743/10000000000 : ℝ)*x 1 + (3977484839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4249342483/10000000000 : ℝ)^4603 ≤ (1663219594513/5000000000000 : ℝ)^3579 := by
    have hnat : (4249342483 : ℕ)^4603*5000000000000^3579 ≤ 1663219594513^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249342483 10000000000 1663219594513 5000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4536483743/10000000000 : ℝ)^4603 ≤ (452284981559/1250000000000 : ℝ)^3579 := by
    have hnat : (4536483743 : ℕ)^4603*1250000000000^3579 ≤ 452284981559^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4536483743 10000000000 452284981559 1250000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3977484839/10000000000 : ℝ)^4603 ≤ (30552809565137/100000000000000 : ℝ)^3579 := by
    have hnat : (3977484839 : ℕ)^4603*100000000000000^3579 ≤ 30552809565137^3579*10000000000^4603 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3977484839 10000000000 30552809565137 100000000000000 4603 3579 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4603/1024 : ℝ)) 4603 3579 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4249342483/10000000000 : ℝ), (4536483743/10000000000 : ℝ), (3977484839/10000000000 : ℝ)] ![(1663219594513/5000000000000 : ℝ), (452284981559/1250000000000 : ℝ), (30552809565137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4249342483/10000000000 : ℝ)|^4603 ≤ (1663219594513/5000000000000 : ℝ)^3579
        have hw : |(4249342483/10000000000 : ℝ)|=(4249342483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4536483743/10000000000 : ℝ)|^4603 ≤ (452284981559/1250000000000 : ℝ)^3579
        have hw : |(4536483743/10000000000 : ℝ)|=(4536483743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3977484839/10000000000 : ℝ)|^4603 ≤ (30552809565137/100000000000000 : ℝ)^3579
        have hw : |(3977484839/10000000000 : ℝ)|=(3977484839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1553_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (166662453/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8957/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8873/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (67/625 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15859/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8957/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8873/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8957/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8873/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8957/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8873/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8957/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8873/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8957/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8873/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8957/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8873/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  have hpowlo : (8873/100000 : ℝ) ^ (4601/1024 : ℝ) ≤ (1877189391694571/100000000000000000000 : ℝ) := by
    have hpowers : (8873/100000 : ℝ)^4601 ≤ (1877189391694571/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8873 : ℕ)^4601*100000000000000000000^1024 ≤ 1877189391694571^1024*100000^4601 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8873 100000 1877189391694571 100000000000000000000 4601 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8873/100000 : ℝ)) (X := (1877189391694571/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4601 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8957/50000 : ℝ) ^ (4601/1024 : ℝ) ≤ (44103361630829079/100000000000000000000 : ℝ) := by
    have hpowers : (8957/50000 : ℝ)^4601 ≤ (44103361630829079/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8957 : ℕ)^4601*100000000000000000000^1024 ≤ 44103361630829079^1024*50000^4601 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8957 50000 44103361630829079 100000000000000000000 4601 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8957/50000 : ℝ)) (X := (44103361630829079/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4601 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001877189391694571/50000000000000000000 : ℝ) ≤ (10000083556352293/10000000000000000 : ℝ) ^ (4601/1024 : ℝ) := by
    have hpowers : (50001877189391694571/50000000000000000000 : ℝ)^1024 ≤ (10000083556352293/10000000000000000 : ℝ)^4601 := by
      have hnat : (50001877189391694571 : ℕ)^1024*10000000000000000^4601 ≤ 10000083556352293^4601*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001877189391694571 50000000000000000000 10000083556352293 10000000000000000 1024 4601 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000083556352293/10000000000000000 : ℝ)) (X := (50001877189391694571/50000000000000000000 : ℝ)) (by norm_num) 4601 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2000919611020450473/2000000000000000000 : ℝ) ≤ (10001023161724417/10000000000000000 : ℝ) ^ (4601/1024 : ℝ) := by
    have hpowers : (2000919611020450473/2000000000000000000 : ℝ)^1024 ≤ (10001023161724417/10000000000000000 : ℝ)^4601 := by
      have hnat : (2000919611020450473 : ℕ)^1024*10000000000000000^4601 ≤ 10001023161724417^4601*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000919611020450473 2000000000000000000 10001023161724417 10000000000000000 1024 4601 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001023161724417/10000000000000000 : ℝ)) (X := (2000919611020450473/2000000000000000000 : ℝ)) (by norm_num) 4601 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50044103361630829079/50000000000000000000 : ℝ) ≤ (10001962767096541/10000000000000000 : ℝ) ^ (4601/1024 : ℝ) := by
    have hpowers : (50044103361630829079/50000000000000000000 : ℝ)^1024 ≤ (10001962767096541/10000000000000000 : ℝ)^4601 := by
      have hnat : (50044103361630829079 : ℕ)^1024*10000000000000000^4601 ≤ 10001962767096541^4601*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50044103361630829079 50000000000000000000 10001962767096541 10000000000000000 1024 4601 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001962767096541/10000000000000000 : ℝ)) (X := (50044103361630829079/50000000000000000000 : ℝ)) (by norm_num) 4601 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1877189391694571/100000000000000000000 : ℝ) ≤ ((90394081196047368509/90410000000000000000 : ℝ)+2*(234901343031/226025000000000 : ℝ)*(8873/100000 : ℝ))^(4601/1024 : ℝ) := by
    rw [show (90394081196047368509/90410000000000000000 : ℝ)+2*(234901343031/226025000000000 : ℝ)*(8873/100000 : ℝ)=(10000083556352293/10000000000000000 : ℝ) by norm_num, show 1+2*(1877189391694571/100000000000000000000 : ℝ)=(50001877189391694571/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(44103361630829079/100000000000000000000 : ℝ)+(1877189391694571/100000000000000000000 : ℝ) ≤ ((90394081196047368509/90410000000000000000 : ℝ)+(234901343031/226025000000000 : ℝ)*((8957/50000 : ℝ)+(8873/100000 : ℝ)))^(4601/1024 : ℝ) := by
    rw [show (90394081196047368509/90410000000000000000 : ℝ)+(234901343031/226025000000000 : ℝ)*((8957/50000 : ℝ)+(8873/100000 : ℝ))=(10001023161724417/10000000000000000 : ℝ) by norm_num, show 1+(44103361630829079/100000000000000000000 : ℝ)+(1877189391694571/100000000000000000000 : ℝ)=(2000919611020450473/2000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(44103361630829079/100000000000000000000 : ℝ) ≤ ((90394081196047368509/90410000000000000000 : ℝ)+2*(234901343031/226025000000000 : ℝ)*(8957/50000 : ℝ))^(4601/1024 : ℝ) := by
    rw [show (90394081196047368509/90410000000000000000 : ℝ)+2*(234901343031/226025000000000 : ℝ)*(8957/50000 : ℝ)=(10001962767096541/10000000000000000 : ℝ) by norm_num, show 1+2*(44103361630829079/100000000000000000000 : ℝ)=(50044103361630829079/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (90394081196047368509/90410000000000000000 : ℝ)*(X 1 0+X 2 0)+(234901343031/226025000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4601/1024 : ℝ)) (lo := (8873/100000 : ℝ)) (hi := (8957/50000 : ℝ)) (c := (90394081196047368509/90410000000000000000 : ℝ)) (alpha := (234901343031/226025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (90394081196047368509/90410000000000000000 : ℝ)*(X 0 1+X 2 1)+(234901343031/226025000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4601/1024 : ℝ)) (lo := (8873/100000 : ℝ)) (hi := (8957/50000 : ℝ)) (c := (90394081196047368509/90410000000000000000 : ℝ)) (alpha := (234901343031/226025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (90394081196047368509/90410000000000000000 : ℝ)*(X 0 2+X 1 2)+(234901343031/226025000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4601/1024 : ℝ)) (lo := (8873/100000 : ℝ)) (hi := (8957/50000 : ℝ)) (c := (90394081196047368509/90410000000000000000 : ℝ)) (alpha := (234901343031/226025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-36126469/200000000 : ℝ)*X 0 0+(1089175371/2000000000 : ℝ)*X 0 1+(2601680211/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070786039/2000000000 : ℝ)*X 1 0+(-96544647/500000000 : ℝ)*X 1 1+(5203360441/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353930789/10000000000 : ℝ)*X 2 0+(650419967/1250000000 : ℝ)*X 2 1+(-1930893081/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2124621273/5000000000 : ℝ)*X 0 0+(1987021067/5000000000 : ℝ)*X 0 1+(567487079/1250000000 : ℝ)*X 0 2+(2124621273/5000000000 : ℝ)*X 1 0+(1987021067/5000000000 : ℝ)*X 1 1+(567487079/1250000000 : ℝ)*X 1 2+(2124621273/5000000000 : ℝ)*X 2 0+(1987021067/5000000000 : ℝ)*X 2 1+(567487079/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-903182453/5000000000 : ℝ)*X 0 0+(5204822949/10000000000 : ℝ)*X 0 1+(5444402919/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5289893503/10000000000 : ℝ)*X 1 0+(-1689851411/10000000000 : ℝ)*X 1 1+(2722201349/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5289892509/10000000000 : ℝ)*X 2 0+(5444404867/10000000000 : ℝ)*X 2 1+(-422462439/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4249342483/10000000000 : ℝ)*X 0 0+(4536483743/10000000000 : ℝ)*X 0 1+(3977484839/10000000000 : ℝ)*X 0 2+(4249342483/10000000000 : ℝ)*X 1 0+(4536483743/10000000000 : ℝ)*X 1 1+(3977484839/10000000000 : ℝ)*X 1 2+(4249342483/10000000000 : ℝ)*X 2 0+(4536483743/10000000000 : ℝ)*X 2 1+(3977484839/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1553_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2181397329734532634408691373/565062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1945941893/100000000000000 : ℝ)*(base19) + (983594533/50000000000000 : ℝ)*(base23) + (449536267/100000000000000 : ℝ)*(upper3) + (116779373/50000000000000 : ℝ)*(upper4) + (92944339/100000000000000 : ℝ)*(upper5) + (368171465388233/12500000000000 : ℝ)*(major0) + (368171465388233/12500000000000 : ℝ)*(major1) + (368171465388233/12500000000000 : ℝ)*(major2) + (4123455204855801/100000000000000 : ℝ)*(sp0) + (412347365766219/10000000000000 : ℝ)*(sp1) + (2061736818207509/50000000000000 : ℝ)*(sp2) + (1767250457783323/100000000000000 : ℝ)*(sp3) + (20398748283/100000000000000 : ℝ)*(sp4) + (17256142539/100000000000000 : ℝ)*(sp7) + (883633856962931/50000000000000 : ℝ)*(f.failure) + (1030868900901021/25000000000000 : ℝ)*(f.sum) + (25130331176501/45205000000000000000000000000 : ℝ)*base65 + (15352292592535070403/1130125000000000000000000000000000 : ℝ)*base68 + (11550295864944445403/1130125000000000000000000000000000 : ℝ)*base70 + (8630043020425570403/1130125000000000000000000000000000 : ℝ)*base72 + (266091907967541/45205000000000000000000000000 : ℝ)*base73 + (14867754850735820403/1130125000000000000000000000000000 : ℝ)*base76 + (13491119922454570403/1130125000000000000000000000000000 : ℝ)*base78 + (8046919158768320403/1130125000000000000000000000000000 : ℝ)*base80 + (377503801080841/45205000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (10529743/5000000000000000000000 : ℝ)*base89 + (10529743/5000000000000000000000 : ℝ)*base91 + (10529743/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17815561142048247033975021321/2260250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8471533/5000000000000 : ℝ)*(base8) + (171187323/50000000000000 : ℝ)*(base21) + (36202139/50000000000000 : ℝ)*(lower2) + (150398491/100000000000000 : ℝ)*(lower4) + (42164427/25000000000000 : ℝ)*(upper5) + (1490722115885377/50000000000000 : ℝ)*(major0) + (1490722115885377/50000000000000 : ℝ)*(major1) + (1490722115885377/50000000000000 : ℝ)*(major2) + (27426861827/100000000000000 : ℝ)*(sp2) + (117321369/25000000000000 : ℝ)*(sp3) + (521747033130473/12500000000000 : ℝ)*(sp4) + (1043494108618611/25000000000000 : ℝ)*(sp5) + (1043487166309493/25000000000000 : ℝ)*(sp6) + (447227824261063/25000000000000 : ℝ)*(sp7) + (13975873174451/781250000000 : ℝ)*(f.failure) + (1043494108618611/25000000000000 : ℝ)*(f.sum) + (28270221684161/11301250000000000000000000000 : ℝ)*base66 + (33207845127860192893/4520500000000000000000000000000000 : ℝ)*base67 + (16681648305399807107/4520500000000000000000000000000000 : ℝ)*base70 + (20737969445246192893/4520500000000000000000000000000000 : ℝ)*base71 + (468830763343/88291015625000000000000000 : ℝ)*base73 + (38227760312072192893/4520500000000000000000000000000000 : ℝ)*base75 + (14074273638406692893/4520500000000000000000000000000000 : ℝ)*base77 + (14095608853929807107/4520500000000000000000000000000000 : ℝ)*base80 + (131252900736091/45205000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (974197/78125000000000000000 : ℝ)*base90 + (974197/78125000000000000000 : ℝ)*base92 + (974197/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1553_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (166662453/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8957/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8873/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (67/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15859/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1553_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1553_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (166662453/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (67/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15859/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1553_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1553_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1553_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4601/1024 : ℝ) ≤ p) (hpb : p ≤ (4603/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (166662453/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (67/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15859/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1553_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
