-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1078_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:47:54.05496+00:00
-- url     : https://prove2.me/submissions/59230d87-cc8f-4768-a0d1-1e7666a3cde7

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
theorem support_rectangle_w1078_s0_0 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1912232979/10000000000 : ℝ)*x 0 + (758655109/1250000000 : ℝ)*x 1 + (4772325047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1912232979/10000000000 : ℝ)^8271 ≤ (11094165674903/100000000000000 : ℝ)^6223 := by
    have hnat : (1912232979 : ℕ)^8271*100000000000000^6223 ≤ 11094165674903^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1912232979 10000000000 11094165674903 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (758655109/1250000000 : ℝ)^8271 ≤ (25747408752331/50000000000000 : ℝ)^6223 := by
    have hnat : (758655109 : ℕ)^8271*50000000000000^6223 ≤ 25747408752331^6223*1250000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      758655109 1250000000 25747408752331 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4772325047/10000000000 : ℝ)^8271 ≤ (37411016796727/100000000000000 : ℝ)^6223 := by
    have hnat : (4772325047 : ℕ)^8271*100000000000000^6223 ≤ 37411016796727^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4772325047 10000000000 37411016796727 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1912232979/10000000000 : ℝ), (758655109/1250000000 : ℝ), (4772325047/10000000000 : ℝ)] ![(11094165674903/100000000000000 : ℝ), (25747408752331/50000000000000 : ℝ), (37411016796727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1912232979/10000000000 : ℝ)|^8271 ≤ (11094165674903/100000000000000 : ℝ)^6223
        have hw : |(-1912232979/10000000000 : ℝ)|=(1912232979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(758655109/1250000000 : ℝ)|^8271 ≤ (25747408752331/50000000000000 : ℝ)^6223
        have hw : |(758655109/1250000000 : ℝ)|=(758655109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4772325047/10000000000 : ℝ)|^8271 ≤ (37411016796727/100000000000000 : ℝ)^6223
        have hw : |(4772325047/10000000000 : ℝ)|=(4772325047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s0_1 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5520397721/10000000000 : ℝ)*x 0 + (-66459711/250000000 : ℝ)*x 1 + (95446501/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5520397721/10000000000 : ℝ)^8271 ≤ (45399636156281/100000000000000 : ℝ)^6223 := by
    have hnat : (5520397721 : ℕ)^8271*100000000000000^6223 ≤ 45399636156281^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5520397721 10000000000 45399636156281 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (66459711/250000000 : ℝ)^8271 ≤ (4297336751951/25000000000000 : ℝ)^6223 := by
    have hnat : (66459711 : ℕ)^8271*25000000000000^6223 ≤ 4297336751951^6223*250000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66459711 250000000 4297336751951 25000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (95446501/200000000 : ℝ)^8271 ≤ (2338188551749/6250000000000 : ℝ)^6223 := by
    have hnat : (95446501 : ℕ)^8271*6250000000000^6223 ≤ 2338188551749^6223*200000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95446501 200000000 2338188551749 6250000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5520397721/10000000000 : ℝ), (-66459711/250000000 : ℝ), (95446501/200000000 : ℝ)] ![(45399636156281/100000000000000 : ℝ), (4297336751951/25000000000000 : ℝ), (2338188551749/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5520397721/10000000000 : ℝ)|^8271 ≤ (45399636156281/100000000000000 : ℝ)^6223
        have hw : |(5520397721/10000000000 : ℝ)|=(5520397721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-66459711/250000000 : ℝ)|^8271 ≤ (4297336751951/25000000000000 : ℝ)^6223
        have hw : |(-66459711/250000000 : ℝ)|=(66459711/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(95446501/200000000 : ℝ)|^8271 ≤ (2338188551749/6250000000000 : ℝ)^6223
        have hw : |(95446501/200000000 : ℝ)|=(95446501/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s0_2 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5520397719/10000000000 : ℝ)*x 0 + (954465011/2000000000 : ℝ)*x 1 + (-531677687/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5520397719/10000000000 : ℝ)^8271 ≤ (2269981806721/5000000000000 : ℝ)^6223 := by
    have hnat : (5520397719 : ℕ)^8271*5000000000000^6223 ≤ 2269981806721^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5520397719 10000000000 2269981806721 5000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (954465011/2000000000 : ℝ)^8271 ≤ (467637711001/1250000000000 : ℝ)^6223 := by
    have hnat : (954465011 : ℕ)^8271*1250000000000^6223 ≤ 467637711001^6223*2000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      954465011 2000000000 467637711001 1250000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (531677687/2000000000 : ℝ)^8271 ≤ (17189346964833/100000000000000 : ℝ)^6223 := by
    have hnat : (531677687 : ℕ)^8271*100000000000000^6223 ≤ 17189346964833^6223*2000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531677687 2000000000 17189346964833 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5520397719/10000000000 : ℝ), (954465011/2000000000 : ℝ), (-531677687/2000000000 : ℝ)] ![(2269981806721/5000000000000 : ℝ), (467637711001/1250000000000 : ℝ), (17189346964833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5520397719/10000000000 : ℝ)|^8271 ≤ (2269981806721/5000000000000 : ℝ)^6223
        have hw : |(5520397719/10000000000 : ℝ)|=(5520397719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(954465011/2000000000 : ℝ)|^8271 ≤ (467637711001/1250000000000 : ℝ)^6223
        have hw : |(954465011/2000000000 : ℝ)|=(954465011/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-531677687/2000000000 : ℝ)|^8271 ≤ (17189346964833/100000000000000 : ℝ)^6223
        have hw : |(-531677687/2000000000 : ℝ)|=(531677687/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s0_3 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4206217867/10000000000 : ℝ)*x 0 + (3124232221/10000000000 : ℝ)*x 1 + (354503947/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4206217867/10000000000 : ℝ)^8271 ≤ (3953883871579/12500000000000 : ℝ)^6223 := by
    have hnat : (4206217867 : ℕ)^8271*12500000000000^6223 ≤ 3953883871579^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4206217867 10000000000 3953883871579 12500000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3124232221/10000000000 : ℝ)^8271 ≤ (33287600197/156250000000 : ℝ)^6223 := by
    have hnat : (3124232221 : ℕ)^8271*156250000000^6223 ≤ 33287600197^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3124232221 10000000000 33287600197 156250000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (354503947/625000000 : ℝ)^8271 ≤ (47064864880849/100000000000000 : ℝ)^6223 := by
    have hnat : (354503947 : ℕ)^8271*100000000000000^6223 ≤ 47064864880849^6223*625000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      354503947 625000000 47064864880849 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4206217867/10000000000 : ℝ), (3124232221/10000000000 : ℝ), (354503947/625000000 : ℝ)] ![(3953883871579/12500000000000 : ℝ), (33287600197/156250000000 : ℝ), (47064864880849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4206217867/10000000000 : ℝ)|^8271 ≤ (3953883871579/12500000000000 : ℝ)^6223
        have hw : |(4206217867/10000000000 : ℝ)|=(4206217867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3124232221/10000000000 : ℝ)|^8271 ≤ (33287600197/156250000000 : ℝ)^6223
        have hw : |(3124232221/10000000000 : ℝ)|=(3124232221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(354503947/625000000 : ℝ)|^8271 ≤ (47064864880849/100000000000000 : ℝ)^6223
        have hw : |(354503947/625000000 : ℝ)|=(354503947/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s0_4 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1917570031/10000000000 : ℝ)*x 0 + (2402903999/5000000000 : ℝ)*x 1 + (3017292751/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1917570031/10000000000 : ℝ)^8271 ≤ (1391917337563/12500000000000 : ℝ)^6223 := by
    have hnat : (1917570031 : ℕ)^8271*12500000000000^6223 ≤ 1391917337563^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1917570031 10000000000 1391917337563 12500000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2402903999/5000000000 : ℝ)^8271 ≤ (37760279139839/100000000000000 : ℝ)^6223 := by
    have hnat : (2402903999 : ℕ)^8271*100000000000000^6223 ≤ 37760279139839^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2402903999 5000000000 37760279139839 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3017292751/5000000000 : ℝ)^8271 ≤ (51104382149141/100000000000000 : ℝ)^6223 := by
    have hnat : (3017292751 : ℕ)^8271*100000000000000^6223 ≤ 51104382149141^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3017292751 5000000000 51104382149141 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1917570031/10000000000 : ℝ), (2402903999/5000000000 : ℝ), (3017292751/5000000000 : ℝ)] ![(1391917337563/12500000000000 : ℝ), (37760279139839/100000000000000 : ℝ), (51104382149141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1917570031/10000000000 : ℝ)|^8271 ≤ (1391917337563/12500000000000 : ℝ)^6223
        have hw : |(-1917570031/10000000000 : ℝ)|=(1917570031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2402903999/5000000000 : ℝ)|^8271 ≤ (37760279139839/100000000000000 : ℝ)^6223
        have hw : |(2402903999/5000000000 : ℝ)|=(2402903999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3017292751/5000000000 : ℝ)|^8271 ≤ (51104382149141/100000000000000 : ℝ)^6223
        have hw : |(3017292751/5000000000 : ℝ)|=(3017292751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s0_5 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4037757/7812500 : ℝ)*x 0 + (-698065701/5000000000 : ℝ)*x 1 + (6034583553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4037757/7812500 : ℝ)^8271 ≤ (41592324169171/100000000000000 : ℝ)^6223 := by
    have hnat : (4037757 : ℕ)^8271*100000000000000^6223 ≤ 41592324169171^6223*7812500^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4037757 7812500 41592324169171 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (698065701/5000000000 : ℝ)^8271 ≤ (7303315611481/100000000000000 : ℝ)^6223 := by
    have hnat : (698065701 : ℕ)^8271*100000000000000^6223 ≤ 7303315611481^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      698065701 5000000000 7303315611481 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6034583553/10000000000 : ℝ)^8271 ≤ (12776090052991/25000000000000 : ℝ)^6223 := by
    have hnat : (6034583553 : ℕ)^8271*25000000000000^6223 ≤ 12776090052991^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6034583553 10000000000 12776090052991 25000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4037757/7812500 : ℝ), (-698065701/5000000000 : ℝ), (6034583553/10000000000 : ℝ)] ![(41592324169171/100000000000000 : ℝ), (7303315611481/100000000000000 : ℝ), (12776090052991/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4037757/7812500 : ℝ)|^8271 ≤ (41592324169171/100000000000000 : ℝ)^6223
        have hw : |(4037757/7812500 : ℝ)|=(4037757/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-698065701/5000000000 : ℝ)|^8271 ≤ (7303315611481/100000000000000 : ℝ)^6223
        have hw : |(-698065701/5000000000 : ℝ)|=(698065701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6034583553/10000000000 : ℝ)|^8271 ≤ (12776090052991/25000000000000 : ℝ)^6223
        have hw : |(6034583553/10000000000 : ℝ)|=(6034583553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s0_6 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1033665773/2000000000 : ℝ)*x 0 + (6034585079/10000000000 : ℝ)*x 1 + (-349032269/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1033665773/2000000000 : ℝ)^8271 ≤ (10398080788263/25000000000000 : ℝ)^6223 := by
    have hnat : (1033665773 : ℕ)^8271*25000000000000^6223 ≤ 10398080788263^6223*2000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033665773 2000000000 10398080788263 25000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6034585079/10000000000 : ℝ)^8271 ≤ (51104377388019/100000000000000 : ℝ)^6223 := by
    have hnat : (6034585079 : ℕ)^8271*100000000000000^6223 ≤ 51104377388019^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6034585079 10000000000 51104377388019 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (349032269/2500000000 : ℝ)^8271 ≤ (7303299439561/100000000000000 : ℝ)^6223 := by
    have hnat : (349032269 : ℕ)^8271*100000000000000^6223 ≤ 7303299439561^6223*2500000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      349032269 2500000000 7303299439561 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1033665773/2000000000 : ℝ), (6034585079/10000000000 : ℝ), (-349032269/2500000000 : ℝ)] ![(10398080788263/25000000000000 : ℝ), (51104377388019/100000000000000 : ℝ), (7303299439561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1033665773/2000000000 : ℝ)|^8271 ≤ (10398080788263/25000000000000 : ℝ)^6223
        have hw : |(1033665773/2000000000 : ℝ)|=(1033665773/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6034585079/10000000000 : ℝ)|^8271 ≤ (51104377388019/100000000000000 : ℝ)^6223
        have hw : |(6034585079/10000000000 : ℝ)|=(6034585079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-349032269/2500000000 : ℝ)|^8271 ≤ (7303299439561/100000000000000 : ℝ)^6223
        have hw : |(-349032269/2500000000 : ℝ)|=(349032269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s0_7 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4216700827/10000000000 : ℝ)*x 0 + (2803141193/5000000000 : ℝ)*x 1 + (1596157919/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4216700827/10000000000 : ℝ)^8271 ≤ (3966986314121/12500000000000 : ℝ)^6223 := by
    have hnat : (4216700827 : ℕ)^8271*12500000000000^6223 ≤ 3966986314121^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4216700827 10000000000 3966986314121 12500000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2803141193/5000000000 : ℝ)^8271 ≤ (46340793865271/100000000000000 : ℝ)^6223 := by
    have hnat : (2803141193 : ℕ)^8271*100000000000000^6223 ≤ 46340793865271^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2803141193 5000000000 46340793865271 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1596157919/5000000000 : ℝ)^8271 ≤ (1096165780399/5000000000000 : ℝ)^6223 := by
    have hnat : (1596157919 : ℕ)^8271*5000000000000^6223 ≤ 1096165780399^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1596157919 5000000000 1096165780399 5000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4216700827/10000000000 : ℝ), (2803141193/5000000000 : ℝ), (1596157919/5000000000 : ℝ)] ![(3966986314121/12500000000000 : ℝ), (46340793865271/100000000000000 : ℝ), (1096165780399/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4216700827/10000000000 : ℝ)|^8271 ≤ (3966986314121/12500000000000 : ℝ)^6223
        have hw : |(4216700827/10000000000 : ℝ)|=(4216700827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2803141193/5000000000 : ℝ)|^8271 ≤ (46340793865271/100000000000000 : ℝ)^6223
        have hw : |(2803141193/5000000000 : ℝ)|=(2803141193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1596157919/5000000000 : ℝ)|^8271 ≤ (1096165780399/5000000000000 : ℝ)^6223
        have hw : |(1596157919/5000000000 : ℝ)|=(1596157919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1078_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29645307/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (147/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14031/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4135/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4135 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4135*1^1024 ≤ 0^1024*1^4135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4135 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4135/1024 : ℝ) ≤ (1236101266352832839/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4135 ≤ (1236101266352832839/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4135*50000000000000000000^1024 ≤ 1236101266352832839^1024*5^4135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1236101266352832839 50000000000000000000 4135 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1236101266352832839/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4135/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4135 := by
      have hnat : (1 : ℕ)^1024*1^4135 ≤ 1^4135*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (51236101266352832839/50000000000000000000 : ℝ) ≤ (5030330431084619/5000000000000000 : ℝ) ^ (4135/1024 : ℝ) := by
    have hpowers : (51236101266352832839/50000000000000000000 : ℝ)^1024 ≤ (5030330431084619/5000000000000000 : ℝ)^4135 := by
      have hnat : (51236101266352832839 : ℕ)^1024*5000000000000000^4135 ≤ 5030330431084619^4135*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51236101266352832839 50000000000000000000 5030330431084619 5000000000000000 1024 4135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5030330431084619/5000000000000000 : ℝ)) (X := (51236101266352832839/50000000000000000000 : ℝ)) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (26236101266352832839/25000000000000000000 : ℝ) ≤ (2530330431084619/2500000000000000 : ℝ) ^ (4135/1024 : ℝ) := by
    have hpowers : (26236101266352832839/25000000000000000000 : ℝ)^1024 ≤ (2530330431084619/2500000000000000 : ℝ)^4135 := by
      have hnat : (26236101266352832839 : ℕ)^1024*2500000000000000^4135 ≤ 2530330431084619^4135*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26236101266352832839 25000000000000000000 2530330431084619 2500000000000000 1024 4135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2530330431084619/2500000000000000 : ℝ)) (X := (26236101266352832839/25000000000000000000 : ℝ)) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(30330431084619/2000000000000000 : ℝ)*(0 : ℝ))^(4135/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(30330431084619/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1236101266352832839/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(30330431084619/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4135/1024 : ℝ) := by
    rw [show (1 : ℝ)+(30330431084619/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5030330431084619/5000000000000000 : ℝ) by norm_num, show 1+(1236101266352832839/50000000000000000000 : ℝ)+(0 : ℝ)=(51236101266352832839/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1236101266352832839/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(30330431084619/2000000000000000 : ℝ)*(2/5 : ℝ))^(4135/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(30330431084619/2000000000000000 : ℝ)*(2/5 : ℝ)=(2530330431084619/2500000000000000 : ℝ) by norm_num, show 1+2*(1236101266352832839/50000000000000000000 : ℝ)=(26236101266352832839/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(30330431084619/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4135/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30330431084619/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(30330431084619/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4135/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30330431084619/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(30330431084619/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4135/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30330431084619/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1912232979/10000000000 : ℝ)*X 0 0+(758655109/1250000000 : ℝ)*X 0 1+(4772325047/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5520397721/10000000000 : ℝ)*X 1 0+(-66459711/250000000 : ℝ)*X 1 1+(95446501/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5520397719/10000000000 : ℝ)*X 2 0+(954465011/2000000000 : ℝ)*X 2 1+(-531677687/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4206217867/10000000000 : ℝ)*X 0 0+(3124232221/10000000000 : ℝ)*X 0 1+(354503947/625000000 : ℝ)*X 0 2+(4206217867/10000000000 : ℝ)*X 1 0+(3124232221/10000000000 : ℝ)*X 1 1+(354503947/625000000 : ℝ)*X 1 2+(4206217867/10000000000 : ℝ)*X 2 0+(3124232221/10000000000 : ℝ)*X 2 1+(354503947/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1917570031/10000000000 : ℝ)*X 0 0+(2402903999/5000000000 : ℝ)*X 0 1+(3017292751/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4037757/7812500 : ℝ)*X 1 0+(-698065701/5000000000 : ℝ)*X 1 1+(6034583553/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1033665773/2000000000 : ℝ)*X 2 0+(6034585079/10000000000 : ℝ)*X 2 1+(-349032269/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4216700827/10000000000 : ℝ)*X 0 0+(2803141193/5000000000 : ℝ)*X 0 1+(1596157919/5000000000 : ℝ)*X 0 2+(4216700827/10000000000 : ℝ)*X 1 0+(2803141193/5000000000 : ℝ)*X 1 1+(1596157919/5000000000 : ℝ)*X 1 2+(4216700827/10000000000 : ℝ)*X 2 0+(2803141193/5000000000 : ℝ)*X 2 1+(1596157919/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (516388278197950535535411/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (55450707/100000000000000 : ℝ)*(base1) + (323495721/25000000000000 : ℝ)*(base19) + (602810397/50000000000000 : ℝ)*(base23) + (44041369/50000000000000 : ℝ)*(base24) + (292691181/100000000000000 : ℝ)*(upper3) + (581780833076877/100000000000000 : ℝ)*(major0) + (581780833076877/100000000000000 : ℝ)*(major1) + (581780833076877/100000000000000 : ℝ)*(major2) + (192766081972781/25000000000000 : ℝ)*(sp0) + (385532905455699/50000000000000 : ℝ)*(sp1) + (3084263244763/400000000000 : ℝ)*(sp2) + (24530754112127/6250000000000 : ℝ)*(sp3) + (566490773/20000000000000 : ℝ)*(sp4) + (1133942651/50000000000000 : ℝ)*(sp7) + (196247194565021/50000000000000 : ℝ)*(f.failure) + (385533552447141/50000000000000 : ℝ)*(f.sum) + (160196490554863/100000000000000000000000000000 : ℝ)*base65 + (57067489145137/200000000000000000000000000000 : ℝ)*base68 + (1039695880345137/200000000000000000000000000000 : ℝ)*base70 + (327549571945137/200000000000000000000000000000 : ℝ)*base72 + (199122466854863/100000000000000000000000000000 : ℝ)*base73 + (527470248745137/200000000000000000000000000000 : ℝ)*base76 + (831904630345137/200000000000000000000000000000 : ℝ)*base78 + (367050740454863/200000000000000000000000000000 : ℝ)*base79 + (98683550254863/100000000000000000000000000000 : ℝ)*base81 + (9006447/1000000000000000000000 : ℝ)*base89 + (9006447/1000000000000000000000 : ℝ)*base91 + (9006447/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (67933661817505898528907/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (199995353/50000000000000 : ℝ)*(base19) + (140368699/25000000000000 : ℝ)*(base23) + (6854229/4000000000000 : ℝ)*(base39) + (48941/2500000000000 : ℝ)*(upper2) + (10694093/50000000000000 : ℝ)*(upper4) + (14223841/6250000000000 : ℝ)*(upper5) + (307018217449651/50000000000000 : ℝ)*(major0) + (307018217449651/50000000000000 : ℝ)*(major1) + (614036263543577/100000000000000 : ℝ)*(major2) + (700387609/100000000000000 : ℝ)*(sp2) + (101727150187939/12500000000000 : ℝ)*(sp4) + (406908400756403/50000000000000 : ℝ)*(sp5) + (25431753468651/3125000000000 : ℝ)*(sp6) + (8285108127223/2000000000000 : ℝ)*(sp7) + (8285108127223/2000000000000 : ℝ)*(f.failure) + (813817372859237/100000000000000 : ℝ)*(f.sum) + (70024048621899/200000000000000000000000000000 : ℝ)*base66 + (773397905742163/200000000000000000000000000000 : ℝ)*base67 + (110845719382031/100000000000000000000000000000 : ℝ)*base70 + (452990081057837/200000000000000000000000000000 : ℝ)*base72 + (225026409378101/200000000000000000000000000000 : ℝ)*base73 + (40234611217969/100000000000000000000000000000 : ℝ)*base75 + (5257107082031/100000000000000000000000000000 : ℝ)*base78 + (34369759282031/100000000000000000000000000000 : ℝ)*base80 + (30373274632031/50000000000000000000000000000 : ℝ)*base82 + (92461/40000000000000000000 : ℝ)*base89 + (92461/40000000000000000000 : ℝ)*base91 + (92461/40000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1078_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29645307/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (147/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14031/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1078_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1078_s1_0 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2121510257/10000000000 : ℝ)*x 0 + (5718958801/10000000000 : ℝ)*x 1 + (4988593137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2121510257/10000000000 : ℝ)^8271 ≤ (12736288622291/100000000000000 : ℝ)^6223 := by
    have hnat : (2121510257 : ℕ)^8271*100000000000000^6223 ≤ 12736288622291^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121510257 10000000000 12736288622291 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5718958801/10000000000 : ℝ)^8271 ≤ (47582752929037/100000000000000 : ℝ)^6223 := by
    have hnat : (5718958801 : ℕ)^8271*100000000000000^6223 ≤ 47582752929037^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5718958801 10000000000 47582752929037 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4988593137/10000000000 : ℝ)^8271 ≤ (7936191686839/20000000000000 : ℝ)^6223 := by
    have hnat : (4988593137 : ℕ)^8271*20000000000000^6223 ≤ 7936191686839^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4988593137 10000000000 7936191686839 20000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2121510257/10000000000 : ℝ), (5718958801/10000000000 : ℝ), (4988593137/10000000000 : ℝ)] ![(12736288622291/100000000000000 : ℝ), (47582752929037/100000000000000 : ℝ), (7936191686839/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2121510257/10000000000 : ℝ)|^8271 ≤ (12736288622291/100000000000000 : ℝ)^6223
        have hw : |(-2121510257/10000000000 : ℝ)|=(2121510257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5718958801/10000000000 : ℝ)|^8271 ≤ (47582752929037/100000000000000 : ℝ)^6223
        have hw : |(5718958801/10000000000 : ℝ)|=(5718958801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4988593137/10000000000 : ℝ)|^8271 ≤ (7936191686839/20000000000000 : ℝ)^6223
        have hw : |(4988593137/10000000000 : ℝ)|=(4988593137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s1_1 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (108452933/200000000 : ℝ)*x 0 + (-2516968901/10000000000 : ℝ)*x 1 + (4988593423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108452933/200000000 : ℝ)^8271 ≤ (44334293256853/100000000000000 : ℝ)^6223 := by
    have hnat : (108452933 : ℕ)^8271*100000000000000^6223 ≤ 44334293256853^6223*200000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108452933 200000000 44334293256853 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2516968901/10000000000 : ℝ)^8271 ≤ (1998093158153/12500000000000 : ℝ)^6223 := by
    have hnat : (2516968901 : ℕ)^8271*12500000000000^6223 ≤ 1998093158153^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2516968901 10000000000 1998093158153 12500000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4988593423/10000000000 : ℝ)^8271 ≤ (39680961457823/100000000000000 : ℝ)^6223 := by
    have hnat : (4988593423 : ℕ)^8271*100000000000000^6223 ≤ 39680961457823^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4988593423 10000000000 39680961457823 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(108452933/200000000 : ℝ), (-2516968901/10000000000 : ℝ), (4988593423/10000000000 : ℝ)] ![(44334293256853/100000000000000 : ℝ), (1998093158153/12500000000000 : ℝ), (39680961457823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(108452933/200000000 : ℝ)|^8271 ≤ (44334293256853/100000000000000 : ℝ)^6223
        have hw : |(108452933/200000000 : ℝ)|=(108452933/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2516968901/10000000000 : ℝ)|^8271 ≤ (1998093158153/12500000000000 : ℝ)^6223
        have hw : |(-2516968901/10000000000 : ℝ)|=(2516968901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4988593423/10000000000 : ℝ)|^8271 ≤ (39680961457823/100000000000000 : ℝ)^6223
        have hw : |(4988593423/10000000000 : ℝ)|=(4988593423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s1_2 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5422647367/10000000000 : ℝ)*x 0 + (99771853/200000000 : ℝ)*x 1 + (-1258484473/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5422647367/10000000000 : ℝ)^8271 ≤ (554178763101/1250000000000 : ℝ)^6223 := by
    have hnat : (5422647367 : ℕ)^8271*1250000000000^6223 ≤ 554178763101^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422647367 10000000000 554178763101 1250000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (99771853/200000000 : ℝ)^8271 ≤ (3968095328557/10000000000000 : ℝ)^6223 := by
    have hnat : (99771853 : ℕ)^8271*10000000000000^6223 ≤ 3968095328557^6223*200000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99771853 200000000 3968095328557 10000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1258484473/5000000000 : ℝ)^8271 ≤ (7992372822531/50000000000000 : ℝ)^6223 := by
    have hnat : (1258484473 : ℕ)^8271*50000000000000^6223 ≤ 7992372822531^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1258484473 5000000000 7992372822531 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5422647367/10000000000 : ℝ), (99771853/200000000 : ℝ), (-1258484473/5000000000 : ℝ)] ![(554178763101/1250000000000 : ℝ), (3968095328557/10000000000000 : ℝ), (7992372822531/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5422647367/10000000000 : ℝ)|^8271 ≤ (554178763101/1250000000000 : ℝ)^6223
        have hw : |(5422647367/10000000000 : ℝ)|=(5422647367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(99771853/200000000 : ℝ)|^8271 ≤ (3968095328557/10000000000000 : ℝ)^6223
        have hw : |(99771853/200000000 : ℝ)|=(99771853/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1258484473/5000000000 : ℝ)|^8271 ≤ (7992372822531/50000000000000 : ℝ)^6223
        have hw : |(-1258484473/5000000000 : ℝ)|=(1258484473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s1_3 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4322809647/10000000000 : ℝ)*x 0 + (916218661/2500000000 : ℝ)*x 1 + (5099698979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4322809647/10000000000 : ℝ)^8271 ≤ (4100210242437/12500000000000 : ℝ)^6223 := by
    have hnat : (4322809647 : ℕ)^8271*12500000000000^6223 ≤ 4100210242437^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4322809647 10000000000 4100210242437 12500000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (916218661/2500000000 : ℝ)^8271 ≤ (3292306394889/12500000000000 : ℝ)^6223 := by
    have hnat : (916218661 : ℕ)^8271*12500000000000^6223 ≤ 3292306394889^6223*2500000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      916218661 2500000000 3292306394889 12500000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5099698979/10000000000 : ℝ)^8271 ≤ (40859866888063/100000000000000 : ℝ)^6223 := by
    have hnat : (5099698979 : ℕ)^8271*100000000000000^6223 ≤ 40859866888063^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5099698979 10000000000 40859866888063 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4322809647/10000000000 : ℝ), (916218661/2500000000 : ℝ), (5099698979/10000000000 : ℝ)] ![(4100210242437/12500000000000 : ℝ), (3292306394889/12500000000000 : ℝ), (40859866888063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4322809647/10000000000 : ℝ)|^8271 ≤ (4100210242437/12500000000000 : ℝ)^6223
        have hw : |(4322809647/10000000000 : ℝ)|=(4322809647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(916218661/2500000000 : ℝ)|^8271 ≤ (3292306394889/12500000000000 : ℝ)^6223
        have hw : |(916218661/2500000000 : ℝ)|=(916218661/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5099698979/10000000000 : ℝ)|^8271 ≤ (40859866888063/100000000000000 : ℝ)^6223
        have hw : |(5099698979/10000000000 : ℝ)|=(5099698979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s1_4 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-106120689/500000000 : ℝ)*x 0 + (4998810793/10000000000 : ℝ)*x 1 + (356783251/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106120689/500000000 : ℝ)^8271 ≤ (398234326943/3125000000000 : ℝ)^6223 := by
    have hnat : (106120689 : ℕ)^8271*3125000000000^6223 ≤ 398234326943^6223*500000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106120689 500000000 398234326943 3125000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4998810793/10000000000 : ℝ)^8271 ≤ (7957803432173/20000000000000 : ℝ)^6223 := by
    have hnat : (4998810793 : ℕ)^8271*20000000000000^6223 ≤ 7957803432173^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4998810793 10000000000 7957803432173 20000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (356783251/625000000 : ℝ)^8271 ≤ (11866871092081/25000000000000 : ℝ)^6223 := by
    have hnat : (356783251 : ℕ)^8271*25000000000000^6223 ≤ 11866871092081^6223*625000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      356783251 625000000 11866871092081 25000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-106120689/500000000 : ℝ), (4998810793/10000000000 : ℝ), (356783251/625000000 : ℝ)] ![(398234326943/3125000000000 : ℝ), (7957803432173/20000000000000 : ℝ), (11866871092081/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-106120689/500000000 : ℝ)|^8271 ≤ (398234326943/3125000000000 : ℝ)^6223
        have hw : |(-106120689/500000000 : ℝ)|=(106120689/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4998810793/10000000000 : ℝ)|^8271 ≤ (7957803432173/20000000000000 : ℝ)^6223
        have hw : |(4998810793/10000000000 : ℝ)|=(4998810793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(356783251/625000000 : ℝ)|^8271 ≤ (11866871092081/25000000000000 : ℝ)^6223
        have hw : |(356783251/625000000 : ℝ)|=(356783251/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s1_5 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (209440227/400000000 : ℝ)*x 0 + (-449256929/2500000000 : ℝ)*x 1 + (713566759/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (209440227/400000000 : ℝ)^8271 ≤ (10579437319773/25000000000000 : ℝ)^6223 := by
    have hnat : (209440227 : ℕ)^8271*25000000000000^6223 ≤ 10579437319773^6223*400000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209440227 400000000 10579437319773 25000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (449256929/2500000000 : ℝ)^8271 ≤ (2553685902009/25000000000000 : ℝ)^6223 := by
    have hnat : (449256929 : ℕ)^8271*25000000000000^6223 ≤ 2553685902009^6223*2500000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449256929 2500000000 2553685902009 25000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (713566759/1250000000 : ℝ)^8271 ≤ (11866876772667/25000000000000 : ℝ)^6223 := by
    have hnat : (713566759 : ℕ)^8271*25000000000000^6223 ≤ 11866876772667^6223*1250000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      713566759 1250000000 11866876772667 25000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(209440227/400000000 : ℝ), (-449256929/2500000000 : ℝ), (713566759/1250000000 : ℝ)] ![(10579437319773/25000000000000 : ℝ), (2553685902009/25000000000000 : ℝ), (11866876772667/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(209440227/400000000 : ℝ)|^8271 ≤ (10579437319773/25000000000000 : ℝ)^6223
        have hw : |(209440227/400000000 : ℝ)|=(209440227/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-449256929/2500000000 : ℝ)|^8271 ≤ (2553685902009/25000000000000 : ℝ)^6223
        have hw : |(-449256929/2500000000 : ℝ)|=(449256929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(713566759/1250000000 : ℝ)|^8271 ≤ (11866876772667/25000000000000 : ℝ)^6223
        have hw : |(713566759/1250000000 : ℝ)|=(713566759/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s1_6 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5236003597/10000000000 : ℝ)*x 0 + (1141707277/2000000000 : ℝ)*x 1 + (-224628411/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5236003597/10000000000 : ℝ)^8271 ≤ (42317726957447/100000000000000 : ℝ)^6223 := by
    have hnat : (5236003597 : ℕ)^8271*100000000000000^6223 ≤ 42317726957447^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236003597 10000000000 42317726957447 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1141707277/2000000000 : ℝ)^8271 ≤ (47467532653309/100000000000000 : ℝ)^6223 := by
    have hnat : (1141707277 : ℕ)^8271*100000000000000^6223 ≤ 47467532653309^6223*2000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1141707277 2000000000 47467532653309 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (224628411/1250000000 : ℝ)^8271 ≤ (10214740374523/100000000000000 : ℝ)^6223 := by
    have hnat : (224628411 : ℕ)^8271*100000000000000^6223 ≤ 10214740374523^6223*1250000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224628411 1250000000 10214740374523 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5236003597/10000000000 : ℝ), (1141707277/2000000000 : ℝ), (-224628411/1250000000 : ℝ)] ![(42317726957447/100000000000000 : ℝ), (47467532653309/100000000000000 : ℝ), (10214740374523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5236003597/10000000000 : ℝ)|^8271 ≤ (42317726957447/100000000000000 : ℝ)^6223
        have hw : |(5236003597/10000000000 : ℝ)|=(5236003597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1141707277/2000000000 : ℝ)|^8271 ≤ (47467532653309/100000000000000 : ℝ)^6223
        have hw : |(1141707277/2000000000 : ℝ)|=(1141707277/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-224628411/1250000000 : ℝ)|^8271 ≤ (10214740374523/100000000000000 : ℝ)^6223
        have hw : |(-224628411/1250000000 : ℝ)|=(224628411/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s1_7 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (540572503/1250000000 : ℝ)*x 0 + (5079622697/10000000000 : ℝ)*x 1 + (3685354253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540572503/1250000000 : ℝ)^8271 ≤ (16409768950553/50000000000000 : ℝ)^6223 := by
    have hnat : (540572503 : ℕ)^8271*50000000000000^6223 ≤ 16409768950553^6223*1250000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540572503 1250000000 16409768950553 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5079622697/10000000000 : ℝ)^8271 ≤ (20323106146177/50000000000000 : ℝ)^6223 := by
    have hnat : (5079622697 : ℕ)^8271*50000000000000^6223 ≤ 20323106146177^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5079622697 10000000000 20323106146177 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3685354253/10000000000 : ℝ)^8271 ≤ (26534249790487/100000000000000 : ℝ)^6223 := by
    have hnat : (3685354253 : ℕ)^8271*100000000000000^6223 ≤ 26534249790487^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3685354253 10000000000 26534249790487 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540572503/1250000000 : ℝ), (5079622697/10000000000 : ℝ), (3685354253/10000000000 : ℝ)] ![(16409768950553/50000000000000 : ℝ), (20323106146177/50000000000000 : ℝ), (26534249790487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540572503/1250000000 : ℝ)|^8271 ≤ (16409768950553/50000000000000 : ℝ)^6223
        have hw : |(540572503/1250000000 : ℝ)|=(540572503/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5079622697/10000000000 : ℝ)|^8271 ≤ (20323106146177/50000000000000 : ℝ)^6223
        have hw : |(5079622697/10000000000 : ℝ)|=(5079622697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3685354253/10000000000 : ℝ)|^8271 ≤ (26534249790487/100000000000000 : ℝ)^6223
        have hw : |(3685354253/10000000000 : ℝ)|=(3685354253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1078_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29645307/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14031/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (147/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1321/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10367/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14031/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (147/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14031/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (147/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14031/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (147/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14031/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (147/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14031/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (147/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14031/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (147/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (147/100000 : ℝ) ^ (4135/1024 : ℝ) ≤ (9105923/2500000000000000000 : ℝ) := by
    have hpowers : (147/100000 : ℝ)^4135 ≤ (9105923/2500000000000000000 : ℝ)^1024 := by
      have hnat : (147 : ℕ)^4135*2500000000000000000^1024 ≤ 9105923^1024*100000^4135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        147 100000 9105923 2500000000000000000 4135 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (147/100000 : ℝ)) (X := (9105923/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14031/50000 : ℝ) ^ (4135/1024 : ℝ) ≤ (59082050761193001/10000000000000000000 : ℝ) := by
    have hpowers : (14031/50000 : ℝ)^4135 ≤ (59082050761193001/10000000000000000000 : ℝ)^1024 := by
      have hnat : (14031 : ℕ)^4135*10000000000000000000^1024 ≤ 59082050761193001^1024*50000^4135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14031 50000 59082050761193001 10000000000000000000 4135 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14031/50000 : ℝ)) (X := (59082050761193001/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250000000009105923/1250000000000000000 : ℝ) ≤ (10000000000018041/10000000000000000 : ℝ) ^ (4135/1024 : ℝ) := by
    have hpowers : (1250000000009105923/1250000000000000000 : ℝ)^1024 ≤ (10000000000018041/10000000000000000 : ℝ)^4135 := by
      have hnat : (1250000000009105923 : ℕ)^1024*10000000000000000^4135 ≤ 10000000000018041^4135*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250000000009105923 1250000000000000000 10000000000018041 10000000000000000 1024 4135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000018041/10000000000000000 : ℝ)) (X := (1250000000009105923/1250000000000000000 : ℝ)) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10059082050797616693/10000000000000000000 : ℝ) ≤ (1001459879524161/1000000000000000 : ℝ) ^ (4135/1024 : ℝ) := by
    have hpowers : (10059082050797616693/10000000000000000000 : ℝ)^1024 ≤ (1001459879524161/1000000000000000 : ℝ)^4135 := by
      have hnat : (10059082050797616693 : ℕ)^1024*1000000000000000^4135 ≤ 1001459879524161^4135*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10059082050797616693 10000000000000000000 1001459879524161 1000000000000000 1024 4135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1001459879524161/1000000000000000 : ℝ)) (X := (10059082050797616693/10000000000000000000 : ℝ)) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5059082050761193001/5000000000000000000 : ℝ) ≤ (10029197590465179/10000000000000000 : ℝ) ^ (4135/1024 : ℝ) := by
    have hpowers : (5059082050761193001/5000000000000000000 : ℝ)^1024 ≤ (10029197590465179/10000000000000000 : ℝ)^4135 := by
      have hnat : (5059082050761193001 : ℕ)^1024*10000000000000000^4135 ≤ 10029197590465179^4135*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5059082050761193001 5000000000000000000 10029197590465179 10000000000000000 1024 4135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10029197590465179/10000000000000000 : ℝ)) (X := (5059082050761193001/5000000000000000000 : ℝ)) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9105923/2500000000000000000 : ℝ) ≤ ((93048569318235961743/93050000000000000000 : ℝ)+2*(4866265074523/930500000000000 : ℝ)*(147/100000 : ℝ))^(4135/1024 : ℝ) := by
    rw [show (93048569318235961743/93050000000000000000 : ℝ)+2*(4866265074523/930500000000000 : ℝ)*(147/100000 : ℝ)=(10000000000018041/10000000000000000 : ℝ) by norm_num, show 1+2*(9105923/2500000000000000000 : ℝ)=(1250000000009105923/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(59082050761193001/10000000000000000000 : ℝ)+(9105923/2500000000000000000 : ℝ) ≤ ((93048569318235961743/93050000000000000000 : ℝ)+(4866265074523/930500000000000 : ℝ)*((14031/50000 : ℝ)+(147/100000 : ℝ)))^(4135/1024 : ℝ) := by
    rw [show (93048569318235961743/93050000000000000000 : ℝ)+(4866265074523/930500000000000 : ℝ)*((14031/50000 : ℝ)+(147/100000 : ℝ))=(1001459879524161/1000000000000000 : ℝ) by norm_num, show 1+(59082050761193001/10000000000000000000 : ℝ)+(9105923/2500000000000000000 : ℝ)=(10059082050797616693/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(59082050761193001/10000000000000000000 : ℝ) ≤ ((93048569318235961743/93050000000000000000 : ℝ)+2*(4866265074523/930500000000000 : ℝ)*(14031/50000 : ℝ))^(4135/1024 : ℝ) := by
    rw [show (93048569318235961743/93050000000000000000 : ℝ)+2*(4866265074523/930500000000000 : ℝ)*(14031/50000 : ℝ)=(10029197590465179/10000000000000000 : ℝ) by norm_num, show 1+2*(59082050761193001/10000000000000000000 : ℝ)=(5059082050761193001/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (93048569318235961743/93050000000000000000 : ℝ)*(X 1 0+X 2 0)+(4866265074523/930500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4135/1024 : ℝ)) (lo := (147/100000 : ℝ)) (hi := (14031/50000 : ℝ)) (c := (93048569318235961743/93050000000000000000 : ℝ)) (alpha := (4866265074523/930500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (93048569318235961743/93050000000000000000 : ℝ)*(X 0 1+X 2 1)+(4866265074523/930500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4135/1024 : ℝ)) (lo := (147/100000 : ℝ)) (hi := (14031/50000 : ℝ)) (c := (93048569318235961743/93050000000000000000 : ℝ)) (alpha := (4866265074523/930500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (93048569318235961743/93050000000000000000 : ℝ)*(X 0 2+X 1 2)+(4866265074523/930500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4135/1024 : ℝ)) (lo := (147/100000 : ℝ)) (hi := (14031/50000 : ℝ)) (c := (93048569318235961743/93050000000000000000 : ℝ)) (alpha := (4866265074523/930500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2121510257/10000000000 : ℝ)*X 0 0+(5718958801/10000000000 : ℝ)*X 0 1+(4988593137/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((108452933/200000000 : ℝ)*X 1 0+(-2516968901/10000000000 : ℝ)*X 1 1+(4988593423/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5422647367/10000000000 : ℝ)*X 2 0+(99771853/200000000 : ℝ)*X 2 1+(-1258484473/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4322809647/10000000000 : ℝ)*X 0 0+(916218661/2500000000 : ℝ)*X 0 1+(5099698979/10000000000 : ℝ)*X 0 2+(4322809647/10000000000 : ℝ)*X 1 0+(916218661/2500000000 : ℝ)*X 1 1+(5099698979/10000000000 : ℝ)*X 1 2+(4322809647/10000000000 : ℝ)*X 2 0+(916218661/2500000000 : ℝ)*X 2 1+(5099698979/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-106120689/500000000 : ℝ)*X 0 0+(4998810793/10000000000 : ℝ)*X 0 1+(356783251/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((209440227/400000000 : ℝ)*X 1 0+(-449256929/2500000000 : ℝ)*X 1 1+(713566759/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5236003597/10000000000 : ℝ)*X 2 0+(1141707277/2000000000 : ℝ)*X 2 1+(-224628411/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((540572503/1250000000 : ℝ)*X 0 0+(5079622697/10000000000 : ℝ)*X 0 1+(3685354253/10000000000 : ℝ)*X 0 2+(540572503/1250000000 : ℝ)*X 1 0+(5079622697/10000000000 : ℝ)*X 1 1+(3685354253/10000000000 : ℝ)*X 1 2+(540572503/1250000000 : ℝ)*X 2 0+(5079622697/10000000000 : ℝ)*X 2 1+(3685354253/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6345348366604119823185242451/2326250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1215341/1250000000000 : ℝ)*(base1) + (535493823/100000000000000 : ℝ)*(base19) + (716531483/100000000000000 : ℝ)*(base23) + (40447081/100000000000000 : ℝ)*(upper3) + (74216281/100000000000000 : ℝ)*(upper5) + (516533481242027/50000000000000 : ℝ)*(major0) + (516533481242027/50000000000000 : ℝ)*(major1) + (516533481242027/50000000000000 : ℝ)*(major2) + (1369179460535727/100000000000000 : ℝ)*(sp0) + (8557386648241/625000000000 : ℝ)*(sp1) + (1369181682680899/100000000000000 : ℝ)*(sp2) + (4355939683431/625000000000 : ℝ)*(sp3) + (47435999/1562500000000 : ℝ)*(sp4) + (494127811/50000000000000 : ℝ)*(sp7) + (696951434831863/100000000000000 : ℝ)*(f.failure) + (684591199606191/50000000000000 : ℝ)*(f.sum) + (249961774604517/46525000000000000000000000000 : ℝ)*base65 + (23163613129085373061/4652500000000000000000000000000000 : ℝ)*base67 + (31830730106705373061/4652500000000000000000000000000000 : ℝ)*base69 + (35525544306987873061/4652500000000000000000000000000000 : ℝ)*base71 + (42390502799973/11631250000000000000000000000 : ℝ)*base73 + (10768349412692873061/4652500000000000000000000000000000 : ℝ)*base75 + (33028459471205373061/4652500000000000000000000000000000 : ℝ)*base77 + (45694610905897873061/4652500000000000000000000000000000 : ℝ)*base79 + (136403062722221/23262500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (7983059/2000000000000000000000 : ℝ)*base90 + (7983059/2000000000000000000000 : ℝ)*base92 + (7983059/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (275631336453196828469519337/72695312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1416150521/50000000000000 : ℝ)*(base19) + (1415583343/50000000000000 : ℝ)*(base23) + (259921243/100000000000000 : ℝ)*(upper2) + (95587439/20000000000000 : ℝ)*(upper3) + (22654651/4000000000000 : ℝ)*(upper5) + (2076390023983/195312500000 : ℝ)*(major0) + (2076390023983/195312500000 : ℝ)*(major1) + (2076390023983/195312500000 : ℝ)*(major2) + (3567051091/25000000000000 : ℝ)*(sp1) + (1999651973/12500000000000 : ℝ)*(sp2) + (281800471106363/20000000000000 : ℝ)*(sp4) + (1408985255026409/100000000000000 : ℝ)*(sp5) + (44030735223417/3125000000000 : ℝ)*(sp6) + (717220902640203/100000000000000 : ℝ)*(sp7) + (717220902640203/100000000000000 : ℝ)*(f.failure) + (281800471106363/20000000000000 : ℝ)*(f.sum) + (71146331594123/11631250000000000000000000000 : ℝ)*base66 + (219418624342361149/72695312500000000000000000000000 : ℝ)*base68 + (8358232731050423/145390625000000000000000000000000 : ℝ)*base70 + (841160697530112923/145390625000000000000000000000000 : ℝ)*base72 + (67638815424233/46525000000000000000000000000 : ℝ)*base73 + (396917059541987923/145390625000000000000000000000000 : ℝ)*base76 + (50983070613930131/18173828125000000000000000000000 : ℝ)*base78 + (142377804796137077/145390625000000000000000000000000 : ℝ)*base79 + (46775193740733/46525000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (8477321/2000000000000000000000 : ℝ)*base89 + (8477321/2000000000000000000000 : ℝ)*base91 + (8477321/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1078_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29645307/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14031/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (147/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1321/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10367/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1078_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1078_s2_0 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-272281183/1250000000 : ℝ)*x 0 + (2761717269/5000000000 : ℝ)*x 1 + (5148106827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272281183/1250000000 : ℝ)^8271 ≤ (6595499602061/50000000000000 : ℝ)^6223 := by
    have hnat : (272281183 : ℕ)^8271*50000000000000^6223 ≤ 6595499602061^6223*1250000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272281183 1250000000 6595499602061 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2761717269/5000000000 : ℝ)^8271 ≤ (45432833103829/100000000000000 : ℝ)^6223 := by
    have hnat : (2761717269 : ℕ)^8271*100000000000000^6223 ≤ 45432833103829^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2761717269 5000000000 45432833103829 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5148106827/10000000000 : ℝ)^8271 ≤ (41376167682741/100000000000000 : ℝ)^6223 := by
    have hnat : (5148106827 : ℕ)^8271*100000000000000^6223 ≤ 41376167682741^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5148106827 10000000000 41376167682741 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-272281183/1250000000 : ℝ), (2761717269/5000000000 : ℝ), (5148106827/10000000000 : ℝ)] ![(6595499602061/50000000000000 : ℝ), (45432833103829/100000000000000 : ℝ), (41376167682741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-272281183/1250000000 : ℝ)|^8271 ≤ (6595499602061/50000000000000 : ℝ)^6223
        have hw : |(-272281183/1250000000 : ℝ)|=(272281183/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2761717269/5000000000 : ℝ)|^8271 ≤ (45432833103829/100000000000000 : ℝ)^6223
        have hw : |(2761717269/5000000000 : ℝ)|=(2761717269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5148106827/10000000000 : ℝ)|^8271 ≤ (41376167682741/100000000000000 : ℝ)^6223
        have hw : |(5148106827/10000000000 : ℝ)|=(5148106827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s2_1 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (537666667/1000000000 : ℝ)*x 0 + (-1186944491/5000000000 : ℝ)*x 1 + (5148107297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537666667/1000000000 : ℝ)^8271 ≤ (8767070737793/20000000000000 : ℝ)^6223 := by
    have hnat : (537666667 : ℕ)^8271*20000000000000^6223 ≤ 8767070737793^6223*1000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537666667 1000000000 8767070737793 20000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1186944491/5000000000 : ℝ)^8271 ≤ (14788473590499/100000000000000 : ℝ)^6223 := by
    have hnat : (1186944491 : ℕ)^8271*100000000000000^6223 ≤ 14788473590499^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1186944491 5000000000 14788473590499 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5148107297/10000000000 : ℝ)^8271 ≤ (41376172703377/100000000000000 : ℝ)^6223 := by
    have hnat : (5148107297 : ℕ)^8271*100000000000000^6223 ≤ 41376172703377^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5148107297 10000000000 41376172703377 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537666667/1000000000 : ℝ), (-1186944491/5000000000 : ℝ), (5148107297/10000000000 : ℝ)] ![(8767070737793/20000000000000 : ℝ), (14788473590499/100000000000000 : ℝ), (41376172703377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537666667/1000000000 : ℝ)|^8271 ≤ (8767070737793/20000000000000 : ℝ)^6223
        have hw : |(537666667/1000000000 : ℝ)|=(537666667/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1186944491/5000000000 : ℝ)|^8271 ≤ (14788473590499/100000000000000 : ℝ)^6223
        have hw : |(-1186944491/5000000000 : ℝ)|=(1186944491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5148107297/10000000000 : ℝ)|^8271 ≤ (41376172703377/100000000000000 : ℝ)^6223
        have hw : |(5148107297/10000000000 : ℝ)|=(5148107297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s2_2 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (134416671/250000000 : ℝ)*x 0 + (1287026779/2500000000 : ℝ)*x 1 + (-2373888993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134416671/250000000 : ℝ)^8271 ≤ (2739709720693/6250000000000 : ℝ)^6223 := by
    have hnat : (134416671 : ℕ)^8271*6250000000000^6223 ≤ 2739709720693^6223*250000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134416671 250000000 2739709720693 6250000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1287026779/2500000000 : ℝ)^8271 ≤ (20688085384949/50000000000000 : ℝ)^6223 := by
    have hnat : (1287026779 : ℕ)^8271*50000000000000^6223 ≤ 20688085384949^6223*2500000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1287026779 2500000000 20688085384949 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2373888993/10000000000 : ℝ)^8271 ≤ (14788473681577/100000000000000 : ℝ)^6223 := by
    have hnat : (2373888993 : ℕ)^8271*100000000000000^6223 ≤ 14788473681577^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2373888993 10000000000 14788473681577 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134416671/250000000 : ℝ), (1287026779/2500000000 : ℝ), (-2373888993/10000000000 : ℝ)] ![(2739709720693/6250000000000 : ℝ), (20688085384949/50000000000000 : ℝ), (14788473681577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134416671/250000000 : ℝ)|^8271 ≤ (2739709720693/6250000000000 : ℝ)^6223
        have hw : |(134416671/250000000 : ℝ)|=(134416671/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1287026779/2500000000 : ℝ)|^8271 ≤ (20688085384949/50000000000000 : ℝ)^6223
        have hw : |(1287026779/2500000000 : ℝ)|=(1287026779/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2373888993/10000000000 : ℝ)|^8271 ≤ (14788473681577/100000000000000 : ℝ)^6223
        have hw : |(-2373888993/10000000000 : ℝ)|=(2373888993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s2_3 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4361562293/10000000000 : ℝ)*x 0 + (200428037/500000000 : ℝ)*x 1 + (4745902671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4361562293/10000000000 : ℝ)^8271 ≤ (16596544421241/50000000000000 : ℝ)^6223 := by
    have hnat : (4361562293 : ℕ)^8271*50000000000000^6223 ≤ 16596544421241^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361562293 10000000000 16596544421241 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (200428037/500000000 : ℝ)^8271 ≤ (29670939024421/100000000000000 : ℝ)^6223 := by
    have hnat : (200428037 : ℕ)^8271*100000000000000^6223 ≤ 29670939024421^6223*500000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200428037 500000000 29670939024421 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4745902671/10000000000 : ℝ)^8271 ≤ (37135972117067/100000000000000 : ℝ)^6223 := by
    have hnat : (4745902671 : ℕ)^8271*100000000000000^6223 ≤ 37135972117067^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4745902671 10000000000 37135972117067 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4361562293/10000000000 : ℝ), (200428037/500000000 : ℝ), (4745902671/10000000000 : ℝ)] ![(16596544421241/50000000000000 : ℝ), (29670939024421/100000000000000 : ℝ), (37135972117067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4361562293/10000000000 : ℝ)|^8271 ≤ (16596544421241/50000000000000 : ℝ)^6223
        have hw : |(4361562293/10000000000 : ℝ)|=(4361562293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(200428037/500000000 : ℝ)|^8271 ≤ (29670939024421/100000000000000 : ℝ)^6223
        have hw : |(200428037/500000000 : ℝ)|=(200428037/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4745902671/10000000000 : ℝ)|^8271 ≤ (37135972117067/100000000000000 : ℝ)^6223
        have hw : |(4745902671/10000000000 : ℝ)|=(4745902671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s2_4 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1089185703/5000000000 : ℝ)*x 0 + (5150813939/10000000000 : ℝ)*x 1 + (552069917/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089185703/5000000000 : ℝ)^8271 ≤ (13191980693519/100000000000000 : ℝ)^6223 := by
    have hnat : (1089185703 : ℕ)^8271*100000000000000^6223 ≤ 13191980693519^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089185703 5000000000 13191980693519 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5150813939/10000000000 : ℝ)^8271 ≤ (41405088111653/100000000000000 : ℝ)^6223 := by
    have hnat : (5150813939 : ℕ)^8271*100000000000000^6223 ≤ 41405088111653^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5150813939 10000000000 41405088111653 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (552069917/1000000000 : ℝ)^8271 ≤ (45402931175667/100000000000000 : ℝ)^6223 := by
    have hnat : (552069917 : ℕ)^8271*100000000000000^6223 ≤ 45402931175667^6223*1000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552069917 1000000000 45402931175667 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1089185703/5000000000 : ℝ), (5150813939/10000000000 : ℝ), (552069917/1000000000 : ℝ)] ![(13191980693519/100000000000000 : ℝ), (41405088111653/100000000000000 : ℝ), (45402931175667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1089185703/5000000000 : ℝ)|^8271 ≤ (13191980693519/100000000000000 : ℝ)^6223
        have hw : |(-1089185703/5000000000 : ℝ)|=(1089185703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5150813939/10000000000 : ℝ)|^8271 ≤ (41405088111653/100000000000000 : ℝ)^6223
        have hw : |(5150813939/10000000000 : ℝ)|=(5150813939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(552069917/1000000000 : ℝ)|^8271 ≤ (45402931175667/100000000000000 : ℝ)^6223
        have hw : |(552069917/1000000000 : ℝ)|=(552069917/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s2_5 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2640925241/5000000000 : ℝ)*x 0 + (-25016213/125000000 : ℝ)*x 1 + (43130463/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2640925241/5000000000 : ℝ)^8271 ≤ (1070272931267/2500000000000 : ℝ)^6223 := by
    have hnat : (2640925241 : ℕ)^8271*2500000000000^6223 ≤ 1070272931267^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640925241 5000000000 1070272931267 2500000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (25016213/125000000 : ℝ)^8271 ≤ (2357230107567/20000000000000 : ℝ)^6223 := by
    have hnat : (25016213 : ℕ)^8271*20000000000000^6223 ≤ 2357230107567^6223*125000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25016213 125000000 2357230107567 20000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43130463/78125000 : ℝ)^8271 ≤ (45402932203153/100000000000000 : ℝ)^6223 := by
    have hnat : (43130463 : ℕ)^8271*100000000000000^6223 ≤ 45402932203153^6223*78125000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43130463 78125000 45402932203153 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2640925241/5000000000 : ℝ), (-25016213/125000000 : ℝ), (43130463/78125000 : ℝ)] ![(1070272931267/2500000000000 : ℝ), (2357230107567/20000000000000 : ℝ), (45402932203153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2640925241/5000000000 : ℝ)|^8271 ≤ (1070272931267/2500000000000 : ℝ)^6223
        have hw : |(2640925241/5000000000 : ℝ)|=(2640925241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-25016213/125000000 : ℝ)|^8271 ≤ (2357230107567/20000000000000 : ℝ)^6223
        have hw : |(-25016213/125000000 : ℝ)|=(25016213/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(43130463/78125000 : ℝ)|^8271 ≤ (45402932203153/100000000000000 : ℝ)^6223
        have hw : |(43130463/78125000 : ℝ)|=(43130463/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s2_6 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2640925361/5000000000 : ℝ)*x 0 + (2760349553/5000000000 : ℝ)*x 1 + (-2001296929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2640925361/5000000000 : ℝ)^8271 ≤ (42810919836141/100000000000000 : ℝ)^6223 := by
    have hnat : (2640925361 : ℕ)^8271*100000000000000^6223 ≤ 42810919836141^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640925361 5000000000 42810919836141 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2760349553/5000000000 : ℝ)^8271 ≤ (22701465238051/50000000000000 : ℝ)^6223 := by
    have hnat : (2760349553 : ℕ)^8271*50000000000000^6223 ≤ 22701465238051^6223*5000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2760349553 5000000000 22701465238051 50000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2001296929/10000000000 : ℝ)^8271 ≤ (92079294289/781250000000 : ℝ)^6223 := by
    have hnat : (2001296929 : ℕ)^8271*781250000000^6223 ≤ 92079294289^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2001296929 10000000000 92079294289 781250000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2640925361/5000000000 : ℝ), (2760349553/5000000000 : ℝ), (-2001296929/10000000000 : ℝ)] ![(42810919836141/100000000000000 : ℝ), (22701465238051/50000000000000 : ℝ), (92079294289/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2640925361/5000000000 : ℝ)|^8271 ≤ (42810919836141/100000000000000 : ℝ)^6223
        have hw : |(2640925361/5000000000 : ℝ)|=(2640925361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2760349553/5000000000 : ℝ)|^8271 ≤ (22701465238051/50000000000000 : ℝ)^6223
        have hw : |(2760349553/5000000000 : ℝ)|=(2760349553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2001296929/10000000000 : ℝ)|^8271 ≤ (92079294289/781250000000 : ℝ)^6223
        have hw : |(-2001296929/10000000000 : ℝ)|=(2001296929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1078_s2_7 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (872360397/2000000000 : ℝ)*x 0 + (948116989/2000000000 : ℝ)*x 1 + (4013933663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872360397/2000000000 : ℝ)^8271 ≤ (33195513337383/100000000000000 : ℝ)^6223 := by
    have hnat : (872360397 : ℕ)^8271*100000000000000^6223 ≤ 33195513337383^6223*2000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872360397 2000000000 33195513337383 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (948116989/2000000000 : ℝ)^8271 ≤ (37080677857851/100000000000000 : ℝ)^6223 := by
    have hnat : (948116989 : ℕ)^8271*100000000000000^6223 ≤ 37080677857851^6223*2000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      948116989 2000000000 37080677857851 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4013933663/10000000000 : ℝ)^8271 ≤ (29723808792667/100000000000000 : ℝ)^6223 := by
    have hnat : (4013933663 : ℕ)^8271*100000000000000^6223 ≤ 29723808792667^6223*10000000000^8271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4013933663 10000000000 29723808792667 100000000000000 8271 6223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8271/2048 : ℝ)) 8271 6223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(872360397/2000000000 : ℝ), (948116989/2000000000 : ℝ), (4013933663/10000000000 : ℝ)] ![(33195513337383/100000000000000 : ℝ), (37080677857851/100000000000000 : ℝ), (29723808792667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(872360397/2000000000 : ℝ)|^8271 ≤ (33195513337383/100000000000000 : ℝ)^6223
        have hw : |(872360397/2000000000 : ℝ)|=(872360397/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(948116989/2000000000 : ℝ)|^8271 ≤ (37080677857851/100000000000000 : ℝ)^6223
        have hw : |(948116989/2000000000 : ℝ)|=(948116989/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4013933663/10000000000 : ℝ)|^8271 ≤ (29723808792667/100000000000000 : ℝ)^6223
        have hw : |(4013933663/10000000000 : ℝ)|=(4013933663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1078_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29645307/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10367/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1321/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (877/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8351/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10367/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1321/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10367/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1321/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10367/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1321/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10367/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1321/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10367/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1321/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10367/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1321/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1321/25000 : ℝ) ^ (4135/1024 : ℝ) ≤ (696969987422629/100000000000000000000 : ℝ) := by
    have hpowers : (1321/25000 : ℝ)^4135 ≤ (696969987422629/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1321 : ℕ)^4135*100000000000000000000^1024 ≤ 696969987422629^1024*25000^4135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1321 25000 696969987422629 100000000000000000000 4135 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1321/25000 : ℝ)) (X := (696969987422629/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (10367/50000 : ℝ) ^ (4135/1024 : ℝ) ≤ (174063459894362379/100000000000000000000 : ℝ) := by
    have hpowers : (10367/50000 : ℝ)^4135 ≤ (174063459894362379/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10367 : ℕ)^4135*100000000000000000000^1024 ≤ 174063459894362379^1024*50000^4135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10367 50000 174063459894362379 100000000000000000000 4135 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10367/50000 : ℝ)) (X := (174063459894362379/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000696969987422629/50000000000000000000 : ℝ) ≤ (250000862990961/250000000000000 : ℝ) ^ (4135/1024 : ℝ) := by
    have hpowers : (50000696969987422629/50000000000000000000 : ℝ)^1024 ≤ (250000862990961/250000000000000 : ℝ)^4135 := by
      have hnat : (50000696969987422629 : ℕ)^1024*250000000000000^4135 ≤ 250000862990961^4135*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000696969987422629 50000000000000000000 250000862990961 250000000000000 1024 4135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250000862990961/250000000000000 : ℝ)) (X := (50000696969987422629/50000000000000000000 : ℝ)) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6260922526867611563/6250000000000000000 : ℝ) ≤ (10004324961383347/10000000000000000 : ℝ) ^ (4135/1024 : ℝ) := by
    have hpowers : (6260922526867611563/6250000000000000000 : ℝ)^1024 ≤ (10004324961383347/10000000000000000 : ℝ)^4135 := by
      have hnat : (6260922526867611563 : ℕ)^1024*10000000000000000^4135 ≤ 10004324961383347^4135*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6260922526867611563 6250000000000000000 10004324961383347 10000000000000000 1024 4135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004324961383347/10000000000000000 : ℝ)) (X := (6260922526867611563/6250000000000000000 : ℝ)) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50174063459894362379/50000000000000000000 : ℝ) ≤ (5004307701564127/5000000000000000 : ℝ) ^ (4135/1024 : ℝ) := by
    have hpowers : (50174063459894362379/50000000000000000000 : ℝ)^1024 ≤ (5004307701564127/5000000000000000 : ℝ)^4135 := by
      have hnat : (50174063459894362379 : ℕ)^1024*5000000000000000^4135 ≤ 5004307701564127^4135*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50174063459894362379 50000000000000000000 5004307701564127 5000000000000000 1024 4135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004307701564127/5000000000000000 : ℝ)) (X := (50174063459894362379/50000000000000000000 : ℝ)) (by norm_num) 4135 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(696969987422629/100000000000000000000 : ℝ) ≤ ((19306898992506715103/19312500000000000000 : ℝ)+2*(4290441744907/1545000000000000 : ℝ)*(1321/25000 : ℝ))^(4135/1024 : ℝ) := by
    rw [show (19306898992506715103/19312500000000000000 : ℝ)+2*(4290441744907/1545000000000000 : ℝ)*(1321/25000 : ℝ)=(250000862990961/250000000000000 : ℝ) by norm_num, show 1+2*(696969987422629/100000000000000000000 : ℝ)=(50000696969987422629/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(174063459894362379/100000000000000000000 : ℝ)+(696969987422629/100000000000000000000 : ℝ) ≤ ((19306898992506715103/19312500000000000000 : ℝ)+(4290441744907/1545000000000000 : ℝ)*((10367/50000 : ℝ)+(1321/25000 : ℝ)))^(4135/1024 : ℝ) := by
    rw [show (19306898992506715103/19312500000000000000 : ℝ)+(4290441744907/1545000000000000 : ℝ)*((10367/50000 : ℝ)+(1321/25000 : ℝ))=(10004324961383347/10000000000000000 : ℝ) by norm_num, show 1+(174063459894362379/100000000000000000000 : ℝ)+(696969987422629/100000000000000000000 : ℝ)=(6260922526867611563/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(174063459894362379/100000000000000000000 : ℝ) ≤ ((19306898992506715103/19312500000000000000 : ℝ)+2*(4290441744907/1545000000000000 : ℝ)*(10367/50000 : ℝ))^(4135/1024 : ℝ) := by
    rw [show (19306898992506715103/19312500000000000000 : ℝ)+2*(4290441744907/1545000000000000 : ℝ)*(10367/50000 : ℝ)=(5004307701564127/5000000000000000 : ℝ) by norm_num, show 1+2*(174063459894362379/100000000000000000000 : ℝ)=(50174063459894362379/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19306898992506715103/19312500000000000000 : ℝ)*(X 1 0+X 2 0)+(4290441744907/1545000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4135/1024 : ℝ)) (lo := (1321/25000 : ℝ)) (hi := (10367/50000 : ℝ)) (c := (19306898992506715103/19312500000000000000 : ℝ)) (alpha := (4290441744907/1545000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19306898992506715103/19312500000000000000 : ℝ)*(X 0 1+X 2 1)+(4290441744907/1545000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4135/1024 : ℝ)) (lo := (1321/25000 : ℝ)) (hi := (10367/50000 : ℝ)) (c := (19306898992506715103/19312500000000000000 : ℝ)) (alpha := (4290441744907/1545000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19306898992506715103/19312500000000000000 : ℝ)*(X 0 2+X 1 2)+(4290441744907/1545000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4135/1024 : ℝ)) (lo := (1321/25000 : ℝ)) (hi := (10367/50000 : ℝ)) (c := (19306898992506715103/19312500000000000000 : ℝ)) (alpha := (4290441744907/1545000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-272281183/1250000000 : ℝ)*X 0 0+(2761717269/5000000000 : ℝ)*X 0 1+(5148106827/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((537666667/1000000000 : ℝ)*X 1 0+(-1186944491/5000000000 : ℝ)*X 1 1+(5148107297/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((134416671/250000000 : ℝ)*X 2 0+(1287026779/2500000000 : ℝ)*X 2 1+(-2373888993/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4361562293/10000000000 : ℝ)*X 0 0+(200428037/500000000 : ℝ)*X 0 1+(4745902671/10000000000 : ℝ)*X 0 2+(4361562293/10000000000 : ℝ)*X 1 0+(200428037/500000000 : ℝ)*X 1 1+(4745902671/10000000000 : ℝ)*X 1 2+(4361562293/10000000000 : ℝ)*X 2 0+(200428037/500000000 : ℝ)*X 2 1+(4745902671/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1089185703/5000000000 : ℝ)*X 0 0+(5150813939/10000000000 : ℝ)*X 0 1+(552069917/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2640925241/5000000000 : ℝ)*X 1 0+(-25016213/125000000 : ℝ)*X 1 1+(43130463/78125000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2640925361/5000000000 : ℝ)*X 2 0+(2760349553/5000000000 : ℝ)*X 2 1+(-2001296929/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((872360397/2000000000 : ℝ)*X 0 0+(948116989/2000000000 : ℝ)*X 0 1+(4013933663/10000000000 : ℝ)*X 0 2+(872360397/2000000000 : ℝ)*X 1 0+(948116989/2000000000 : ℝ)*X 1 1+(4013933663/10000000000 : ℝ)*X 1 2+(872360397/2000000000 : ℝ)*X 2 0+(948116989/2000000000 : ℝ)*X 2 1+(4013933663/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1078_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (728725098236819821967613249/80468750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27173543/50000000000000 : ℝ)*(base1) + (424581121/25000000000000 : ℝ)*(base19) + (178256699/10000000000000 : ℝ)*(base23) + (10870727/6250000000000 : ℝ)*(upper3) + (186188819/100000000000000 : ℝ)*(upper5) + (1005154814558733/50000000000000 : ℝ)*(major0) + (1005154814558733/50000000000000 : ℝ)*(major1) + (1005154814558733/50000000000000 : ℝ)*(major2) + (1332178778106143/50000000000000 : ℝ)*(sp0) + (2664375860970351/100000000000000 : ℝ)*(sp1) + (666093944181961/25000000000000 : ℝ)*(sp2) + (1356232013003949/100000000000000 : ℝ)*(sp3) + (4011485927/20000000000000 : ℝ)*(sp4) + (4664861173/50000000000000 : ℝ)*(sp7) + (678120698536691/50000000000000 : ℝ)*(f.failure) + (532875511858967/20000000000000 : ℝ)*(f.sum) + (1359434335299/6437500000000000000000000000 : ℝ)*base66 + (521677307689947667/321875000000000000000000000000000 : ℝ)*base68 + (2642608659121197667/321875000000000000000000000000000 : ℝ)*base70 + (20451521508697667/321875000000000000000000000000000 : ℝ)*base72 + (35254639931223/12875000000000000000000000000 : ℝ)*base74 + (1801862074199322667/321875000000000000000000000000000 : ℝ)*base76 + (812132628914947667/321875000000000000000000000000000 : ℝ)*base78 + (2867755997269427333/321875000000000000000000000000000 : ℝ)*base79 + (24584258860049/6437500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (4540863/1000000000000000000000 : ℝ)*base90 + (4540863/1000000000000000000000 : ℝ)*base92 + (4540863/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1545161179888621785672313357/160937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1887983189/100000000000000 : ℝ)*(base19) + (433915449/20000000000000 : ℝ)*(base23) + (1560859/625000000000 : ℝ)*(upper3) + (57410527/100000000000000 : ℝ)*(lower4) + (197966039/100000000000000 : ℝ)*(upper5) + (1019929293653773/50000000000000 : ℝ)*(major0) + (1019929293653773/50000000000000 : ℝ)*(major1) + (1019929293653773/50000000000000 : ℝ)*(major2) + (16676695783/100000000000000 : ℝ)*(sp1) + (9732543429/50000000000000 : ℝ)*(sp2) + (168971278660139/6250000000000 : ℝ)*(sp4) + (675880473470813/25000000000000 : ℝ)*(sp5) + (67587970597453/2500000000000 : ℝ)*(sp6) + (344044099004869/25000000000000 : ℝ)*(sp7) + (344044099004869/25000000000000 : ℝ)*(f.failure) + (168971278660139/6250000000000 : ℝ)*(f.sum) + (168635805203611/38625000000000000000000000000 : ℝ)*base65 + (11636941797879078881/965625000000000000000000000000000 : ℝ)*base68 + (9242139182904078881/965625000000000000000000000000000 : ℝ)*base70 + (4968925330385328881/965625000000000000000000000000000 : ℝ)*base72 + (6118841995861/38625000000000000000000000000 : ℝ)*base73 + (15325191397563453881/965625000000000000000000000000000 : ℝ)*base76 + (8340164853429078881/965625000000000000000000000000000 : ℝ)*base78 + (6295994519154078881/965625000000000000000000000000000 : ℝ)*base80 + (12048089944139/38625000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (5999783/500000000000000000000 : ℝ)*base89 + (5999783/500000000000000000000 : ℝ)*base91 + (5999783/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1078_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29645307/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10367/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1321/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (877/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8351/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1078_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1078_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29645307/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (877/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8351/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1078_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1078_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1078_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29645307/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (877/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8351/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1078_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
