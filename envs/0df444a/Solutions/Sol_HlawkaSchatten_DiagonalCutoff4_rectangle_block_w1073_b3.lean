-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1073_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:12:25.881016+00:00
-- url     : https://prove2.me/submissions/35bdec68-33a0-460a-aaef-005bb2272e55

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
theorem support_rectangle_w1073_s9_0 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2200329793/10000000000 : ℝ)*x 0 + (5394206943/10000000000 : ℝ)*x 1 + (1052921197/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2200329793/10000000000 : ℝ)^4133 ≤ (3340914673211/25000000000000 : ℝ)^3109 := by
    have hnat : (2200329793 : ℕ)^4133*25000000000000^3109 ≤ 3340914673211^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2200329793 10000000000 3340914673211 25000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394206943/10000000000 : ℝ)^4133 ≤ (44018331366973/100000000000000 : ℝ)^3109 := by
    have hnat : (5394206943 : ℕ)^4133*100000000000000^3109 ≤ 44018331366973^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394206943 10000000000 44018331366973 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052921197/2000000000 : ℝ)^4133 ≤ (10654502481729/25000000000000 : ℝ)^3109 := by
    have hnat : (1052921197 : ℕ)^4133*25000000000000^3109 ≤ 10654502481729^3109*2000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052921197 2000000000 10654502481729 25000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2200329793/10000000000 : ℝ), (5394206943/10000000000 : ℝ), (1052921197/2000000000 : ℝ)] ![(3340914673211/25000000000000 : ℝ), (44018331366973/100000000000000 : ℝ), (10654502481729/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2200329793/10000000000 : ℝ)|^4133 ≤ (3340914673211/25000000000000 : ℝ)^3109
        have hw : |(-2200329793/10000000000 : ℝ)|=(2200329793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394206943/10000000000 : ℝ)|^4133 ≤ (44018331366973/100000000000000 : ℝ)^3109
        have hw : |(5394206943/10000000000 : ℝ)|=(5394206943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052921197/2000000000 : ℝ)|^4133 ≤ (10654502481729/25000000000000 : ℝ)^3109
        have hw : |(1052921197/2000000000 : ℝ)|=(1052921197/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s9_1 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344955063/10000000000 : ℝ)*x 0 + (-1133041387/5000000000 : ℝ)*x 1 + (2632303157/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344955063/10000000000 : ℝ)^4133 ≤ (21742425394643/50000000000000 : ℝ)^3109 := by
    have hnat : (5344955063 : ℕ)^4133*50000000000000^3109 ≤ 21742425394643^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344955063 10000000000 21742425394643 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1133041387/5000000000 : ℝ)^4133 ≤ (3474283932347/25000000000000 : ℝ)^3109 := by
    have hnat : (1133041387 : ℕ)^4133*25000000000000^3109 ≤ 3474283932347^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133041387 5000000000 3474283932347 25000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632303157/5000000000 : ℝ)^4133 ≤ (42618013467443/100000000000000 : ℝ)^3109 := by
    have hnat : (2632303157 : ℕ)^4133*100000000000000^3109 ≤ 42618013467443^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632303157 5000000000 42618013467443 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344955063/10000000000 : ℝ), (-1133041387/5000000000 : ℝ), (2632303157/5000000000 : ℝ)] ![(21742425394643/50000000000000 : ℝ), (3474283932347/25000000000000 : ℝ), (42618013467443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344955063/10000000000 : ℝ)|^4133 ≤ (21742425394643/50000000000000 : ℝ)^3109
        have hw : |(5344955063/10000000000 : ℝ)|=(5344955063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1133041387/5000000000 : ℝ)|^4133 ≤ (3474283932347/25000000000000 : ℝ)^3109
        have hw : |(-1133041387/5000000000 : ℝ)|=(1133041387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632303157/5000000000 : ℝ)|^4133 ≤ (42618013467443/100000000000000 : ℝ)^3109
        have hw : |(2632303157/5000000000 : ℝ)|=(2632303157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s9_2 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344955543/10000000000 : ℝ)*x 0 + (2632303017/5000000000 : ℝ)*x 1 + (-2266082507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344955543/10000000000 : ℝ)^4133 ≤ (4348485598063/10000000000000 : ℝ)^3109 := by
    have hnat : (5344955543 : ℕ)^4133*10000000000000^3109 ≤ 4348485598063^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344955543 10000000000 4348485598063 10000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632303017/5000000000 : ℝ)^4133 ≤ (42618010454229/100000000000000 : ℝ)^3109 := by
    have hnat : (2632303017 : ℕ)^4133*100000000000000^3109 ≤ 42618010454229^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632303017 5000000000 42618010454229 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2266082507/10000000000 : ℝ)^4133 ≤ (13897133552653/100000000000000 : ℝ)^3109 := by
    have hnat : (2266082507 : ℕ)^4133*100000000000000^3109 ≤ 13897133552653^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2266082507 10000000000 13897133552653 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344955543/10000000000 : ℝ), (2632303017/5000000000 : ℝ), (-2266082507/10000000000 : ℝ)] ![(4348485598063/10000000000000 : ℝ), (42618010454229/100000000000000 : ℝ), (13897133552653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344955543/10000000000 : ℝ)|^4133 ≤ (4348485598063/10000000000000 : ℝ)^3109
        have hw : |(5344955543/10000000000 : ℝ)|=(5344955543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632303017/5000000000 : ℝ)|^4133 ≤ (42618010454229/100000000000000 : ℝ)^3109
        have hw : |(2632303017/5000000000 : ℝ)|=(2632303017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2266082507/10000000000 : ℝ)|^4133 ≤ (13897133552653/100000000000000 : ℝ)^3109
        have hw : |(-2266082507/10000000000 : ℝ)|=(2266082507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s9_3 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2187243969/5000000000 : ℝ)*x 0 + (2124591037/5000000000 : ℝ)*x 1 + (900706593/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187243969/5000000000 : ℝ)^4133 ≤ (16658302177537/50000000000000 : ℝ)^3109 := by
    have hnat : (2187243969 : ℕ)^4133*50000000000000^3109 ≤ 16658302177537^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187243969 5000000000 16658302177537 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2124591037/5000000000 : ℝ)^4133 ≤ (32053955174377/100000000000000 : ℝ)^3109 := by
    have hnat : (2124591037 : ℕ)^4133*100000000000000^3109 ≤ 32053955174377^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124591037 5000000000 32053955174377 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (900706593/2000000000 : ℝ)^4133 ≤ (8657360112297/25000000000000 : ℝ)^3109 := by
    have hnat : (900706593 : ℕ)^4133*25000000000000^3109 ≤ 8657360112297^3109*2000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900706593 2000000000 8657360112297 25000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2187243969/5000000000 : ℝ), (2124591037/5000000000 : ℝ), (900706593/2000000000 : ℝ)] ![(16658302177537/50000000000000 : ℝ), (32053955174377/100000000000000 : ℝ), (8657360112297/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2187243969/5000000000 : ℝ)|^4133 ≤ (16658302177537/50000000000000 : ℝ)^3109
        have hw : |(2187243969/5000000000 : ℝ)|=(2187243969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2124591037/5000000000 : ℝ)|^4133 ≤ (32053955174377/100000000000000 : ℝ)^3109
        have hw : |(2124591037/5000000000 : ℝ)|=(2124591037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(900706593/2000000000 : ℝ)|^4133 ≤ (8657360112297/25000000000000 : ℝ)^3109
        have hw : |(900706593/2000000000 : ℝ)|=(900706593/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s9_4 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2200334847/10000000000 : ℝ)*x 0 + (526493049/1000000000 : ℝ)*x 1 + (5393881259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2200334847/10000000000 : ℝ)^4133 ≤ (1670462437281/12500000000000 : ℝ)^3109 := by
    have hnat : (2200334847 : ℕ)^4133*12500000000000^3109 ≤ 1670462437281^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2200334847 10000000000 1670462437281 12500000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526493049/1000000000 : ℝ)^4133 ≤ (21310751058109/50000000000000 : ℝ)^3109 := by
    have hnat : (526493049 : ℕ)^4133*50000000000000^3109 ≤ 21310751058109^3109*1000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526493049 1000000000 21310751058109 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393881259/10000000000 : ℝ)^4133 ≤ (4401479837411/10000000000000 : ℝ)^3109 := by
    have hnat : (5393881259 : ℕ)^4133*10000000000000^3109 ≤ 4401479837411^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393881259 10000000000 4401479837411 10000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2200334847/10000000000 : ℝ), (526493049/1000000000 : ℝ), (5393881259/10000000000 : ℝ)] ![(1670462437281/12500000000000 : ℝ), (21310751058109/50000000000000 : ℝ), (4401479837411/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2200334847/10000000000 : ℝ)|^4133 ≤ (1670462437281/12500000000000 : ℝ)^3109
        have hw : |(-2200334847/10000000000 : ℝ)|=(2200334847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526493049/1000000000 : ℝ)|^4133 ≤ (21310751058109/50000000000000 : ℝ)^3109
        have hw : |(526493049/1000000000 : ℝ)|=(526493049/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393881259/10000000000 : ℝ)|^4133 ≤ (4401479837411/10000000000000 : ℝ)^3109
        have hw : |(5393881259/10000000000 : ℝ)|=(5393881259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s9_5 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (332018321/625000000 : ℝ)*x 0 + (-2136807957/10000000000 : ℝ)*x 1 + (5267462/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332018321/625000000 : ℝ)^4133 ≤ (84242105851/195312500000 : ℝ)^3109 := by
    have hnat : (332018321 : ℕ)^4133*195312500000^3109 ≤ 84242105851^3109*625000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332018321 625000000 84242105851 195312500000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2136807957/10000000000 : ℝ)^4133 ≤ (6426622634141/50000000000000 : ℝ)^3109 := by
    have hnat : (2136807957 : ℕ)^4133*50000000000000^3109 ≤ 6426622634141^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136807957 10000000000 6426622634141 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267462/9765625 : ℝ)^4133 ≤ (8802959303827/20000000000000 : ℝ)^3109 := by
    have hnat : (5267462 : ℕ)^4133*20000000000000^3109 ≤ 8802959303827^3109*9765625^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267462 9765625 8802959303827 20000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(332018321/625000000 : ℝ), (-2136807957/10000000000 : ℝ), (5267462/9765625 : ℝ)] ![(84242105851/195312500000 : ℝ), (6426622634141/50000000000000 : ℝ), (8802959303827/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(332018321/625000000 : ℝ)|^4133 ≤ (84242105851/195312500000 : ℝ)^3109
        have hw : |(332018321/625000000 : ℝ)|=(332018321/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2136807957/10000000000 : ℝ)|^4133 ≤ (6426622634141/50000000000000 : ℝ)^3109
        have hw : |(-2136807957/10000000000 : ℝ)|=(2136807957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267462/9765625 : ℝ)|^4133 ≤ (8802959303827/20000000000000 : ℝ)^3109
        have hw : |(5267462/9765625 : ℝ)|=(5267462/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_s9_6 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4374497349/10000000000 : ℝ)*x 0 + (450289683/1000000000 : ℝ)*x 1 + (169992839/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4374497349/10000000000 : ℝ)^4133 ≤ (8329174909447/25000000000000 : ℝ)^3109 := by
    have hnat : (4374497349 : ℕ)^4133*25000000000000^3109 ≤ 8329174909447^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4374497349 10000000000 8329174909447 25000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (450289683/1000000000 : ℝ)^4133 ≤ (3462293801449/10000000000000 : ℝ)^3109 := by
    have hnat : (450289683 : ℕ)^4133*10000000000000^3109 ≤ 3462293801449^3109*1000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450289683 1000000000 3462293801449 10000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169992839/400000000 : ℝ)^4133 ≤ (32060362330241/100000000000000 : ℝ)^3109 := by
    have hnat : (169992839 : ℕ)^4133*100000000000000^3109 ≤ 32060362330241^3109*400000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169992839 400000000 32060362330241 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4374497349/10000000000 : ℝ), (450289683/1000000000 : ℝ), (169992839/400000000 : ℝ)] ![(8329174909447/25000000000000 : ℝ), (3462293801449/10000000000000 : ℝ), (32060362330241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4374497349/10000000000 : ℝ)|^4133 ≤ (8329174909447/25000000000000 : ℝ)^3109
        have hw : |(4374497349/10000000000 : ℝ)|=(4374497349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(450289683/1000000000 : ℝ)|^4133 ≤ (3462293801449/10000000000000 : ℝ)^3109
        have hw : |(450289683/1000000000 : ℝ)|=(450289683/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169992839/400000000 : ℝ)|^4133 ≤ (32060362330241/100000000000000 : ℝ)^3109
        have hw : |(169992839/400000000 : ℝ)|=(169992839/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1073_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148129231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14007/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11261/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5631/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14007/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14007/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11261/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14007/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11261/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14007/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11261/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14007/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11261/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14007/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11261/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14007/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11261/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11261/100000 : ℝ) ^ (8265/2048 : ℝ) ≤ (14876533314300109/100000000000000000000 : ℝ) := by
    have hpowers : (11261/100000 : ℝ)^8265 ≤ (14876533314300109/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11261 : ℕ)^8265*100000000000000000000^2048 ≤ 14876533314300109^2048*100000^8265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11261 100000 14876533314300109 100000000000000000000 8265 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11261/100000 : ℝ)) (X := (14876533314300109/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14007/100000 : ℝ) ^ (8265/2048 : ℝ) ≤ (7177651740125557/20000000000000000000 : ℝ) := by
    have hpowers : (14007/100000 : ℝ)^8265 ≤ (7177651740125557/20000000000000000000 : ℝ)^2048 := by
      have hnat : (14007 : ℕ)^8265*20000000000000000000^2048 ≤ 7177651740125557^2048*100000^8265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14007 100000 7177651740125557 20000000000000000000 8265 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14007/100000 : ℝ)) (X := (7177651740125557/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014876533314300109/50000000000000000000 : ℝ) ≤ (2500184293596317/2500000000000000 : ℝ) ^ (8265/2048 : ℝ) := by
    have hpowers : (50014876533314300109/50000000000000000000 : ℝ)^2048 ≤ (2500184293596317/2500000000000000 : ℝ)^8265 := by
      have hnat : (50014876533314300109 : ℕ)^2048*2500000000000000^8265 ≤ 2500184293596317^8265*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014876533314300109 50000000000000000000 2500184293596317 2500000000000000 2048 8265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500184293596317/2500000000000000 : ℝ)) (X := (50014876533314300109/50000000000000000000 : ℝ)) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025382396007463947/50000000000000000000 : ℝ) ≤ (2000251534058821/2000000000000000 : ℝ) ^ (8265/2048 : ℝ) := by
    have hpowers : (50025382396007463947/50000000000000000000 : ℝ)^2048 ≤ (2000251534058821/2000000000000000 : ℝ)^8265 := by
      have hnat : (50025382396007463947 : ℕ)^2048*2000000000000000^8265 ≤ 2000251534058821^8265*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025382396007463947 50000000000000000000 2000251534058821 2000000000000000 2048 8265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000251534058821/2000000000000000 : ℝ)) (X := (50025382396007463947/50000000000000000000 : ℝ)) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007177651740125557/10000000000000000000 : ℝ) ≤ (5000889083101471/5000000000000000 : ℝ) ^ (8265/2048 : ℝ) := by
    have hpowers : (10007177651740125557/10000000000000000000 : ℝ)^2048 ≤ (5000889083101471/5000000000000000 : ℝ)^8265 := by
      have hnat : (10007177651740125557 : ℕ)^2048*5000000000000000^8265 ≤ 5000889083101471^8265*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007177651740125557 10000000000000000000 5000889083101471 5000000000000000 2048 8265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000889083101471/5000000000000000 : ℝ)) (X := (10007177651740125557/10000000000000000000 : ℝ)) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14876533314300109/100000000000000000000 : ℝ) ≤ ((13725150836001559507/13730000000000000000 : ℝ)+2*(520495908837/274600000000000 : ℝ)*(11261/100000 : ℝ))^(8265/2048 : ℝ) := by
    rw [show (13725150836001559507/13730000000000000000 : ℝ)+2*(520495908837/274600000000000 : ℝ)*(11261/100000 : ℝ)=(2500184293596317/2500000000000000 : ℝ) by norm_num, show 1+2*(14876533314300109/100000000000000000000 : ℝ)=(50014876533314300109/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7177651740125557/20000000000000000000 : ℝ)+(14876533314300109/100000000000000000000 : ℝ) ≤ ((13725150836001559507/13730000000000000000 : ℝ)+(520495908837/274600000000000 : ℝ)*((14007/100000 : ℝ)+(11261/100000 : ℝ)))^(8265/2048 : ℝ) := by
    rw [show (13725150836001559507/13730000000000000000 : ℝ)+(520495908837/274600000000000 : ℝ)*((14007/100000 : ℝ)+(11261/100000 : ℝ))=(2000251534058821/2000000000000000 : ℝ) by norm_num, show 1+(7177651740125557/20000000000000000000 : ℝ)+(14876533314300109/100000000000000000000 : ℝ)=(50025382396007463947/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7177651740125557/20000000000000000000 : ℝ) ≤ ((13725150836001559507/13730000000000000000 : ℝ)+2*(520495908837/274600000000000 : ℝ)*(14007/100000 : ℝ))^(8265/2048 : ℝ) := by
    rw [show (13725150836001559507/13730000000000000000 : ℝ)+2*(520495908837/274600000000000 : ℝ)*(14007/100000 : ℝ)=(5000889083101471/5000000000000000 : ℝ) by norm_num, show 1+2*(7177651740125557/20000000000000000000 : ℝ)=(10007177651740125557/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13725150836001559507/13730000000000000000 : ℝ)*(X 1 0+X 2 0)+(520495908837/274600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8265/2048 : ℝ)) (lo := (11261/100000 : ℝ)) (hi := (14007/100000 : ℝ)) (c := (13725150836001559507/13730000000000000000 : ℝ)) (alpha := (520495908837/274600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13725150836001559507/13730000000000000000 : ℝ)*(X 0 1+X 2 1)+(520495908837/274600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8265/2048 : ℝ)) (lo := (11261/100000 : ℝ)) (hi := (14007/100000 : ℝ)) (c := (13725150836001559507/13730000000000000000 : ℝ)) (alpha := (520495908837/274600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13725150836001559507/13730000000000000000 : ℝ)*(X 0 2+X 1 2)+(520495908837/274600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8265/2048 : ℝ)) (lo := (11261/100000 : ℝ)) (hi := (14007/100000 : ℝ)) (c := (13725150836001559507/13730000000000000000 : ℝ)) (alpha := (520495908837/274600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2200329793/10000000000 : ℝ)*X 0 0+(5394206943/10000000000 : ℝ)*X 0 1+(1052921197/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344955063/10000000000 : ℝ)*X 1 0+(-1133041387/5000000000 : ℝ)*X 1 1+(2632303157/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344955543/10000000000 : ℝ)*X 2 0+(2632303017/5000000000 : ℝ)*X 2 1+(-2266082507/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2187243969/5000000000 : ℝ)*X 0 0+(2124591037/5000000000 : ℝ)*X 0 1+(900706593/2000000000 : ℝ)*X 0 2+(2187243969/5000000000 : ℝ)*X 1 0+(2124591037/5000000000 : ℝ)*X 1 1+(900706593/2000000000 : ℝ)*X 1 2+(2187243969/5000000000 : ℝ)*X 2 0+(2124591037/5000000000 : ℝ)*X 2 1+(900706593/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2200334847/10000000000 : ℝ)*X 0 0+(526493049/1000000000 : ℝ)*X 0 1+(5393881259/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((332018321/625000000 : ℝ)*X 1 0+(-2136807957/10000000000 : ℝ)*X 1 1+(5267462/9765625 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s9_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((4374497349/10000000000 : ℝ)*X 0 0+(450289683/1000000000 : ℝ)*X 0 1+(169992839/400000000 : ℝ)*X 0 2+(4374497349/10000000000 : ℝ)*X 1 0+(450289683/1000000000 : ℝ)*X 1 1+(169992839/400000000 : ℝ)*X 1 2+(4374497349/10000000000 : ℝ)*X 2 0+(450289683/1000000000 : ℝ)*X 2 1+(169992839/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_s9_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (589647508611409943028297219/343250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (648234179/100000000000000 : ℝ)*(base19) + (1118544091/100000000000000 : ℝ)*(base23) + (25700891/20000000000000 : ℝ)*(upper4) + (152312999/50000000000000 : ℝ)*(upper5) + (2911909769996939/50000000000000 : ℝ)*(major0) + (2911909769996939/50000000000000 : ℝ)*(major1) + (2911909769996939/50000000000000 : ℝ)*(major2) + (3858006256215639/50000000000000 : ℝ)*(sp0) + (3858027623121689/50000000000000 : ℝ)*(sp1) + (3858028844130053/50000000000000 : ℝ)*(sp2) + (393157896617359/10000000000000 : ℝ)*(sp3) + (46294372919/100000000000000 : ℝ)*(sp4) + (2912326641/100000000000000 : ℝ)*(sp5) + (624874367/50000000000000 : ℝ)*(sp6) + (982895053980581/25000000000000 : ℝ)*(f.failure) + (7716058806804197/100000000000000 : ℝ)*(f.sum) + (6876567122927/1716250000000000000000000000 : ℝ)*base65 + (2773149824042500927/686500000000000000000000000000000 : ℝ)*base68 + (7999606226401999073/686500000000000000000000000000000 : ℝ)*base69 + (2167052863310500927/686500000000000000000000000000000 : ℝ)*base72 + (2644435443191/858125000000000000000000000 : ℝ)*base73 + (2680089089536500927/686500000000000000000000000000000 : ℝ)*base76 + (4804417404757499073/686500000000000000000000000000000 : ℝ)*base77 + (6025591954152500927/686500000000000000000000000000000 : ℝ)*base80 + (3432463981227/6865000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2463211/2500000000000000000000 : ℝ)*base89 + (2463211/2500000000000000000000 : ℝ)*base91 + (2463211/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1073_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148129231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14007/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11261/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5631/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14007/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1073_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1073_box_0 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-414221369/2000000000 : ℝ)*x 0 + (1075454579/2000000000 : ℝ)*x 1 + (2688636189/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (414221369/2000000000 : ℝ)^4133 ≤ (2466110943217/20000000000000 : ℝ)^3109 := by
    have hnat : (414221369 : ℕ)^4133*20000000000000^3109 ≤ 2466110943217^3109*2000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414221369 2000000000 2466110943217 20000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1075454579/2000000000 : ℝ)^4133 ≤ (43834725438751/100000000000000 : ℝ)^3109 := by
    have hnat : (1075454579 : ℕ)^4133*100000000000000^3109 ≤ 43834725438751^3109*2000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075454579 2000000000 43834725438751 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688636189/5000000000 : ℝ)^4133 ≤ (43834719836127/100000000000000 : ℝ)^3109 := by
    have hnat : (2688636189 : ℕ)^4133*100000000000000^3109 ≤ 43834719836127^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688636189 5000000000 43834719836127 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-414221369/2000000000 : ℝ), (1075454579/2000000000 : ℝ), (2688636189/5000000000 : ℝ)] ![(2466110943217/20000000000000 : ℝ), (43834725438751/100000000000000 : ℝ), (43834719836127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-414221369/2000000000 : ℝ)|^4133 ≤ (2466110943217/20000000000000 : ℝ)^3109
        have hw : |(-414221369/2000000000 : ℝ)|=(414221369/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1075454579/2000000000 : ℝ)|^4133 ≤ (43834725438751/100000000000000 : ℝ)^3109
        have hw : |(1075454579/2000000000 : ℝ)|=(1075454579/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688636189/5000000000 : ℝ)|^4133 ≤ (43834719836127/100000000000000 : ℝ)^3109
        have hw : |(2688636189/5000000000 : ℝ)|=(2688636189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_box_1 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (264764139/500000000 : ℝ)*x 0 + (-436423797/2000000000 : ℝ)*x 1 + (1075454449/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264764139/500000000 : ℝ)^4133 ≤ (42948454003709/100000000000000 : ℝ)^3109 := by
    have hnat : (264764139 : ℕ)^4133*100000000000000^3109 ≤ 42948454003709^3109*500000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264764139 500000000 42948454003709 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (436423797/2000000000 : ℝ)^4133 ≤ (2643365518443/20000000000000 : ℝ)^3109 := by
    have hnat : (436423797 : ℕ)^4133*20000000000000^3109 ≤ 2643365518443^3109*2000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436423797 2000000000 2643365518443 20000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1075454449/2000000000 : ℝ)^4133 ≤ (21917359197417/50000000000000 : ℝ)^3109 := by
    have hnat : (1075454449 : ℕ)^4133*50000000000000^3109 ≤ 21917359197417^3109*2000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075454449 2000000000 21917359197417 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264764139/500000000 : ℝ), (-436423797/2000000000 : ℝ), (1075454449/2000000000 : ℝ)] ![(42948454003709/100000000000000 : ℝ), (2643365518443/20000000000000 : ℝ), (21917359197417/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264764139/500000000 : ℝ)|^4133 ≤ (42948454003709/100000000000000 : ℝ)^3109
        have hw : |(264764139/500000000 : ℝ)|=(264764139/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-436423797/2000000000 : ℝ)|^4133 ≤ (2643365518443/20000000000000 : ℝ)^3109
        have hw : |(-436423797/2000000000 : ℝ)|=(436423797/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1075454449/2000000000 : ℝ)|^4133 ≤ (21917359197417/50000000000000 : ℝ)^3109
        have hw : |(1075454449/2000000000 : ℝ)|=(1075454449/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_box_2 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647641571/5000000000 : ℝ)*x 0 + (1075454391/2000000000 : ℝ)*x 1 + (-218211889/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647641571/5000000000 : ℝ)^4133 ≤ (42948457906827/100000000000000 : ℝ)^3109 := by
    have hnat : (2647641571 : ℕ)^4133*100000000000000^3109 ≤ 42948457906827^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647641571 5000000000 42948457906827 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1075454391/2000000000 : ℝ)^4133 ≤ (43834715252163/100000000000000 : ℝ)^3109 := by
    have hnat : (1075454391 : ℕ)^4133*100000000000000^3109 ≤ 43834715252163^3109*2000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075454391 2000000000 43834715252163 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (218211889/1000000000 : ℝ)^4133 ≤ (13216826827293/100000000000000 : ℝ)^3109 := by
    have hnat : (218211889 : ℕ)^4133*100000000000000^3109 ≤ 13216826827293^3109*1000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218211889 1000000000 13216826827293 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647641571/5000000000 : ℝ), (1075454391/2000000000 : ℝ), (-218211889/1000000000 : ℝ)] ![(42948457906827/100000000000000 : ℝ), (43834715252163/100000000000000 : ℝ), (13216826827293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647641571/5000000000 : ℝ)|^4133 ≤ (42948457906827/100000000000000 : ℝ)^3109
        have hw : |(2647641571/5000000000 : ℝ)|=(2647641571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1075454391/2000000000 : ℝ)|^4133 ≤ (43834715252163/100000000000000 : ℝ)^3109
        have hw : |(1075454391/2000000000 : ℝ)|=(1075454391/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-218211889/1000000000 : ℝ)|^4133 ≤ (13216826827293/100000000000000 : ℝ)^3109
        have hw : |(-218211889/1000000000 : ℝ)|=(218211889/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_box_3 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (44827939/100000000 : ℝ)*x 0 + (432249161/1000000000 : ℝ)*x 1 + (2161245973/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (44827939/100000000 : ℝ)^4133 ≤ (17208803104267/50000000000000 : ℝ)^3109 := by
    have hnat : (44827939 : ℕ)^4133*50000000000000^3109 ≤ 17208803104267^3109*100000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44827939 100000000 17208803104267 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (432249161/1000000000 : ℝ)^4133 ≤ (32791195194229/100000000000000 : ℝ)^3109 := by
    have hnat : (432249161 : ℕ)^4133*100000000000000^3109 ≤ 32791195194229^3109*1000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432249161 1000000000 32791195194229 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2161245973/5000000000 : ℝ)^4133 ≤ (16395599291363/50000000000000 : ℝ)^3109 := by
    have hnat : (2161245973 : ℕ)^4133*50000000000000^3109 ≤ 16395599291363^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161245973 5000000000 16395599291363 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(44827939/100000000 : ℝ), (432249161/1000000000 : ℝ), (2161245973/5000000000 : ℝ)] ![(17208803104267/50000000000000 : ℝ), (32791195194229/100000000000000 : ℝ), (16395599291363/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(44827939/100000000 : ℝ)|^4133 ≤ (17208803104267/50000000000000 : ℝ)^3109
        have hw : |(44827939/100000000 : ℝ)|=(44827939/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(432249161/1000000000 : ℝ)|^4133 ≤ (32791195194229/100000000000000 : ℝ)^3109
        have hw : |(432249161/1000000000 : ℝ)|=(432249161/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2161245973/5000000000 : ℝ)|^4133 ≤ (16395599291363/50000000000000 : ℝ)^3109
        have hw : |(2161245973/5000000000 : ℝ)|=(2161245973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_box_4 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-291366427/1250000000 : ℝ)*x 0 + (2640097521/5000000000 : ℝ)*x 1 + (264009751/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (291366427/1250000000 : ℝ)^4133 ≤ (7214147113377/50000000000000 : ℝ)^3109 := by
    have hnat : (291366427 : ℕ)^4133*50000000000000^3109 ≤ 7214147113377^3109*1250000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      291366427 1250000000 7214147113377 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640097521/5000000000 : ℝ)^4133 ≤ (42785852995541/100000000000000 : ℝ)^3109 := by
    have hnat : (2640097521 : ℕ)^4133*100000000000000^3109 ≤ 42785852995541^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640097521 5000000000 42785852995541 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (264009751/500000000 : ℝ)^4133 ≤ (21392926379279/50000000000000 : ℝ)^3109 := by
    have hnat : (264009751 : ℕ)^4133*50000000000000^3109 ≤ 21392926379279^3109*500000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264009751 500000000 21392926379279 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-291366427/1250000000 : ℝ), (2640097521/5000000000 : ℝ), (264009751/500000000 : ℝ)] ![(7214147113377/50000000000000 : ℝ), (42785852995541/100000000000000 : ℝ), (21392926379279/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-291366427/1250000000 : ℝ)|^4133 ≤ (7214147113377/50000000000000 : ℝ)^3109
        have hw : |(-291366427/1250000000 : ℝ)|=(291366427/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640097521/5000000000 : ℝ)|^4133 ≤ (42785852995541/100000000000000 : ℝ)^3109
        have hw : |(2640097521/5000000000 : ℝ)|=(2640097521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(264009751/500000000 : ℝ)|^4133 ≤ (21392926379279/50000000000000 : ℝ)^3109
        have hw : |(264009751/500000000 : ℝ)|=(264009751/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_box_5 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2681987581/5000000000 : ℝ)*x 0 + (-444018771/2000000000 : ℝ)*x 1 + (5280195109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681987581/5000000000 : ℝ)^4133 ≤ (21845339669547/50000000000000 : ℝ)^3109 := by
    have hnat : (2681987581 : ℕ)^4133*50000000000000^3109 ≤ 21845339669547^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681987581 5000000000 21845339669547 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (444018771/2000000000 : ℝ)^4133 ≤ (1690433365901/12500000000000 : ℝ)^3109 := by
    have hnat : (444018771 : ℕ)^4133*12500000000000^3109 ≤ 1690433365901^3109*2000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      444018771 2000000000 1690433365901 12500000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5280195109/10000000000 : ℝ)^4133 ≤ (42785853717263/100000000000000 : ℝ)^3109 := by
    have hnat : (5280195109 : ℕ)^4133*100000000000000^3109 ≤ 42785853717263^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280195109 10000000000 42785853717263 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681987581/5000000000 : ℝ), (-444018771/2000000000 : ℝ), (5280195109/10000000000 : ℝ)] ![(21845339669547/50000000000000 : ℝ), (1690433365901/12500000000000 : ℝ), (42785853717263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681987581/5000000000 : ℝ)|^4133 ≤ (21845339669547/50000000000000 : ℝ)^3109
        have hw : |(2681987581/5000000000 : ℝ)|=(2681987581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-444018771/2000000000 : ℝ)|^4133 ≤ (1690433365901/12500000000000 : ℝ)^3109
        have hw : |(-444018771/2000000000 : ℝ)|=(444018771/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5280195109/10000000000 : ℝ)|^4133 ≤ (42785853717263/100000000000000 : ℝ)^3109
        have hw : |(5280195109/10000000000 : ℝ)|=(5280195109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_box_6 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2681987651/5000000000 : ℝ)*x 0 + (5280194939/10000000000 : ℝ)*x 1 + (-1110046947/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681987651/5000000000 : ℝ)^4133 ≤ (1365333776719/3125000000000 : ℝ)^3109 := by
    have hnat : (2681987651 : ℕ)^4133*3125000000000^3109 ≤ 1365333776719^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681987651 5000000000 1365333776719 3125000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5280194939/10000000000 : ℝ)^4133 ≤ (42785851886029/100000000000000 : ℝ)^3109 := by
    have hnat : (5280194939 : ℕ)^4133*100000000000000^3109 ≤ 42785851886029^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280194939 10000000000 42785851886029 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1110046947/5000000000 : ℝ)^4133 ≤ (13523467243019/100000000000000 : ℝ)^3109 := by
    have hnat : (1110046947 : ℕ)^4133*100000000000000^3109 ≤ 13523467243019^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1110046947 5000000000 13523467243019 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681987651/5000000000 : ℝ), (5280194939/10000000000 : ℝ), (-1110046947/5000000000 : ℝ)] ![(1365333776719/3125000000000 : ℝ), (42785851886029/100000000000000 : ℝ), (13523467243019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681987651/5000000000 : ℝ)|^4133 ≤ (1365333776719/3125000000000 : ℝ)^3109
        have hw : |(2681987651/5000000000 : ℝ)|=(2681987651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5280194939/10000000000 : ℝ)|^4133 ≤ (42785851886029/100000000000000 : ℝ)^3109
        have hw : |(5280194939/10000000000 : ℝ)|=(5280194939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1110046947/5000000000 : ℝ)|^4133 ≤ (13523467243019/100000000000000 : ℝ)^3109
        have hw : |(-1110046947/5000000000 : ℝ)|=(1110046947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_box_7 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4265850157/10000000000 : ℝ)*x 0 + (1107735559/2500000000 : ℝ)*x 1 + (443094227/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4265850157/10000000000 : ℝ)^4133 ≤ (32221213150943/100000000000000 : ℝ)^3109 := by
    have hnat : (4265850157 : ℕ)^4133*100000000000000^3109 ≤ 32221213150943^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4265850157 10000000000 32221213150943 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1107735559/2500000000 : ℝ)^4133 ≤ (33889393242689/100000000000000 : ℝ)^3109 := by
    have hnat : (1107735559 : ℕ)^4133*100000000000000^3109 ≤ 33889393242689^3109*2500000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107735559 2500000000 33889393242689 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (443094227/1000000000 : ℝ)^4133 ≤ (33889393588383/100000000000000 : ℝ)^3109 := by
    have hnat : (443094227 : ℕ)^4133*100000000000000^3109 ≤ 33889393588383^3109*1000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443094227 1000000000 33889393588383 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4265850157/10000000000 : ℝ), (1107735559/2500000000 : ℝ), (443094227/1000000000 : ℝ)] ![(32221213150943/100000000000000 : ℝ), (33889393242689/100000000000000 : ℝ), (33889393588383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4265850157/10000000000 : ℝ)|^4133 ≤ (32221213150943/100000000000000 : ℝ)^3109
        have hw : |(4265850157/10000000000 : ℝ)|=(4265850157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1107735559/2500000000 : ℝ)|^4133 ≤ (33889393242689/100000000000000 : ℝ)^3109
        have hw : |(1107735559/2500000000 : ℝ)|=(1107735559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(443094227/1000000000 : ℝ)|^4133 ≤ (33889393588383/100000000000000 : ℝ)^3109
        have hw : |(443094227/1000000000 : ℝ)|=(443094227/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_box_8 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2276681793/10000000000 : ℝ)*x 0 + (521430823/1000000000 : ℝ)*x 1 + (1077374841/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2276681793/10000000000 : ℝ)^4133 ≤ (3495902849427/25000000000000 : ℝ)^3109 := by
    have hnat : (2276681793 : ℕ)^4133*25000000000000^3109 ≤ 3495902849427^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2276681793 10000000000 3495902849427 25000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521430823/1000000000 : ℝ)^4133 ≤ (42077585134869/100000000000000 : ℝ)^3109 := by
    have hnat : (521430823 : ℕ)^4133*100000000000000^3109 ≤ 42077585134869^3109*1000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521430823 1000000000 42077585134869 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077374841/2000000000 : ℝ)^4133 ≤ (8787760691783/20000000000000 : ℝ)^3109 := by
    have hnat : (1077374841 : ℕ)^4133*20000000000000^3109 ≤ 8787760691783^3109*2000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077374841 2000000000 8787760691783 20000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2276681793/10000000000 : ℝ), (521430823/1000000000 : ℝ), (1077374841/2000000000 : ℝ)] ![(3495902849427/25000000000000 : ℝ), (42077585134869/100000000000000 : ℝ), (8787760691783/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2276681793/10000000000 : ℝ)|^4133 ≤ (3495902849427/25000000000000 : ℝ)^3109
        have hw : |(-2276681793/10000000000 : ℝ)|=(2276681793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521430823/1000000000 : ℝ)|^4133 ≤ (42077585134869/100000000000000 : ℝ)^3109
        have hw : |(521430823/1000000000 : ℝ)|=(521430823/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1077374841/2000000000 : ℝ)|^4133 ≤ (8787760691783/20000000000000 : ℝ)^3109
        have hw : |(1077374841/2000000000 : ℝ)|=(1077374841/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_box_9 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644242319/5000000000 : ℝ)*x 0 + (-2178292451/10000000000 : ℝ)*x 1 + (1077374827/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644242319/5000000000 : ℝ)^4133 ≤ (42875171307813/100000000000000 : ℝ)^3109 := by
    have hnat : (2644242319 : ℕ)^4133*100000000000000^3109 ≤ 42875171307813^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644242319 5000000000 42875171307813 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2178292451/10000000000 : ℝ)^4133 ≤ (13186025971321/100000000000000 : ℝ)^3109 := by
    have hnat : (2178292451 : ℕ)^4133*100000000000000^3109 ≤ 13186025971321^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178292451 10000000000 13186025971321 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077374827/2000000000 : ℝ)^4133 ≤ (21969401349947/50000000000000 : ℝ)^3109 := by
    have hnat : (1077374827 : ℕ)^4133*50000000000000^3109 ≤ 21969401349947^3109*2000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077374827 2000000000 21969401349947 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644242319/5000000000 : ℝ), (-2178292451/10000000000 : ℝ), (1077374827/2000000000 : ℝ)] ![(42875171307813/100000000000000 : ℝ), (13186025971321/100000000000000 : ℝ), (21969401349947/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644242319/5000000000 : ℝ)|^4133 ≤ (42875171307813/100000000000000 : ℝ)^3109
        have hw : |(2644242319/5000000000 : ℝ)|=(2644242319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2178292451/10000000000 : ℝ)|^4133 ≤ (13186025971321/100000000000000 : ℝ)^3109
        have hw : |(-2178292451/10000000000 : ℝ)|=(2178292451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1077374827/2000000000 : ℝ)|^4133 ≤ (21969401349947/50000000000000 : ℝ)^3109
        have hw : |(1077374827/2000000000 : ℝ)|=(1077374827/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_box_10 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5288484743/10000000000 : ℝ)*x 0 + (5386874163/10000000000 : ℝ)*x 1 + (-2178292273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288484743/10000000000 : ℝ)^4133 ≤ (21437586219727/50000000000000 : ℝ)^3109 := by
    have hnat : (5288484743 : ℕ)^4133*50000000000000^3109 ≤ 21437586219727^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288484743 10000000000 21437586219727 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386874163/10000000000 : ℝ)^4133 ≤ (43938803003503/100000000000000 : ℝ)^3109 := by
    have hnat : (5386874163 : ℕ)^4133*100000000000000^3109 ≤ 43938803003503^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386874163 10000000000 43938803003503 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2178292273/10000000000 : ℝ)^4133 ≤ (13186024538927/100000000000000 : ℝ)^3109 := by
    have hnat : (2178292273 : ℕ)^4133*100000000000000^3109 ≤ 13186024538927^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178292273 10000000000 13186024538927 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288484743/10000000000 : ℝ), (5386874163/10000000000 : ℝ), (-2178292273/10000000000 : ℝ)] ![(21437586219727/50000000000000 : ℝ), (43938803003503/100000000000000 : ℝ), (13186024538927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288484743/10000000000 : ℝ)|^4133 ≤ (21437586219727/50000000000000 : ℝ)^3109
        have hw : |(5288484743/10000000000 : ℝ)|=(5288484743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386874163/10000000000 : ℝ)|^4133 ≤ (43938803003503/100000000000000 : ℝ)^3109
        have hw : |(5386874163/10000000000 : ℝ)|=(5386874163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2178292273/10000000000 : ℝ)|^4133 ≤ (13186024538927/100000000000000 : ℝ)^3109
        have hw : |(-2178292273/10000000000 : ℝ)|=(2178292273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_box_11 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2251988613/5000000000 : ℝ)*x 0 + (269484969/625000000 : ℝ)*x 1 + (4311759681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2251988613/5000000000 : ℝ)^4133 ≤ (17316990884339/50000000000000 : ℝ)^3109 := by
    have hnat : (2251988613 : ℕ)^4133*50000000000000^3109 ≤ 17316990884339^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251988613 5000000000 17316990884339 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269484969/625000000 : ℝ)^4133 ≤ (32683008210411/100000000000000 : ℝ)^3109 := by
    have hnat : (269484969 : ℕ)^4133*100000000000000^3109 ≤ 32683008210411^3109*625000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269484969 625000000 32683008210411 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4311759681/10000000000 : ℝ)^4133 ≤ (16341504996981/50000000000000 : ℝ)^3109 := by
    have hnat : (4311759681 : ℕ)^4133*50000000000000^3109 ≤ 16341504996981^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4311759681 10000000000 16341504996981 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2251988613/5000000000 : ℝ), (269484969/625000000 : ℝ), (4311759681/10000000000 : ℝ)] ![(17316990884339/50000000000000 : ℝ), (32683008210411/100000000000000 : ℝ), (16341504996981/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2251988613/5000000000 : ℝ)|^4133 ≤ (17316990884339/50000000000000 : ℝ)^3109
        have hw : |(2251988613/5000000000 : ℝ)|=(2251988613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269484969/625000000 : ℝ)|^4133 ≤ (32683008210411/100000000000000 : ℝ)^3109
        have hw : |(269484969/625000000 : ℝ)|=(269484969/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4311759681/10000000000 : ℝ)|^4133 ≤ (16341504996981/50000000000000 : ℝ)^3109
        have hw : |(4311759681/10000000000 : ℝ)|=(4311759681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_box_12 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2125720377/10000000000 : ℝ)*x 0 + (5441829571/10000000000 : ℝ)*x 1 + (5272190199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2125720377/10000000000 : ℝ)^4133 ≤ (1595582613581/12500000000000 : ℝ)^3109 := by
    have hnat : (2125720377 : ℕ)^4133*12500000000000^3109 ≤ 1595582613581^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125720377 10000000000 1595582613581 12500000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5441829571/10000000000 : ℝ)^4133 ≤ (2783480776543/6250000000000 : ℝ)^3109 := by
    have hnat : (5441829571 : ℕ)^4133*6250000000000^3109 ≤ 2783480776543^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441829571 10000000000 2783480776543 6250000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272190199/10000000000 : ℝ)^4133 ≤ (21349823323067/50000000000000 : ℝ)^3109 := by
    have hnat : (5272190199 : ℕ)^4133*50000000000000^3109 ≤ 21349823323067^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272190199 10000000000 21349823323067 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2125720377/10000000000 : ℝ), (5441829571/10000000000 : ℝ), (5272190199/10000000000 : ℝ)] ![(1595582613581/12500000000000 : ℝ), (2783480776543/6250000000000 : ℝ), (21349823323067/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2125720377/10000000000 : ℝ)|^4133 ≤ (1595582613581/12500000000000 : ℝ)^3109
        have hw : |(-2125720377/10000000000 : ℝ)|=(2125720377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5441829571/10000000000 : ℝ)|^4133 ≤ (2783480776543/6250000000000 : ℝ)^3109
        have hw : |(5441829571/10000000000 : ℝ)|=(5441829571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272190199/10000000000 : ℝ)|^4133 ≤ (21349823323067/50000000000000 : ℝ)^3109
        have hw : |(5272190199/10000000000 : ℝ)|=(5272190199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_box_13 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1073927413/2000000000 : ℝ)*x 0 + (-1111583301/5000000000 : ℝ)*x 1 + (2636095179/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073927413/2000000000 : ℝ)^4133 ≤ (10937999216009/25000000000000 : ℝ)^3109 := by
    have hnat : (1073927413 : ℕ)^4133*25000000000000^3109 ≤ 10937999216009^3109*2000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073927413 2000000000 10937999216009 25000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1111583301/5000000000 : ℝ)^4133 ≤ (6774177381787/50000000000000 : ℝ)^3109 := by
    have hnat : (1111583301 : ℕ)^4133*50000000000000^3109 ≤ 6774177381787^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1111583301 5000000000 6774177381787 50000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2636095179/5000000000 : ℝ)^4133 ≤ (42699648358021/100000000000000 : ℝ)^3109 := by
    have hnat : (2636095179 : ℕ)^4133*100000000000000^3109 ≤ 42699648358021^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636095179 5000000000 42699648358021 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073927413/2000000000 : ℝ), (-1111583301/5000000000 : ℝ), (2636095179/5000000000 : ℝ)] ![(10937999216009/25000000000000 : ℝ), (6774177381787/50000000000000 : ℝ), (42699648358021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073927413/2000000000 : ℝ)|^4133 ≤ (10937999216009/25000000000000 : ℝ)^3109
        have hw : |(1073927413/2000000000 : ℝ)|=(1073927413/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1111583301/5000000000 : ℝ)|^4133 ≤ (6774177381787/50000000000000 : ℝ)^3109
        have hw : |(-1111583301/5000000000 : ℝ)|=(1111583301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2636095179/5000000000 : ℝ)|^4133 ≤ (42699648358021/100000000000000 : ℝ)^3109
        have hw : |(2636095179/5000000000 : ℝ)|=(2636095179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_box_14 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5369637171/10000000000 : ℝ)*x 0 + (2636095047/5000000000 : ℝ)*x 1 + (-2223166811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369637171/10000000000 : ℝ)^4133 ≤ (43751998012199/100000000000000 : ℝ)^3109 := by
    have hnat : (5369637171 : ℕ)^4133*100000000000000^3109 ≤ 43751998012199^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369637171 10000000000 43751998012199 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2636095047/5000000000 : ℝ)^4133 ≤ (42699645515643/100000000000000 : ℝ)^3109 := by
    have hnat : (2636095047 : ℕ)^4133*100000000000000^3109 ≤ 42699645515643^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636095047 5000000000 42699645515643 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2223166811/10000000000 : ℝ)^4133 ≤ (13548356456763/100000000000000 : ℝ)^3109 := by
    have hnat : (2223166811 : ℕ)^4133*100000000000000^3109 ≤ 13548356456763^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2223166811 10000000000 13548356456763 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369637171/10000000000 : ℝ), (2636095047/5000000000 : ℝ), (-2223166811/10000000000 : ℝ)] ![(43751998012199/100000000000000 : ℝ), (42699645515643/100000000000000 : ℝ), (13548356456763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369637171/10000000000 : ℝ)|^4133 ≤ (43751998012199/100000000000000 : ℝ)^3109
        have hw : |(5369637171/10000000000 : ℝ)|=(5369637171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2636095047/5000000000 : ℝ)|^4133 ≤ (42699645515643/100000000000000 : ℝ)^3109
        have hw : |(2636095047/5000000000 : ℝ)|=(2636095047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2223166811/10000000000 : ℝ)|^4133 ≤ (13548356456763/100000000000000 : ℝ)^3109
        have hw : |(-2223166811/10000000000 : ℝ)|=(2223166811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1073_box_15 (p : ℝ) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4247731643/10000000000 : ℝ)*x 0 + (2219939733/5000000000 : ℝ)*x 1 + (4439879907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4247731643/10000000000 : ℝ)^4133 ≤ (32039410847539/100000000000000 : ℝ)^3109 := by
    have hnat : (4247731643 : ℕ)^4133*100000000000000^3109 ≤ 32039410847539^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4247731643 10000000000 32039410847539 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2219939733/5000000000 : ℝ)^4133 ≤ (33980292323597/100000000000000 : ℝ)^3109 := by
    have hnat : (2219939733 : ℕ)^4133*100000000000000^3109 ≤ 33980292323597^3109*5000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2219939733 5000000000 33980292323597 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4439879907/10000000000 : ℝ)^4133 ≤ (33980296810423/100000000000000 : ℝ)^3109 := by
    have hnat : (4439879907 : ℕ)^4133*100000000000000^3109 ≤ 33980296810423^3109*10000000000^4133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4439879907 10000000000 33980296810423 100000000000000 4133 3109 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4133/1024 : ℝ)) 4133 3109 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4247731643/10000000000 : ℝ), (2219939733/5000000000 : ℝ), (4439879907/10000000000 : ℝ)] ![(32039410847539/100000000000000 : ℝ), (33980292323597/100000000000000 : ℝ), (33980296810423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4247731643/10000000000 : ℝ)|^4133 ≤ (32039410847539/100000000000000 : ℝ)^3109
        have hw : |(4247731643/10000000000 : ℝ)|=(4247731643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2219939733/5000000000 : ℝ)|^4133 ≤ (33980292323597/100000000000000 : ℝ)^3109
        have hw : |(2219939733/5000000000 : ℝ)|=(2219939733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4439879907/10000000000 : ℝ)|^4133 ≤ (33980296810423/100000000000000 : ℝ)^3109
        have hw : |(4439879907/10000000000 : ℝ)|=(4439879907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1073_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148129231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14007/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5631/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(2489/4000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29623/50000 : ℝ) ∧ (39797/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (10371/12500 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14007/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5631/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14007/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5631/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14007/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5631/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14007/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5631/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14007/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5631/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14007/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5631/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5631/50000 : ℝ) ^ (8265/2048 : ℝ) ≤ (14881865388969527/100000000000000000000 : ℝ) := by
    have hpowers : (5631/50000 : ℝ)^8265 ≤ (14881865388969527/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5631 : ℕ)^8265*100000000000000000000^2048 ≤ 14881865388969527^2048*50000^8265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5631 50000 14881865388969527 100000000000000000000 8265 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5631/50000 : ℝ)) (X := (14881865388969527/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14007/100000 : ℝ) ^ (8265/2048 : ℝ) ≤ (7177651740125557/20000000000000000000 : ℝ) := by
    have hpowers : (14007/100000 : ℝ)^8265 ≤ (7177651740125557/20000000000000000000 : ℝ)^2048 := by
      have hnat : (14007 : ℕ)^8265*20000000000000000000^2048 ≤ 7177651740125557^2048*100000^8265 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14007 100000 7177651740125557 20000000000000000000 8265 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14007/100000 : ℝ)) (X := (7177651740125557/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014881865388969527/50000000000000000000 : ℝ) ≤ (10000737438575109/10000000000000000 : ℝ) ^ (8265/2048 : ℝ) := by
    have hpowers : (50014881865388969527/50000000000000000000 : ℝ)^2048 ≤ (10000737438575109/10000000000000000 : ℝ)^8265 := by
      have hnat : (50014881865388969527 : ℕ)^2048*10000000000000000^8265 ≤ 10000737438575109^8265*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014881865388969527 50000000000000000000 10000737438575109 10000000000000000 2048 8265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000737438575109/10000000000000000 : ℝ)) (X := (50014881865388969527/50000000000000000000 : ℝ)) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (781646641594449979/781250000000000000 : ℝ) ≤ (62507861264801/62500000000000 : ℝ) ^ (8265/2048 : ℝ) := by
    have hpowers : (781646641594449979/781250000000000000 : ℝ)^2048 ≤ (62507861264801/62500000000000 : ℝ)^8265 := by
      have hnat : (781646641594449979 : ℕ)^2048*62500000000000^8265 ≤ 62507861264801^8265*781250000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781646641594449979 781250000000000000 62507861264801 62500000000000 2048 8265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (62507861264801/62500000000000 : ℝ)) (X := (781646641594449979/781250000000000000 : ℝ)) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007177651740125557/10000000000000000000 : ℝ) ≤ (10001778166161211/10000000000000000 : ℝ) ^ (8265/2048 : ℝ) := by
    have hpowers : (10007177651740125557/10000000000000000000 : ℝ)^2048 ≤ (10001778166161211/10000000000000000 : ℝ)^8265 := by
      have hnat : (10007177651740125557 : ℕ)^2048*10000000000000000^8265 ≤ 10001778166161211^8265*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007177651740125557 10000000000000000000 10001778166161211 10000000000000000 2048 8265 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001778166161211/10000000000000000 : ℝ)) (X := (10007177651740125557/10000000000000000000 : ℝ)) (by norm_num) 8265 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14881865388969527/100000000000000000000 : ℝ) ≤ ((9146767864937997827/9150000000000000000 : ℝ)+2*(520363793051/274500000000000 : ℝ)*(5631/50000 : ℝ))^(8265/2048 : ℝ) := by
    rw [show (9146767864937997827/9150000000000000000 : ℝ)+2*(520363793051/274500000000000 : ℝ)*(5631/50000 : ℝ)=(10000737438575109/10000000000000000 : ℝ) by norm_num, show 1+2*(14881865388969527/100000000000000000000 : ℝ)=(50014881865388969527/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7177651740125557/20000000000000000000 : ℝ)+(14881865388969527/100000000000000000000 : ℝ) ≤ ((9146767864937997827/9150000000000000000 : ℝ)+(520363793051/274500000000000 : ℝ)*((14007/100000 : ℝ)+(5631/50000 : ℝ)))^(8265/2048 : ℝ) := by
    rw [show (9146767864937997827/9150000000000000000 : ℝ)+(520363793051/274500000000000 : ℝ)*((14007/100000 : ℝ)+(5631/50000 : ℝ))=(62507861264801/62500000000000 : ℝ) by norm_num, show 1+(7177651740125557/20000000000000000000 : ℝ)+(14881865388969527/100000000000000000000 : ℝ)=(781646641594449979/781250000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7177651740125557/20000000000000000000 : ℝ) ≤ ((9146767864937997827/9150000000000000000 : ℝ)+2*(520363793051/274500000000000 : ℝ)*(14007/100000 : ℝ))^(8265/2048 : ℝ) := by
    rw [show (9146767864937997827/9150000000000000000 : ℝ)+2*(520363793051/274500000000000 : ℝ)*(14007/100000 : ℝ)=(10001778166161211/10000000000000000 : ℝ) by norm_num, show 1+2*(7177651740125557/20000000000000000000 : ℝ)=(10007177651740125557/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9146767864937997827/9150000000000000000 : ℝ)*(X 1 0+X 2 0)+(520363793051/274500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8265/2048 : ℝ)) (lo := (5631/50000 : ℝ)) (hi := (14007/100000 : ℝ)) (c := (9146767864937997827/9150000000000000000 : ℝ)) (alpha := (520363793051/274500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9146767864937997827/9150000000000000000 : ℝ)*(X 0 1+X 2 1)+(520363793051/274500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8265/2048 : ℝ)) (lo := (5631/50000 : ℝ)) (hi := (14007/100000 : ℝ)) (c := (9146767864937997827/9150000000000000000 : ℝ)) (alpha := (520363793051/274500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9146767864937997827/9150000000000000000 : ℝ)*(X 0 2+X 1 2)+(520363793051/274500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8265/2048 : ℝ)) (lo := (5631/50000 : ℝ)) (hi := (14007/100000 : ℝ)) (c := (9146767864937997827/9150000000000000000 : ℝ)) (alpha := (520363793051/274500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-414221369/2000000000 : ℝ)*X 0 0+(1075454579/2000000000 : ℝ)*X 0 1+(2688636189/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((264764139/500000000 : ℝ)*X 1 0+(-436423797/2000000000 : ℝ)*X 1 1+(1075454449/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2647641571/5000000000 : ℝ)*X 2 0+(1075454391/2000000000 : ℝ)*X 2 1+(-218211889/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((44827939/100000000 : ℝ)*X 0 0+(432249161/1000000000 : ℝ)*X 0 1+(2161245973/5000000000 : ℝ)*X 0 2+(44827939/100000000 : ℝ)*X 1 0+(432249161/1000000000 : ℝ)*X 1 1+(2161245973/5000000000 : ℝ)*X 1 2+(44827939/100000000 : ℝ)*X 2 0+(432249161/1000000000 : ℝ)*X 2 1+(2161245973/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-291366427/1250000000 : ℝ)*X 0 0+(2640097521/5000000000 : ℝ)*X 0 1+(264009751/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2681987581/5000000000 : ℝ)*X 1 0+(-444018771/2000000000 : ℝ)*X 1 1+(5280195109/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2681987651/5000000000 : ℝ)*X 2 0+(5280194939/10000000000 : ℝ)*X 2 1+(-1110046947/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4265850157/10000000000 : ℝ)*X 0 0+(1107735559/2500000000 : ℝ)*X 0 1+(443094227/1000000000 : ℝ)*X 0 2+(4265850157/10000000000 : ℝ)*X 1 0+(1107735559/2500000000 : ℝ)*X 1 1+(443094227/1000000000 : ℝ)*X 1 2+(4265850157/10000000000 : ℝ)*X 2 0+(1107735559/2500000000 : ℝ)*X 2 1+(443094227/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2276681793/10000000000 : ℝ)*X 0 0+(521430823/1000000000 : ℝ)*X 0 1+(1077374841/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2644242319/5000000000 : ℝ)*X 1 0+(-2178292451/10000000000 : ℝ)*X 1 1+(1077374827/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5288484743/10000000000 : ℝ)*X 2 0+(5386874163/10000000000 : ℝ)*X 2 1+(-2178292273/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2251988613/5000000000 : ℝ)*X 0 0+(269484969/625000000 : ℝ)*X 0 1+(4311759681/10000000000 : ℝ)*X 0 2+(2251988613/5000000000 : ℝ)*X 1 0+(269484969/625000000 : ℝ)*X 1 1+(4311759681/10000000000 : ℝ)*X 1 2+(2251988613/5000000000 : ℝ)*X 2 0+(269484969/625000000 : ℝ)*X 2 1+(4311759681/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2125720377/10000000000 : ℝ)*X 0 0+(5441829571/10000000000 : ℝ)*X 0 1+(5272190199/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1073927413/2000000000 : ℝ)*X 1 0+(-1111583301/5000000000 : ℝ)*X 1 1+(2636095179/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5369637171/10000000000 : ℝ)*X 2 0+(2636095047/5000000000 : ℝ)*X 2 1+(-2223166811/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4247731643/10000000000 : ℝ)*X 0 0+(2219939733/5000000000 : ℝ)*X 0 1+(4439879907/10000000000 : ℝ)*X 0 2+(4247731643/10000000000 : ℝ)*X 1 0+(2219939733/5000000000 : ℝ)*X 1 1+(4439879907/10000000000 : ℝ)*X 1 2+(4247731643/10000000000 : ℝ)*X 2 0+(2219939733/5000000000 : ℝ)*X 2 1+(4439879907/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1073_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-2489/4000 : ℝ) ≤ (-118611467425944901145305099/190625000000000000000000000 : ℝ) := by norm_num
    linear_combination (21323397/100000000000000 : ℝ)*(lower1) + (45532633/100000000000000 : ℝ)*(lower2) + (4267199/20000000000000 : ℝ)*(lower3) + (25304053/100000000000000 : ℝ)*(lower4) + (102301/400000000000 : ℝ)*(lower5) + (1931271174281771/50000000000000 : ℝ)*(major0) + (1931271174281771/50000000000000 : ℝ)*(major1) + (1931271174281771/50000000000000 : ℝ)*(major2) + (112689901/4000000000000 : ℝ)*(sp2) + (1284569113750147/25000000000000 : ℝ)*(sp4) + (80284676716733/1562500000000 : ℝ)*(sp5) + (5138273637753063/100000000000000 : ℝ)*(sp6) + (260754904517363/10000000000000 : ℝ)*(sp7) + (14286282419/25000000000000 : ℝ)*(sp13) + (260754904517363/10000000000000 : ℝ)*(f.failure) + (1284569113750147/25000000000000 : ℝ)*(f.sum) + (32311053331673/3431250000000000000000000000 : ℝ)*base65 + (8753569039223234851/1372500000000000000000000000000000 : ℝ)*base67 + (66795371849933234851/1372500000000000000000000000000000 : ℝ)*base69 + (68608446467481765149/1372500000000000000000000000000000 : ℝ)*base72 + (29323996117921/6862500000000000000000000000 : ℝ)*base73 + (2620135522926765149/1372500000000000000000000000000000 : ℝ)*base76 + (62046354918248234851/1372500000000000000000000000000000 : ℝ)*base77 + (2494514298186765149/1372500000000000000000000000000000 : ℝ)*base80 + (183055761462421/6862500000000000000000000000 : ℝ)*base81 + (12662147/1000000000000000000000 : ℝ)*base90 + (12662147/1000000000000000000000 : ℝ)*base92 + (12662147/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (29623/50000 : ℝ) ≤ (22588479702986083957414042928719/38125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (161800893/100000000000000 : ℝ)*(lower1) + (71933141/100000000000000 : ℝ)*(lower2) + (73814721/100000000000000 : ℝ)*(upper4) + (981395604078801/25000000000000 : ℝ)*(major0) + (981395604078801/25000000000000 : ℝ)*(major1) + (981395604078801/25000000000000 : ℝ)*(major2) + (1295324346375151/25000000000000 : ℝ)*(sp0) + (5181057107567547/100000000000000 : ℝ)*(sp1) + (5180995609193889/100000000000000 : ℝ)*(sp2) + (662524303256291/25000000000000 : ℝ)*(sp3) + (9312077369/100000000000000 : ℝ)*(sp7) + (1428947071/12500000000000 : ℝ)*(sp8) + (2013676077/800000000000 : ℝ)*(sp9) + (313207883283/100000000000000 : ℝ)*(sp10) + (2650106525102533/100000000000000 : ℝ)*(f.failure) + (1295327204269293/25000000000000 : ℝ)*(f.sum) + (47380361822293/4575000000000000000000000000 : ℝ)*base65 + (1445756307546465427/228750000000000000000000000000000 : ℝ)*base67 + (295499014663965427/228750000000000000000000000000000 : ℝ)*base69 + (2221021259275215427/228750000000000000000000000000000 : ℝ)*base71 + (1150638772291/2287500000000000000000000000 : ℝ)*base74 + (259187779971465427/228750000000000000000000000000000 : ℝ)*base75 + (2115844503336465427/228750000000000000000000000000000 : ℝ)*base77 + (1377928065756465427/228750000000000000000000000000000 : ℝ)*base79 + (10585554187907/4575000000000000000000000000 : ℝ)*base82 + (9442123/10000000000000000000000 : ℝ)*base89 + (9442123/10000000000000000000000 : ℝ)*base91 + (9442123/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (39797/50000 : ℝ) ≤ (60692532918516558200543648528597/76250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7629/12207031250 : ℝ)*(upper0) + (37046963/50000000000000 : ℝ)*(lower3) + (47355331/50000000000000 : ℝ)*(upper4) + (2196905754692489/50000000000000 : ℝ)*(major0) + (2196905754692489/50000000000000 : ℝ)*(major1) + (2196905754692489/50000000000000 : ℝ)*(major2) + (529121173/1000000000000 : ℝ)*(sp1) + (6420145087/6250000000000 : ℝ)*(sp2) + (10012699527/20000000000000 : ℝ)*(sp3) + (1619428389/100000000000000 : ℝ)*(sp4) + (724360952397689/12500000000000 : ℝ)*(sp8) + (5794836326492601/100000000000000 : ℝ)*(sp9) + (5794786516288509/100000000000000 : ℝ)*(sp10) + (1483075730917323/50000000000000 : ℝ)*(sp11) + (2966201525332281/100000000000000 : ℝ)*(f.failure) + (5794889238609901/100000000000000 : ℝ)*(f.sum) + (31972872932861/6862500000000000000000000000 : ℝ)*base66 + (13131592650179564209/1372500000000000000000000000000000 : ℝ)*base67 + (10267017029460435791/1372500000000000000000000000000000 : ℝ)*base70 + (563276722815435791/1372500000000000000000000000000000 : ℝ)*base72 + (59888015481203/13725000000000000000000000000 : ℝ)*base73 + (11665542722152064209/1372500000000000000000000000000000 : ℝ)*base75 + (12946193545342064209/1372500000000000000000000000000000 : ℝ)*base77 + (30800110118377064209/1372500000000000000000000000000000 : ℝ)*base79 + (64938765303397/13725000000000000000000000000 : ℝ)*base82 + (4005911/10000000000000000000000 : ℝ)*base89 + (4005911/10000000000000000000000 : ℝ)*base91 + (4005911/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-10371/12500 : ℝ) ≤ (-11861539660801015952213636280683/14296875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6930659/20000000000000 : ℝ)*(lower0) + (123288407/100000000000000 : ℝ)*(lower1) + (42454033/50000000000000 : ℝ)*(lower4) + (69193437992153/1562500000000 : ℝ)*(major0) + (69193437992153/1562500000000 : ℝ)*(major1) + (69193437992153/1562500000000 : ℝ)*(major2) + (42359789/390625000000 : ℝ)*(sp0) + (89641819851/50000000000000 : ℝ)*(sp5) + (439611763387/100000000000000 : ℝ)*(sp6) + (7631199381/100000000000000 : ℝ)*(sp7) + (5894866281402629/100000000000000 : ℝ)*(sp12) + (368418615116807/6250000000000 : ℝ)*(sp13) + (2947218756872613/50000000000000 : ℝ)*(sp14) + (29895306264439/1000000000000 : ℝ)*(sp15) + (1494769128821641/50000000000000 : ℝ)*(f.failure) + (2947438562754307/50000000000000 : ℝ)*(f.sum) + (5319534033001/1715625000000000000000000000 : ℝ)*base66 + (444883558509516359/21445312500000000000000000000000 : ℝ)*base67 + (158253426915656617/10722656250000000000000000000000 : ℝ)*base69 + (20186470814988373/2680664062500000000000000000000 : ℝ)*base71 + (172249468346471/6862500000000000000000000000 : ℝ)*base73 + (362347061947079593/42890625000000000000000000000000 : ℝ)*base75 + (163763277297375367/10722656250000000000000000000000 : ℝ)*base77 + (282032568874429871/5361328125000000000000000000000 : ℝ)*base79 + (9039359479271/6862500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (17488071/5000000000000000000000 : ℝ)*base89 + (17488071/5000000000000000000000 : ℝ)*base91 + (17488071/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1073_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148129231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14007/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5631/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2489/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(29623/50000 : ℝ) else (39797/50000 : ℝ) ≤ X j i ∧ X j i ≤ (10371/12500 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1073_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1073_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148129231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14007/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11261/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2489/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(29623/50000 : ℝ) else (39797/50000 : ℝ) ≤ X j i ∧ X j i ≤ (10371/12500 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1073_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1073_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8265/2048 : ℝ) ≤ p) (hpb : p ≤ (4133/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148129231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14007/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11261/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2489/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(29623/50000 : ℝ) else (39797/50000 : ℝ) ≤ X j i ∧ X j i ≤ (10371/12500 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1073_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
