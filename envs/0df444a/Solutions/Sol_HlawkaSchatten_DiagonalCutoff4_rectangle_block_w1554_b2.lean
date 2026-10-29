-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1554_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:11:19.741309+00:00
-- url     : https://prove2.me/submissions/029ebf07-a731-4b05-b68d-2c9bdf9ce4fa

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
theorem support_rectangle_w1554_box_0 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-800648373/5000000000 : ℝ)*x 0 + (1079661527/2000000000 : ℝ)*x 1 + (1349577119/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (800648373/5000000000 : ℝ)^4605 ≤ (948391470163/10000000000000 : ℝ)^3581 := by
    have hnat : (800648373 : ℕ)^4605*10000000000000^3581 ≤ 948391470163^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      800648373 5000000000 948391470163 10000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1079661527/2000000000 : ℝ)^4605 ≤ (45258038113637/100000000000000 : ℝ)^3581 := by
    have hnat : (1079661527 : ℕ)^4605*100000000000000^3581 ≤ 45258038113637^3581*2000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079661527 2000000000 45258038113637 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1349577119/2500000000 : ℝ)^4605 ≤ (45258047180549/100000000000000 : ℝ)^3581 := by
    have hnat : (1349577119 : ℕ)^4605*100000000000000^3581 ≤ 45258047180549^3581*2500000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349577119 2500000000 45258047180549 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-800648373/5000000000 : ℝ), (1079661527/2000000000 : ℝ), (1349577119/2500000000 : ℝ)] ![(948391470163/10000000000000 : ℝ), (45258038113637/100000000000000 : ℝ), (45258047180549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-800648373/5000000000 : ℝ)|^4605 ≤ (948391470163/10000000000000 : ℝ)^3581
        have hw : |(-800648373/5000000000 : ℝ)|=(800648373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1079661527/2000000000 : ℝ)|^4605 ≤ (45258038113637/100000000000000 : ℝ)^3581
        have hw : |(1079661527/2000000000 : ℝ)|=(1079661527/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1349577119/2500000000 : ℝ)|^4605 ≤ (45258047180549/100000000000000 : ℝ)^3581
        have hw : |(1349577119/2500000000 : ℝ)|=(1349577119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_box_1 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5271114471/10000000000 : ℝ)*x 0 + (-1778015973/10000000000 : ℝ)*x 1 + (107966161/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5271114471/10000000000 : ℝ)^4605 ≤ (43891400556359/100000000000000 : ℝ)^3581 := by
    have hnat : (5271114471 : ℕ)^4605*100000000000000^3581 ≤ 43891400556359^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271114471 10000000000 43891400556359 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1778015973/10000000000 : ℝ)^4605 ≤ (271263920941/2500000000000 : ℝ)^3581 := by
    have hnat : (1778015973 : ℕ)^4605*2500000000000^3581 ≤ 271263920941^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1778015973 10000000000 271263920941 2500000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (107966161/200000000 : ℝ)^4605 ≤ (45258042587797/100000000000000 : ℝ)^3581 := by
    have hnat : (107966161 : ℕ)^4605*100000000000000^3581 ≤ 45258042587797^3581*200000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107966161 200000000 45258042587797 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5271114471/10000000000 : ℝ), (-1778015973/10000000000 : ℝ), (107966161/200000000 : ℝ)] ![(43891400556359/100000000000000 : ℝ), (271263920941/2500000000000 : ℝ), (45258042587797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5271114471/10000000000 : ℝ)|^4605 ≤ (43891400556359/100000000000000 : ℝ)^3581
        have hw : |(5271114471/10000000000 : ℝ)|=(5271114471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1778015973/10000000000 : ℝ)|^4605 ≤ (271263920941/2500000000000 : ℝ)^3581
        have hw : |(-1778015973/10000000000 : ℝ)|=(1778015973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(107966161/200000000 : ℝ)|^4605 ≤ (45258042587797/100000000000000 : ℝ)^3581
        have hw : |(107966161/200000000 : ℝ)|=(107966161/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_box_2 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5271114017/10000000000 : ℝ)*x 0 + (2699154277/5000000000 : ℝ)*x 1 + (-1778015901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5271114017/10000000000 : ℝ)^4605 ≤ (8778279138999/20000000000000 : ℝ)^3581 := by
    have hnat : (5271114017 : ℕ)^4605*20000000000000^3581 ≤ 8778279138999^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271114017 10000000000 8778279138999 20000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2699154277/5000000000 : ℝ)^4605 ≤ (11314512005369/25000000000000 : ℝ)^3581 := by
    have hnat : (2699154277 : ℕ)^4605*25000000000000^3581 ≤ 11314512005369^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699154277 5000000000 11314512005369 25000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1778015901/10000000000 : ℝ)^4605 ≤ (10850556272607/100000000000000 : ℝ)^3581 := by
    have hnat : (1778015901 : ℕ)^4605*100000000000000^3581 ≤ 10850556272607^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1778015901 10000000000 10850556272607 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5271114017/10000000000 : ℝ), (2699154277/5000000000 : ℝ), (-1778015901/10000000000 : ℝ)] ![(8778279138999/20000000000000 : ℝ), (11314512005369/25000000000000 : ℝ), (10850556272607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5271114017/10000000000 : ℝ)|^4605 ≤ (8778279138999/20000000000000 : ℝ)^3581
        have hw : |(5271114017/10000000000 : ℝ)|=(5271114017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2699154277/5000000000 : ℝ)|^4605 ≤ (11314512005369/25000000000000 : ℝ)^3581
        have hw : |(2699154277/5000000000 : ℝ)|=(2699154277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1778015901/10000000000 : ℝ)|^4605 ≤ (10850556272607/100000000000000 : ℝ)^3581
        have hw : |(-1778015901/10000000000 : ℝ)|=(1778015901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_box_3 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4451902641/10000000000 : ℝ)*x 0 + (1039170871/2500000000 : ℝ)*x 1 + (1039170623/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4451902641/10000000000 : ℝ)^4605 ≤ (35322058731199/100000000000000 : ℝ)^3581 := by
    have hnat : (4451902641 : ℕ)^4605*100000000000000^3581 ≤ 35322058731199^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4451902641 10000000000 35322058731199 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1039170871/2500000000 : ℝ)^4605 ≤ (16169487794067/50000000000000 : ℝ)^3581 := by
    have hnat : (1039170871 : ℕ)^4605*50000000000000^3581 ≤ 16169487794067^3581*2500000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039170871 2500000000 16169487794067 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1039170623/2500000000 : ℝ)^4605 ≤ (1616948283173/5000000000000 : ℝ)^3581 := by
    have hnat : (1039170623 : ℕ)^4605*5000000000000^3581 ≤ 1616948283173^3581*2500000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039170623 2500000000 1616948283173 5000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4451902641/10000000000 : ℝ), (1039170871/2500000000 : ℝ), (1039170623/2500000000 : ℝ)] ![(35322058731199/100000000000000 : ℝ), (16169487794067/50000000000000 : ℝ), (1616948283173/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4451902641/10000000000 : ℝ)|^4605 ≤ (35322058731199/100000000000000 : ℝ)^3581
        have hw : |(4451902641/10000000000 : ℝ)|=(4451902641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1039170871/2500000000 : ℝ)|^4605 ≤ (16169487794067/50000000000000 : ℝ)^3581
        have hw : |(1039170871/2500000000 : ℝ)|=(1039170871/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1039170623/2500000000 : ℝ)|^4605 ≤ (1616948283173/5000000000000 : ℝ)^3581
        have hw : |(1039170623/2500000000 : ℝ)|=(1039170623/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_box_4 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2019524983/10000000000 : ℝ)*x 0 + (2622372137/5000000000 : ℝ)*x 1 + (1311186173/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2019524983/10000000000 : ℝ)^4605 ≤ (6390763114603/50000000000000 : ℝ)^3581 := by
    have hnat : (2019524983 : ℕ)^4605*50000000000000^3581 ≤ 6390763114603^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2019524983 10000000000 6390763114603 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622372137/5000000000 : ℝ)^4605 ≤ (272557716493/625000000000 : ℝ)^3581 := by
    have hnat : (2622372137 : ℕ)^4605*625000000000^3581 ≤ 272557716493^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622372137 5000000000 272557716493 625000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311186173/2500000000 : ℝ)^4605 ≤ (43609239108347/100000000000000 : ℝ)^3581 := by
    have hnat : (1311186173 : ℕ)^4605*100000000000000^3581 ≤ 43609239108347^3581*2500000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311186173 2500000000 43609239108347 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2019524983/10000000000 : ℝ), (2622372137/5000000000 : ℝ), (1311186173/2500000000 : ℝ)] ![(6390763114603/50000000000000 : ℝ), (272557716493/625000000000 : ℝ), (43609239108347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2019524983/10000000000 : ℝ)|^4605 ≤ (6390763114603/50000000000000 : ℝ)^3581
        have hw : |(-2019524983/10000000000 : ℝ)|=(2019524983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622372137/5000000000 : ℝ)|^4605 ≤ (272557716493/625000000000 : ℝ)^3581
        have hw : |(2622372137/5000000000 : ℝ)|=(2622372137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311186173/2500000000 : ℝ)|^4605 ≤ (43609239108347/100000000000000 : ℝ)^3581
        have hw : |(1311186173/2500000000 : ℝ)|=(1311186173/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_box_5 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2688843829/5000000000 : ℝ)*x 0 + (-368391409/2000000000 : ℝ)*x 1 + (5244744951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688843829/5000000000 : ℝ)^4605 ≤ (9007170685587/20000000000000 : ℝ)^3581 := by
    have hnat : (2688843829 : ℕ)^4605*20000000000000^3581 ≤ 9007170685587^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688843829 5000000000 9007170685587 20000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (368391409/2000000000 : ℝ)^4605 ≤ (11354904686523/100000000000000 : ℝ)^3581 := by
    have hnat : (368391409 : ℕ)^4605*100000000000000^3581 ≤ 11354904686523^3581*2000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      368391409 2000000000 11354904686523 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244744951/10000000000 : ℝ)^4605 ≤ (21804620938853/50000000000000 : ℝ)^3581 := by
    have hnat : (5244744951 : ℕ)^4605*50000000000000^3581 ≤ 21804620938853^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244744951 10000000000 21804620938853 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688843829/5000000000 : ℝ), (-368391409/2000000000 : ℝ), (5244744951/10000000000 : ℝ)] ![(9007170685587/20000000000000 : ℝ), (11354904686523/100000000000000 : ℝ), (21804620938853/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688843829/5000000000 : ℝ)|^4605 ≤ (9007170685587/20000000000000 : ℝ)^3581
        have hw : |(2688843829/5000000000 : ℝ)|=(2688843829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-368391409/2000000000 : ℝ)|^4605 ≤ (11354904686523/100000000000000 : ℝ)^3581
        have hw : |(-368391409/2000000000 : ℝ)|=(368391409/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244744951/10000000000 : ℝ)|^4605 ≤ (21804620938853/50000000000000 : ℝ)^3581
        have hw : |(5244744951/10000000000 : ℝ)|=(5244744951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_box_6 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1344422157/2500000000 : ℝ)*x 0 + (2622372087/5000000000 : ℝ)*x 1 + (-1841956773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344422157/2500000000 : ℝ)^4605 ≤ (11258965968543/25000000000000 : ℝ)^3581 := by
    have hnat : (1344422157 : ℕ)^4605*25000000000000^3581 ≤ 11258965968543^3581*2500000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344422157 2500000000 11258965968543 25000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622372087/5000000000 : ℝ)^4605 ≤ (4360923356963/10000000000000 : ℝ)^3581 := by
    have hnat : (2622372087 : ℕ)^4605*10000000000000^3581 ≤ 4360923356963^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622372087 5000000000 4360923356963 10000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1841956773/10000000000 : ℝ)^4605 ≤ (5677451265139/50000000000000 : ℝ)^3581 := by
    have hnat : (1841956773 : ℕ)^4605*50000000000000^3581 ≤ 5677451265139^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1841956773 10000000000 5677451265139 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1344422157/2500000000 : ℝ), (2622372087/5000000000 : ℝ), (-1841956773/10000000000 : ℝ)] ![(11258965968543/25000000000000 : ℝ), (4360923356963/10000000000000 : ℝ), (5677451265139/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1344422157/2500000000 : ℝ)|^4605 ≤ (11258965968543/25000000000000 : ℝ)^3581
        have hw : |(1344422157/2500000000 : ℝ)|=(1344422157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622372087/5000000000 : ℝ)|^4605 ≤ (4360923356963/10000000000000 : ℝ)^3581
        have hw : |(2622372087/5000000000 : ℝ)|=(2622372087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1841956773/10000000000 : ℝ)|^4605 ≤ (5677451265139/50000000000000 : ℝ)^3581
        have hw : |(-1841956773/10000000000 : ℝ)|=(1841956773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_box_7 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2023346021/5000000000 : ℝ)*x 0 + (27244749/62500000 : ℝ)*x 1 + (4359158331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2023346021/5000000000 : ℝ)^4605 ≤ (31242732681253/100000000000000 : ℝ)^3581 := by
    have hnat : (2023346021 : ℕ)^4605*100000000000000^3581 ≤ 31242732681253^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2023346021 5000000000 31242732681253 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27244749/62500000 : ℝ)^4605 ≤ (34378641299309/100000000000000 : ℝ)^3581 := by
    have hnat : (27244749 : ℕ)^4605*100000000000000^3581 ≤ 34378641299309^3581*62500000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27244749 62500000 34378641299309 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4359158331/10000000000 : ℝ)^4605 ≤ (8594656498867/25000000000000 : ℝ)^3581 := by
    have hnat : (4359158331 : ℕ)^4605*25000000000000^3581 ≤ 8594656498867^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359158331 10000000000 8594656498867 25000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2023346021/5000000000 : ℝ), (27244749/62500000 : ℝ), (4359158331/10000000000 : ℝ)] ![(31242732681253/100000000000000 : ℝ), (34378641299309/100000000000000 : ℝ), (8594656498867/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2023346021/5000000000 : ℝ)|^4605 ≤ (31242732681253/100000000000000 : ℝ)^3581
        have hw : |(2023346021/5000000000 : ℝ)|=(2023346021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(27244749/62500000 : ℝ)|^4605 ≤ (34378641299309/100000000000000 : ℝ)^3581
        have hw : |(27244749/62500000 : ℝ)|=(27244749/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4359158331/10000000000 : ℝ)|^4605 ≤ (8594656498867/25000000000000 : ℝ)^3581
        have hw : |(4359158331/10000000000 : ℝ)|=(4359158331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_box_8 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1930942741/10000000000 : ℝ)*x 0 + (5136718349/10000000000 : ℝ)*x 1 + (2709315741/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1930942741/10000000000 : ℝ)^4605 ≤ (47129473293/390625000000 : ℝ)^3581 := by
    have hnat : (1930942741 : ℕ)^4605*390625000000^3581 ≤ 47129473293^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1930942741 10000000000 47129473293 390625000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5136718349/10000000000 : ℝ)^4605 ≤ (42457585273049/100000000000000 : ℝ)^3581 := by
    have hnat : (5136718349 : ℕ)^4605*100000000000000^3581 ≤ 42457585273049^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5136718349 10000000000 42457585273049 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2709315741/5000000000 : ℝ)^4605 ≤ (355291168351/781250000000 : ℝ)^3581 := by
    have hnat : (2709315741 : ℕ)^4605*781250000000^3581 ≤ 355291168351^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709315741 5000000000 355291168351 781250000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1930942741/10000000000 : ℝ), (5136718349/10000000000 : ℝ), (2709315741/5000000000 : ℝ)] ![(47129473293/390625000000 : ℝ), (42457585273049/100000000000000 : ℝ), (355291168351/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1930942741/10000000000 : ℝ)|^4605 ≤ (47129473293/390625000000 : ℝ)^3581
        have hw : |(-1930942741/10000000000 : ℝ)|=(1930942741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5136718349/10000000000 : ℝ)|^4605 ≤ (42457585273049/100000000000000 : ℝ)^3581
        have hw : |(5136718349/10000000000 : ℝ)|=(5136718349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2709315741/5000000000 : ℝ)|^4605 ≤ (355291168351/781250000000 : ℝ)^3581
        have hw : |(2709315741/5000000000 : ℝ)|=(2709315741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_box_9 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1051401117/2000000000 : ℝ)*x 0 + (-1769317681/10000000000 : ℝ)*x 1 + (2709315959/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051401117/2000000000 : ℝ)^4605 ≤ (21870191282773/50000000000000 : ℝ)^3581 := by
    have hnat : (1051401117 : ℕ)^4605*50000000000000^3581 ≤ 21870191282773^3581*2000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051401117 2000000000 21870191282773 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1769317681/10000000000 : ℝ)^4605 ≤ (1078234316527/10000000000000 : ℝ)^3581 := by
    have hnat : (1769317681 : ℕ)^4605*10000000000000^3581 ≤ 1078234316527^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1769317681 10000000000 1078234316527 10000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2709315959/5000000000 : ℝ)^4605 ≤ (9095454850909/20000000000000 : ℝ)^3581 := by
    have hnat : (2709315959 : ℕ)^4605*20000000000000^3581 ≤ 9095454850909^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709315959 5000000000 9095454850909 20000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051401117/2000000000 : ℝ), (-1769317681/10000000000 : ℝ), (2709315959/5000000000 : ℝ)] ![(21870191282773/50000000000000 : ℝ), (1078234316527/10000000000000 : ℝ), (9095454850909/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051401117/2000000000 : ℝ)|^4605 ≤ (21870191282773/50000000000000 : ℝ)^3581
        have hw : |(1051401117/2000000000 : ℝ)|=(1051401117/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1769317681/10000000000 : ℝ)|^4605 ≤ (1078234316527/10000000000000 : ℝ)^3581
        have hw : |(-1769317681/10000000000 : ℝ)|=(1769317681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2709315959/5000000000 : ℝ)|^4605 ≤ (9095454850909/20000000000000 : ℝ)^3581
        have hw : |(2709315959/5000000000 : ℝ)|=(2709315959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_box_10 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1314251443/2500000000 : ℝ)*x 0 + (5418631171/10000000000 : ℝ)*x 1 + (-884659227/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314251443/2500000000 : ℝ)^4605 ≤ (2187019228319/5000000000000 : ℝ)^3581 := by
    have hnat : (1314251443 : ℕ)^4605*5000000000000^3581 ≤ 2187019228319^3581*2500000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314251443 2500000000 2187019228319 5000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5418631171/10000000000 : ℝ)^4605 ≤ (22738633096199/50000000000000 : ℝ)^3581 := by
    have hnat : (5418631171 : ℕ)^4605*50000000000000^3581 ≤ 22738633096199^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418631171 10000000000 22738633096199 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (884659227/5000000000 : ℝ)^4605 ≤ (1347793652879/12500000000000 : ℝ)^3581 := by
    have hnat : (884659227 : ℕ)^4605*12500000000000^3581 ≤ 1347793652879^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884659227 5000000000 1347793652879 12500000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314251443/2500000000 : ℝ), (5418631171/10000000000 : ℝ), (-884659227/5000000000 : ℝ)] ![(2187019228319/5000000000000 : ℝ), (22738633096199/50000000000000 : ℝ), (1347793652879/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314251443/2500000000 : ℝ)|^4605 ≤ (2187019228319/5000000000000 : ℝ)^3581
        have hw : |(1314251443/2500000000 : ℝ)|=(1314251443/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5418631171/10000000000 : ℝ)|^4605 ≤ (22738633096199/50000000000000 : ℝ)^3581
        have hw : |(5418631171/10000000000 : ℝ)|=(5418631171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-884659227/5000000000 : ℝ)|^4605 ≤ (1347793652879/12500000000000 : ℝ)^3581
        have hw : |(-884659227/5000000000 : ℝ)|=(884659227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_box_11 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2252190587/5000000000 : ℝ)*x 0 + (2064927203/5000000000 : ℝ)*x 1 + (165194147/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2252190587/5000000000 : ℝ)^4605 ≤ (35858394364149/100000000000000 : ℝ)^3581 := by
    have hnat : (2252190587 : ℕ)^4605*100000000000000^3581 ≤ 35858394364149^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252190587 5000000000 35858394364149 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2064927203/5000000000 : ℝ)^4605 ≤ (32070806460793/100000000000000 : ℝ)^3581 := by
    have hnat : (2064927203 : ℕ)^4605*100000000000000^3581 ≤ 32070806460793^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064927203 5000000000 32070806460793 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (165194147/400000000 : ℝ)^4605 ≤ (32070799160877/100000000000000 : ℝ)^3581 := by
    have hnat : (165194147 : ℕ)^4605*100000000000000^3581 ≤ 32070799160877^3581*400000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165194147 400000000 32070799160877 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2252190587/5000000000 : ℝ), (2064927203/5000000000 : ℝ), (165194147/400000000 : ℝ)] ![(35858394364149/100000000000000 : ℝ), (32070806460793/100000000000000 : ℝ), (32070799160877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2252190587/5000000000 : ℝ)|^4605 ≤ (35858394364149/100000000000000 : ℝ)^3581
        have hw : |(2252190587/5000000000 : ℝ)|=(2252190587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2064927203/5000000000 : ℝ)|^4605 ≤ (32070806460793/100000000000000 : ℝ)^3581
        have hw : |(2064927203/5000000000 : ℝ)|=(2064927203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(165194147/400000000 : ℝ)|^4605 ≤ (32070799160877/100000000000000 : ℝ)^3581
        have hw : |(165194147/400000000 : ℝ)|=(165194147/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_box_12 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-422403689/2500000000 : ℝ)*x 0 + (687874303/1250000000 : ℝ)*x 1 + (5229696683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (422403689/2500000000 : ℝ)^4605 ≤ (10161802984337/100000000000000 : ℝ)^3581 := by
    have hnat : (422403689 : ℕ)^4605*100000000000000^3581 ≤ 10161802984337^3581*2500000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422403689 2500000000 10161802984337 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (687874303/1250000000 : ℝ)^4605 ≤ (4638979275143/10000000000000 : ℝ)^3581 := by
    have hnat : (687874303 : ℕ)^4605*10000000000000^3581 ≤ 4638979275143^3581*1250000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      687874303 1250000000 4638979275143 10000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5229696683/10000000000 : ℝ)^4605 ≤ (10862101061031/25000000000000 : ℝ)^3581 := by
    have hnat : (5229696683 : ℕ)^4605*25000000000000^3581 ≤ 10862101061031^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229696683 10000000000 10862101061031 25000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-422403689/2500000000 : ℝ), (687874303/1250000000 : ℝ), (5229696683/10000000000 : ℝ)] ![(10161802984337/100000000000000 : ℝ), (4638979275143/10000000000000 : ℝ), (10862101061031/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-422403689/2500000000 : ℝ)|^4605 ≤ (10161802984337/100000000000000 : ℝ)^3581
        have hw : |(-422403689/2500000000 : ℝ)|=(422403689/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(687874303/1250000000 : ℝ)|^4605 ≤ (4638979275143/10000000000000 : ℝ)^3581
        have hw : |(687874303/1250000000 : ℝ)|=(687874303/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5229696683/10000000000 : ℝ)|^4605 ≤ (10862101061031/25000000000000 : ℝ)^3581
        have hw : |(5229696683/10000000000 : ℝ)|=(5229696683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_box_13 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (336758271/625000000 : ℝ)*x 0 + (-231006279/1250000000 : ℝ)*x 1 + (5229696549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (336758271/625000000 : ℝ)^4605 ≤ (45148366690973/100000000000000 : ℝ)^3581 := by
    have hnat : (336758271 : ℕ)^4605*100000000000000^3581 ≤ 45148366690973^3581*625000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336758271 625000000 45148366690973 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (231006279/1250000000 : ℝ)^4605 ≤ (456129219283/4000000000000 : ℝ)^3581 := by
    have hnat : (231006279 : ℕ)^4605*4000000000000^3581 ≤ 456129219283^3581*1250000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      231006279 1250000000 456129219283 4000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5229696549/10000000000 : ℝ)^4605 ≤ (8689680562501/20000000000000 : ℝ)^3581 := by
    have hnat : (5229696549 : ℕ)^4605*20000000000000^3581 ≤ 8689680562501^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229696549 10000000000 8689680562501 20000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(336758271/625000000 : ℝ), (-231006279/1250000000 : ℝ), (5229696549/10000000000 : ℝ)] ![(45148366690973/100000000000000 : ℝ), (456129219283/4000000000000 : ℝ), (8689680562501/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(336758271/625000000 : ℝ)|^4605 ≤ (45148366690973/100000000000000 : ℝ)^3581
        have hw : |(336758271/625000000 : ℝ)|=(336758271/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-231006279/1250000000 : ℝ)|^4605 ≤ (456129219283/4000000000000 : ℝ)^3581
        have hw : |(-231006279/1250000000 : ℝ)|=(231006279/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5229696549/10000000000 : ℝ)|^4605 ≤ (8689680562501/20000000000000 : ℝ)^3581
        have hw : |(5229696549/10000000000 : ℝ)|=(5229696549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_box_14 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5388131927/10000000000 : ℝ)*x 0 + (653712121/1250000000 : ℝ)*x 1 + (-1848050223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5388131927/10000000000 : ℝ)^4605 ≤ (22574181141939/50000000000000 : ℝ)^3581 := by
    have hnat : (5388131927 : ℕ)^4605*50000000000000^3581 ≤ 22574181141939^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388131927 10000000000 22574181141939 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (653712121/1250000000 : ℝ)^4605 ≤ (8689681457797/20000000000000 : ℝ)^3581 := by
    have hnat : (653712121 : ℕ)^4605*20000000000000^3581 ≤ 8689681457797^3581*1250000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653712121 1250000000 8689681457797 20000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1848050223/10000000000 : ℝ)^4605 ≤ (11403230410661/100000000000000 : ℝ)^3581 := by
    have hnat : (1848050223 : ℕ)^4605*100000000000000^3581 ≤ 11403230410661^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1848050223 10000000000 11403230410661 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5388131927/10000000000 : ℝ), (653712121/1250000000 : ℝ), (-1848050223/10000000000 : ℝ)] ![(22574181141939/50000000000000 : ℝ), (8689681457797/20000000000000 : ℝ), (11403230410661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5388131927/10000000000 : ℝ)|^4605 ≤ (22574181141939/50000000000000 : ℝ)^3581
        have hw : |(5388131927/10000000000 : ℝ)|=(5388131927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(653712121/1250000000 : ℝ)|^4605 ≤ (8689681457797/20000000000000 : ℝ)^3581
        have hw : |(653712121/1250000000 : ℝ)|=(653712121/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1848050223/10000000000 : ℝ)|^4605 ≤ (11403230410661/100000000000000 : ℝ)^3581
        have hw : |(-1848050223/10000000000 : ℝ)|=(1848050223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_box_15 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4006122111/10000000000 : ℝ)*x 0 + (4378975749/10000000000 : ℝ)*x 1 + (2189487891/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4006122111/10000000000 : ℝ)^4605 ≤ (3855065206149/12500000000000 : ℝ)^3581 := by
    have hnat : (4006122111 : ℕ)^4605*12500000000000^3581 ≤ 3855065206149^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4006122111 10000000000 3855065206149 12500000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4378975749/10000000000 : ℝ)^4605 ≤ (8644934749293/25000000000000 : ℝ)^3581 := by
    have hnat : (4378975749 : ℕ)^4605*25000000000000^3581 ≤ 8644934749293^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4378975749 10000000000 8644934749293 25000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2189487891/5000000000 : ℝ)^4605 ≤ (34579739332283/100000000000000 : ℝ)^3581 := by
    have hnat : (2189487891 : ℕ)^4605*100000000000000^3581 ≤ 34579739332283^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189487891 5000000000 34579739332283 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4006122111/10000000000 : ℝ), (4378975749/10000000000 : ℝ), (2189487891/5000000000 : ℝ)] ![(3855065206149/12500000000000 : ℝ), (8644934749293/25000000000000 : ℝ), (34579739332283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4006122111/10000000000 : ℝ)|^4605 ≤ (3855065206149/12500000000000 : ℝ)^3581
        have hw : |(4006122111/10000000000 : ℝ)|=(4006122111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4378975749/10000000000 : ℝ)|^4605 ≤ (8644934749293/25000000000000 : ℝ)^3581
        have hw : |(4378975749/10000000000 : ℝ)|=(4378975749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2189487891/5000000000 : ℝ)|^4605 ≤ (34579739332283/100000000000000 : ℝ)^3581
        have hw : |(2189487891/5000000000 : ℝ)|=(2189487891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1554_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41685679/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2767/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(63801/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29413/50000 : ℝ) ∧ (80759/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (86267/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2767/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2767/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2767/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2767/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2767/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2767/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2767/25000 : ℝ) ^ (4603/1024 : ℝ) ≤ (315397920477377/6250000000000000000 : ℝ) := by
    have hpowers : (2767/25000 : ℝ)^4603 ≤ (315397920477377/6250000000000000000 : ℝ)^1024 := by
      have hnat : (2767 : ℕ)^4603*6250000000000000000^1024 ≤ 315397920477377^1024*25000^4603 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2767 25000 315397920477377 6250000000000000000 4603 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2767/25000 : ℝ)) (X := (315397920477377/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4603 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3097/20000 : ℝ) ^ (4603/1024 : ℝ) ≤ (2283263085487429/10000000000000000000 : ℝ) := by
    have hpowers : (3097/20000 : ℝ)^4603 ≤ (2283263085487429/10000000000000000000 : ℝ)^1024 := by
      have hnat : (3097 : ℕ)^4603*10000000000000000000^1024 ≤ 2283263085487429^1024*20000^4603 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3097 20000 2283263085487429 10000000000000000000 4603 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3097/20000 : ℝ)) (X := (2283263085487429/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4603 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125315397920477377/3125000000000000000 : ℝ) ≤ (10000224517783319/10000000000000000 : ℝ) ^ (4603/1024 : ℝ) := by
    have hpowers : (3125315397920477377/3125000000000000000 : ℝ)^1024 ≤ (10000224517783319/10000000000000000 : ℝ)^4603 := by
      have hnat : (3125315397920477377 : ℕ)^1024*10000000000000000^4603 ≤ 10000224517783319^4603*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125315397920477377 3125000000000000000 10000224517783319 10000000000000000 1024 4603 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000224517783319/10000000000000000 : ℝ)) (X := (3125315397920477377/3125000000000000000 : ℝ)) (by norm_num) 4603 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50013939498791256161/50000000000000000000 : ℝ) ≤ (2500155034759177/2500000000000000 : ℝ) ^ (4603/1024 : ℝ) := by
    have hpowers : (50013939498791256161/50000000000000000000 : ℝ)^1024 ≤ (2500155034759177/2500000000000000 : ℝ)^4603 := by
      have hnat : (50013939498791256161 : ℕ)^1024*2500000000000000^4603 ≤ 2500155034759177^4603*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013939498791256161 50000000000000000000 2500155034759177 2500000000000000 1024 4603 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500155034759177/2500000000000000 : ℝ)) (X := (50013939498791256161/50000000000000000000 : ℝ)) (by norm_num) 4603 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5002283263085487429/5000000000000000000 : ℝ) ≤ (10001015760290097/10000000000000000 : ℝ) ^ (4603/1024 : ℝ) := by
    have hpowers : (5002283263085487429/5000000000000000000 : ℝ)^1024 ≤ (10001015760290097/10000000000000000 : ℝ)^4603 := by
      have hnat : (5002283263085487429 : ℕ)^1024*10000000000000000^4603 ≤ 10001015760290097^4603*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002283263085487429 5000000000000000000 10001015760290097 10000000000000000 1024 4603 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001015760290097/10000000000000000 : ℝ)) (X := (5002283263085487429/5000000000000000000 : ℝ)) (by norm_num) 4603 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(315397920477377/6250000000000000000 : ℝ) ≤ ((44162234222983901119/44170000000000000000 : ℝ)+2*(395621253389/441700000000000 : ℝ)*(2767/25000 : ℝ))^(4603/1024 : ℝ) := by
    rw [show (44162234222983901119/44170000000000000000 : ℝ)+2*(395621253389/441700000000000 : ℝ)*(2767/25000 : ℝ)=(10000224517783319/10000000000000000 : ℝ) by norm_num, show 1+2*(315397920477377/6250000000000000000 : ℝ)=(3125315397920477377/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2283263085487429/10000000000000000000 : ℝ)+(315397920477377/6250000000000000000 : ℝ) ≤ ((44162234222983901119/44170000000000000000 : ℝ)+(395621253389/441700000000000 : ℝ)*((3097/20000 : ℝ)+(2767/25000 : ℝ)))^(4603/1024 : ℝ) := by
    rw [show (44162234222983901119/44170000000000000000 : ℝ)+(395621253389/441700000000000 : ℝ)*((3097/20000 : ℝ)+(2767/25000 : ℝ))=(2500155034759177/2500000000000000 : ℝ) by norm_num, show 1+(2283263085487429/10000000000000000000 : ℝ)+(315397920477377/6250000000000000000 : ℝ)=(50013939498791256161/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2283263085487429/10000000000000000000 : ℝ) ≤ ((44162234222983901119/44170000000000000000 : ℝ)+2*(395621253389/441700000000000 : ℝ)*(3097/20000 : ℝ))^(4603/1024 : ℝ) := by
    rw [show (44162234222983901119/44170000000000000000 : ℝ)+2*(395621253389/441700000000000 : ℝ)*(3097/20000 : ℝ)=(10001015760290097/10000000000000000 : ℝ) by norm_num, show 1+2*(2283263085487429/10000000000000000000 : ℝ)=(5002283263085487429/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (44162234222983901119/44170000000000000000 : ℝ)*(X 1 0+X 2 0)+(395621253389/441700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4603/1024 : ℝ)) (lo := (2767/25000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (44162234222983901119/44170000000000000000 : ℝ)) (alpha := (395621253389/441700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (44162234222983901119/44170000000000000000 : ℝ)*(X 0 1+X 2 1)+(395621253389/441700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4603/1024 : ℝ)) (lo := (2767/25000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (44162234222983901119/44170000000000000000 : ℝ)) (alpha := (395621253389/441700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (44162234222983901119/44170000000000000000 : ℝ)*(X 0 2+X 1 2)+(395621253389/441700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4603/1024 : ℝ)) (lo := (2767/25000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (44162234222983901119/44170000000000000000 : ℝ)) (alpha := (395621253389/441700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-800648373/5000000000 : ℝ)*X 0 0+(1079661527/2000000000 : ℝ)*X 0 1+(1349577119/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5271114471/10000000000 : ℝ)*X 1 0+(-1778015973/10000000000 : ℝ)*X 1 1+(107966161/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5271114017/10000000000 : ℝ)*X 2 0+(2699154277/5000000000 : ℝ)*X 2 1+(-1778015901/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4451902641/10000000000 : ℝ)*X 0 0+(1039170871/2500000000 : ℝ)*X 0 1+(1039170623/2500000000 : ℝ)*X 0 2+(4451902641/10000000000 : ℝ)*X 1 0+(1039170871/2500000000 : ℝ)*X 1 1+(1039170623/2500000000 : ℝ)*X 1 2+(4451902641/10000000000 : ℝ)*X 2 0+(1039170871/2500000000 : ℝ)*X 2 1+(1039170623/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2019524983/10000000000 : ℝ)*X 0 0+(2622372137/5000000000 : ℝ)*X 0 1+(1311186173/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2688843829/5000000000 : ℝ)*X 1 0+(-368391409/2000000000 : ℝ)*X 1 1+(5244744951/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1344422157/2500000000 : ℝ)*X 2 0+(2622372087/5000000000 : ℝ)*X 2 1+(-1841956773/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2023346021/5000000000 : ℝ)*X 0 0+(27244749/62500000 : ℝ)*X 0 1+(4359158331/10000000000 : ℝ)*X 0 2+(2023346021/5000000000 : ℝ)*X 1 0+(27244749/62500000 : ℝ)*X 1 1+(4359158331/10000000000 : ℝ)*X 1 2+(2023346021/5000000000 : ℝ)*X 2 0+(27244749/62500000 : ℝ)*X 2 1+(4359158331/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1930942741/10000000000 : ℝ)*X 0 0+(5136718349/10000000000 : ℝ)*X 0 1+(2709315741/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1051401117/2000000000 : ℝ)*X 1 0+(-1769317681/10000000000 : ℝ)*X 1 1+(2709315959/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1314251443/2500000000 : ℝ)*X 2 0+(5418631171/10000000000 : ℝ)*X 2 1+(-884659227/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2252190587/5000000000 : ℝ)*X 0 0+(2064927203/5000000000 : ℝ)*X 0 1+(165194147/400000000 : ℝ)*X 0 2+(2252190587/5000000000 : ℝ)*X 1 0+(2064927203/5000000000 : ℝ)*X 1 1+(165194147/400000000 : ℝ)*X 1 2+(2252190587/5000000000 : ℝ)*X 2 0+(2064927203/5000000000 : ℝ)*X 2 1+(165194147/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-422403689/2500000000 : ℝ)*X 0 0+(687874303/1250000000 : ℝ)*X 0 1+(5229696683/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((336758271/625000000 : ℝ)*X 1 0+(-231006279/1250000000 : ℝ)*X 1 1+(5229696549/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5388131927/10000000000 : ℝ)*X 2 0+(653712121/1250000000 : ℝ)*X 2 1+(-1848050223/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4006122111/10000000000 : ℝ)*X 0 0+(4378975749/10000000000 : ℝ)*X 0 1+(2189487891/5000000000 : ℝ)*X 0 2+(4006122111/10000000000 : ℝ)*X 1 0+(4378975749/10000000000 : ℝ)*X 1 1+(2189487891/5000000000 : ℝ)*X 1 2+(4006122111/10000000000 : ℝ)*X 2 0+(4378975749/10000000000 : ℝ)*X 2 1+(2189487891/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-63801/100000 : ℝ) ≤ (-1408999448178164526738295905079713/2208500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17279423/100000000000000 : ℝ)*(lower0) + (9764789/20000000000000 : ℝ)*(upper1) + (63600479/25000000000000 : ℝ)*(lower2) + (19235409/100000000000000 : ℝ)*(lower5) + (2284711039365497/100000000000000 : ℝ)*(major0) + (2284711039365497/100000000000000 : ℝ)*(major1) + (2284711039365497/100000000000000 : ℝ)*(major2) + (1056171499/100000000000000 : ℝ)*(sp3) + (1610242091788183/50000000000000 : ℝ)*(sp4) + (3220431467107259/100000000000000 : ℝ)*(sp5) + (3220486983726829/100000000000000 : ℝ)*(sp6) + (1370200350026957/100000000000000 : ℝ)*(sp7) + (2800150463/100000000000000 : ℝ)*(sp8) + (5551661957/10000000000000 : ℝ)*(sp13) + (171275175774807/12500000000000 : ℝ)*(f.failure) + (3220486983726829/100000000000000 : ℝ)*(f.sum) + (67242911510987/22085000000000000000000000000 : ℝ)*base66 + (30351706838857408857/4417000000000000000000000000000000 : ℝ)*base68 + (42587885390839408857/4417000000000000000000000000000000 : ℝ)*base70 + (28335906096433408857/4417000000000000000000000000000000 : ℝ)*base72 + (11373678109937/5521250000000000000000000000 : ℝ)*base73 + (17352406257856408857/4417000000000000000000000000000000 : ℝ)*base76 + (24616242930823408857/4417000000000000000000000000000000 : ℝ)*base78 + (54786861685232408857/4417000000000000000000000000000000 : ℝ)*base80 + (82845704619403/22085000000000000000000000000 : ℝ)*base81 + (2763953/312500000000000000000 : ℝ)*base89 + (2763953/312500000000000000000 : ℝ)*base91 + (2763953/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (29413/50000 : ℝ) ≤ (129923342989998441631552910934861/220850000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (35009203/50000000000000 : ℝ)*(upper1) + (74366371/50000000000000 : ℝ)*(upper3) + (1175579/10000000000000 : ℝ)*(upper5) + (236384582471473/10000000000000 : ℝ)*(major0) + (236384582471473/10000000000000 : ℝ)*(major1) + (236384582471473/10000000000000 : ℝ)*(major2) + (1645205334539051/50000000000000 : ℝ)*(sp0) + (205650191833831/6250000000000 : ℝ)*(sp1) + (329040985142489/10000000000000 : ℝ)*(sp2) + (708830246607827/50000000000000 : ℝ)*(sp3) + (11585375981/100000000000000 : ℝ)*(sp6) + (128742027/100000000000000 : ℝ)*(sp7) + (734698383/4000000000000 : ℝ)*(sp9) + (672982673/6250000000000 : ℝ)*(sp12) + (708830310978841/50000000000000 : ℝ)*(f.failure) + (329042143680087/10000000000000 : ℝ)*(f.sum) + (4240607795889/2208500000000000000000000000 : ℝ)*base65 + (2122814843300621713/441700000000000000000000000000000 : ℝ)*base68 + (1801084888568278287/441700000000000000000000000000000 : ℝ)*base69 + (3493323158526321713/441700000000000000000000000000000 : ℝ)*base72 + (4067232469033/4417000000000000000000000000 : ℝ)*base73 + (10786068304666478287/441700000000000000000000000000000 : ℝ)*base75 + (3232502138498221713/441700000000000000000000000000000 : ℝ)*base78 + (4245200725079021713/441700000000000000000000000000000 : ℝ)*base80 + (11123626919483/220850000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (16718039/1250000000000000000000 : ℝ)*base89 + (16718039/1250000000000000000000 : ℝ)*base91 + (16718039/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (80759/100000 : ℝ) ≤ (1783610383934191826409537828644079/2208500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1669531/10000000000000 : ℝ)*(upper0) + (23136881/10000000000000 : ℝ)*(upper1) + (105858871/50000000000000 : ℝ)*(upper2) + (2552447785145947/100000000000000 : ℝ)*(major0) + (2552447785145947/100000000000000 : ℝ)*(major1) + (2552447785145947/100000000000000 : ℝ)*(major2) + (55481982801/20000000000000 : ℝ)*(sp1) + (80338844353/100000000000000 : ℝ)*(sp2) + (4086199937/50000000000000 : ℝ)*(sp3) + (1277967259/12500000000000 : ℝ)*(sp4) + (3547194770617307/100000000000000 : ℝ)*(sp8) + (1773463792220687/50000000000000 : ℝ)*(sp9) + (1773562327755513/50000000000000 : ℝ)*(sp10) + (30615240287491/2000000000000 : ℝ)*(sp11) + (191346273346803/12500000000000 : ℝ)*(f.failure) + (3547204994355379/100000000000000 : ℝ)*(f.sum) + (9286449849913/5521250000000000000000000000 : ℝ)*base66 + (9203947224709085307/4417000000000000000000000000000000 : ℝ)*base68 + (4086569458082085307/4417000000000000000000000000000000 : ℝ)*base70 + (3954850202673085307/4417000000000000000000000000000000 : ℝ)*base72 + (28491218936981/11042500000000000000000000000 : ℝ)*base74 + (2314357964989914693/4417000000000000000000000000000000 : ℝ)*base75 + (8933241750649085307/4417000000000000000000000000000000 : ℝ)*base78 + (22728219213161914693/4417000000000000000000000000000000 : ℝ)*base79 + (29551102299149/11042500000000000000000000000 : ℝ)*base81 + (1159237/312500000000000000000 : ℝ)*base89 + (1159237/312500000000000000000 : ℝ)*base91 + (1159237/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-86267/100000 : ℝ) ≤ (-19051614386628030638629808751/22085000000000000000000000000 : ℝ) := by norm_num
    linear_combination (565897/20000000000000 : ℝ)*(lower0) + (10590327/25000000000000 : ℝ)*(upper3) + (28877959/50000000000000 : ℝ)*(lower4) + (648134951673149/25000000000000 : ℝ)*(major0) + (648134951673149/25000000000000 : ℝ)*(major1) + (648134951673149/25000000000000 : ℝ)*(major2) + (298474177/50000000000000 : ℝ)*(sp4) + (21996371503/25000000000000 : ℝ)*(sp5) + (23327260041/100000000000000 : ℝ)*(sp7) + (2123146673/100000000000000 : ℝ)*(sp8) + (1829508724241361/50000000000000 : ℝ)*(sp12) + (457366522886467/12500000000000 : ℝ)*(sp13) + (914755042144437/25000000000000 : ℝ)*(sp14) + (155479110115109/10000000000000 : ℝ)*(sp15) + (388703607102783/25000000000000 : ℝ)*(f.failure) + (914755042144437/25000000000000 : ℝ)*(f.sum) + (57564855980419/22085000000000000000000000000 : ℝ)*base65 + (6219915200047296269/1104250000000000000000000000000000 : ℝ)*base68 + (5804018370237703731/1104250000000000000000000000000000 : ℝ)*base69 + (1204654693572546269/1104250000000000000000000000000000 : ℝ)*base72 + (37527951582207/11042500000000000000000000000 : ℝ)*base73 + (3882030392404703731/1104250000000000000000000000000000 : ℝ)*base75 + (2442016735089546269/1104250000000000000000000000000000 : ℝ)*base78 + (8324274113884953731/1104250000000000000000000000000000 : ℝ)*base79 + (131090327601349/22085000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (7144657/625000000000000000000 : ℝ)*base89 + (7144657/625000000000000000000 : ℝ)*base91 + (7144657/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1554_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41685679/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2767/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63801/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29413/50000 : ℝ) else (80759/100000 : ℝ) ≤ X j i ∧ X j i ≤ (86267/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1554_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1554_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41685679/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2767/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63801/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29413/50000 : ℝ) else (80759/100000 : ℝ) ≤ X j i ∧ X j i ≤ (86267/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1554_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41685679/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2767/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63801/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29413/50000 : ℝ) else (80759/100000 : ℝ) ≤ X j i ∧ X j i ≤ (86267/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1554_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
