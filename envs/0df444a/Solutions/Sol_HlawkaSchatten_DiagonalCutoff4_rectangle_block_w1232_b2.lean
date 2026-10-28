-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1232_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:15:39.574995+00:00
-- url     : https://prove2.me/submissions/59f94836-88e6-40a4-99b2-bd22b95029b2

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
theorem support_rectangle_w1232_s6_0 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2124556447/10000000000 : ℝ)*x 0 + (5391588391/10000000000 : ℝ)*x 1 + (1053377443/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2124556447/10000000000 : ℝ)^8425 ≤ (12918666599683/100000000000000 : ℝ)^6377 := by
    have hnat : (2124556447 : ℕ)^8425*100000000000000^6377 ≤ 12918666599683^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124556447 10000000000 12918666599683 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391588391/10000000000 : ℝ)^8425 ≤ (22106828841123/50000000000000 : ℝ)^6377 := by
    have hnat : (5391588391 : ℕ)^8425*50000000000000^6377 ≤ 22106828841123^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391588391 10000000000 22106828841123 50000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053377443/2000000000 : ℝ)^8425 ≤ (5358459463143/12500000000000 : ℝ)^6377 := by
    have hnat : (1053377443 : ℕ)^8425*12500000000000^6377 ≤ 5358459463143^6377*2000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053377443 2000000000 5358459463143 12500000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2124556447/10000000000 : ℝ), (5391588391/10000000000 : ℝ), (1053377443/2000000000 : ℝ)] ![(12918666599683/100000000000000 : ℝ), (22106828841123/50000000000000 : ℝ), (5358459463143/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2124556447/10000000000 : ℝ)|^8425 ≤ (12918666599683/100000000000000 : ℝ)^6377
        have hw : |(-2124556447/10000000000 : ℝ)|=(2124556447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391588391/10000000000 : ℝ)|^8425 ≤ (22106828841123/50000000000000 : ℝ)^6377
        have hw : |(5391588391/10000000000 : ℝ)|=(5391588391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053377443/2000000000 : ℝ)|^8425 ≤ (5358459463143/12500000000000 : ℝ)^6377
        have hw : |(1053377443/2000000000 : ℝ)|=(1053377443/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s6_1 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (213776527/400000000 : ℝ)*x 0 + (-2136512/9765625 : ℝ)*x 1 + (2633443589/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213776527/400000000 : ℝ)^8425 ≤ (21851637886873/50000000000000 : ℝ)^6377 := by
    have hnat : (213776527 : ℕ)^8425*50000000000000^6377 ≤ 21851637886873^6377*400000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213776527 400000000 21851637886873 50000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2136512/9765625 : ℝ)^8425 ≤ (839315556671/6250000000000 : ℝ)^6377 := by
    have hnat : (2136512 : ℕ)^8425*6250000000000^6377 ≤ 839315556671^6377*9765625^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136512 9765625 839315556671 6250000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633443589/5000000000 : ℝ)^8425 ≤ (10716918826821/25000000000000 : ℝ)^6377 := by
    have hnat : (2633443589 : ℕ)^8425*25000000000000^6377 ≤ 10716918826821^6377*5000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633443589 5000000000 10716918826821 25000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213776527/400000000 : ℝ), (-2136512/9765625 : ℝ), (2633443589/5000000000 : ℝ)] ![(21851637886873/50000000000000 : ℝ), (839315556671/6250000000000 : ℝ), (10716918826821/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213776527/400000000 : ℝ)|^8425 ≤ (21851637886873/50000000000000 : ℝ)^6377
        have hw : |(213776527/400000000 : ℝ)|=(213776527/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2136512/9765625 : ℝ)|^8425 ≤ (839315556671/6250000000000 : ℝ)^6377
        have hw : |(-2136512/9765625 : ℝ)|=(2136512/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633443589/5000000000 : ℝ)|^8425 ≤ (10716918826821/25000000000000 : ℝ)^6377
        have hw : |(2633443589/5000000000 : ℝ)|=(2633443589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s6_2 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068882631/2000000000 : ℝ)*x 0 + (5266887191/10000000000 : ℝ)*x 1 + (-2187788297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068882631/2000000000 : ℝ)^8425 ≤ (1748131022307/4000000000000 : ℝ)^6377 := by
    have hnat : (1068882631 : ℕ)^8425*4000000000000^6377 ≤ 1748131022307^6377*2000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068882631 2000000000 1748131022307 4000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266887191/10000000000 : ℝ)^8425 ≤ (1339614857721/3125000000000 : ℝ)^6377 := by
    have hnat : (5266887191 : ℕ)^8425*3125000000000^6377 ≤ 1339614857721^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266887191 10000000000 1339614857721 3125000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2187788297/10000000000 : ℝ)^8425 ≤ (6714524489861/50000000000000 : ℝ)^6377 := by
    have hnat : (2187788297 : ℕ)^8425*50000000000000^6377 ≤ 6714524489861^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187788297 10000000000 6714524489861 50000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068882631/2000000000 : ℝ), (5266887191/10000000000 : ℝ), (-2187788297/10000000000 : ℝ)] ![(1748131022307/4000000000000 : ℝ), (1339614857721/3125000000000 : ℝ), (6714524489861/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068882631/2000000000 : ℝ)|^8425 ≤ (1748131022307/4000000000000 : ℝ)^6377
        have hw : |(1068882631/2000000000 : ℝ)|=(1068882631/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266887191/10000000000 : ℝ)|^8425 ≤ (1339614857721/3125000000000 : ℝ)^6377
        have hw : |(5266887191/10000000000 : ℝ)|=(5266887191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2187788297/10000000000 : ℝ)|^8425 ≤ (6714524489861/50000000000000 : ℝ)^6377
        have hw : |(-2187788297/10000000000 : ℝ)|=(2187788297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s6_3 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (136004261/312500000 : ℝ)*x 0 + (845536429/2000000000 : ℝ)*x 1 + (4480158991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136004261/312500000 : ℝ)^8425 ≤ (33317338441777/100000000000000 : ℝ)^6377 := by
    have hnat : (136004261 : ℕ)^8425*100000000000000^6377 ≤ 33317338441777^6377*312500000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136004261 312500000 33317338441777 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (845536429/2000000000 : ℝ)^8425 ≤ (8016107786361/25000000000000 : ℝ)^6377 := by
    have hnat : (845536429 : ℕ)^8425*25000000000000^6377 ≤ 8016107786361^6377*2000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845536429 2000000000 8016107786361 25000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4480158991/10000000000 : ℝ)^8425 ≤ (8654557599277/25000000000000 : ℝ)^6377 := by
    have hnat : (4480158991 : ℕ)^8425*25000000000000^6377 ≤ 8654557599277^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4480158991 10000000000 8654557599277 25000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(136004261/312500000 : ℝ), (845536429/2000000000 : ℝ), (4480158991/10000000000 : ℝ)] ![(33317338441777/100000000000000 : ℝ), (8016107786361/25000000000000 : ℝ), (8654557599277/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(136004261/312500000 : ℝ)|^8425 ≤ (33317338441777/100000000000000 : ℝ)^6377
        have hw : |(136004261/312500000 : ℝ)|=(136004261/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(845536429/2000000000 : ℝ)|^8425 ≤ (8016107786361/25000000000000 : ℝ)^6377
        have hw : |(845536429/2000000000 : ℝ)|=(845536429/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4480158991/10000000000 : ℝ)|^8425 ≤ (8654557599277/25000000000000 : ℝ)^6377
        have hw : |(4480158991/10000000000 : ℝ)|=(4480158991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s6_4 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2124561219/10000000000 : ℝ)*x 0 + (5267202377/10000000000 : ℝ)*x 1 + (1347818011/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2124561219/10000000000 : ℝ)^8425 ≤ (403709529231/3125000000000 : ℝ)^6377 := by
    have hnat : (2124561219 : ℕ)^8425*3125000000000^6377 ≤ 403709529231^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124561219 10000000000 403709529231 3125000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267202377/10000000000 : ℝ)^8425 ≤ (21435532336429/50000000000000 : ℝ)^6377 := by
    have hnat : (5267202377 : ℕ)^8425*50000000000000^6377 ≤ 21435532336429^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267202377 10000000000 21435532336429 50000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347818011/2500000000 : ℝ)^8425 ≤ (11052557594151/25000000000000 : ℝ)^6377 := by
    have hnat : (1347818011 : ℕ)^8425*25000000000000^6377 ≤ 11052557594151^6377*2500000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347818011 2500000000 11052557594151 25000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2124561219/10000000000 : ℝ), (5267202377/10000000000 : ℝ), (1347818011/2500000000 : ℝ)] ![(403709529231/3125000000000 : ℝ), (21435532336429/50000000000000 : ℝ), (11052557594151/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2124561219/10000000000 : ℝ)|^8425 ≤ (403709529231/3125000000000 : ℝ)^6377
        have hw : |(-2124561219/10000000000 : ℝ)|=(2124561219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267202377/10000000000 : ℝ)|^8425 ≤ (21435532336429/50000000000000 : ℝ)^6377
        have hw : |(5267202377/10000000000 : ℝ)|=(5267202377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347818011/2500000000 : ℝ)|^8425 ≤ (11052557594151/25000000000000 : ℝ)^6377
        have hw : |(1347818011/2500000000 : ℝ)|=(1347818011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s6_5 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (6640771/12500000 : ℝ)*x 0 + (-103170189/500000000 : ℝ)*x 1 + (5391271611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6640771/12500000 : ℝ)^8425 ≤ (21680044948489/50000000000000 : ℝ)^6377 := by
    have hnat : (6640771 : ℕ)^8425*50000000000000^6377 ≤ 21680044948489^6377*12500000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6640771 12500000 21680044948489 50000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103170189/500000000 : ℝ)^8425 ≤ (6214842200523/50000000000000 : ℝ)^6377 := by
    have hnat : (103170189 : ℕ)^8425*50000000000000^6377 ≤ 6214842200523^6377*500000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103170189 500000000 6214842200523 50000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391271611/10000000000 : ℝ)^8425 ≤ (44210225685523/100000000000000 : ℝ)^6377 := by
    have hnat : (5391271611 : ℕ)^8425*100000000000000^6377 ≤ 44210225685523^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391271611 10000000000 44210225685523 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6640771/12500000 : ℝ), (-103170189/500000000 : ℝ), (5391271611/10000000000 : ℝ)] ![(21680044948489/50000000000000 : ℝ), (6214842200523/50000000000000 : ℝ), (44210225685523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6640771/12500000 : ℝ)|^8425 ≤ (21680044948489/50000000000000 : ℝ)^6377
        have hw : |(6640771/12500000 : ℝ)|=(6640771/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-103170189/500000000 : ℝ)|^8425 ≤ (6214842200523/50000000000000 : ℝ)^6377
        have hw : |(-103170189/500000000 : ℝ)|=(103170189/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391271611/10000000000 : ℝ)|^8425 ≤ (44210225685523/100000000000000 : ℝ)^6377
        have hw : |(5391271611/10000000000 : ℝ)|=(5391271611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s6_6 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (265630833/500000000 : ℝ)*x 0 + (5391271893/10000000000 : ℝ)*x 1 + (-1031701793/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265630833/500000000 : ℝ)^8425 ≤ (21680044193687/50000000000000 : ℝ)^6377 := by
    have hnat : (265630833 : ℕ)^8425*50000000000000^6377 ≤ 21680044193687^6377*500000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265630833 500000000 21680044193687 50000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391271893/10000000000 : ℝ)^8425 ≤ (8842045748137/20000000000000 : ℝ)^6377 := by
    have hnat : (5391271893 : ℕ)^8425*20000000000000^6377 ≤ 8842045748137^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391271893 10000000000 8842045748137 20000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1031701793/5000000000 : ℝ)^8425 ≤ (12429682857103/100000000000000 : ℝ)^6377 := by
    have hnat : (1031701793 : ℕ)^8425*100000000000000^6377 ≤ 12429682857103^6377*5000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031701793 5000000000 12429682857103 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265630833/500000000 : ℝ), (5391271893/10000000000 : ℝ), (-1031701793/5000000000 : ℝ)] ![(21680044193687/50000000000000 : ℝ), (8842045748137/20000000000000 : ℝ), (12429682857103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265630833/500000000 : ℝ)|^8425 ≤ (21680044193687/50000000000000 : ℝ)^6377
        have hw : |(265630833/500000000 : ℝ)|=(265630833/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391271893/10000000000 : ℝ)|^8425 ≤ (8842045748137/20000000000000 : ℝ)^6377
        have hw : |(5391271893/10000000000 : ℝ)|=(5391271893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1031701793/5000000000 : ℝ)|^8425 ≤ (12429682857103/100000000000000 : ℝ)^6377
        have hw : |(-1031701793/5000000000 : ℝ)|=(1031701793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s6_7 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2176073157/5000000000 : ℝ)*x 0 + (895904099/2000000000 : ℝ)*x 1 + (4228322561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2176073157/5000000000 : ℝ)^8425 ≤ (33317439197099/100000000000000 : ℝ)^6377 := by
    have hnat : (2176073157 : ℕ)^8425*100000000000000^6377 ≤ 33317439197099^6377*5000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176073157 5000000000 33317439197099 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (895904099/2000000000 : ℝ)^8425 ≤ (17305856207441/50000000000000 : ℝ)^6377 := by
    have hnat : (895904099 : ℕ)^8425*50000000000000^6377 ≤ 17305856207441^6377*2000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895904099 2000000000 17305856207441 50000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4228322561/10000000000 : ℝ)^8425 ≤ (16035424186513/50000000000000 : ℝ)^6377 := by
    have hnat : (4228322561 : ℕ)^8425*50000000000000^6377 ≤ 16035424186513^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228322561 10000000000 16035424186513 50000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2176073157/5000000000 : ℝ), (895904099/2000000000 : ℝ), (4228322561/10000000000 : ℝ)] ![(33317439197099/100000000000000 : ℝ), (17305856207441/50000000000000 : ℝ), (16035424186513/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2176073157/5000000000 : ℝ)|^8425 ≤ (33317439197099/100000000000000 : ℝ)^6377
        have hw : |(2176073157/5000000000 : ℝ)|=(2176073157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(895904099/2000000000 : ℝ)|^8425 ≤ (17305856207441/50000000000000 : ℝ)^6377
        have hw : |(895904099/2000000000 : ℝ)|=(895904099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4228322561/10000000000 : ℝ)|^8425 ≤ (16035424186513/50000000000000 : ℝ)^6377
        have hw : |(4228322561/10000000000 : ℝ)|=(4228322561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1232_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37808179/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7063/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11441/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5731/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1763/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7063/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11441/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7063/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11441/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7063/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11441/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7063/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11441/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7063/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11441/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7063/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11441/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11441/100000 : ℝ) ^ (1053/256 : ℝ) ≤ (13402862610883781/100000000000000000000 : ℝ) := by
    have hpowers : (11441/100000 : ℝ)^1053 ≤ (13402862610883781/100000000000000000000 : ℝ)^256 := by
      have hnat : (11441 : ℕ)^1053*100000000000000000000^256 ≤ 13402862610883781^256*100000^1053 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11441 100000 13402862610883781 100000000000000000000 1053 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11441/100000 : ℝ)) (X := (13402862610883781/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1053 256 (by norm_num) hpowers
    exact h
  have hpowhi : (7063/50000 : ℝ) ^ (1053/256 : ℝ) ≤ (3189994397935029/10000000000000000000 : ℝ) := by
    have hpowers : (7063/50000 : ℝ)^1053 ≤ (3189994397935029/10000000000000000000 : ℝ)^256 := by
      have hnat : (7063 : ℕ)^1053*10000000000000000000^256 ≤ 3189994397935029^256*50000^1053 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7063 50000 3189994397935029 10000000000000000000 1053 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7063/50000 : ℝ)) (X := (3189994397935029/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1053 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013402862610883781/50000000000000000000 : ℝ) ≤ (10000651621047343/10000000000000000 : ℝ) ^ (1053/256 : ℝ) := by
    have hpowers : (50013402862610883781/50000000000000000000 : ℝ)^256 ≤ (10000651621047343/10000000000000000 : ℝ)^1053 := by
      have hnat : (50013402862610883781 : ℕ)^256*10000000000000000^1053 ≤ 10000651621047343^1053*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013402862610883781 50000000000000000000 10000651621047343 10000000000000000 256 1053 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000651621047343/10000000000000000 : ℝ)) (X := (50013402862610883781/50000000000000000000 : ℝ)) (by norm_num) 1053 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045302806590234071/100000000000000000000 : ℝ) ≤ (5000550594998899/5000000000000000 : ℝ) ^ (1053/256 : ℝ) := by
    have hpowers : (100045302806590234071/100000000000000000000 : ℝ)^256 ≤ (5000550594998899/5000000000000000 : ℝ)^1053 := by
      have hnat : (100045302806590234071 : ℕ)^256*5000000000000000^1053 ≤ 5000550594998899^1053*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045302806590234071 100000000000000000000 5000550594998899 5000000000000000 256 1053 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000550594998899/5000000000000000 : ℝ)) (X := (100045302806590234071/100000000000000000000 : ℝ)) (by norm_num) 1053 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003189994397935029/5000000000000000000 : ℝ) ≤ (10001550758948253/10000000000000000 : ℝ) ^ (1053/256 : ℝ) := by
    have hpowers : (5003189994397935029/5000000000000000000 : ℝ)^256 ≤ (10001550758948253/10000000000000000 : ℝ)^1053 := by
      have hnat : (5003189994397935029 : ℕ)^256*10000000000000000^1053 ≤ 10001550758948253^1053*5000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003189994397935029 5000000000000000000 10001550758948253 10000000000000000 256 1053 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001550758948253/10000000000000000 : ℝ)) (X := (5003189994397935029/5000000000000000000 : ℝ)) (by norm_num) 1053 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13402862610883781/100000000000000000000 : ℝ) ≤ ((5368292513157560929/5370000000000000000 : ℝ)+2*(89913790091/53700000000000 : ℝ)*(11441/100000 : ℝ))^(1053/256 : ℝ) := by
    rw [show (5368292513157560929/5370000000000000000 : ℝ)+2*(89913790091/53700000000000 : ℝ)*(11441/100000 : ℝ)=(10000651621047343/10000000000000000 : ℝ) by norm_num, show 1+2*(13402862610883781/100000000000000000000 : ℝ)=(50013402862610883781/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3189994397935029/10000000000000000000 : ℝ)+(13402862610883781/100000000000000000000 : ℝ) ≤ ((5368292513157560929/5370000000000000000 : ℝ)+(89913790091/53700000000000 : ℝ)*((7063/50000 : ℝ)+(11441/100000 : ℝ)))^(1053/256 : ℝ) := by
    rw [show (5368292513157560929/5370000000000000000 : ℝ)+(89913790091/53700000000000 : ℝ)*((7063/50000 : ℝ)+(11441/100000 : ℝ))=(5000550594998899/5000000000000000 : ℝ) by norm_num, show 1+(3189994397935029/10000000000000000000 : ℝ)+(13402862610883781/100000000000000000000 : ℝ)=(100045302806590234071/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3189994397935029/10000000000000000000 : ℝ) ≤ ((5368292513157560929/5370000000000000000 : ℝ)+2*(89913790091/53700000000000 : ℝ)*(7063/50000 : ℝ))^(1053/256 : ℝ) := by
    rw [show (5368292513157560929/5370000000000000000 : ℝ)+2*(89913790091/53700000000000 : ℝ)*(7063/50000 : ℝ)=(10001550758948253/10000000000000000 : ℝ) by norm_num, show 1+2*(3189994397935029/10000000000000000000 : ℝ)=(5003189994397935029/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5368292513157560929/5370000000000000000 : ℝ)*(X 1 0+X 2 0)+(89913790091/53700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1053/256 : ℝ)) (lo := (11441/100000 : ℝ)) (hi := (7063/50000 : ℝ)) (c := (5368292513157560929/5370000000000000000 : ℝ)) (alpha := (89913790091/53700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5368292513157560929/5370000000000000000 : ℝ)*(X 0 1+X 2 1)+(89913790091/53700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1053/256 : ℝ)) (lo := (11441/100000 : ℝ)) (hi := (7063/50000 : ℝ)) (c := (5368292513157560929/5370000000000000000 : ℝ)) (alpha := (89913790091/53700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5368292513157560929/5370000000000000000 : ℝ)*(X 0 2+X 1 2)+(89913790091/53700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1053/256 : ℝ)) (lo := (11441/100000 : ℝ)) (hi := (7063/50000 : ℝ)) (c := (5368292513157560929/5370000000000000000 : ℝ)) (alpha := (89913790091/53700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2124556447/10000000000 : ℝ)*X 0 0+(5391588391/10000000000 : ℝ)*X 0 1+(1053377443/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((213776527/400000000 : ℝ)*X 1 0+(-2136512/9765625 : ℝ)*X 1 1+(2633443589/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068882631/2000000000 : ℝ)*X 2 0+(5266887191/10000000000 : ℝ)*X 2 1+(-2187788297/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((136004261/312500000 : ℝ)*X 0 0+(845536429/2000000000 : ℝ)*X 0 1+(4480158991/10000000000 : ℝ)*X 0 2+(136004261/312500000 : ℝ)*X 1 0+(845536429/2000000000 : ℝ)*X 1 1+(4480158991/10000000000 : ℝ)*X 1 2+(136004261/312500000 : ℝ)*X 2 0+(845536429/2000000000 : ℝ)*X 2 1+(4480158991/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2124561219/10000000000 : ℝ)*X 0 0+(5267202377/10000000000 : ℝ)*X 0 1+(1347818011/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((6640771/12500000 : ℝ)*X 1 0+(-103170189/500000000 : ℝ)*X 1 1+(5391271611/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((265630833/500000000 : ℝ)*X 2 0+(5391271893/10000000000 : ℝ)*X 2 1+(-1031701793/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2176073157/5000000000 : ℝ)*X 0 0+(895904099/2000000000 : ℝ)*X 0 1+(4228322561/10000000000 : ℝ)*X 0 2+(2176073157/5000000000 : ℝ)*X 1 0+(895904099/2000000000 : ℝ)*X 1 1+(4228322561/10000000000 : ℝ)*X 1 2+(2176073157/5000000000 : ℝ)*X 2 0+(895904099/2000000000 : ℝ)*X 2 1+(4228322561/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (79001259890693507355808001/11187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (647507587/50000000000000 : ℝ)*(base19) + (589139423/50000000000000 : ℝ)*(base23) + (46350239/100000000000000 : ℝ)*(lower2) + (84583073/50000000000000 : ℝ)*(upper3) + (84994649/100000000000000 : ℝ)*(upper5) + (5990017603026647/100000000000000 : ℝ)*(major0) + (5990017603026647/100000000000000 : ℝ)*(major1) + (748752200378331/12500000000000 : ℝ)*(major2) + (1603841368786971/20000000000000 : ℝ)*(sp0) + (2004809710350209/25000000000000 : ℝ)*(sp1) + (2004809739534291/25000000000000 : ℝ)*(sp2) + (3960775969792377/100000000000000 : ℝ)*(sp3) + (8323120289/25000000000000 : ℝ)*(sp4) + (147378589/781250000000 : ℝ)*(sp7) + (495099354281471/12500000000000 : ℝ)*(f.failure) + (8019240136416011/100000000000000 : ℝ)*(f.sum) + (2350868824187/1074000000000000000000000000 : ℝ)*base65 + (9271456415204124937/537000000000000000000000000000000 : ℝ)*base68 + (230049608457791999/67125000000000000000000000000000 : ℝ)*base69 + (6916215119805875063/537000000000000000000000000000000 : ℝ)*base71 + (5896934038369/1074000000000000000000000000 : ℝ)*base74 + (306914505094916999/67125000000000000000000000000000 : ℝ)*base75 + (2266325430118925021/179000000000000000000000000000000 : ℝ)*base77 + (1339907345124074979/179000000000000000000000000000000 : ℝ)*base80 + (1310122668671/1342500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (76309/312500000000000000000 : ℝ)*base89 + (76309/312500000000000000000 : ℝ)*base91 + (3048691/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1708312444914210419497/223750000000000000000000000 : ℝ) := by norm_num
    linear_combination (36162301/2000000000000 : ℝ)*(base19) + (80612361/4000000000000 : ℝ)*(base23) + (95196913/50000000000000 : ℝ)*(upper3) + (33991201/20000000000000 : ℝ)*(lower4) + (293011013/100000000000000 : ℝ)*(upper5) + (6020453521550003/100000000000000 : ℝ)*(major0) + (6020453521550003/100000000000000 : ℝ)*(major1) + (6020453521550003/100000000000000 : ℝ)*(major2) + (11814977923/50000000000000 : ℝ)*(sp1) + (20142580551/50000000000000 : ℝ)*(sp2) + (1007498341652013/12500000000000 : ℝ)*(sp4) + (8059961295145207/100000000000000 : ℝ)*(sp5) + (4029972216372989/50000000000000 : ℝ)*(sp6) + (796184011077339/20000000000000 : ℝ)*(sp7) + (796184011077339/20000000000000 : ℝ)*(f.failure) + (1007498341652013/12500000000000 : ℝ)*(f.sum) + (13349067816283/2685000000000000000000000000 : ℝ)*base65 + (1933207915033689071/179000000000000000000000000000000 : ℝ)*base68 + (764611648635689071/179000000000000000000000000000000 : ℝ)*base70 + (30682056153310929/179000000000000000000000000000000 : ℝ)*base71 + (684090544609/335625000000000000000000000 : ℝ)*base74 + (2650786307833310929/179000000000000000000000000000000 : ℝ)*base75 + (1119800102593310929/179000000000000000000000000000000 : ℝ)*base77 + (3302909046445689071/179000000000000000000000000000000 : ℝ)*base80 + (292712689277/167812500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (755681/500000000000000000000 : ℝ)*base89 + (755681/500000000000000000000 : ℝ)*base91 + (755681/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1232_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37808179/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7063/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11441/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5731/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1232_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1232_s7_0 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2124573323/10000000000 : ℝ)*x 0 + (5391386721/10000000000 : ℝ)*x 1 + (1316769449/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2124573323/10000000000 : ℝ)^8425 ≤ (3229700543153/25000000000000 : ℝ)^6377 := by
    have hnat : (2124573323 : ℕ)^8425*25000000000000^6377 ≤ 3229700543153^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124573323 10000000000 3229700543153 25000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391386721/10000000000 : ℝ)^8425 ≤ (44211472780573/100000000000000 : ℝ)^6377 := by
    have hnat : (5391386721 : ℕ)^8425*100000000000000^6377 ≤ 44211472780573^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391386721 10000000000 44211472780573 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316769449/2500000000 : ℝ)^8425 ≤ (8573945006687/20000000000000 : ℝ)^6377 := by
    have hnat : (1316769449 : ℕ)^8425*20000000000000^6377 ≤ 8573945006687^6377*2500000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316769449 2500000000 8573945006687 20000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2124573323/10000000000 : ℝ), (5391386721/10000000000 : ℝ), (1316769449/2500000000 : ℝ)] ![(3229700543153/25000000000000 : ℝ), (44211472780573/100000000000000 : ℝ), (8573945006687/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2124573323/10000000000 : ℝ)|^8425 ≤ (3229700543153/25000000000000 : ℝ)^6377
        have hw : |(-2124573323/10000000000 : ℝ)|=(2124573323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391386721/10000000000 : ℝ)|^8425 ≤ (44211472780573/100000000000000 : ℝ)^6377
        have hw : |(5391386721/10000000000 : ℝ)|=(5391386721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316769449/2500000000 : ℝ)|^8425 ≤ (8573945006687/20000000000000 : ℝ)^6377
        have hw : |(1316769449/2500000000 : ℝ)|=(1316769449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s7_1 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068871887/2000000000 : ℝ)*x 0 + (-2187601049/10000000000 : ℝ)*x 1 + (658385297/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068871887/2000000000 : ℝ)^8425 ≤ (43702695190609/100000000000000 : ℝ)^6377 := by
    have hnat : (1068871887 : ℕ)^8425*100000000000000^6377 ≤ 43702695190609^6377*2000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068871887 2000000000 43702695190609 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2187601049/10000000000 : ℝ)^8425 ≤ (1678441314389/12500000000000 : ℝ)^6377 := by
    have hnat : (2187601049 : ℕ)^8425*12500000000000^6377 ≤ 1678441314389^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187601049 10000000000 1678441314389 12500000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658385297/1250000000 : ℝ)^8425 ≤ (5358721785341/12500000000000 : ℝ)^6377 := by
    have hnat : (658385297 : ℕ)^8425*12500000000000^6377 ≤ 5358721785341^6377*1250000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658385297 1250000000 5358721785341 12500000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068871887/2000000000 : ℝ), (-2187601049/10000000000 : ℝ), (658385297/1250000000 : ℝ)] ![(43702695190609/100000000000000 : ℝ), (1678441314389/12500000000000 : ℝ), (5358721785341/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068871887/2000000000 : ℝ)|^8425 ≤ (43702695190609/100000000000000 : ℝ)^6377
        have hw : |(1068871887/2000000000 : ℝ)|=(1068871887/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2187601049/10000000000 : ℝ)|^8425 ≤ (1678441314389/12500000000000 : ℝ)^6377
        have hw : |(-2187601049/10000000000 : ℝ)|=(2187601049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658385297/1250000000 : ℝ)|^8425 ≤ (5358721785341/12500000000000 : ℝ)^6377
        have hw : |(658385297/1250000000 : ℝ)|=(658385297/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s7_2 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336091079/2500000000 : ℝ)*x 0 + (5267079031/10000000000 : ℝ)*x 1 + (-1093799491/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336091079/2500000000 : ℝ)^8425 ≤ (10925686980673/25000000000000 : ℝ)^6377 := by
    have hnat : (1336091079 : ℕ)^8425*25000000000000^6377 ≤ 10925686980673^6377*2500000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336091079 2500000000 10925686980673 25000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267079031/10000000000 : ℝ)^8425 ≤ (21434869156769/50000000000000 : ℝ)^6377 := by
    have hnat : (5267079031 : ℕ)^8425*50000000000000^6377 ≤ 21434869156769^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267079031 10000000000 21434869156769 50000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1093799491/5000000000 : ℝ)^8425 ≤ (13427513753263/100000000000000 : ℝ)^6377 := by
    have hnat : (1093799491 : ℕ)^8425*100000000000000^6377 ≤ 13427513753263^6377*5000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093799491 5000000000 13427513753263 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336091079/2500000000 : ℝ), (5267079031/10000000000 : ℝ), (-1093799491/5000000000 : ℝ)] ![(10925686980673/25000000000000 : ℝ), (21434869156769/50000000000000 : ℝ), (13427513753263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336091079/2500000000 : ℝ)|^8425 ≤ (10925686980673/25000000000000 : ℝ)^6377
        have hw : |(1336091079/2500000000 : ℝ)|=(1336091079/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267079031/10000000000 : ℝ)|^8425 ≤ (21434869156769/50000000000000 : ℝ)^6377
        have hw : |(5267079031/10000000000 : ℝ)|=(5267079031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1093799491/5000000000 : ℝ)|^8425 ≤ (13427513753263/100000000000000 : ℝ)^6377
        have hw : |(-1093799491/5000000000 : ℝ)|=(1093799491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s7_3 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1088038533/2500000000 : ℝ)*x 0 + (4228076403/10000000000 : ℝ)*x 1 + (2239877191/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088038533/2500000000 : ℝ)^8425 ≤ (8329379567033/25000000000000 : ℝ)^6377 := by
    have hnat : (1088038533 : ℕ)^8425*25000000000000^6377 ≤ 8329379567033^6377*2500000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088038533 2500000000 8329379567033 25000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4228076403/10000000000 : ℝ)^8425 ≤ (32068381733279/100000000000000 : ℝ)^6377 := by
    have hnat : (4228076403 : ℕ)^8425*100000000000000^6377 ≤ 32068381733279^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228076403 10000000000 32068381733279 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2239877191/5000000000 : ℝ)^8425 ≤ (34614099977529/100000000000000 : ℝ)^6377 := by
    have hnat : (2239877191 : ℕ)^8425*100000000000000^6377 ≤ 34614099977529^6377*5000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239877191 5000000000 34614099977529 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1088038533/2500000000 : ℝ), (4228076403/10000000000 : ℝ), (2239877191/5000000000 : ℝ)] ![(8329379567033/25000000000000 : ℝ), (32068381733279/100000000000000 : ℝ), (34614099977529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1088038533/2500000000 : ℝ)|^8425 ≤ (8329379567033/25000000000000 : ℝ)^6377
        have hw : |(1088038533/2500000000 : ℝ)|=(1088038533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4228076403/10000000000 : ℝ)|^8425 ≤ (32068381733279/100000000000000 : ℝ)^6377
        have hw : |(4228076403/10000000000 : ℝ)|=(4228076403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2239877191/5000000000 : ℝ)|^8425 ≤ (34614099977529/100000000000000 : ℝ)^6377
        have hw : |(2239877191/5000000000 : ℝ)|=(2239877191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s7_4 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2124578621/10000000000 : ℝ)*x 0 + (5267392919/10000000000 : ℝ)*x 1 + (1078214003/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2124578621/10000000000 : ℝ)^8425 ≤ (3229711183509/25000000000000 : ℝ)^6377 := by
    have hnat : (2124578621 : ℕ)^8425*25000000000000^6377 ≤ 3229711183509^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124578621 10000000000 3229711183509 25000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267392919/10000000000 : ℝ)^8425 ≤ (42873113621151/100000000000000 : ℝ)^6377 := by
    have hnat : (5267392919 : ℕ)^8425*100000000000000^6377 ≤ 42873113621151^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267392919 10000000000 42873113621151 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078214003/2000000000 : ℝ)^8425 ≤ (44208041626779/100000000000000 : ℝ)^6377 := by
    have hnat : (1078214003 : ℕ)^8425*100000000000000^6377 ≤ 44208041626779^6377*2000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078214003 2000000000 44208041626779 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2124578621/10000000000 : ℝ), (5267392919/10000000000 : ℝ), (1078214003/2000000000 : ℝ)] ![(3229711183509/25000000000000 : ℝ), (42873113621151/100000000000000 : ℝ), (44208041626779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2124578621/10000000000 : ℝ)|^8425 ≤ (3229711183509/25000000000000 : ℝ)^6377
        have hw : |(-2124578621/10000000000 : ℝ)|=(2124578621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267392919/10000000000 : ℝ)|^8425 ≤ (42873113621151/100000000000000 : ℝ)^6377
        have hw : |(5267392919/10000000000 : ℝ)|=(5267392919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078214003/2000000000 : ℝ)|^8425 ≤ (44208041626779/100000000000000 : ℝ)^6377
        have hw : |(1078214003/2000000000 : ℝ)|=(1078214003/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s7_5 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312665979/10000000000 : ℝ)*x 0 + (-2063611627/10000000000 : ℝ)*x 1 + (2695534989/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312665979/10000000000 : ℝ)^8425 ≤ (21680310094757/50000000000000 : ℝ)^6377 := by
    have hnat : (5312665979 : ℕ)^8425*50000000000000^6377 ≤ 21680310094757^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312665979 10000000000 21680310094757 50000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2063611627/10000000000 : ℝ)^8425 ≤ (12431338571111/100000000000000 : ℝ)^6377 := by
    have hnat : (2063611627 : ℕ)^8425*100000000000000^6377 ≤ 12431338571111^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063611627 10000000000 12431338571111 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695534989/5000000000 : ℝ)^8425 ≤ (44208041225929/100000000000000 : ℝ)^6377 := by
    have hnat : (2695534989 : ℕ)^8425*100000000000000^6377 ≤ 44208041225929^6377*5000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695534989 5000000000 44208041225929 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312665979/10000000000 : ℝ), (-2063611627/10000000000 : ℝ), (2695534989/5000000000 : ℝ)] ![(21680310094757/50000000000000 : ℝ), (12431338571111/100000000000000 : ℝ), (44208041225929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312665979/10000000000 : ℝ)|^8425 ≤ (21680310094757/50000000000000 : ℝ)^6377
        have hw : |(5312665979/10000000000 : ℝ)|=(5312665979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2063611627/10000000000 : ℝ)|^8425 ≤ (12431338571111/100000000000000 : ℝ)^6377
        have hw : |(-2063611627/10000000000 : ℝ)|=(2063611627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695534989/5000000000 : ℝ)|^8425 ≤ (44208041225929/100000000000000 : ℝ)^6377
        have hw : |(2695534989/5000000000 : ℝ)|=(2695534989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s7_6 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (41505203/78125000 : ℝ)*x 0 + (2695535003/5000000000 : ℝ)*x 1 + (-1031805791/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41505203/78125000 : ℝ)^8425 ≤ (43360620243429/100000000000000 : ℝ)^6377 := by
    have hnat : (41505203 : ℕ)^8425*100000000000000^6377 ≤ 43360620243429^6377*78125000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41505203 78125000 43360620243429 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695535003/5000000000 : ℝ)^8425 ≤ (1768321661171/4000000000000 : ℝ)^6377 := by
    have hnat : (2695535003 : ℕ)^8425*4000000000000^6377 ≤ 1768321661171^6377*5000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695535003 5000000000 1768321661171 4000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1031805791/5000000000 : ℝ)^8425 ≤ (1553917276621/12500000000000 : ℝ)^6377 := by
    have hnat : (1031805791 : ℕ)^8425*12500000000000^6377 ≤ 1553917276621^6377*5000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031805791 5000000000 1553917276621 12500000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41505203/78125000 : ℝ), (2695535003/5000000000 : ℝ), (-1031805791/5000000000 : ℝ)] ![(43360620243429/100000000000000 : ℝ), (1768321661171/4000000000000 : ℝ), (1553917276621/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41505203/78125000 : ℝ)|^8425 ≤ (43360620243429/100000000000000 : ℝ)^6377
        have hw : |(41505203/78125000 : ℝ)|=(41505203/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695535003/5000000000 : ℝ)|^8425 ≤ (1768321661171/4000000000000 : ℝ)^6377
        have hw : |(2695535003/5000000000 : ℝ)|=(2695535003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1031805791/5000000000 : ℝ)|^8425 ≤ (1553917276621/12500000000000 : ℝ)^6377
        have hw : |(-1031805791/5000000000 : ℝ)|=(1031805791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s7_7 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4352155839/10000000000 : ℝ)*x 0 + (895824427/2000000000 : ℝ)*x 1 + (4228718747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4352155839/10000000000 : ℝ)^8425 ≤ (2082345970793/6250000000000 : ℝ)^6377 := by
    have hnat : (4352155839 : ℕ)^8425*6250000000000^6377 ≤ 2082345970793^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352155839 10000000000 2082345970793 6250000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (895824427/2000000000 : ℝ)^8425 ≤ (3460764597297/10000000000000 : ℝ)^6377 := by
    have hnat : (895824427 : ℕ)^8425*10000000000000^6377 ≤ 3460764597297^6377*2000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895824427 2000000000 3460764597297 10000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4228718747/10000000000 : ℝ)^8425 ≤ (1282992738937/4000000000000 : ℝ)^6377 := by
    have hnat : (4228718747 : ℕ)^8425*4000000000000^6377 ≤ 1282992738937^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228718747 10000000000 1282992738937 4000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4352155839/10000000000 : ℝ), (895824427/2000000000 : ℝ), (4228718747/10000000000 : ℝ)] ![(2082345970793/6250000000000 : ℝ), (3460764597297/10000000000000 : ℝ), (1282992738937/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4352155839/10000000000 : ℝ)|^8425 ≤ (2082345970793/6250000000000 : ℝ)^6377
        have hw : |(4352155839/10000000000 : ℝ)|=(4352155839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(895824427/2000000000 : ℝ)|^8425 ≤ (3460764597297/10000000000000 : ℝ)^6377
        have hw : |(895824427/2000000000 : ℝ)|=(895824427/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4228718747/10000000000 : ℝ)|^8425 ≤ (1282992738937/4000000000000 : ℝ)^6377
        have hw : |(4228718747/10000000000 : ℝ)|=(4228718747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s7_8 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-61924713/10000000000 : ℝ)*x 0 + (5912161903/10000000000 : ℝ)*x 1 + (2956107501/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (61924713/10000000000 : ℝ)^8425 ≤ (120979550937/100000000000000 : ℝ)^6377 := by
    have hnat : (61924713 : ℕ)^8425*100000000000000^6377 ≤ 120979550937^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61924713 10000000000 120979550937 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5912161903/10000000000 : ℝ)^8425 ≤ (9987842786733/20000000000000 : ℝ)^6377 := by
    have hnat : (5912161903 : ℕ)^8425*20000000000000^6377 ≤ 9987842786733^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5912161903 10000000000 9987842786733 20000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2956107501/5000000000 : ℝ)^8425 ≤ (24969903249229/50000000000000 : ℝ)^6377 := by
    have hnat : (2956107501 : ℕ)^8425*50000000000000^6377 ≤ 24969903249229^6377*5000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2956107501 5000000000 24969903249229 50000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-61924713/10000000000 : ℝ), (5912161903/10000000000 : ℝ), (2956107501/5000000000 : ℝ)] ![(120979550937/100000000000000 : ℝ), (9987842786733/20000000000000 : ℝ), (24969903249229/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-61924713/10000000000 : ℝ)|^8425 ≤ (120979550937/100000000000000 : ℝ)^6377
        have hw : |(-61924713/10000000000 : ℝ)|=(61924713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5912161903/10000000000 : ℝ)|^8425 ≤ (9987842786733/20000000000000 : ℝ)^6377
        have hw : |(5912161903/10000000000 : ℝ)|=(5912161903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2956107501/5000000000 : ℝ)|^8425 ≤ (24969903249229/50000000000000 : ℝ)^6377
        have hw : |(2956107501/5000000000 : ℝ)|=(2956107501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1232_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37808179/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5731/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5733/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (141/1000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1763/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5731/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1763/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5731/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1763/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5731/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1763/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5731/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1763/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5731/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1763/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5731/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5731/50000 : ℝ) ^ (1053/256 : ℝ) ≤ (2700868593603563/20000000000000000000 : ℝ) := by
    have hpowers : (5731/50000 : ℝ)^1053 ≤ (2700868593603563/20000000000000000000 : ℝ)^256 := by
      have hnat : (5731 : ℕ)^1053*20000000000000000000^256 ≤ 2700868593603563^256*50000^1053 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5731 50000 2700868593603563 20000000000000000000 1053 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5731/50000 : ℝ)) (X := (2700868593603563/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1053 256 (by norm_num) hpowers
    exact h
  have hpowhi : (1763/12500 : ℝ) ^ (1053/256 : ℝ) ≤ (3169608548568413/10000000000000000000 : ℝ) := by
    have hpowers : (1763/12500 : ℝ)^1053 ≤ (3169608548568413/10000000000000000000 : ℝ)^256 := by
      have hnat : (1763 : ℕ)^1053*10000000000000000000^256 ≤ 3169608548568413^256*12500^1053 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1763 12500 3169608548568413 10000000000000000000 1053 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1763/12500 : ℝ)) (X := (3169608548568413/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1053 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002700868593603563/10000000000000000000 : ℝ) ≤ (78130129330627/78125000000000 : ℝ) ^ (1053/256 : ℝ) := by
    have hpowers : (10002700868593603563/10000000000000000000 : ℝ)^256 ≤ (78130129330627/78125000000000 : ℝ)^1053 := by
      have hnat : (10002700868593603563 : ℕ)^256*78125000000000^1053 ≤ 78130129330627^1053*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002700868593603563 10000000000000000000 78130129330627 78125000000000 256 1053 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78130129330627/78125000000000 : ℝ)) (X := (10002700868593603563/10000000000000000000 : ℝ)) (by norm_num) 1053 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009040085690740389/20000000000000000000 : ℝ) ≤ (5000549350942397/5000000000000000 : ℝ) ^ (1053/256 : ℝ) := by
    have hpowers : (20009040085690740389/20000000000000000000 : ℝ)^256 ≤ (5000549350942397/5000000000000000 : ℝ)^1053 := by
      have hnat : (20009040085690740389 : ℕ)^256*5000000000000000^1053 ≤ 5000549350942397^1053*20000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009040085690740389 20000000000000000000 5000549350942397 5000000000000000 256 1053 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000549350942397/5000000000000000 : ℝ)) (X := (20009040085690740389/20000000000000000000 : ℝ)) (by norm_num) 1053 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003169608548568413/5000000000000000000 : ℝ) ≤ (2500385212362333/2500000000000000 : ℝ) ^ (1053/256 : ℝ) := by
    have hpowers : (5003169608548568413/5000000000000000000 : ℝ)^256 ≤ (2500385212362333/2500000000000000 : ℝ)^1053 := by
      have hnat : (5003169608548568413 : ℕ)^256*2500000000000000^1053 ≤ 2500385212362333^1053*5000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003169608548568413 5000000000000000000 2500385212362333 2500000000000000 256 1053 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500385212362333/2500000000000000 : ℝ)) (X := (5003169608548568413/5000000000000000000 : ℝ)) (by norm_num) 1053 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2700868593603563/20000000000000000000 : ℝ) ≤ ((660289970643616181/660500000000000000 : ℝ)+2*(221073782269/132100000000000 : ℝ)*(5731/50000 : ℝ))^(1053/256 : ℝ) := by
    rw [show (660289970643616181/660500000000000000 : ℝ)+2*(221073782269/132100000000000 : ℝ)*(5731/50000 : ℝ)=(78130129330627/78125000000000 : ℝ) by norm_num, show 1+2*(2700868593603563/20000000000000000000 : ℝ)=(10002700868593603563/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3169608548568413/10000000000000000000 : ℝ)+(2700868593603563/20000000000000000000 : ℝ) ≤ ((660289970643616181/660500000000000000 : ℝ)+(221073782269/132100000000000 : ℝ)*((1763/12500 : ℝ)+(5731/50000 : ℝ)))^(1053/256 : ℝ) := by
    rw [show (660289970643616181/660500000000000000 : ℝ)+(221073782269/132100000000000 : ℝ)*((1763/12500 : ℝ)+(5731/50000 : ℝ))=(5000549350942397/5000000000000000 : ℝ) by norm_num, show 1+(3169608548568413/10000000000000000000 : ℝ)+(2700868593603563/20000000000000000000 : ℝ)=(20009040085690740389/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3169608548568413/10000000000000000000 : ℝ) ≤ ((660289970643616181/660500000000000000 : ℝ)+2*(221073782269/132100000000000 : ℝ)*(1763/12500 : ℝ))^(1053/256 : ℝ) := by
    rw [show (660289970643616181/660500000000000000 : ℝ)+2*(221073782269/132100000000000 : ℝ)*(1763/12500 : ℝ)=(2500385212362333/2500000000000000 : ℝ) by norm_num, show 1+2*(3169608548568413/10000000000000000000 : ℝ)=(5003169608548568413/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (660289970643616181/660500000000000000 : ℝ)*(X 1 0+X 2 0)+(221073782269/132100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1053/256 : ℝ)) (lo := (5731/50000 : ℝ)) (hi := (1763/12500 : ℝ)) (c := (660289970643616181/660500000000000000 : ℝ)) (alpha := (221073782269/132100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (660289970643616181/660500000000000000 : ℝ)*(X 0 1+X 2 1)+(221073782269/132100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1053/256 : ℝ)) (lo := (5731/50000 : ℝ)) (hi := (1763/12500 : ℝ)) (c := (660289970643616181/660500000000000000 : ℝ)) (alpha := (221073782269/132100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (660289970643616181/660500000000000000 : ℝ)*(X 0 2+X 1 2)+(221073782269/132100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1053/256 : ℝ)) (lo := (5731/50000 : ℝ)) (hi := (1763/12500 : ℝ)) (c := (660289970643616181/660500000000000000 : ℝ)) (alpha := (221073782269/132100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2124573323/10000000000 : ℝ)*X 0 0+(5391386721/10000000000 : ℝ)*X 0 1+(1316769449/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068871887/2000000000 : ℝ)*X 1 0+(-2187601049/10000000000 : ℝ)*X 1 1+(658385297/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336091079/2500000000 : ℝ)*X 2 0+(5267079031/10000000000 : ℝ)*X 2 1+(-1093799491/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1088038533/2500000000 : ℝ)*X 0 0+(4228076403/10000000000 : ℝ)*X 0 1+(2239877191/5000000000 : ℝ)*X 0 2+(1088038533/2500000000 : ℝ)*X 1 0+(4228076403/10000000000 : ℝ)*X 1 1+(2239877191/5000000000 : ℝ)*X 1 2+(1088038533/2500000000 : ℝ)*X 2 0+(4228076403/10000000000 : ℝ)*X 2 1+(2239877191/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2124578621/10000000000 : ℝ)*X 0 0+(5267392919/10000000000 : ℝ)*X 0 1+(1078214003/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312665979/10000000000 : ℝ)*X 1 0+(-2063611627/10000000000 : ℝ)*X 1 1+(2695534989/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((41505203/78125000 : ℝ)*X 2 0+(2695535003/5000000000 : ℝ)*X 2 1+(-1031805791/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4352155839/10000000000 : ℝ)*X 0 0+(895824427/2000000000 : ℝ)*X 0 1+(4228718747/10000000000 : ℝ)*X 0 2+(4352155839/10000000000 : ℝ)*X 1 0+(895824427/2000000000 : ℝ)*X 1 1+(4228718747/10000000000 : ℝ)*X 1 2+(4352155839/10000000000 : ℝ)*X 2 0+(895824427/2000000000 : ℝ)*X 2 1+(4228718747/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-61924713/10000000000 : ℝ)*X 0 0+(5912161903/10000000000 : ℝ)*X 0 1+(2956107501/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s7_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16665083491798052406463623/3302500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1204892397/20000000000000 : ℝ)*(lower2) + (2172451/25000000000000 : ℝ)*(lower3) + (1048922131/50000000000000 : ℝ)*(lower4) + (661566133/100000000000000 : ℝ)*(lower5) + (6009034411425203/100000000000000 : ℝ)*(major0) + (6009034411425203/100000000000000 : ℝ)*(major1) + (1502258602856301/25000000000000 : ℝ)*(major2) + (804449358382557/10000000000000 : ℝ)*(sp0) + (8044699286983017/100000000000000 : ℝ)*(sp1) + (8044699286983017/100000000000000 : ℝ)*(sp2) + (993326045039689/25000000000000 : ℝ)*(sp3) + (183778299481/100000000000000 : ℝ)*(sp4) + (1629687547/2500000000000 : ℝ)*(sp7) + (10962428983/50000000000000 : ℝ)*(sp8) + (794673873532127/20000000000000 : ℝ)*(f.failure) + (8044699286983017/100000000000000 : ℝ)*(f.sum) + (279319013519547/13210000000000000000000000000 : ℝ)*base66 + (168194545127360257/66050000000000000000000000000000 : ℝ)*base68 + (524511077822269/16512500000000000000000000000000 : ℝ)*base70 + (783379207625960257/66050000000000000000000000000000 : ℝ)*base72 + (46081735584867/13210000000000000000000000000 : ℝ)*base74 + (125266483696884769/16512500000000000000000000000000 : ℝ)*base76 + (108403776318155257/66050000000000000000000000000000 : ℝ)*base78 + (450905160369705257/66050000000000000000000000000000 : ℝ)*base80 + (8585799919483/6605000000000000000000000000 : ℝ)*base82 + (4866733/500000000000000000000 : ℝ)*base89 + (4866733/500000000000000000000 : ℝ)*base91 + (133267/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (271145811857740508778280731/16512500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (414350451/50000000000000 : ℝ)*(lower2) + (321616919/100000000000000 : ℝ)*(lower3) + (412329051/50000000000000 : ℝ)*(lower4) + (254427397/100000000000000 : ℝ)*(lower5) + (1207917002205531/20000000000000 : ℝ)*(major0) + (1207917002205531/20000000000000 : ℝ)*(major1) + (754948126378457/12500000000000 : ℝ)*(major2) + (819429529/10000000000000 : ℝ)*(sp0) + (771058937/10000000000000 : ℝ)*(sp3) + (2021395828459947/25000000000000 : ℝ)*(sp4) + (16171198110077/200000000000 : ℝ)*(sp5) + (16171198110077/200000000000 : ℝ)*(sp6) + (998390677268193/25000000000000 : ℝ)*(sp7) + (7546903421/100000000000000 : ℝ)*(sp8) + (1996785209831071/50000000000000 : ℝ)*(f.failure) + (16171198110077/200000000000 : ℝ)*(f.sum) + (500873856484689/13210000000000000000000000000 : ℝ)*base65 + (280607823907211111/13210000000000000000000000000000 : ℝ)*base67 + (28120880456055523/2064062500000000000000000000000 : ℝ)*base69 + (93636597596681111/13210000000000000000000000000000 : ℝ)*base71 + (39208445276359/13210000000000000000000000000 : ℝ)*base73 + (12743884672669949/1032031250000000000000000000000 : ℝ)*base75 + (155830230889412111/13210000000000000000000000000000 : ℝ)*base77 + (137743114979192111/13210000000000000000000000000000 : ℝ)*base79 + (956010690173/264200000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (4629709/1250000000000000000000 : ℝ)*base89 + (4629709/1250000000000000000000 : ℝ)*base91 + (7870291/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1232_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37808179/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5731/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5733/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (141/1000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1232_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1232_s8_0 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2124576623/10000000000 : ℝ)*x 0 + (1347836781/2500000000 : ℝ)*x 1 + (210684609/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2124576623/10000000000 : ℝ)^8425 ≤ (12918828683121/100000000000000 : ℝ)^6377 := by
    have hnat : (2124576623 : ℕ)^8425*100000000000000^6377 ≤ 12918828683121^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124576623 10000000000 12918828683121 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347836781/2500000000 : ℝ)^8425 ≤ (11052760947003/25000000000000 : ℝ)^6377 := by
    have hnat : (1347836781 : ℕ)^8425*25000000000000^6377 ≤ 11052760947003^6377*2500000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347836781 2500000000 11052760947003 25000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210684609/400000000 : ℝ)^8425 ≤ (42870127512391/100000000000000 : ℝ)^6377 := by
    have hnat : (210684609 : ℕ)^8425*100000000000000^6377 ≤ 42870127512391^6377*400000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210684609 400000000 42870127512391 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2124576623/10000000000 : ℝ), (1347836781/2500000000 : ℝ), (210684609/400000000 : ℝ)] ![(12918828683121/100000000000000 : ℝ), (11052760947003/25000000000000 : ℝ), (42870127512391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2124576623/10000000000 : ℝ)|^8425 ≤ (12918828683121/100000000000000 : ℝ)^6377
        have hw : |(-2124576623/10000000000 : ℝ)|=(2124576623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347836781/2500000000 : ℝ)|^8425 ≤ (11052760947003/25000000000000 : ℝ)^6377
        have hw : |(1347836781/2500000000 : ℝ)|=(1347836781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210684609/400000000 : ℝ)|^8425 ≤ (42870127512391/100000000000000 : ℝ)^6377
        have hw : |(210684609/400000000 : ℝ)|=(210684609/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s8_1 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344352217/10000000000 : ℝ)*x 0 + (-1093783583/5000000000 : ℝ)*x 1 + (263355759/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344352217/10000000000 : ℝ)^8425 ≤ (43702617210679/100000000000000 : ℝ)^6377 := by
    have hnat : (5344352217 : ℕ)^8425*100000000000000^6377 ≤ 43702617210679^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344352217 10000000000 43702617210679 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1093783583/5000000000 : ℝ)^8425 ≤ (6713627874777/50000000000000 : ℝ)^6377 := by
    have hnat : (1093783583 : ℕ)^8425*50000000000000^6377 ≤ 6713627874777^6377*5000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093783583 5000000000 6713627874777 50000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263355759/500000000 : ℝ)^8425 ≤ (42870127028499/100000000000000 : ℝ)^6377 := by
    have hnat : (263355759 : ℕ)^8425*100000000000000^6377 ≤ 42870127028499^6377*500000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263355759 500000000 42870127028499 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344352217/10000000000 : ℝ), (-1093783583/5000000000 : ℝ), (263355759/500000000 : ℝ)] ![(43702617210679/100000000000000 : ℝ), (6713627874777/50000000000000 : ℝ), (42870127028499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344352217/10000000000 : ℝ)|^8425 ≤ (43702617210679/100000000000000 : ℝ)^6377
        have hw : |(5344352217/10000000000 : ℝ)|=(5344352217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1093783583/5000000000 : ℝ)|^8425 ≤ (6713627874777/50000000000000 : ℝ)^6377
        have hw : |(-1093783583/5000000000 : ℝ)|=(1093783583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263355759/500000000 : ℝ)|^8425 ≤ (42870127028499/100000000000000 : ℝ)^6377
        have hw : |(263355759/500000000 : ℝ)|=(263355759/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s8_2 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068870429/2000000000 : ℝ)*x 0 + (329194701/625000000 : ℝ)*x 1 + (-1093783607/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068870429/2000000000 : ℝ)^8425 ≤ (1748104657313/4000000000000 : ℝ)^6377 := by
    have hnat : (1068870429 : ℕ)^8425*4000000000000^6377 ≤ 1748104657313^6377*2000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068870429 2000000000 1748104657313 4000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329194701/625000000 : ℝ)^8425 ≤ (10717531853903/25000000000000 : ℝ)^6377 := by
    have hnat : (329194701 : ℕ)^8425*25000000000000^6377 ≤ 10717531853903^6377*625000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329194701 625000000 10717531853903 25000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1093783607/5000000000 : ℝ)^8425 ≤ (13427256138797/100000000000000 : ℝ)^6377 := by
    have hnat : (1093783607 : ℕ)^8425*100000000000000^6377 ≤ 13427256138797^6377*5000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093783607 5000000000 13427256138797 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068870429/2000000000 : ℝ), (329194701/625000000 : ℝ), (-1093783607/5000000000 : ℝ)] ![(1748104657313/4000000000000 : ℝ), (10717531853903/25000000000000 : ℝ), (13427256138797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068870429/2000000000 : ℝ)|^8425 ≤ (1748104657313/4000000000000 : ℝ)^6377
        have hw : |(1068870429/2000000000 : ℝ)|=(1068870429/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329194701/625000000 : ℝ)|^8425 ≤ (10717531853903/25000000000000 : ℝ)^6377
        have hw : |(329194701/625000000 : ℝ)|=(329194701/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1093783607/5000000000 : ℝ)|^8425 ≤ (13427256138797/100000000000000 : ℝ)^6377
        have hw : |(-1093783607/5000000000 : ℝ)|=(1093783607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s8_3 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (272009273/625000000 : ℝ)*x 0 + (845631139/2000000000 : ℝ)*x 1 + (4479682259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272009273/625000000 : ℝ)^8425 ≤ (33317459971193/100000000000000 : ℝ)^6377 := by
    have hnat : (272009273 : ℕ)^8425*100000000000000^6377 ≤ 33317459971193^6377*625000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272009273 625000000 33317459971193 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (845631139/2000000000 : ℝ)^8425 ≤ (32069176278081/100000000000000 : ℝ)^6377 := by
    have hnat : (845631139 : ℕ)^8425*100000000000000^6377 ≤ 32069176278081^6377*2000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845631139 2000000000 32069176278081 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4479682259/10000000000 : ℝ)^8425 ≤ (34613363728061/100000000000000 : ℝ)^6377 := by
    have hnat : (4479682259 : ℕ)^8425*100000000000000^6377 ≤ 34613363728061^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4479682259 10000000000 34613363728061 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(272009273/625000000 : ℝ), (845631139/2000000000 : ℝ), (4479682259/10000000000 : ℝ)] ![(33317459971193/100000000000000 : ℝ), (32069176278081/100000000000000 : ℝ), (34613363728061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(272009273/625000000 : ℝ)|^8425 ≤ (33317459971193/100000000000000 : ℝ)^6377
        have hw : |(272009273/625000000 : ℝ)|=(272009273/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(845631139/2000000000 : ℝ)|^8425 ≤ (32069176278081/100000000000000 : ℝ)^6377
        have hw : |(845631139/2000000000 : ℝ)|=(845631139/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4479682259/10000000000 : ℝ)|^8425 ≤ (34613363728061/100000000000000 : ℝ)^6377
        have hw : |(4479682259/10000000000 : ℝ)|=(4479682259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s8_4 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-42491621/200000000 : ℝ)*x 0 + (658428539/1250000000 : ℝ)*x 1 + (5391033083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42491621/200000000 : ℝ)^8425 ≤ (12918864247391/100000000000000 : ℝ)^6377 := by
    have hnat : (42491621 : ℕ)^8425*100000000000000^6377 ≤ 12918864247391^6377*200000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42491621 200000000 12918864247391 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658428539/1250000000 : ℝ)^8425 ≤ (42873494214019/100000000000000 : ℝ)^6377 := by
    have hnat : (658428539 : ℕ)^8425*100000000000000^6377 ≤ 42873494214019^6377*1250000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658428539 1250000000 42873494214019 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391033083/10000000000 : ℝ)^8425 ≤ (22103820757127/50000000000000 : ℝ)^6377 := by
    have hnat : (5391033083 : ℕ)^8425*50000000000000^6377 ≤ 22103820757127^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391033083 10000000000 22103820757127 50000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-42491621/200000000 : ℝ), (658428539/1250000000 : ℝ), (5391033083/10000000000 : ℝ)] ![(12918864247391/100000000000000 : ℝ), (42873494214019/100000000000000 : ℝ), (22103820757127/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-42491621/200000000 : ℝ)|^8425 ≤ (12918864247391/100000000000000 : ℝ)^6377
        have hw : |(-42491621/200000000 : ℝ)|=(42491621/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658428539/1250000000 : ℝ)|^8425 ≤ (42873494214019/100000000000000 : ℝ)^6377
        have hw : |(658428539/1250000000 : ℝ)|=(658428539/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391033083/10000000000 : ℝ)|^8425 ≤ (22103820757127/50000000000000 : ℝ)^6377
        have hw : |(5391033083/10000000000 : ℝ)|=(5391033083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s8_5 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312675053/10000000000 : ℝ)*x 0 + (-1031824747/5000000000 : ℝ)*x 1 + (673879141/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312675053/10000000000 : ℝ)^8425 ≤ (2710044877111/6250000000000 : ℝ)^6377 := by
    have hnat : (5312675053 : ℕ)^8425*6250000000000^6377 ≤ 2710044877111^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312675053 10000000000 2710044877111 6250000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1031824747/5000000000 : ℝ)^8425 ≤ (2486327988997/20000000000000 : ℝ)^6377 := by
    have hnat : (1031824747 : ℕ)^8425*20000000000000^6377 ≤ 2486327988997^6377*5000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031824747 5000000000 2486327988997 20000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673879141/1250000000 : ℝ)^8425 ≤ (44207642001773/100000000000000 : ℝ)^6377 := by
    have hnat : (673879141 : ℕ)^8425*100000000000000^6377 ≤ 44207642001773^6377*1250000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673879141 1250000000 44207642001773 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312675053/10000000000 : ℝ), (-1031824747/5000000000 : ℝ), (673879141/1250000000 : ℝ)] ![(2710044877111/6250000000000 : ℝ), (2486327988997/20000000000000 : ℝ), (44207642001773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312675053/10000000000 : ℝ)|^8425 ≤ (2710044877111/6250000000000 : ℝ)^6377
        have hw : |(5312675053/10000000000 : ℝ)|=(5312675053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1031824747/5000000000 : ℝ)|^8425 ≤ (2486327988997/20000000000000 : ℝ)^6377
        have hw : |(-1031824747/5000000000 : ℝ)|=(1031824747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673879141/1250000000 : ℝ)|^8425 ≤ (44207642001773/100000000000000 : ℝ)^6377
        have hw : |(673879141/1250000000 : ℝ)|=(673879141/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s8_6 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664084401/1250000000 : ℝ)*x 0 + (2695516541/5000000000 : ℝ)*x 1 + (-2063649347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664084401/1250000000 : ℝ)^8425 ≤ (4336071970513/10000000000000 : ℝ)^6377 := by
    have hnat : (664084401 : ℕ)^8425*10000000000000^6377 ≤ 4336071970513^6377*1250000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664084401 1250000000 4336071970513 10000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695516541/5000000000 : ℝ)^8425 ≤ (44207641503421/100000000000000 : ℝ)^6377 := by
    have hnat : (2695516541 : ℕ)^8425*100000000000000^6377 ≤ 44207641503421^6377*5000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695516541 5000000000 44207641503421 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2063649347/10000000000 : ℝ)^8425 ≤ (2486327755009/20000000000000 : ℝ)^6377 := by
    have hnat : (2063649347 : ℕ)^8425*20000000000000^6377 ≤ 2486327755009^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063649347 10000000000 2486327755009 20000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664084401/1250000000 : ℝ), (2695516541/5000000000 : ℝ), (-2063649347/10000000000 : ℝ)] ![(4336071970513/10000000000000 : ℝ), (44207641503421/100000000000000 : ℝ), (2486327755009/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664084401/1250000000 : ℝ)|^8425 ≤ (4336071970513/10000000000000 : ℝ)^6377
        have hw : |(664084401/1250000000 : ℝ)|=(664084401/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695516541/5000000000 : ℝ)|^8425 ≤ (44207641503421/100000000000000 : ℝ)^6377
        have hw : |(2695516541/5000000000 : ℝ)|=(2695516541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2063649347/10000000000 : ℝ)|^8425 ≤ (2486327755009/20000000000000 : ℝ)^6377
        have hw : |(-2063649347/10000000000 : ℝ)|=(2063649347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1232_s8_7 (p : ℝ) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (870431499/2000000000 : ℝ)*x 0 + (4479048751/10000000000 : ℝ)*x 1 + (4228791829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870431499/2000000000 : ℝ)^8425 ≤ (16658776140717/50000000000000 : ℝ)^6377 := by
    have hnat : (870431499 : ℕ)^8425*50000000000000^6377 ≤ 16658776140717^6377*2000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870431499 2000000000 16658776140717 50000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4479048751/10000000000 : ℝ)^8425 ≤ (8651724221223/25000000000000 : ℝ)^6377 := by
    have hnat : (4479048751 : ℕ)^8425*25000000000000^6377 ≤ 8651724221223^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4479048751 10000000000 8651724221223 25000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4228791829/10000000000 : ℝ)^8425 ≤ (32075550826531/100000000000000 : ℝ)^6377 := by
    have hnat : (4228791829 : ℕ)^8425*100000000000000^6377 ≤ 32075550826531^6377*10000000000^8425 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228791829 10000000000 32075550826531 100000000000000 8425 6377 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8425/2048 : ℝ)) 8425 6377 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(870431499/2000000000 : ℝ), (4479048751/10000000000 : ℝ), (4228791829/10000000000 : ℝ)] ![(16658776140717/50000000000000 : ℝ), (8651724221223/25000000000000 : ℝ), (32075550826531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(870431499/2000000000 : ℝ)|^8425 ≤ (16658776140717/50000000000000 : ℝ)^6377
        have hw : |(870431499/2000000000 : ℝ)|=(870431499/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4479048751/10000000000 : ℝ)|^8425 ≤ (8651724221223/25000000000000 : ℝ)^6377
        have hw : |(4479048751/10000000000 : ℝ)|=(4479048751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4228791829/10000000000 : ℝ)|^8425 ≤ (32075550826531/100000000000000 : ℝ)^6377
        have hw : |(4228791829/10000000000 : ℝ)|=(4228791829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1232_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37808179/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (141/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5733/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11467/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14099/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (141/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5733/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (141/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5733/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (141/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5733/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (141/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5733/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (141/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5733/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (141/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5733/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5733/50000 : ℝ) ^ (1053/256 : ℝ) ≤ (3380934576703343/25000000000000000000 : ℝ) := by
    have hpowers : (5733/50000 : ℝ)^1053 ≤ (3380934576703343/25000000000000000000 : ℝ)^256 := by
      have hnat : (5733 : ℕ)^1053*25000000000000000000^256 ≤ 3380934576703343^256*50000^1053 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5733 50000 3380934576703343 25000000000000000000 1053 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5733/50000 : ℝ)) (X := (3380934576703343/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1053 256 (by norm_num) hpowers
    exact h
  have hpowhi : (141/1000 : ℝ) ^ (1053/256 : ℝ) ≤ (31659126504297943/100000000000000000000 : ℝ) := by
    have hpowers : (141/1000 : ℝ)^1053 ≤ (31659126504297943/100000000000000000000 : ℝ)^256 := by
      have hnat : (141 : ℕ)^1053*100000000000000000000^256 ≤ 31659126504297943^256*1000^1053 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        141 1000 31659126504297943 100000000000000000000 1053 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (141/1000 : ℝ)) (X := (31659126504297943/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1053 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503380934576703343/12500000000000000000 : ℝ) ≤ (10000657497186587/10000000000000000 : ℝ) ^ (1053/256 : ℝ) := by
    have hpowers : (12503380934576703343/12500000000000000000 : ℝ)^256 ≤ (10000657497186587/10000000000000000 : ℝ)^1053 := by
      have hnat : (12503380934576703343 : ℕ)^256*10000000000000000^1053 ≤ 10000657497186587^1053*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503380934576703343 12500000000000000000 10000657497186587 10000000000000000 256 1053 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000657497186587/10000000000000000 : ℝ)) (X := (12503380934576703343/12500000000000000000 : ℝ)) (by norm_num) 1053 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009036572962222263/20000000000000000000 : ℝ) ≤ (2500274568758113/2500000000000000 : ℝ) ^ (1053/256 : ℝ) := by
    have hpowers : (20009036572962222263/20000000000000000000 : ℝ)^256 ≤ (2500274568758113/2500000000000000 : ℝ)^1053 := by
      have hnat : (20009036572962222263 : ℕ)^256*2500000000000000^1053 ≤ 2500274568758113^1053*20000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009036572962222263 20000000000000000000 2500274568758113 2500000000000000 256 1053 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500274568758113/2500000000000000 : ℝ)) (X := (20009036572962222263/20000000000000000000 : ℝ)) (by norm_num) 1053 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031659126504297943/50000000000000000000 : ℝ) ≤ (10001539052878317/10000000000000000 : ℝ) ^ (1053/256 : ℝ) := by
    have hpowers : (50031659126504297943/50000000000000000000 : ℝ)^256 ≤ (10001539052878317/10000000000000000 : ℝ)^1053 := by
      have hnat : (50031659126504297943 : ℕ)^256*10000000000000000^1053 ≤ 10001539052878317^1053*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031659126504297943 50000000000000000000 10001539052878317 10000000000000000 256 1053 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001539052878317/10000000000000000 : ℝ)) (X := (50031659126504297943/50000000000000000000 : ℝ)) (by norm_num) 1053 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3380934576703343/25000000000000000000 : ℝ) ≤ ((4388603988338015663/4390000000000000000 : ℝ)+2*(88155569173/52680000000000 : ℝ)*(5733/50000 : ℝ))^(1053/256 : ℝ) := by
    rw [show (4388603988338015663/4390000000000000000 : ℝ)+2*(88155569173/52680000000000 : ℝ)*(5733/50000 : ℝ)=(10000657497186587/10000000000000000 : ℝ) by norm_num, show 1+2*(3380934576703343/25000000000000000000 : ℝ)=(12503380934576703343/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31659126504297943/100000000000000000000 : ℝ)+(3380934576703343/25000000000000000000 : ℝ) ≤ ((4388603988338015663/4390000000000000000 : ℝ)+(88155569173/52680000000000 : ℝ)*((141/1000 : ℝ)+(5733/50000 : ℝ)))^(1053/256 : ℝ) := by
    rw [show (4388603988338015663/4390000000000000000 : ℝ)+(88155569173/52680000000000 : ℝ)*((141/1000 : ℝ)+(5733/50000 : ℝ))=(2500274568758113/2500000000000000 : ℝ) by norm_num, show 1+(31659126504297943/100000000000000000000 : ℝ)+(3380934576703343/25000000000000000000 : ℝ)=(20009036572962222263/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31659126504297943/100000000000000000000 : ℝ) ≤ ((4388603988338015663/4390000000000000000 : ℝ)+2*(88155569173/52680000000000 : ℝ)*(141/1000 : ℝ))^(1053/256 : ℝ) := by
    rw [show (4388603988338015663/4390000000000000000 : ℝ)+2*(88155569173/52680000000000 : ℝ)*(141/1000 : ℝ)=(10001539052878317/10000000000000000 : ℝ) by norm_num, show 1+2*(31659126504297943/100000000000000000000 : ℝ)=(50031659126504297943/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4388603988338015663/4390000000000000000 : ℝ)*(X 1 0+X 2 0)+(88155569173/52680000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1053/256 : ℝ)) (lo := (5733/50000 : ℝ)) (hi := (141/1000 : ℝ)) (c := (4388603988338015663/4390000000000000000 : ℝ)) (alpha := (88155569173/52680000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4388603988338015663/4390000000000000000 : ℝ)*(X 0 1+X 2 1)+(88155569173/52680000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1053/256 : ℝ)) (lo := (5733/50000 : ℝ)) (hi := (141/1000 : ℝ)) (c := (4388603988338015663/4390000000000000000 : ℝ)) (alpha := (88155569173/52680000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4388603988338015663/4390000000000000000 : ℝ)*(X 0 2+X 1 2)+(88155569173/52680000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1053/256 : ℝ)) (lo := (5733/50000 : ℝ)) (hi := (141/1000 : ℝ)) (c := (4388603988338015663/4390000000000000000 : ℝ)) (alpha := (88155569173/52680000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2124576623/10000000000 : ℝ)*X 0 0+(1347836781/2500000000 : ℝ)*X 0 1+(210684609/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344352217/10000000000 : ℝ)*X 1 0+(-1093783583/5000000000 : ℝ)*X 1 1+(263355759/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068870429/2000000000 : ℝ)*X 2 0+(329194701/625000000 : ℝ)*X 2 1+(-1093783607/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((272009273/625000000 : ℝ)*X 0 0+(845631139/2000000000 : ℝ)*X 0 1+(4479682259/10000000000 : ℝ)*X 0 2+(272009273/625000000 : ℝ)*X 1 0+(845631139/2000000000 : ℝ)*X 1 1+(4479682259/10000000000 : ℝ)*X 1 2+(272009273/625000000 : ℝ)*X 2 0+(845631139/2000000000 : ℝ)*X 2 1+(4479682259/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-42491621/200000000 : ℝ)*X 0 0+(658428539/1250000000 : ℝ)*X 0 1+(5391033083/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312675053/10000000000 : ℝ)*X 1 0+(-1031824747/5000000000 : ℝ)*X 1 1+(673879141/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664084401/1250000000 : ℝ)*X 2 0+(2695516541/5000000000 : ℝ)*X 2 1+(-2063649347/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((870431499/2000000000 : ℝ)*X 0 0+(4479048751/10000000000 : ℝ)*X 0 1+(4228791829/10000000000 : ℝ)*X 0 2+(870431499/2000000000 : ℝ)*X 1 0+(4479048751/10000000000 : ℝ)*X 1 1+(4228791829/10000000000 : ℝ)*X 1 2+(870431499/2000000000 : ℝ)*X 2 0+(4479048751/10000000000 : ℝ)*X 2 1+(4228791829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1232_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1160076031154001477921146987/219500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1210321481/100000000000000 : ℝ)*(base19) + (977880489/100000000000000 : ℝ)*(base23) + (4141757/6250000000000 : ℝ)*(lower2) + (45531341/20000000000000 : ℝ)*(upper3) + (1899669/5000000000000 : ℝ)*(upper5) + (1503158984077227/25000000000000 : ℝ)*(major0) + (1503158984077227/25000000000000 : ℝ)*(major1) + (6012635936308909/100000000000000 : ℝ)*(major2) + (503093496949971/6250000000000 : ℝ)*(sp0) + (4024759836425577/50000000000000 : ℝ)*(sp1) + (4024759952646073/50000000000000 : ℝ)*(sp2) + (1987867491710717/50000000000000 : ℝ)*(sp3) + (249319731/1000000000000 : ℝ)*(sp4) + (3957463563/25000000000000 : ℝ)*(sp7) + (1987875406637843/50000000000000 : ℝ)*(f.failure) + (2012380220793159/25000000000000 : ℝ)*(f.sum) + (7578770146909/5268000000000000000000000000 : ℝ)*base65 + (2187174913353382003/329250000000000000000000000000000 : ℝ)*base67 + (4490919276459441667/439000000000000000000000000000000 : ℝ)*base69 + (3953172739073617997/329250000000000000000000000000000 : ℝ)*base72 + (16459249552117/5268000000000000000000000000 : ℝ)*base73 + (18771890070479441667/439000000000000000000000000000000 : ℝ)*base75 + (1123930217752356501/109750000000000000000000000000000 : ℝ)*base77 + (2110537962141356501/109750000000000000000000000000000 : ℝ)*base79 + (68566316223/54875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (6317897/1250000000000000000000 : ℝ)*base89 + (6317897/1250000000000000000000 : ℝ)*base91 + (6182103/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1279890816783809507503318199/109750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (185870931/25000000000000 : ℝ)*(base19) + (1434897069/100000000000000 : ℝ)*(base23) + (145987573/50000000000000 : ℝ)*(lower1) + (87100269/100000000000000 : ℝ)*(upper3) + (44261367/25000000000000 : ℝ)*(lower4) + (204561/195312500000 : ℝ)*(upper5) + (3021539990959891/50000000000000 : ℝ)*(major0) + (3021539990959891/50000000000000 : ℝ)*(major1) + (3021539990959891/50000000000000 : ℝ)*(major2) + (20481992119/100000000000000 : ℝ)*(sp2) + (1011284770850579/12500000000000 : ℝ)*(sp4) + (8090277423320907/100000000000000 : ℝ)*(sp5) + (8090256249915443/100000000000000 : ℝ)*(sp6) + (799176281661143/20000000000000 : ℝ)*(sp7) + (799176281661143/20000000000000 : ℝ)*(f.failure) + (1011284770850579/12500000000000 : ℝ)*(f.sum) + (4222897446059/658500000000000000000000000 : ℝ)*base65 + (18760602749892431801/658500000000000000000000000000000 : ℝ)*base68 + (4700304192549431801/658500000000000000000000000000000 : ℝ)*base70 + (49412436943141931801/658500000000000000000000000000000 : ℝ)*base72 + (208197341797/164625000000000000000000000 : ℝ)*base74 + (146872012624989431801/658500000000000000000000000000000 : ℝ)*base76 + (4491747924370068199/658500000000000000000000000000000 : ℝ)*base77 + (14346718222016568199/658500000000000000000000000000000 : ℝ)*base79 + (2161178531573/1317000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1888597/500000000000000000000 : ℝ)*base89 + (1888597/500000000000000000000 : ℝ)*base91 + (1888597/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1232_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37808179/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (141/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5733/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11467/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14099/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1232_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1232_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37808179/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7063/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11441/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11467/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14099/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1232_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1232_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1232_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1053/256 : ℝ) ≤ p) (hpb : p ≤ (8425/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37808179/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7063/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11441/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11467/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14099/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1232_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
