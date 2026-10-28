-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1288_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:25:08.387196+00:00
-- url     : https://prove2.me/submissions/fc0b5608-b183-4fd6-b427-348cb34c80ee

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
theorem support_rectangle_w1288_box_0 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-959941547/5000000000 : ℝ)*x 0 + (5392175593/10000000000 : ℝ)*x 1 + (5392175447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (959941547/5000000000 : ℝ)^531 ≤ (11366586226633/100000000000000 : ℝ)^403 := by
    have hnat : (959941547 : ℕ)^531*100000000000000^403 ≤ 11366586226633^403*5000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      959941547 5000000000 11366586226633 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392175593/10000000000 : ℝ)^531 ≤ (2215835383373/5000000000000 : ℝ)^403 := by
    have hnat : (5392175593 : ℕ)^531*5000000000000^403 ≤ 2215835383373^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392175593 10000000000 2215835383373 5000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392175447/10000000000 : ℝ)^531 ≤ (4431670608641/10000000000000 : ℝ)^403 := by
    have hnat : (5392175447 : ℕ)^531*10000000000000^403 ≤ 4431670608641^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392175447 10000000000 4431670608641 10000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-959941547/5000000000 : ℝ), (5392175593/10000000000 : ℝ), (5392175447/10000000000 : ℝ)] ![(11366586226633/100000000000000 : ℝ), (2215835383373/5000000000000 : ℝ), (4431670608641/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-959941547/5000000000 : ℝ)|^531 ≤ (11366586226633/100000000000000 : ℝ)^403
        have hw : |(-959941547/5000000000 : ℝ)|=(959941547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392175593/10000000000 : ℝ)|^531 ≤ (2215835383373/5000000000000 : ℝ)^403
        have hw : |(5392175593/10000000000 : ℝ)|=(5392175593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392175447/10000000000 : ℝ)|^531 ≤ (4431670608641/10000000000000 : ℝ)^403
        have hw : |(5392175447/10000000000 : ℝ)|=(5392175447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_box_1 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5284296407/10000000000 : ℝ)*x 0 + (-10336961/50000000 : ℝ)*x 1 + (5392175507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284296407/10000000000 : ℝ)^531 ≤ (21576100210517/50000000000000 : ℝ)^403 := by
    have hnat : (5284296407 : ℕ)^531*50000000000000^403 ≤ 21576100210517^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284296407 10000000000 21576100210517 50000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10336961/50000000 : ℝ)^531 ≤ (12531092832907/100000000000000 : ℝ)^403 := by
    have hnat : (10336961 : ℕ)^531*100000000000000^403 ≤ 12531092832907^403*50000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10336961 50000000 12531092832907 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392175507/10000000000 : ℝ)^531 ≤ (44316706736157/100000000000000 : ℝ)^403 := by
    have hnat : (5392175507 : ℕ)^531*100000000000000^403 ≤ 44316706736157^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392175507 10000000000 44316706736157 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284296407/10000000000 : ℝ), (-10336961/50000000 : ℝ), (5392175507/10000000000 : ℝ)] ![(21576100210517/50000000000000 : ℝ), (12531092832907/100000000000000 : ℝ), (44316706736157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284296407/10000000000 : ℝ)|^531 ≤ (21576100210517/50000000000000 : ℝ)^403
        have hw : |(5284296407/10000000000 : ℝ)|=(5284296407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-10336961/50000000 : ℝ)|^531 ≤ (12531092832907/100000000000000 : ℝ)^403
        have hw : |(-10336961/50000000 : ℝ)|=(10336961/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392175507/10000000000 : ℝ)|^531 ≤ (44316706736157/100000000000000 : ℝ)^403
        have hw : |(5392175507/10000000000 : ℝ)|=(5392175507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_box_2 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1321074143/2500000000 : ℝ)*x 0 + (2696087757/5000000000 : ℝ)*x 1 + (-64605999/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321074143/2500000000 : ℝ)^531 ≤ (21576101098203/50000000000000 : ℝ)^403 := by
    have hnat : (1321074143 : ℕ)^531*50000000000000^403 ≤ 21576101098203^403*2500000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321074143 2500000000 21576101098203 50000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696087757/5000000000 : ℝ)^531 ≤ (1107917670299/2500000000000 : ℝ)^403 := by
    have hnat : (2696087757 : ℕ)^531*2500000000000^403 ≤ 1107917670299^403*5000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696087757 5000000000 1107917670299 2500000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (64605999/312500000 : ℝ)^531 ≤ (12531090980043/100000000000000 : ℝ)^403 := by
    have hnat : (64605999 : ℕ)^531*100000000000000^403 ≤ 12531090980043^403*312500000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64605999 312500000 12531090980043 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321074143/2500000000 : ℝ), (2696087757/5000000000 : ℝ), (-64605999/312500000 : ℝ)] ![(21576101098203/50000000000000 : ℝ), (1107917670299/2500000000000 : ℝ), (12531090980043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321074143/2500000000 : ℝ)|^531 ≤ (21576101098203/50000000000000 : ℝ)^403
        have hw : |(1321074143/2500000000 : ℝ)|=(1321074143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696087757/5000000000 : ℝ)|^531 ≤ (1107917670299/2500000000000 : ℝ)^403
        have hw : |(2696087757/5000000000 : ℝ)|=(2696087757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-64605999/312500000 : ℝ)|^531 ≤ (12531090980043/100000000000000 : ℝ)^403
        have hw : |(-64605999/312500000 : ℝ)|=(64605999/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_box_3 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4490468927/10000000000 : ℝ)*x 0 + (4270194603/10000000000 : ℝ)*x 1 + (266887159/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4490468927/10000000000 : ℝ)^531 ≤ (17410984552237/50000000000000 : ℝ)^403 := by
    have hnat : (4490468927 : ℕ)^531*50000000000000^403 ≤ 17410984552237^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490468927 10000000000 17410984552237 50000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4270194603/10000000000 : ℝ)^531 ≤ (32589015741349/100000000000000 : ℝ)^403 := by
    have hnat : (4270194603 : ℕ)^531*100000000000000^403 ≤ 32589015741349^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4270194603 10000000000 32589015741349 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (266887159/625000000 : ℝ)^531 ≤ (32589015148061/100000000000000 : ℝ)^403 := by
    have hnat : (266887159 : ℕ)^531*100000000000000^403 ≤ 32589015148061^403*625000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266887159 625000000 32589015148061 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4490468927/10000000000 : ℝ), (4270194603/10000000000 : ℝ), (266887159/625000000 : ℝ)] ![(17410984552237/50000000000000 : ℝ), (32589015741349/100000000000000 : ℝ), (32589015148061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4490468927/10000000000 : ℝ)|^531 ≤ (17410984552237/50000000000000 : ℝ)^403
        have hw : |(4490468927/10000000000 : ℝ)|=(4490468927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4270194603/10000000000 : ℝ)|^531 ≤ (32589015741349/100000000000000 : ℝ)^403
        have hw : |(4270194603/10000000000 : ℝ)|=(4270194603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(266887159/625000000 : ℝ)|^531 ≤ (32589015148061/100000000000000 : ℝ)^403
        have hw : |(266887159/625000000 : ℝ)|=(266887159/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_box_4 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-226600451/1000000000 : ℝ)*x 0 + (1052717221/2000000000 : ℝ)*x 1 + (5263586259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (226600451/1000000000 : ℝ)^531 ≤ (14140998347027/100000000000000 : ℝ)^403 := by
    have hnat : (226600451 : ℕ)^531*100000000000000^403 ≤ 14140998347027^403*1000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226600451 1000000000 14140998347027 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052717221/2000000000 : ℝ)^531 ≤ (42929499994161/100000000000000 : ℝ)^403 := by
    have hnat : (1052717221 : ℕ)^531*100000000000000^403 ≤ 42929499994161^403*2000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052717221 2000000000 42929499994161 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263586259/10000000000 : ℝ)^531 ≤ (10732375412277/25000000000000 : ℝ)^403 := by
    have hnat : (5263586259 : ℕ)^531*25000000000000^403 ≤ 10732375412277^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263586259 10000000000 10732375412277 25000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-226600451/1000000000 : ℝ), (1052717221/2000000000 : ℝ), (5263586259/10000000000 : ℝ)] ![(14140998347027/100000000000000 : ℝ), (42929499994161/100000000000000 : ℝ), (10732375412277/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-226600451/1000000000 : ℝ)|^531 ≤ (14140998347027/100000000000000 : ℝ)^403
        have hw : |(-226600451/1000000000 : ℝ)|=(226600451/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052717221/2000000000 : ℝ)|^531 ≤ (42929499994161/100000000000000 : ℝ)^403
        have hw : |(1052717221/2000000000 : ℝ)|=(1052717221/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263586259/10000000000 : ℝ)|^531 ≤ (10732375412277/25000000000000 : ℝ)^403
        have hw : |(5263586259/10000000000 : ℝ)|=(5263586259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_box_5 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5374824269/10000000000 : ℝ)*x 0 + (-132411989/625000000 : ℝ)*x 1 + (5263585987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374824269/10000000000 : ℝ)^531 ≤ (1379028259023/3125000000000 : ℝ)^403 := by
    have hnat : (5374824269 : ℕ)^531*3125000000000^403 ≤ 1379028259023^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374824269 10000000000 1379028259023 3125000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (132411989/625000000 : ℝ)^531 ≤ (12941596976157/100000000000000 : ℝ)^403 := by
    have hnat : (132411989 : ℕ)^531*100000000000000^403 ≤ 12941596976157^403*625000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132411989 625000000 12941596976157 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263585987/10000000000 : ℝ)^531 ≤ (10732374681521/25000000000000 : ℝ)^403 := by
    have hnat : (5263585987 : ℕ)^531*25000000000000^403 ≤ 10732374681521^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263585987 10000000000 10732374681521 25000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374824269/10000000000 : ℝ), (-132411989/625000000 : ℝ), (5263585987/10000000000 : ℝ)] ![(1379028259023/3125000000000 : ℝ), (12941596976157/100000000000000 : ℝ), (10732374681521/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374824269/10000000000 : ℝ)|^531 ≤ (1379028259023/3125000000000 : ℝ)^403
        have hw : |(5374824269/10000000000 : ℝ)|=(5374824269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-132411989/625000000 : ℝ)|^531 ≤ (12941596976157/100000000000000 : ℝ)^403
        have hw : |(-132411989/625000000 : ℝ)|=(132411989/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263585987/10000000000 : ℝ)|^531 ≤ (10732374681521/25000000000000 : ℝ)^403
        have hw : |(5263585987/10000000000 : ℝ)|=(5263585987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_box_6 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5374824291/10000000000 : ℝ)*x 0 + (5263585953/10000000000 : ℝ)*x 1 + (-1059295919/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374824291/10000000000 : ℝ)^531 ≤ (11032226131683/25000000000000 : ℝ)^403 := by
    have hnat : (5374824291 : ℕ)^531*25000000000000^403 ≤ 11032226131683^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374824291 10000000000 11032226131683 25000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263585953/10000000000 : ℝ)^531 ≤ (21464749180353/50000000000000 : ℝ)^403 := by
    have hnat : (5263585953 : ℕ)^531*50000000000000^403 ≤ 21464749180353^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263585953 10000000000 21464749180353 50000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1059295919/5000000000 : ℝ)^531 ≤ (323539927221/2500000000000 : ℝ)^403 := by
    have hnat : (1059295919 : ℕ)^531*2500000000000^403 ≤ 323539927221^403*5000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059295919 5000000000 323539927221 2500000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374824291/10000000000 : ℝ), (5263585953/10000000000 : ℝ), (-1059295919/5000000000 : ℝ)] ![(11032226131683/25000000000000 : ℝ), (21464749180353/50000000000000 : ℝ), (323539927221/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374824291/10000000000 : ℝ)|^531 ≤ (11032226131683/25000000000000 : ℝ)^403
        have hw : |(5374824291/10000000000 : ℝ)|=(5374824291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263585953/10000000000 : ℝ)|^531 ≤ (21464749180353/50000000000000 : ℝ)^403
        have hw : |(5263585953/10000000000 : ℝ)|=(5263585953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1059295919/5000000000 : ℝ)|^531 ≤ (323539927221/2500000000000 : ℝ)^403
        have hw : |(-1059295919/5000000000 : ℝ)|=(1059295919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_box_7 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (209528649/500000000 : ℝ)*x 0 + (2210043577/5000000000 : ℝ)*x 1 + (2210043461/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (209528649/500000000 : ℝ)^531 ≤ (31790744191877/100000000000000 : ℝ)^403 := by
    have hnat : (209528649 : ℕ)^531*100000000000000^403 ≤ 31790744191877^403*500000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209528649 500000000 31790744191877 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2210043577/5000000000 : ℝ)^531 ≤ (17052314537451/50000000000000 : ℝ)^403 := by
    have hnat : (2210043577 : ℕ)^531*50000000000000^403 ≤ 17052314537451^403*5000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210043577 5000000000 17052314537451 50000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2210043461/5000000000 : ℝ)^531 ≤ (2131539169767/6250000000000 : ℝ)^403 := by
    have hnat : (2210043461 : ℕ)^531*6250000000000^403 ≤ 2131539169767^403*5000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210043461 5000000000 2131539169767 6250000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(209528649/500000000 : ℝ), (2210043577/5000000000 : ℝ), (2210043461/5000000000 : ℝ)] ![(31790744191877/100000000000000 : ℝ), (17052314537451/50000000000000 : ℝ), (2131539169767/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(209528649/500000000 : ℝ)|^531 ≤ (31790744191877/100000000000000 : ℝ)^403
        have hw : |(209528649/500000000 : ℝ)|=(209528649/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2210043577/5000000000 : ℝ)|^531 ≤ (17052314537451/50000000000000 : ℝ)^403
        have hw : |(2210043577/5000000000 : ℝ)|=(2210043577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2210043461/5000000000 : ℝ)|^531 ≤ (2131539169767/6250000000000 : ℝ)^403
        have hw : |(2210043461/5000000000 : ℝ)|=(2210043461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_box_8 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2193472931/10000000000 : ℝ)*x 0 + (5175325123/10000000000 : ℝ)*x 1 + (5406214447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2193472931/10000000000 : ℝ)^531 ≤ (6773827364631/50000000000000 : ℝ)^403 := by
    have hnat : (2193472931 : ℕ)^531*50000000000000^403 ≤ 6773827364631^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2193472931 10000000000 6773827364631 50000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5175325123/10000000000 : ℝ)^531 ≤ (41983546403691/100000000000000 : ℝ)^403 := by
    have hnat : (5175325123 : ℕ)^531*100000000000000^403 ≤ 41983546403691^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175325123 10000000000 41983546403691 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406214447/10000000000 : ℝ)^531 ≤ (44468798843741/100000000000000 : ℝ)^403 := by
    have hnat : (5406214447 : ℕ)^531*100000000000000^403 ≤ 44468798843741^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406214447 10000000000 44468798843741 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2193472931/10000000000 : ℝ), (5175325123/10000000000 : ℝ), (5406214447/10000000000 : ℝ)] ![(6773827364631/50000000000000 : ℝ), (41983546403691/100000000000000 : ℝ), (44468798843741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2193472931/10000000000 : ℝ)|^531 ≤ (6773827364631/50000000000000 : ℝ)^403
        have hw : |(-2193472931/10000000000 : ℝ)|=(2193472931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5175325123/10000000000 : ℝ)|^531 ≤ (41983546403691/100000000000000 : ℝ)^403
        have hw : |(5175325123/10000000000 : ℝ)|=(5175325123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406214447/10000000000 : ℝ)|^531 ≤ (44468798843741/100000000000000 : ℝ)^403
        have hw : |(5406214447/10000000000 : ℝ)|=(5406214447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_box_9 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5274406927/10000000000 : ℝ)*x 0 + (-2061665251/10000000000 : ℝ)*x 1 + (5406214759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5274406927/10000000000 : ℝ)^531 ≤ (21522911487743/50000000000000 : ℝ)^403 := by
    have hnat : (5274406927 : ℕ)^531*50000000000000^403 ≤ 21522911487743^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274406927 10000000000 21522911487743 50000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2061665251/10000000000 : ℝ)^531 ≤ (99882998307/800000000000 : ℝ)^403 := by
    have hnat : (2061665251 : ℕ)^531*800000000000^403 ≤ 99882998307^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2061665251 10000000000 99882998307 800000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406214759/10000000000 : ℝ)^531 ≤ (694825034769/1562500000000 : ℝ)^403 := by
    have hnat : (5406214759 : ℕ)^531*1562500000000^403 ≤ 694825034769^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406214759 10000000000 694825034769 1562500000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5274406927/10000000000 : ℝ), (-2061665251/10000000000 : ℝ), (5406214759/10000000000 : ℝ)] ![(21522911487743/50000000000000 : ℝ), (99882998307/800000000000 : ℝ), (694825034769/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5274406927/10000000000 : ℝ)|^531 ≤ (21522911487743/50000000000000 : ℝ)^403
        have hw : |(5274406927/10000000000 : ℝ)|=(5274406927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2061665251/10000000000 : ℝ)|^531 ≤ (99882998307/800000000000 : ℝ)^403
        have hw : |(-2061665251/10000000000 : ℝ)|=(2061665251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406214759/10000000000 : ℝ)|^531 ≤ (694825034769/1562500000000 : ℝ)^403
        have hw : |(5406214759/10000000000 : ℝ)|=(5406214759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_box_10 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5274406563/10000000000 : ℝ)*x 0 + (2703107273/5000000000 : ℝ)*x 1 + (-206166603/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5274406563/10000000000 : ℝ)^531 ≤ (43045819061239/100000000000000 : ℝ)^403 := by
    have hnat : (5274406563 : ℕ)^531*100000000000000^403 ≤ 43045819061239^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274406563 10000000000 43045819061239 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703107273/5000000000 : ℝ)^531 ≤ (44468799916709/100000000000000 : ℝ)^403 := by
    have hnat : (2703107273 : ℕ)^531*100000000000000^403 ≤ 44468799916709^403*5000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703107273 5000000000 44468799916709 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (206166603/1000000000 : ℝ)^531 ≤ (6242690502183/50000000000000 : ℝ)^403 := by
    have hnat : (206166603 : ℕ)^531*50000000000000^403 ≤ 6242690502183^403*1000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206166603 1000000000 6242690502183 50000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5274406563/10000000000 : ℝ), (2703107273/5000000000 : ℝ), (-206166603/1000000000 : ℝ)] ![(43045819061239/100000000000000 : ℝ), (44468799916709/100000000000000 : ℝ), (6242690502183/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5274406563/10000000000 : ℝ)|^531 ≤ (43045819061239/100000000000000 : ℝ)^403
        have hw : |(5274406563/10000000000 : ℝ)|=(5274406563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703107273/5000000000 : ℝ)|^531 ≤ (44468799916709/100000000000000 : ℝ)^403
        have hw : |(2703107273/5000000000 : ℝ)|=(2703107273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-206166603/1000000000 : ℝ)|^531 ≤ (6242690502183/50000000000000 : ℝ)^403
        have hw : |(-206166603/1000000000 : ℝ)|=(206166603/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_box_11 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (452264997/1000000000 : ℝ)*x 0 + (2126908449/5000000000 : ℝ)*x 1 + (850763169/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (452264997/1000000000 : ℝ)^531 ≤ (8787789354951/25000000000000 : ℝ)^403 := by
    have hnat : (452264997 : ℕ)^531*25000000000000^403 ≤ 8787789354951^403*1000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452264997 1000000000 8787789354951 25000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2126908449/5000000000 : ℝ)^531 ≤ (506631665147/1562500000000 : ℝ)^403 := by
    have hnat : (2126908449 : ℕ)^531*1562500000000^403 ≤ 506631665147^403*5000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126908449 5000000000 506631665147 1562500000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (850763169/2000000000 : ℝ)^531 ≤ (16212207996827/50000000000000 : ℝ)^403 := by
    have hnat : (850763169 : ℕ)^531*50000000000000^403 ≤ 16212207996827^403*2000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850763169 2000000000 16212207996827 50000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(452264997/1000000000 : ℝ), (2126908449/5000000000 : ℝ), (850763169/2000000000 : ℝ)] ![(8787789354951/25000000000000 : ℝ), (506631665147/1562500000000 : ℝ), (16212207996827/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(452264997/1000000000 : ℝ)|^531 ≤ (8787789354951/25000000000000 : ℝ)^403
        have hw : |(452264997/1000000000 : ℝ)|=(452264997/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2126908449/5000000000 : ℝ)|^531 ≤ (506631665147/1562500000000 : ℝ)^403
        have hw : |(2126908449/5000000000 : ℝ)|=(2126908449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(850763169/2000000000 : ℝ)|^531 ≤ (16212207996827/50000000000000 : ℝ)^403
        have hw : |(850763169/2000000000 : ℝ)|=(850763169/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_box_12 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1992862283/10000000000 : ℝ)*x 0 + (1369525851/2500000000 : ℝ)*x 1 + (52525673/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1992862283/10000000000 : ℝ)^531 ≤ (5969648541823/50000000000000 : ℝ)^403 := by
    have hnat : (1992862283 : ℕ)^531*50000000000000^403 ≤ 5969648541823^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1992862283 10000000000 5969648541823 50000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1369525851/2500000000 : ℝ)^531 ≤ (45249576168451/100000000000000 : ℝ)^403 := by
    have hnat : (1369525851 : ℕ)^531*100000000000000^403 ≤ 45249576168451^403*2500000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369525851 2500000000 45249576168451 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52525673/100000000 : ℝ)^531 ≤ (42811126737417/100000000000000 : ℝ)^403 := by
    have hnat : (52525673 : ℕ)^531*100000000000000^403 ≤ 42811126737417^403*100000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52525673 100000000 42811126737417 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1992862283/10000000000 : ℝ), (1369525851/2500000000 : ℝ), (52525673/100000000 : ℝ)] ![(5969648541823/50000000000000 : ℝ), (45249576168451/100000000000000 : ℝ), (42811126737417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1992862283/10000000000 : ℝ)|^531 ≤ (5969648541823/50000000000000 : ℝ)^403
        have hw : |(-1992862283/10000000000 : ℝ)|=(1992862283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1369525851/2500000000 : ℝ)|^531 ≤ (45249576168451/100000000000000 : ℝ)^403
        have hw : |(1369525851/2500000000 : ℝ)|=(1369525851/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(52525673/100000000 : ℝ)|^531 ≤ (42811126737417/100000000000000 : ℝ)^403
        have hw : |(52525673/100000000 : ℝ)|=(52525673/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_box_13 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2691289289/5000000000 : ℝ)*x 0 + (-530718189/2500000000 : ℝ)*x 1 + (1313141803/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2691289289/5000000000 : ℝ)^531 ≤ (44212809881939/100000000000000 : ℝ)^403 := by
    have hnat : (2691289289 : ℕ)^531*100000000000000^403 ≤ 44212809881939^403*5000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2691289289 5000000000 44212809881939 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (530718189/2500000000 : ℝ)^531 ≤ (12976064307643/100000000000000 : ℝ)^403 := by
    have hnat : (530718189 : ℕ)^531*100000000000000^403 ≤ 12976064307643^403*2500000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530718189 2500000000 12976064307643 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313141803/2500000000 : ℝ)^531 ≤ (21405562896181/50000000000000 : ℝ)^403 := by
    have hnat : (1313141803 : ℕ)^531*50000000000000^403 ≤ 21405562896181^403*2500000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313141803 2500000000 21405562896181 50000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2691289289/5000000000 : ℝ), (-530718189/2500000000 : ℝ), (1313141803/2500000000 : ℝ)] ![(44212809881939/100000000000000 : ℝ), (12976064307643/100000000000000 : ℝ), (21405562896181/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2691289289/5000000000 : ℝ)|^531 ≤ (44212809881939/100000000000000 : ℝ)^403
        have hw : |(2691289289/5000000000 : ℝ)|=(2691289289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-530718189/2500000000 : ℝ)|^531 ≤ (12976064307643/100000000000000 : ℝ)^403
        have hw : |(-530718189/2500000000 : ℝ)|=(530718189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313141803/2500000000 : ℝ)|^531 ≤ (21405562896181/50000000000000 : ℝ)^403
        have hw : |(1313141803/2500000000 : ℝ)|=(1313141803/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_box_14 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2691289067/5000000000 : ℝ)*x 0 + (5252568087/10000000000 : ℝ)*x 1 + (-1061436093/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2691289067/5000000000 : ℝ)^531 ≤ (11053201269133/25000000000000 : ℝ)^403 := by
    have hnat : (2691289067 : ℕ)^531*25000000000000^403 ≤ 11053201269133^403*5000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2691289067 5000000000 11053201269133 25000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5252568087/10000000000 : ℝ)^531 ≤ (21405567594609/50000000000000 : ℝ)^403 := by
    have hnat : (5252568087 : ℕ)^531*50000000000000^403 ≤ 21405567594609^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252568087 10000000000 21405567594609 50000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1061436093/5000000000 : ℝ)^531 ≤ (405501866153/3125000000000 : ℝ)^403 := by
    have hnat : (1061436093 : ℕ)^531*3125000000000^403 ≤ 405501866153^403*5000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061436093 5000000000 405501866153 3125000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2691289067/5000000000 : ℝ), (5252568087/10000000000 : ℝ), (-1061436093/5000000000 : ℝ)] ![(11053201269133/25000000000000 : ℝ), (21405567594609/50000000000000 : ℝ), (405501866153/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2691289067/5000000000 : ℝ)|^531 ≤ (11053201269133/25000000000000 : ℝ)^403
        have hw : |(2691289067/5000000000 : ℝ)|=(2691289067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5252568087/10000000000 : ℝ)|^531 ≤ (21405567594609/50000000000000 : ℝ)^403
        have hw : |(5252568087/10000000000 : ℝ)|=(5252568087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1061436093/5000000000 : ℝ)|^531 ≤ (405501866153/3125000000000 : ℝ)^403
        have hw : |(-1061436093/5000000000 : ℝ)|=(1061436093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_box_15 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2082214151/5000000000 : ℝ)*x 0 + (4432921799/10000000000 : ℝ)*x 1 + (1108230141/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2082214151/5000000000 : ℝ)^531 ≤ (31529666999041/100000000000000 : ℝ)^403 := by
    have hnat : (2082214151 : ℕ)^531*100000000000000^403 ≤ 31529666999041^403*5000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082214151 5000000000 31529666999041 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4432921799/10000000000 : ℝ)^531 ≤ (34235172776661/100000000000000 : ℝ)^403 := by
    have hnat : (4432921799 : ℕ)^531*100000000000000^403 ≤ 34235172776661^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4432921799 10000000000 34235172776661 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1108230141/2500000000 : ℝ)^531 ≤ (34235160209451/100000000000000 : ℝ)^403 := by
    have hnat : (1108230141 : ℕ)^531*100000000000000^403 ≤ 34235160209451^403*2500000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108230141 2500000000 34235160209451 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2082214151/5000000000 : ℝ), (4432921799/10000000000 : ℝ), (1108230141/2500000000 : ℝ)] ![(31529666999041/100000000000000 : ℝ), (34235172776661/100000000000000 : ℝ), (34235160209451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2082214151/5000000000 : ℝ)|^531 ≤ (31529666999041/100000000000000 : ℝ)^403
        have hw : |(2082214151/5000000000 : ℝ)|=(2082214151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4432921799/10000000000 : ℝ)|^531 ≤ (34235172776661/100000000000000 : ℝ)^403
        have hw : |(4432921799/10000000000 : ℝ)|=(4432921799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1108230141/2500000000 : ℝ)|^531 ≤ (34235160209451/100000000000000 : ℝ)^403
        have hw : |(1108230141/2500000000 : ℝ)|=(1108230141/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1288_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152604817/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14669/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5509/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31419/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58837/100000 : ℝ) ∧ (4977/6250 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84139/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14669/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5509/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14669/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5509/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14669/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5509/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14669/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5509/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14669/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5509/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14669/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5509/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5509/50000 : ℝ) ^ (4247/1024 : ℝ) ≤ (332666194361443/3125000000000000000 : ℝ) := by
    have hpowers : (5509/50000 : ℝ)^4247 ≤ (332666194361443/3125000000000000000 : ℝ)^1024 := by
      have hnat : (5509 : ℕ)^4247*3125000000000000000^1024 ≤ 332666194361443^1024*50000^4247 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5509 50000 332666194361443 3125000000000000000 4247 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5509/50000 : ℝ)) (X := (332666194361443/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4247 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14669/100000 : ℝ) ^ (4247/1024 : ℝ) ≤ (8722052178780439/25000000000000000000 : ℝ) := by
    have hpowers : (14669/100000 : ℝ)^4247 ≤ (8722052178780439/25000000000000000000 : ℝ)^1024 := by
      have hnat : (14669 : ℕ)^4247*25000000000000000000^1024 ≤ 8722052178780439^1024*100000^4247 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14669 100000 8722052178780439 25000000000000000000 4247 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14669/100000 : ℝ)) (X := (8722052178780439/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4247 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562832666194361443/1562500000000000000 : ℝ) ≤ (10000513299992139/10000000000000000 : ℝ) ^ (4247/1024 : ℝ) := by
    have hpowers : (1562832666194361443/1562500000000000000 : ℝ)^1024 ≤ (10000513299992139/10000000000000000 : ℝ)^4247 := by
      have hnat : (1562832666194361443 : ℕ)^1024*10000000000000000^4247 ≤ 10000513299992139^4247*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562832666194361443 1562500000000000000 10000513299992139 10000000000000000 1024 4247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000513299992139/10000000000000000 : ℝ)) (X := (1562832666194361443/1562500000000000000 : ℝ)) (by norm_num) 4247 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011383381733671983/25000000000000000000 : ℝ) ≤ (5000548837743061/5000000000000000 : ℝ) ^ (4247/1024 : ℝ) := by
    have hpowers : (25011383381733671983/25000000000000000000 : ℝ)^1024 ≤ (5000548837743061/5000000000000000 : ℝ)^4247 := by
      have hnat : (25011383381733671983 : ℕ)^1024*5000000000000000^4247 ≤ 5000548837743061^4247*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011383381733671983 25000000000000000000 5000548837743061 5000000000000000 1024 4247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000548837743061/5000000000000000 : ℝ)) (X := (25011383381733671983/25000000000000000000 : ℝ)) (by norm_num) 4247 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508722052178780439/12500000000000000000 : ℝ) ≤ (2000336410196021/2000000000000000 : ℝ) ^ (4247/1024 : ℝ) := by
    have hpowers : (12508722052178780439/12500000000000000000 : ℝ)^1024 ≤ (2000336410196021/2000000000000000 : ℝ)^4247 := by
      have hnat : (12508722052178780439 : ℕ)^1024*2000000000000000^4247 ≤ 2000336410196021^4247*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508722052178780439 12500000000000000000 2000336410196021 2000000000000000 1024 4247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000336410196021/2000000000000000 : ℝ)) (X := (12508722052178780439/12500000000000000000 : ℝ)) (by norm_num) 4247 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(332666194361443/3125000000000000000 : ℝ) ≤ ((36498996759885890101/36510000000000000000 : ℝ)+2*(584375493983/365100000000000 : ℝ)*(5509/50000 : ℝ))^(4247/1024 : ℝ) := by
    rw [show (36498996759885890101/36510000000000000000 : ℝ)+2*(584375493983/365100000000000 : ℝ)*(5509/50000 : ℝ)=(10000513299992139/10000000000000000 : ℝ) by norm_num, show 1+2*(332666194361443/3125000000000000000 : ℝ)=(1562832666194361443/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8722052178780439/25000000000000000000 : ℝ)+(332666194361443/3125000000000000000 : ℝ) ≤ ((36498996759885890101/36510000000000000000 : ℝ)+(584375493983/365100000000000 : ℝ)*((14669/100000 : ℝ)+(5509/50000 : ℝ)))^(4247/1024 : ℝ) := by
    rw [show (36498996759885890101/36510000000000000000 : ℝ)+(584375493983/365100000000000 : ℝ)*((14669/100000 : ℝ)+(5509/50000 : ℝ))=(5000548837743061/5000000000000000 : ℝ) by norm_num, show 1+(8722052178780439/25000000000000000000 : ℝ)+(332666194361443/3125000000000000000 : ℝ)=(25011383381733671983/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8722052178780439/25000000000000000000 : ℝ) ≤ ((36498996759885890101/36510000000000000000 : ℝ)+2*(584375493983/365100000000000 : ℝ)*(14669/100000 : ℝ))^(4247/1024 : ℝ) := by
    rw [show (36498996759885890101/36510000000000000000 : ℝ)+2*(584375493983/365100000000000 : ℝ)*(14669/100000 : ℝ)=(2000336410196021/2000000000000000 : ℝ) by norm_num, show 1+2*(8722052178780439/25000000000000000000 : ℝ)=(12508722052178780439/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (36498996759885890101/36510000000000000000 : ℝ)*(X 1 0+X 2 0)+(584375493983/365100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4247/1024 : ℝ)) (lo := (5509/50000 : ℝ)) (hi := (14669/100000 : ℝ)) (c := (36498996759885890101/36510000000000000000 : ℝ)) (alpha := (584375493983/365100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (36498996759885890101/36510000000000000000 : ℝ)*(X 0 1+X 2 1)+(584375493983/365100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4247/1024 : ℝ)) (lo := (5509/50000 : ℝ)) (hi := (14669/100000 : ℝ)) (c := (36498996759885890101/36510000000000000000 : ℝ)) (alpha := (584375493983/365100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (36498996759885890101/36510000000000000000 : ℝ)*(X 0 2+X 1 2)+(584375493983/365100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4247/1024 : ℝ)) (lo := (5509/50000 : ℝ)) (hi := (14669/100000 : ℝ)) (c := (36498996759885890101/36510000000000000000 : ℝ)) (alpha := (584375493983/365100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-959941547/5000000000 : ℝ)*X 0 0+(5392175593/10000000000 : ℝ)*X 0 1+(5392175447/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5284296407/10000000000 : ℝ)*X 1 0+(-10336961/50000000 : ℝ)*X 1 1+(5392175507/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1321074143/2500000000 : ℝ)*X 2 0+(2696087757/5000000000 : ℝ)*X 2 1+(-64605999/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4490468927/10000000000 : ℝ)*X 0 0+(4270194603/10000000000 : ℝ)*X 0 1+(266887159/625000000 : ℝ)*X 0 2+(4490468927/10000000000 : ℝ)*X 1 0+(4270194603/10000000000 : ℝ)*X 1 1+(266887159/625000000 : ℝ)*X 1 2+(4490468927/10000000000 : ℝ)*X 2 0+(4270194603/10000000000 : ℝ)*X 2 1+(266887159/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-226600451/1000000000 : ℝ)*X 0 0+(1052717221/2000000000 : ℝ)*X 0 1+(5263586259/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5374824269/10000000000 : ℝ)*X 1 0+(-132411989/625000000 : ℝ)*X 1 1+(5263585987/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5374824291/10000000000 : ℝ)*X 2 0+(5263585953/10000000000 : ℝ)*X 2 1+(-1059295919/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((209528649/500000000 : ℝ)*X 0 0+(2210043577/5000000000 : ℝ)*X 0 1+(2210043461/5000000000 : ℝ)*X 0 2+(209528649/500000000 : ℝ)*X 1 0+(2210043577/5000000000 : ℝ)*X 1 1+(2210043461/5000000000 : ℝ)*X 1 2+(209528649/500000000 : ℝ)*X 2 0+(2210043577/5000000000 : ℝ)*X 2 1+(2210043461/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2193472931/10000000000 : ℝ)*X 0 0+(5175325123/10000000000 : ℝ)*X 0 1+(5406214447/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5274406927/10000000000 : ℝ)*X 1 0+(-2061665251/10000000000 : ℝ)*X 1 1+(5406214759/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5274406563/10000000000 : ℝ)*X 2 0+(2703107273/5000000000 : ℝ)*X 2 1+(-206166603/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((452264997/1000000000 : ℝ)*X 0 0+(2126908449/5000000000 : ℝ)*X 0 1+(850763169/2000000000 : ℝ)*X 0 2+(452264997/1000000000 : ℝ)*X 1 0+(2126908449/5000000000 : ℝ)*X 1 1+(850763169/2000000000 : ℝ)*X 1 2+(452264997/1000000000 : ℝ)*X 2 0+(2126908449/5000000000 : ℝ)*X 2 1+(850763169/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1992862283/10000000000 : ℝ)*X 0 0+(1369525851/2500000000 : ℝ)*X 0 1+(52525673/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2691289289/5000000000 : ℝ)*X 1 0+(-530718189/2500000000 : ℝ)*X 1 1+(1313141803/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2691289067/5000000000 : ℝ)*X 2 0+(5252568087/10000000000 : ℝ)*X 2 1+(-1061436093/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2082214151/5000000000 : ℝ)*X 0 0+(4432921799/10000000000 : ℝ)*X 0 1+(1108230141/2500000000 : ℝ)*X 0 2+(2082214151/5000000000 : ℝ)*X 1 0+(4432921799/10000000000 : ℝ)*X 1 1+(1108230141/2500000000 : ℝ)*X 1 2+(2082214151/5000000000 : ℝ)*X 2 0+(4432921799/10000000000 : ℝ)*X 2 1+(1108230141/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31419/50000 : ℝ) ≤ (-47794424543273438389365532693597/76062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16420853/50000000000000 : ℝ)*(lower0) + (10732057/100000000000000 : ℝ)*(upper1) + (13869/1562500000000 : ℝ)*(lower4) + (714887690076103/25000000000000 : ℝ)*(major0) + (714887690076103/25000000000000 : ℝ)*(major1) + (714887690076103/25000000000000 : ℝ)*(major2) + (1820510067/25000000000000 : ℝ)*(sp1) + (4159833747/50000000000000 : ℝ)*(sp2) + (241638670066807/6250000000000 : ℝ)*(sp4) + (1933106077853671/50000000000000 : ℝ)*(sp5) + (3866211118080117/100000000000000 : ℝ)*(sp6) + (1873816556665313/100000000000000 : ℝ)*(sp7) + (716678699/100000000000000 : ℝ)*(sp12) + (10768395083/100000000000000 : ℝ)*(sp15) + (468456831265099/25000000000000 : ℝ)*(f.failure) + (386621943774761/10000000000000 : ℝ)*(f.sum) + (37850992599401/18255000000000000000000000000 : ℝ)*base65 + (1477701881732331199/304250000000000000000000000000000 : ℝ)*base68 + (457516226464081199/304250000000000000000000000000000 : ℝ)*base70 + (499696099853581199/304250000000000000000000000000000 : ℝ)*base72 + (171209707783309/18255000000000000000000000000 : ℝ)*base74 + (1504193601467418801/304250000000000000000000000000000 : ℝ)*base75 + (3053860410452831199/304250000000000000000000000000000 : ℝ)*base78 + (693186946891581199/304250000000000000000000000000000 : ℝ)*base80 + (20632657295549/4563750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (11381883/2500000000000000000000 : ℝ)*base89 + (11381883/2500000000000000000000 : ℝ)*base91 + (11381883/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (58837/100000 : ℝ) ≤ (358041349296677784932769451299337/608500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18309987/100000000000000 : ℝ)*(upper0) + (29452249/100000000000000 : ℝ)*(lower1) + (120584863/100000000000000 : ℝ)*(upper4) + (2926444745605637/100000000000000 : ℝ)*(major0) + (2926444745605637/100000000000000 : ℝ)*(major1) + (2926444745605637/100000000000000 : ℝ)*(major2) + (3915610323800181/100000000000000 : ℝ)*(sp0) + (978901519912269/25000000000000 : ℝ)*(sp1) + (244725546489743/6250000000000 : ℝ)*(sp2) + (958830598143033/50000000000000 : ℝ)*(sp3) + (5312086881/100000000000000 : ℝ)*(sp6) + (908446603/100000000000000 : ℝ)*(sp7) + (933030647/25000000000000 : ℝ)*(sp8) + (1994068423/25000000000000 : ℝ)*(sp9) + (1917662104732669/100000000000000 : ℝ)*(f.failure) + (244725878495173/6250000000000 : ℝ)*(f.sum) + (64331966791229/18255000000000000000000000000 : ℝ)*base66 + (3843664546360600221/1217000000000000000000000000000000 : ℝ)*base68 + (531519084592600221/1217000000000000000000000000000000 : ℝ)*base70 + (42964079317600221/1217000000000000000000000000000000 : ℝ)*base72 + (104013761337331/18255000000000000000000000000 : ℝ)*base73 + (5147955805718399779/1217000000000000000000000000000000 : ℝ)*base75 + (2635013302664600221/1217000000000000000000000000000000 : ℝ)*base78 + (24310573649783399779/1217000000000000000000000000000000 : ℝ)*base79 + (27169758138869/18255000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (86666573/10000000000000000000000 : ℝ)*base89 + (86666573/10000000000000000000000 : ℝ)*base91 + (86666573/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (4977/6250 : ℝ) ≤ (242288660975981564009070101733653/304250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (110905449/50000000000000 : ℝ)*(upper1) + (270567367/100000000000000 : ℝ)*(upper2) + (136879241/50000000000000 : ℝ)*(lower5) + (3240563770028353/100000000000000 : ℝ)*(major0) + (3240563770028353/100000000000000 : ℝ)*(major1) + (3240563770028353/100000000000000 : ℝ)*(major2) + (336443607849/100000000000000 : ℝ)*(sp1) + (55563463677/25000000000000 : ℝ)*(sp2) + (20513549943/25000000000000 : ℝ)*(sp3) + (8091036857/100000000000000 : ℝ)*(sp4) + (2165537112178979/50000000000000 : ℝ)*(sp8) + (866149174357393/20000000000000 : ℝ)*(sp9) + (2165430030770053/50000000000000 : ℝ)*(sp10) + (26542728262691/1250000000000 : ℝ)*(sp11) + (530875078803763/25000000000000 : ℝ)*(f.failure) + (2165541157697407/50000000000000 : ℝ)*(f.sum) + (84498544531619/18255000000000000000000000000 : ℝ)*base65 + (17250839778704355449/1217000000000000000000000000000000 : ℝ)*base68 + (11590986536798355449/1217000000000000000000000000000000 : ℝ)*base70 + (3373691284743355449/1217000000000000000000000000000000 : ℝ)*base72 + (185496319489/4563750000000000000000000000 : ℝ)*base74 + (2318345373688644551/1217000000000000000000000000000000 : ℝ)*base75 + (2877850868395355449/1217000000000000000000000000000000 : ℝ)*base78 + (5908826907977355449/1217000000000000000000000000000000 : ℝ)*base80 + (45465616491779/18255000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (6526371/2500000000000000000000 : ℝ)*base89 + (6526371/2500000000000000000000 : ℝ)*base91 + (6526371/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-84139/100000 : ℝ) ≤ (-2559849675458342306417283137793/3042500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (356957613/100000000000000 : ℝ)*(lower0) + (21281541/50000000000000 : ℝ)*(lower1) + (62748609/100000000000000 : ℝ)*(lower2) + (15865027/10000000000000 : ℝ)*(upper5) + (32764135626507/1000000000000 : ℝ)*(major0) + (32764135626507/1000000000000 : ℝ)*(major1) + (32764135626507/1000000000000 : ℝ)*(major2) + (10290424313/50000000000000 : ℝ)*(sp0) + (83699559039/25000000000000 : ℝ)*(sp5) + (14682654891/50000000000000 : ℝ)*(sp7) + (2216929889255859/50000000000000 : ℝ)*(sp12) + (1108386390281047/25000000000000 : ℝ)*(sp13) + (554235044920043/12500000000000 : ℝ)*(sp14) + (26837035800887/1250000000000 : ℝ)*(sp15) + (1073496114690371/50000000000000 : ℝ)*(f.failure) + (554235044920043/12500000000000 : ℝ)*(f.sum) + (2084430837487/608500000000000000000000000 : ℝ)*base66 + (646735883990931/12170000000000000000000000000000 : ℝ)*base68 + (135263108694350931/12170000000000000000000000000000 : ℝ)*base70 + (16483218810509069/12170000000000000000000000000000 : ℝ)*base71 + (865118548381/38031250000000000000000000 : ℝ)*base74 + (167060429609370931/12170000000000000000000000000000 : ℝ)*base76 + (59610965395050931/12170000000000000000000000000000 : ℝ)*base78 + (388301015208450931/12170000000000000000000000000000 : ℝ)*base80 + (38028849233/7606250000000000000000000 : ℝ)*base82 + (78117107/5000000000000000000000 : ℝ)*base89 + (78117107/5000000000000000000000 : ℝ)*base91 + (78117107/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1288_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152604817/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14669/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5509/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31419/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58837/100000 : ℝ) else (4977/6250 : ℝ) ≤ X j i ∧ X j i ≤ (84139/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1288_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1288_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152604817/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14669/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5509/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31419/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58837/100000 : ℝ) else (4977/6250 : ℝ) ≤ X j i ∧ X j i ≤ (84139/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1288_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152604817/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14669/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5509/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31419/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58837/100000 : ℝ) else (4977/6250 : ℝ) ≤ X j i ∧ X j i ≤ (84139/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1288_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
