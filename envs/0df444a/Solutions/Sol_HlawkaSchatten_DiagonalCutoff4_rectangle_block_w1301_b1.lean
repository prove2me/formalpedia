-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1301_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:36:41.815641+00:00
-- url     : https://prove2.me/submissions/9e5299a8-5391-4ef3-a2f6-72a52ae653f5

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
theorem support_rectangle_w1301_s3_0 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2077693203/10000000000 : ℝ)*x 0 + (679094933/1250000000 : ℝ)*x 1 + (5226787353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2077693203/10000000000 : ℝ)^4261 ≤ (12638733628811/100000000000000 : ℝ)^3237 := by
    have hnat : (2077693203 : ℕ)^4261*100000000000000^3237 ≤ 12638733628811^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077693203 10000000000 12638733628811 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (679094933/1250000000 : ℝ)^4261 ≤ (11197891521707/25000000000000 : ℝ)^3237 := by
    have hnat : (679094933 : ℕ)^4261*25000000000000^3237 ≤ 11197891521707^3237*1250000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679094933 1250000000 11197891521707 25000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5226787353/10000000000 : ℝ)^4261 ≤ (4256970026849/10000000000000 : ℝ)^3237 := by
    have hnat : (5226787353 : ℕ)^4261*10000000000000^3237 ≤ 4256970026849^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226787353 10000000000 4256970026849 10000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2077693203/10000000000 : ℝ), (679094933/1250000000 : ℝ), (5226787353/10000000000 : ℝ)] ![(12638733628811/100000000000000 : ℝ), (11197891521707/25000000000000 : ℝ), (4256970026849/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2077693203/10000000000 : ℝ)|^4261 ≤ (12638733628811/100000000000000 : ℝ)^3237
        have hw : |(-2077693203/10000000000 : ℝ)|=(2077693203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(679094933/1250000000 : ℝ)|^4261 ≤ (11197891521707/25000000000000 : ℝ)^3237
        have hw : |(679094933/1250000000 : ℝ)|=(679094933/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5226787353/10000000000 : ℝ)|^4261 ≤ (4256970026849/10000000000000 : ℝ)^3237
        have hw : |(5226787353/10000000000 : ℝ)|=(5226787353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s3_1 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354207557/10000000000 : ℝ)*x 0 + (-545769651/2500000000 : ℝ)*x 1 + (5226787539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354207557/10000000000 : ℝ)^4261 ≤ (43941008594049/100000000000000 : ℝ)^3237 := by
    have hnat : (5354207557 : ℕ)^4261*100000000000000^3237 ≤ 43941008594049^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354207557 10000000000 43941008594049 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (545769651/2500000000 : ℝ)^4261 ≤ (13489289138153/100000000000000 : ℝ)^3237 := by
    have hnat : (545769651 : ℕ)^4261*100000000000000^3237 ≤ 13489289138153^3237*2500000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545769651 2500000000 13489289138153 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5226787539/10000000000 : ℝ)^4261 ≤ (665151597853/1562500000000 : ℝ)^3237 := by
    have hnat : (5226787539 : ℕ)^4261*1562500000000^3237 ≤ 665151597853^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226787539 10000000000 665151597853 1562500000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354207557/10000000000 : ℝ), (-545769651/2500000000 : ℝ), (5226787539/10000000000 : ℝ)] ![(43941008594049/100000000000000 : ℝ), (13489289138153/100000000000000 : ℝ), (665151597853/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354207557/10000000000 : ℝ)|^4261 ≤ (43941008594049/100000000000000 : ℝ)^3237
        have hw : |(5354207557/10000000000 : ℝ)|=(5354207557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-545769651/2500000000 : ℝ)|^4261 ≤ (13489289138153/100000000000000 : ℝ)^3237
        have hw : |(-545769651/2500000000 : ℝ)|=(545769651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5226787539/10000000000 : ℝ)|^4261 ≤ (665151597853/1562500000000 : ℝ)^3237
        have hw : |(5226787539/10000000000 : ℝ)|=(5226787539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s3_2 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677103821/5000000000 : ℝ)*x 0 + (1045357429/2000000000 : ℝ)*x 1 + (-218307901/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677103821/5000000000 : ℝ)^4261 ≤ (21970504756151/50000000000000 : ℝ)^3237 := by
    have hnat : (2677103821 : ℕ)^4261*50000000000000^3237 ≤ 21970504756151^3237*5000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677103821 5000000000 21970504756151 50000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1045357429/2000000000 : ℝ)^4261 ≤ (1702787921541/4000000000000 : ℝ)^3237 := by
    have hnat : (1045357429 : ℕ)^4261*4000000000000^3237 ≤ 1702787921541^3237*2000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045357429 2000000000 1702787921541 4000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (218307901/1000000000 : ℝ)^4261 ≤ (6744646220219/50000000000000 : ℝ)^3237 := by
    have hnat : (218307901 : ℕ)^4261*50000000000000^3237 ≤ 6744646220219^3237*1000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218307901 1000000000 6744646220219 50000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677103821/5000000000 : ℝ), (1045357429/2000000000 : ℝ), (-218307901/1000000000 : ℝ)] ![(21970504756151/50000000000000 : ℝ), (1702787921541/4000000000000 : ℝ), (6744646220219/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677103821/5000000000 : ℝ)|^4261 ≤ (21970504756151/50000000000000 : ℝ)^3237
        have hw : |(2677103821/5000000000 : ℝ)|=(2677103821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1045357429/2000000000 : ℝ)|^4261 ≤ (1702787921541/4000000000000 : ℝ)^3237
        have hw : |(1045357429/2000000000 : ℝ)|=(1045357429/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-218307901/1000000000 : ℝ)|^4261 ≤ (6744646220219/50000000000000 : ℝ)^3237
        have hw : |(-218307901/1000000000 : ℝ)|=(218307901/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s3_3 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4336108807/10000000000 : ℝ)*x 0 + (825733521/2000000000 : ℝ)*x 1 + (113836147/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4336108807/10000000000 : ℝ)^4261 ≤ (6657782504601/20000000000000 : ℝ)^3237 := by
    have hnat : (4336108807 : ℕ)^4261*20000000000000^3237 ≤ 6657782504601^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4336108807 10000000000 6657782504601 20000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (825733521/2000000000 : ℝ)^4261 ≤ (15604302230689/50000000000000 : ℝ)^3237 := by
    have hnat : (825733521 : ℕ)^4261*50000000000000^3237 ≤ 15604302230689^3237*2000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      825733521 2000000000 15604302230689 50000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (113836147/250000000 : ℝ)^4261 ≤ (1775124150381/5000000000000 : ℝ)^3237 := by
    have hnat : (113836147 : ℕ)^4261*5000000000000^3237 ≤ 1775124150381^3237*250000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113836147 250000000 1775124150381 5000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4336108807/10000000000 : ℝ), (825733521/2000000000 : ℝ), (113836147/250000000 : ℝ)] ![(6657782504601/20000000000000 : ℝ), (15604302230689/50000000000000 : ℝ), (1775124150381/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4336108807/10000000000 : ℝ)|^4261 ≤ (6657782504601/20000000000000 : ℝ)^3237
        have hw : |(4336108807/10000000000 : ℝ)|=(4336108807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(825733521/2000000000 : ℝ)|^4261 ≤ (15604302230689/50000000000000 : ℝ)^3237
        have hw : |(825733521/2000000000 : ℝ)|=(825733521/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(113836147/250000000 : ℝ)|^4261 ≤ (1775124150381/5000000000000 : ℝ)^3237
        have hw : |(113836147/250000000 : ℝ)|=(113836147/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s3_4 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2077715147/10000000000 : ℝ)*x 0 + (5227668653/10000000000 : ℝ)*x 1 + (5431872637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2077715147/10000000000 : ℝ)^4261 ≤ (12638909343269/100000000000000 : ℝ)^3237 := by
    have hnat : (2077715147 : ℕ)^4261*100000000000000^3237 ≤ 12638909343269^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077715147 10000000000 12638909343269 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5227668653/10000000000 : ℝ)^4261 ≤ (21289574461263/50000000000000 : ℝ)^3237 := by
    have hnat : (5227668653 : ℕ)^4261*50000000000000^3237 ≤ 21289574461263^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227668653 10000000000 21289574461263 50000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5431872637/10000000000 : ℝ)^4261 ≤ (22390970858551/50000000000000 : ℝ)^3237 := by
    have hnat : (5431872637 : ℕ)^4261*50000000000000^3237 ≤ 22390970858551^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431872637 10000000000 22390970858551 50000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2077715147/10000000000 : ℝ), (5227668653/10000000000 : ℝ), (5431872637/10000000000 : ℝ)] ![(12638909343269/100000000000000 : ℝ), (21289574461263/50000000000000 : ℝ), (22390970858551/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2077715147/10000000000 : ℝ)|^4261 ≤ (12638909343269/100000000000000 : ℝ)^3237
        have hw : |(-2077715147/10000000000 : ℝ)|=(2077715147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5227668653/10000000000 : ℝ)|^4261 ≤ (21289574461263/50000000000000 : ℝ)^3237
        have hw : |(5227668653/10000000000 : ℝ)|=(5227668653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5431872637/10000000000 : ℝ)|^4261 ≤ (22390970858551/50000000000000 : ℝ)^3237
        have hw : |(5431872637/10000000000 : ℝ)|=(5431872637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s3_5 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5301410381/10000000000 : ℝ)*x 0 + (-988996699/5000000000 : ℝ)*x 1 + (5431872601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301410381/10000000000 : ℝ)^4261 ≤ (43371533263133/100000000000000 : ℝ)^3237 := by
    have hnat : (5301410381 : ℕ)^4261*100000000000000^3237 ≤ 43371533263133^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301410381 10000000000 43371533263133 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (988996699/5000000000 : ℝ)^4261 ≤ (11846525392037/100000000000000 : ℝ)^3237 := by
    have hnat : (988996699 : ℕ)^4261*100000000000000^3237 ≤ 11846525392037^3237*5000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      988996699 5000000000 11846525392037 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5431872601/10000000000 : ℝ)^4261 ≤ (22390970663209/50000000000000 : ℝ)^3237 := by
    have hnat : (5431872601 : ℕ)^4261*50000000000000^3237 ≤ 22390970663209^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431872601 10000000000 22390970663209 50000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301410381/10000000000 : ℝ), (-988996699/5000000000 : ℝ), (5431872601/10000000000 : ℝ)] ![(43371533263133/100000000000000 : ℝ), (11846525392037/100000000000000 : ℝ), (22390970663209/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301410381/10000000000 : ℝ)|^4261 ≤ (43371533263133/100000000000000 : ℝ)^3237
        have hw : |(5301410381/10000000000 : ℝ)|=(5301410381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-988996699/5000000000 : ℝ)|^4261 ≤ (11846525392037/100000000000000 : ℝ)^3237
        have hw : |(-988996699/5000000000 : ℝ)|=(988996699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5431872601/10000000000 : ℝ)|^4261 ≤ (22390970663209/50000000000000 : ℝ)^3237
        have hw : |(5431872601/10000000000 : ℝ)|=(5431872601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s3_6 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5301410471/10000000000 : ℝ)*x 0 + (5431872501/10000000000 : ℝ)*x 1 + (-1977993413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301410471/10000000000 : ℝ)^4261 ≤ (21685767116179/50000000000000 : ℝ)^3237 := by
    have hnat : (5301410471 : ℕ)^4261*50000000000000^3237 ≤ 21685767116179^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301410471 10000000000 21685767116179 50000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5431872501/10000000000 : ℝ)^4261 ≤ (44781940241187/100000000000000 : ℝ)^3237 := by
    have hnat : (5431872501 : ℕ)^4261*100000000000000^3237 ≤ 44781940241187^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431872501 10000000000 44781940241187 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1977993413/10000000000 : ℝ)^4261 ≤ (5923262755147/50000000000000 : ℝ)^3237 := by
    have hnat : (1977993413 : ℕ)^4261*50000000000000^3237 ≤ 5923262755147^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1977993413 10000000000 5923262755147 50000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301410471/10000000000 : ℝ), (5431872501/10000000000 : ℝ), (-1977993413/10000000000 : ℝ)] ![(21685767116179/50000000000000 : ℝ), (44781940241187/100000000000000 : ℝ), (5923262755147/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301410471/10000000000 : ℝ)|^4261 ≤ (21685767116179/50000000000000 : ℝ)^3237
        have hw : |(5301410471/10000000000 : ℝ)|=(5301410471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5431872501/10000000000 : ℝ)|^4261 ≤ (44781940241187/100000000000000 : ℝ)^3237
        have hw : |(5431872501/10000000000 : ℝ)|=(5431872501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1977993413/10000000000 : ℝ)|^4261 ≤ (5923262755147/50000000000000 : ℝ)^3237
        have hw : |(-1977993413/10000000000 : ℝ)|=(1977993413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s3_7 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4336153561/10000000000 : ℝ)*x 0 + (4551628147/10000000000 : ℝ)*x 1 + (413049683/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4336153561/10000000000 : ℝ)^4261 ≤ (8322341199047/25000000000000 : ℝ)^3237 := by
    have hnat : (4336153561 : ℕ)^4261*25000000000000^3237 ≤ 8322341199047^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4336153561 10000000000 8322341199047 25000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4551628147/10000000000 : ℝ)^4261 ≤ (283870625849/800000000000 : ℝ)^3237 := by
    have hnat : (4551628147 : ℕ)^4261*800000000000^3237 ≤ 283870625849^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4551628147 10000000000 283870625849 800000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (413049683/1000000000 : ℝ)^4261 ≤ (31226806952291/100000000000000 : ℝ)^3237 := by
    have hnat : (413049683 : ℕ)^4261*100000000000000^3237 ≤ 31226806952291^3237*1000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413049683 1000000000 31226806952291 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4336153561/10000000000 : ℝ), (4551628147/10000000000 : ℝ), (413049683/1000000000 : ℝ)] ![(8322341199047/25000000000000 : ℝ), (283870625849/800000000000 : ℝ), (31226806952291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4336153561/10000000000 : ℝ)|^4261 ≤ (8322341199047/25000000000000 : ℝ)^3237
        have hw : |(4336153561/10000000000 : ℝ)|=(4336153561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4551628147/10000000000 : ℝ)|^4261 ≤ (283870625849/800000000000 : ℝ)^3237
        have hw : |(4551628147/10000000000 : ℝ)|=(4551628147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(413049683/1000000000 : ℝ)|^4261 ≤ (31226806952291/100000000000000 : ℝ)^3237
        have hw : |(413049683/1000000000 : ℝ)|=(413049683/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1301_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76557683/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16277/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (957/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (10697/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3011/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16277/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (957/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16277/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (957/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16277/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (957/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16277/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (957/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16277/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (957/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16277/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (957/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (957/10000 : ℝ) ^ (1065/256 : ℝ) ≤ (144003960757563/2500000000000000000 : ℝ) := by
    have hpowers : (957/10000 : ℝ)^1065 ≤ (144003960757563/2500000000000000000 : ℝ)^256 := by
      have hnat : (957 : ℕ)^1065*2500000000000000000^256 ≤ 144003960757563^256*10000^1065 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        957 10000 144003960757563 2500000000000000000 1065 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (957/10000 : ℝ)) (X := (144003960757563/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have hpowhi : (16277/100000 : ℝ) ^ (1065/256 : ℝ) ≤ (26241953700614217/50000000000000000000 : ℝ) := by
    have hpowers : (16277/100000 : ℝ)^1065 ≤ (26241953700614217/50000000000000000000 : ℝ)^256 := by
      have hnat : (16277 : ℕ)^1065*50000000000000000000^256 ≤ 26241953700614217^256*100000^1065 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16277 100000 26241953700614217 50000000000000000000 1065 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16277/100000 : ℝ)) (X := (26241953700614217/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250144003960757563/1250000000000000000 : ℝ) ≤ (5000138454088313/5000000000000000 : ℝ) ^ (1065/256 : ℝ) := by
    have hpowers : (1250144003960757563/1250000000000000000 : ℝ)^256 ≤ (5000138454088313/5000000000000000 : ℝ)^1065 := by
      have hnat : (1250144003960757563 : ℕ)^256*5000000000000000^1065 ≤ 5000138454088313^1065*1250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250144003960757563 1250000000000000000 5000138454088313 5000000000000000 256 1065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000138454088313/5000000000000000 : ℝ)) (X := (1250144003960757563/1250000000000000000 : ℝ)) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50029122032915765477/50000000000000000000 : ℝ) ≤ (10001399735540981/10000000000000000 : ℝ) ^ (1065/256 : ℝ) := by
    have hpowers : (50029122032915765477/50000000000000000000 : ℝ)^256 ≤ (10001399735540981/10000000000000000 : ℝ)^1065 := by
      have hnat : (50029122032915765477 : ℕ)^256*10000000000000000^1065 ≤ 10001399735540981^1065*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029122032915765477 50000000000000000000 10001399735540981 10000000000000000 256 1065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001399735540981/10000000000000000 : ℝ)) (X := (50029122032915765477/50000000000000000000 : ℝ)) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25026241953700614217/25000000000000000000 : ℝ) ≤ (1250315320363167/1250000000000000 : ℝ) ^ (1065/256 : ℝ) := by
    have hpowers : (25026241953700614217/25000000000000000000 : ℝ)^256 ≤ (1250315320363167/1250000000000000 : ℝ)^1065 := by
      have hnat : (25026241953700614217 : ℕ)^256*1250000000000000^1065 ≤ 1250315320363167^1065*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25026241953700614217 25000000000000000000 1250315320363167 1250000000000000 256 1065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250315320363167/1250000000000000 : ℝ)) (X := (25026241953700614217/25000000000000000000 : ℝ)) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(144003960757563/2500000000000000000 : ℝ) ≤ ((33525183153693437941/33535000000000000000 : ℝ)+2*(224565472871/134140000000000 : ℝ)*(957/10000 : ℝ))^(1065/256 : ℝ) := by
    rw [show (33525183153693437941/33535000000000000000 : ℝ)+2*(224565472871/134140000000000 : ℝ)*(957/10000 : ℝ)=(5000138454088313/5000000000000000 : ℝ) by norm_num, show 1+2*(144003960757563/2500000000000000000 : ℝ)=(1250144003960757563/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26241953700614217/50000000000000000000 : ℝ)+(144003960757563/2500000000000000000 : ℝ) ≤ ((33525183153693437941/33535000000000000000 : ℝ)+(224565472871/134140000000000 : ℝ)*((16277/100000 : ℝ)+(957/10000 : ℝ)))^(1065/256 : ℝ) := by
    rw [show (33525183153693437941/33535000000000000000 : ℝ)+(224565472871/134140000000000 : ℝ)*((16277/100000 : ℝ)+(957/10000 : ℝ))=(10001399735540981/10000000000000000 : ℝ) by norm_num, show 1+(26241953700614217/50000000000000000000 : ℝ)+(144003960757563/2500000000000000000 : ℝ)=(50029122032915765477/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26241953700614217/50000000000000000000 : ℝ) ≤ ((33525183153693437941/33535000000000000000 : ℝ)+2*(224565472871/134140000000000 : ℝ)*(16277/100000 : ℝ))^(1065/256 : ℝ) := by
    rw [show (33525183153693437941/33535000000000000000 : ℝ)+2*(224565472871/134140000000000 : ℝ)*(16277/100000 : ℝ)=(1250315320363167/1250000000000000 : ℝ) by norm_num, show 1+2*(26241953700614217/50000000000000000000 : ℝ)=(25026241953700614217/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (33525183153693437941/33535000000000000000 : ℝ)*(X 1 0+X 2 0)+(224565472871/134140000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1065/256 : ℝ)) (lo := (957/10000 : ℝ)) (hi := (16277/100000 : ℝ)) (c := (33525183153693437941/33535000000000000000 : ℝ)) (alpha := (224565472871/134140000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (33525183153693437941/33535000000000000000 : ℝ)*(X 0 1+X 2 1)+(224565472871/134140000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1065/256 : ℝ)) (lo := (957/10000 : ℝ)) (hi := (16277/100000 : ℝ)) (c := (33525183153693437941/33535000000000000000 : ℝ)) (alpha := (224565472871/134140000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (33525183153693437941/33535000000000000000 : ℝ)*(X 0 2+X 1 2)+(224565472871/134140000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1065/256 : ℝ)) (lo := (957/10000 : ℝ)) (hi := (16277/100000 : ℝ)) (c := (33525183153693437941/33535000000000000000 : ℝ)) (alpha := (224565472871/134140000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2077693203/10000000000 : ℝ)*X 0 0+(679094933/1250000000 : ℝ)*X 0 1+(5226787353/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5354207557/10000000000 : ℝ)*X 1 0+(-545769651/2500000000 : ℝ)*X 1 1+(5226787539/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677103821/5000000000 : ℝ)*X 2 0+(1045357429/2000000000 : ℝ)*X 2 1+(-218307901/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4336108807/10000000000 : ℝ)*X 0 0+(825733521/2000000000 : ℝ)*X 0 1+(113836147/250000000 : ℝ)*X 0 2+(4336108807/10000000000 : ℝ)*X 1 0+(825733521/2000000000 : ℝ)*X 1 1+(113836147/250000000 : ℝ)*X 1 2+(4336108807/10000000000 : ℝ)*X 2 0+(825733521/2000000000 : ℝ)*X 2 1+(113836147/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2077715147/10000000000 : ℝ)*X 0 0+(5227668653/10000000000 : ℝ)*X 0 1+(5431872637/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5301410381/10000000000 : ℝ)*X 1 0+(-988996699/5000000000 : ℝ)*X 1 1+(5431872601/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5301410471/10000000000 : ℝ)*X 2 0+(5431872501/10000000000 : ℝ)*X 2 1+(-1977993413/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4336153561/10000000000 : ℝ)*X 0 0+(4551628147/10000000000 : ℝ)*X 0 1+(413049683/1000000000 : ℝ)*X 0 2+(4336153561/10000000000 : ℝ)*X 1 0+(4551628147/10000000000 : ℝ)*X 1 1+(413049683/1000000000 : ℝ)*X 1 2+(4336153561/10000000000 : ℝ)*X 2 0+(4551628147/10000000000 : ℝ)*X 2 1+(413049683/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (431811890985137478603463497/52398437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (411613567/25000000000000 : ℝ)*(base19) + (1689559929/100000000000000 : ℝ)*(base23) + (5524169/6250000000000 : ℝ)*(lower2) + (21301211/5000000000000 : ℝ)*(upper3) + (35099093/50000000000000 : ℝ)*(lower4) + (3604640990006949/100000000000000 : ℝ)*(major0) + (3604640990006949/100000000000000 : ℝ)*(major1) + (72092819800139/2000000000000 : ℝ)*(major2) + (4855060379641699/100000000000000 : ℝ)*(sp0) + (4855080683466163/100000000000000 : ℝ)*(sp1) + (2427540320180251/50000000000000 : ℝ)*(sp2) + (2354181485931767/100000000000000 : ℝ)*(sp3) + (5487569683/25000000000000 : ℝ)*(sp4) + (3577892801/20000000000000 : ℝ)*(sp7) + (588549843848943/25000000000000 : ℝ)*(f.failure) + (4855082329920431/100000000000000 : ℝ)*(f.sum) + (15511101120007/13414000000000000000000000000 : ℝ)*base65 + (18428034080404247991/3353500000000000000000000000000000 : ℝ)*base68 + (496670921544301201/67070000000000000000000000000000 : ℝ)*base70 + (13703970243574747991/3353500000000000000000000000000000 : ℝ)*base72 + (2404128151623/13414000000000000000000000000 : ℝ)*base74 + (108875791654121201/67070000000000000000000000000000 : ℝ)*base76 + (3999167280635157789/176500000000000000000000000000000 : ℝ)*base78 + (1848127098738157789/176500000000000000000000000000000 : ℝ)*base80 + (831031610529/353000000000000000000000000 : ℝ)*base82 + (15579069/1250000000000000000000 : ℝ)*base89 + (15579069/1250000000000000000000 : ℝ)*base91 + (3079069/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (233875384220192704988870229/26199218750000000000000000000000 : ℝ) := by norm_num
    linear_combination (1032234119/50000000000000 : ℝ)*(base19) + (2244773183/100000000000000 : ℝ)*(base23) + (21642857/10000000000000 : ℝ)*(upper3) + (11287867/25000000000000 : ℝ)*(lower4) + (225941789/100000000000000 : ℝ)*(upper5) + (113619071097879/3125000000000 : ℝ)*(major0) + (113619071097879/3125000000000 : ℝ)*(major1) + (113619071097879/3125000000000 : ℝ)*(major2) + (17285934559/50000000000000 : ℝ)*(sp1) + (35776865879/100000000000000 : ℝ)*(sp2) + (4897064145035399/100000000000000 : ℝ)*(sp4) + (2448513754349021/50000000000000 : ℝ)*(sp5) + (306064132712271/6250000000000 : ℝ)*(sp6) + (1187278053834299/50000000000000 : ℝ)*(sp7) + (1187278053834299/50000000000000 : ℝ)*(f.failure) + (4897064145035399/100000000000000 : ℝ)*(f.sum) + (112424750213/6707000000000000000000000000 : ℝ)*base65 + (119504140965466941/26199218750000000000000000000000 : ℝ)*base67 + (291853181017112993/52398437500000000000000000000000 : ℝ)*base70 + (438516024425179111/104796875000000000000000000000000 : ℝ)*base72 + (1776352999731/3353500000000000000000000000 : ℝ)*base73 + (862596286442852139/104796875000000000000000000000000 : ℝ)*base75 + (500402895135414639/104796875000000000000000000000000 : ℝ)*base77 + (137547582055960033/13099609375000000000000000000000 : ℝ)*base79 + (12120416404193/3353500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2630783/2500000000000000000000 : ℝ)*base90 + (2630783/2500000000000000000000 : ℝ)*base92 + (2630783/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1301_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76557683/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16277/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (957/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10697/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3011/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1301_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1301_s4_0 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2079522791/10000000000 : ℝ)*x 0 + (1083649477/2000000000 : ℝ)*x 1 + (1048019939/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2079522791/10000000000 : ℝ)^4261 ≤ (1265338589343/10000000000000 : ℝ)^3237 := by
    have hnat : (2079522791 : ℕ)^4261*10000000000000^3237 ≤ 1265338589343^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079522791 10000000000 1265338589343 10000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083649477/2000000000 : ℝ)^4261 ≤ (8926826992661/20000000000000 : ℝ)^3237 := by
    have hnat : (1083649477 : ℕ)^4261*20000000000000^3237 ≤ 8926826992661^3237*2000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083649477 2000000000 8926826992661 20000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048019939/2000000000 : ℝ)^4261 ≤ (21356239559661/50000000000000 : ℝ)^3237 := by
    have hnat : (1048019939 : ℕ)^4261*50000000000000^3237 ≤ 21356239559661^3237*2000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048019939 2000000000 21356239559661 50000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2079522791/10000000000 : ℝ), (1083649477/2000000000 : ℝ), (1048019939/2000000000 : ℝ)] ![(1265338589343/10000000000000 : ℝ), (8926826992661/20000000000000 : ℝ), (21356239559661/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2079522791/10000000000 : ℝ)|^4261 ≤ (1265338589343/10000000000000 : ℝ)^3237
        have hw : |(-2079522791/10000000000 : ℝ)|=(2079522791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083649477/2000000000 : ℝ)|^4261 ≤ (8926826992661/20000000000000 : ℝ)^3237
        have hw : |(1083649477/2000000000 : ℝ)|=(1083649477/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048019939/2000000000 : ℝ)|^4261 ≤ (21356239559661/50000000000000 : ℝ)^3237
        have hw : |(1048019939/2000000000 : ℝ)|=(1048019939/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s4_1 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675266677/5000000000 : ℝ)*x 0 + (-2170391957/10000000000 : ℝ)*x 1 + (5240100223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675266677/5000000000 : ℝ)^4261 ≤ (2743832534627/6250000000000 : ℝ)^3237 := by
    have hnat : (2675266677 : ℕ)^4261*6250000000000^3237 ≤ 2743832534627^3237*5000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675266677 5000000000 2743832534627 6250000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2170391957/10000000000 : ℝ)^4261 ≤ (13386194644813/100000000000000 : ℝ)^3237 := by
    have hnat : (2170391957 : ℕ)^4261*100000000000000^3237 ≤ 13386194644813^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170391957 10000000000 13386194644813 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5240100223/10000000000 : ℝ)^4261 ≤ (21356242392279/50000000000000 : ℝ)^3237 := by
    have hnat : (5240100223 : ℕ)^4261*50000000000000^3237 ≤ 21356242392279^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240100223 10000000000 21356242392279 50000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675266677/5000000000 : ℝ), (-2170391957/10000000000 : ℝ), (5240100223/10000000000 : ℝ)] ![(2743832534627/6250000000000 : ℝ), (13386194644813/100000000000000 : ℝ), (21356242392279/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675266677/5000000000 : ℝ)|^4261 ≤ (2743832534627/6250000000000 : ℝ)^3237
        have hw : |(2675266677/5000000000 : ℝ)|=(2675266677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2170391957/10000000000 : ℝ)|^4261 ≤ (13386194644813/100000000000000 : ℝ)^3237
        have hw : |(-2170391957/10000000000 : ℝ)|=(2170391957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5240100223/10000000000 : ℝ)|^4261 ≤ (21356242392279/50000000000000 : ℝ)^3237
        have hw : |(5240100223/10000000000 : ℝ)|=(5240100223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s4_2 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350533571/10000000000 : ℝ)*x 0 + (5240100179/10000000000 : ℝ)*x 1 + (-2170391727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350533571/10000000000 : ℝ)^4261 ≤ (4390132289777/10000000000000 : ℝ)^3237 := by
    have hnat : (5350533571 : ℕ)^4261*10000000000000^3237 ≤ 4390132289777^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350533571 10000000000 4390132289777 10000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5240100179/10000000000 : ℝ)^4261 ≤ (8542496862491/20000000000000 : ℝ)^3237 := by
    have hnat : (5240100179 : ℕ)^4261*20000000000000^3237 ≤ 8542496862491^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240100179 10000000000 8542496862491 20000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2170391727/10000000000 : ℝ)^4261 ≤ (6693096388753/50000000000000 : ℝ)^3237 := by
    have hnat : (2170391727 : ℕ)^4261*50000000000000^3237 ≤ 6693096388753^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170391727 10000000000 6693096388753 50000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350533571/10000000000 : ℝ), (5240100179/10000000000 : ℝ), (-2170391727/10000000000 : ℝ)] ![(4390132289777/10000000000000 : ℝ), (8542496862491/20000000000000 : ℝ), (6693096388753/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350533571/10000000000 : ℝ)|^4261 ≤ (4390132289777/10000000000000 : ℝ)^3237
        have hw : |(5350533571/10000000000 : ℝ)|=(5350533571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5240100179/10000000000 : ℝ)|^4261 ≤ (8542496862491/20000000000000 : ℝ)^3237
        have hw : |(5240100179/10000000000 : ℝ)|=(5240100179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2170391727/10000000000 : ℝ)|^4261 ≤ (6693096388753/50000000000000 : ℝ)^3237
        have hw : |(-2170391727/10000000000 : ℝ)|=(2170391727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s4_3 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (271075959/625000000 : ℝ)*x 0 + (2598263/6250000 : ℝ)*x 1 + (2262307469/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271075959/625000000 : ℝ)^4261 ≤ (8325023838361/25000000000000 : ℝ)^3237 := by
    have hnat : (271075959 : ℕ)^4261*25000000000000^3237 ≤ 8325023838361^3237*625000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271075959 625000000 8325023838361 25000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2598263/6250000 : ℝ)^4261 ≤ (7873256427503/25000000000000 : ℝ)^3237 := by
    have hnat : (2598263 : ℕ)^4261*25000000000000^3237 ≤ 7873256427503^3237*6250000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598263 6250000 7873256427503 25000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2262307469/5000000000 : ℝ)^4261 ≤ (35206878925159/100000000000000 : ℝ)^3237 := by
    have hnat : (2262307469 : ℕ)^4261*100000000000000^3237 ≤ 35206878925159^3237*5000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262307469 5000000000 35206878925159 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(271075959/625000000 : ℝ), (2598263/6250000 : ℝ), (2262307469/5000000000 : ℝ)] ![(8325023838361/25000000000000 : ℝ), (7873256427503/25000000000000 : ℝ), (35206878925159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(271075959/625000000 : ℝ)|^4261 ≤ (8325023838361/25000000000000 : ℝ)^3237
        have hw : |(271075959/625000000 : ℝ)|=(271075959/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2598263/6250000 : ℝ)|^4261 ≤ (7873256427503/25000000000000 : ℝ)^3237
        have hw : |(2598263/6250000 : ℝ)|=(2598263/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2262307469/5000000000 : ℝ)|^4261 ≤ (35206878925159/100000000000000 : ℝ)^3237
        have hw : |(2262307469/5000000000 : ℝ)|=(2262307469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s4_4 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-259942101/1250000000 : ℝ)*x 0 + (2620380053/5000000000 : ℝ)*x 1 + (5417583543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (259942101/1250000000 : ℝ)^4261 ≤ (12653498164391/100000000000000 : ℝ)^3237 := by
    have hnat : (259942101 : ℕ)^4261*100000000000000^3237 ≤ 12653498164391^3237*1250000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259942101 1250000000 12653498164391 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620380053/5000000000 : ℝ)^4261 ≤ (42719565215131/100000000000000 : ℝ)^3237 := by
    have hnat : (2620380053 : ℕ)^4261*100000000000000^3237 ≤ 42719565215131^3237*5000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620380053 5000000000 42719565215131 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5417583543/10000000000 : ℝ)^4261 ≤ (11156734151349/25000000000000 : ℝ)^3237 := by
    have hnat : (5417583543 : ℕ)^4261*25000000000000^3237 ≤ 11156734151349^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417583543 10000000000 11156734151349 25000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-259942101/1250000000 : ℝ), (2620380053/5000000000 : ℝ), (5417583543/10000000000 : ℝ)] ![(12653498164391/100000000000000 : ℝ), (42719565215131/100000000000000 : ℝ), (11156734151349/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-259942101/1250000000 : ℝ)|^4261 ≤ (12653498164391/100000000000000 : ℝ)^3237
        have hw : |(-259942101/1250000000 : ℝ)|=(259942101/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620380053/5000000000 : ℝ)|^4261 ≤ (42719565215131/100000000000000 : ℝ)^3237
        have hw : |(2620380053/5000000000 : ℝ)|=(2620380053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5417583543/10000000000 : ℝ)|^4261 ≤ (11156734151349/25000000000000 : ℝ)^3237
        have hw : |(5417583543/10000000000 : ℝ)|=(5417583543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s4_5 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652435959/5000000000 : ℝ)*x 0 + (-1992908089/10000000000 : ℝ)*x 1 + (2708791713/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652435959/5000000000 : ℝ)^4261 ≤ (43408814988937/100000000000000 : ℝ)^3237 := by
    have hnat : (2652435959 : ℕ)^4261*100000000000000^3237 ≤ 43408814988937^3237*5000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652435959 5000000000 43408814988937 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1992908089/10000000000 : ℝ)^4261 ≤ (2991062416301/25000000000000 : ℝ)^3237 := by
    have hnat : (1992908089 : ℕ)^4261*25000000000000^3237 ≤ 2991062416301^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1992908089 10000000000 2991062416301 25000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2708791713/5000000000 : ℝ)^4261 ≤ (44626935336733/100000000000000 : ℝ)^3237 := by
    have hnat : (2708791713 : ℕ)^4261*100000000000000^3237 ≤ 44626935336733^3237*5000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708791713 5000000000 44626935336733 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652435959/5000000000 : ℝ), (-1992908089/10000000000 : ℝ), (2708791713/5000000000 : ℝ)] ![(43408814988937/100000000000000 : ℝ), (2991062416301/25000000000000 : ℝ), (44626935336733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652435959/5000000000 : ℝ)|^4261 ≤ (43408814988937/100000000000000 : ℝ)^3237
        have hw : |(2652435959/5000000000 : ℝ)|=(2652435959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1992908089/10000000000 : ℝ)|^4261 ≤ (2991062416301/25000000000000 : ℝ)^3237
        have hw : |(-1992908089/10000000000 : ℝ)|=(1992908089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2708791713/5000000000 : ℝ)|^4261 ≤ (44626935336733/100000000000000 : ℝ)^3237
        have hw : |(2708791713/5000000000 : ℝ)|=(2708791713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s4_6 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326217903/2500000000 : ℝ)*x 0 + (1083516753/2000000000 : ℝ)*x 1 + (-49822701/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326217903/2500000000 : ℝ)^4261 ≤ (43408811692891/100000000000000 : ℝ)^3237 := by
    have hnat : (1326217903 : ℕ)^4261*100000000000000^3237 ≤ 43408811692891^3237*2500000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326217903 2500000000 43408811692891 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083516753/2000000000 : ℝ)^4261 ≤ (22313469506301/50000000000000 : ℝ)^3237 := by
    have hnat : (1083516753 : ℕ)^4261*50000000000000^3237 ≤ 22313469506301^3237*2000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083516753 2000000000 22313469506301 50000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (49822701/250000000 : ℝ)^4261 ≤ (11964249277979/100000000000000 : ℝ)^3237 := by
    have hnat : (49822701 : ℕ)^4261*100000000000000^3237 ≤ 11964249277979^3237*250000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49822701 250000000 11964249277979 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326217903/2500000000 : ℝ), (1083516753/2000000000 : ℝ), (-49822701/250000000 : ℝ)] ![(43408811692891/100000000000000 : ℝ), (22313469506301/50000000000000 : ℝ), (11964249277979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326217903/2500000000 : ℝ)|^4261 ≤ (43408811692891/100000000000000 : ℝ)^3237
        have hw : |(1326217903/2500000000 : ℝ)|=(1326217903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083516753/2000000000 : ℝ)|^4261 ≤ (22313469506301/50000000000000 : ℝ)^3237
        have hw : |(1083516753/2000000000 : ℝ)|=(1083516753/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-49822701/250000000 : ℝ)|^4261 ≤ (11964249277979/100000000000000 : ℝ)^3237
        have hw : |(-49822701/250000000 : ℝ)|=(49822701/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s4_7 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2168622089/5000000000 : ℝ)*x 0 + (4523254033/10000000000 : ℝ)*x 1 + (831717859/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2168622089/5000000000 : ℝ)^4261 ≤ (832509669157/2500000000000 : ℝ)^3237 := by
    have hnat : (2168622089 : ℕ)^4261*2500000000000^3237 ≤ 832509669157^3237*5000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168622089 5000000000 832509669157 2500000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4523254033/10000000000 : ℝ)^4261 ≤ (3519294023761/10000000000000 : ℝ)^3237 := by
    have hnat : (4523254033 : ℕ)^4261*10000000000000^3237 ≤ 3519294023761^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4523254033 10000000000 3519294023761 10000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (831717859/2000000000 : ℝ)^4261 ≤ (15753336492717/50000000000000 : ℝ)^3237 := by
    have hnat : (831717859 : ℕ)^4261*50000000000000^3237 ≤ 15753336492717^3237*2000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      831717859 2000000000 15753336492717 50000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2168622089/5000000000 : ℝ), (4523254033/10000000000 : ℝ), (831717859/2000000000 : ℝ)] ![(832509669157/2500000000000 : ℝ), (3519294023761/10000000000000 : ℝ), (15753336492717/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2168622089/5000000000 : ℝ)|^4261 ≤ (832509669157/2500000000000 : ℝ)^3237
        have hw : |(2168622089/5000000000 : ℝ)|=(2168622089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4523254033/10000000000 : ℝ)|^4261 ≤ (3519294023761/10000000000000 : ℝ)^3237
        have hw : |(4523254033/10000000000 : ℝ)|=(4523254033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(831717859/2000000000 : ℝ)|^4261 ≤ (15753336492717/50000000000000 : ℝ)^3237
        have hw : |(831717859/2000000000 : ℝ)|=(831717859/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1301_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76557683/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3011/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10697/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5491/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (461/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3011/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10697/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3011/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10697/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3011/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10697/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3011/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10697/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3011/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10697/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3011/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10697/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10697/100000 : ℝ) ^ (1065/256 : ℝ) ≤ (9153311130525611/100000000000000000000 : ℝ) := by
    have hpowers : (10697/100000 : ℝ)^1065 ≤ (9153311130525611/100000000000000000000 : ℝ)^256 := by
      have hnat : (10697 : ℕ)^1065*100000000000000000000^256 ≤ 9153311130525611^256*100000^1065 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10697 100000 9153311130525611 100000000000000000000 1065 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10697/100000 : ℝ)) (X := (9153311130525611/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have hpowhi : (3011/20000 : ℝ) ^ (1065/256 : ℝ) ≤ (18966774373951099/50000000000000000000 : ℝ) := by
    have hpowers : (3011/20000 : ℝ)^1065 ≤ (18966774373951099/50000000000000000000 : ℝ)^256 := by
      have hnat : (3011 : ℕ)^1065*50000000000000000000^256 ≤ 18966774373951099^256*20000^1065 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3011 20000 18966774373951099 50000000000000000000 1065 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3011/20000 : ℝ)) (X := (18966774373951099/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009153311130525611/50000000000000000000 : ℝ) ≤ (5000220007956719/5000000000000000 : ℝ) ^ (1065/256 : ℝ) := by
    have hpowers : (50009153311130525611/50000000000000000000 : ℝ)^256 ≤ (5000220007956719/5000000000000000 : ℝ)^1065 := by
      have hnat : (50009153311130525611 : ℕ)^256*5000000000000000^1065 ≤ 5000220007956719^1065*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009153311130525611 50000000000000000000 5000220007956719 5000000000000000 256 1065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000220007956719/5000000000000000 : ℝ)) (X := (50009153311130525611/50000000000000000000 : ℝ)) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047086859878427809/100000000000000000000 : ℝ) ≤ (10001131650791053/10000000000000000 : ℝ) ^ (1065/256 : ℝ) := by
    have hpowers : (100047086859878427809/100000000000000000000 : ℝ)^256 ≤ (10001131650791053/10000000000000000 : ℝ)^1065 := by
      have hnat : (100047086859878427809 : ℕ)^256*10000000000000000^1065 ≤ 10001131650791053^1065*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047086859878427809 100000000000000000000 10001131650791053 10000000000000000 256 1065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001131650791053/10000000000000000 : ℝ)) (X := (100047086859878427809/100000000000000000000 : ℝ)) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018966774373951099/25000000000000000000 : ℝ) ≤ (2500455821417167/2500000000000000 : ℝ) ^ (1065/256 : ℝ) := by
    have hpowers : (25018966774373951099/25000000000000000000 : ℝ)^256 ≤ (2500455821417167/2500000000000000 : ℝ)^1065 := by
      have hnat : (25018966774373951099 : ℕ)^256*2500000000000000^1065 ≤ 2500455821417167^1065*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018966774373951099 25000000000000000000 2500455821417167 2500000000000000 256 1065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500455821417167/2500000000000000 : ℝ)) (X := (25018966774373951099/25000000000000000000 : ℝ)) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9153311130525611/100000000000000000000 : ℝ) ≤ ((21783560376389533747/21790000000000000000 : ℝ)+2*(138326975523/87160000000000 : ℝ)*(10697/100000 : ℝ))^(1065/256 : ℝ) := by
    rw [show (21783560376389533747/21790000000000000000 : ℝ)+2*(138326975523/87160000000000 : ℝ)*(10697/100000 : ℝ)=(5000220007956719/5000000000000000 : ℝ) by norm_num, show 1+2*(9153311130525611/100000000000000000000 : ℝ)=(50009153311130525611/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18966774373951099/50000000000000000000 : ℝ)+(9153311130525611/100000000000000000000 : ℝ) ≤ ((21783560376389533747/21790000000000000000 : ℝ)+(138326975523/87160000000000 : ℝ)*((3011/20000 : ℝ)+(10697/100000 : ℝ)))^(1065/256 : ℝ) := by
    rw [show (21783560376389533747/21790000000000000000 : ℝ)+(138326975523/87160000000000 : ℝ)*((3011/20000 : ℝ)+(10697/100000 : ℝ))=(10001131650791053/10000000000000000 : ℝ) by norm_num, show 1+(18966774373951099/50000000000000000000 : ℝ)+(9153311130525611/100000000000000000000 : ℝ)=(100047086859878427809/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18966774373951099/50000000000000000000 : ℝ) ≤ ((21783560376389533747/21790000000000000000 : ℝ)+2*(138326975523/87160000000000 : ℝ)*(3011/20000 : ℝ))^(1065/256 : ℝ) := by
    rw [show (21783560376389533747/21790000000000000000 : ℝ)+2*(138326975523/87160000000000 : ℝ)*(3011/20000 : ℝ)=(2500455821417167/2500000000000000 : ℝ) by norm_num, show 1+2*(18966774373951099/50000000000000000000 : ℝ)=(25018966774373951099/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (21783560376389533747/21790000000000000000 : ℝ)*(X 1 0+X 2 0)+(138326975523/87160000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1065/256 : ℝ)) (lo := (10697/100000 : ℝ)) (hi := (3011/20000 : ℝ)) (c := (21783560376389533747/21790000000000000000 : ℝ)) (alpha := (138326975523/87160000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (21783560376389533747/21790000000000000000 : ℝ)*(X 0 1+X 2 1)+(138326975523/87160000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1065/256 : ℝ)) (lo := (10697/100000 : ℝ)) (hi := (3011/20000 : ℝ)) (c := (21783560376389533747/21790000000000000000 : ℝ)) (alpha := (138326975523/87160000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (21783560376389533747/21790000000000000000 : ℝ)*(X 0 2+X 1 2)+(138326975523/87160000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1065/256 : ℝ)) (lo := (10697/100000 : ℝ)) (hi := (3011/20000 : ℝ)) (c := (21783560376389533747/21790000000000000000 : ℝ)) (alpha := (138326975523/87160000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2079522791/10000000000 : ℝ)*X 0 0+(1083649477/2000000000 : ℝ)*X 0 1+(1048019939/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675266677/5000000000 : ℝ)*X 1 0+(-2170391957/10000000000 : ℝ)*X 1 1+(5240100223/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350533571/10000000000 : ℝ)*X 2 0+(5240100179/10000000000 : ℝ)*X 2 1+(-2170391727/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((271075959/625000000 : ℝ)*X 0 0+(2598263/6250000 : ℝ)*X 0 1+(2262307469/5000000000 : ℝ)*X 0 2+(271075959/625000000 : ℝ)*X 1 0+(2598263/6250000 : ℝ)*X 1 1+(2262307469/5000000000 : ℝ)*X 1 2+(271075959/625000000 : ℝ)*X 2 0+(2598263/6250000 : ℝ)*X 2 1+(2262307469/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-259942101/1250000000 : ℝ)*X 0 0+(2620380053/5000000000 : ℝ)*X 0 1+(5417583543/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652435959/5000000000 : ℝ)*X 1 0+(-1992908089/10000000000 : ℝ)*X 1 1+(2708791713/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326217903/2500000000 : ℝ)*X 2 0+(1083516753/2000000000 : ℝ)*X 2 1+(-49822701/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2168622089/5000000000 : ℝ)*X 0 0+(4523254033/10000000000 : ℝ)*X 0 1+(831717859/2000000000 : ℝ)*X 0 2+(2168622089/5000000000 : ℝ)*X 1 0+(4523254033/10000000000 : ℝ)*X 1 1+(831717859/2000000000 : ℝ)*X 1 2+(2168622089/5000000000 : ℝ)*X 2 0+(4523254033/10000000000 : ℝ)*X 2 1+(831717859/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3425910008450160579089164143/1089500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (45527551/20000000000000 : ℝ)*(base19) + (400851307/100000000000000 : ℝ)*(base23) + (29384007/100000000000000 : ℝ)*(lower2) + (265617717/100000000000000 : ℝ)*(upper5) + (2083808607891937/50000000000000 : ℝ)*(major0) + (2083808607891937/50000000000000 : ℝ)*(major1) + (33340937726271/800000000000 : ℝ)*(major2) + (5613331015414467/100000000000000 : ℝ)*(sp0) + (1403338398003389/25000000000000 : ℝ)*(sp1) + (5613353474147583/100000000000000 : ℝ)*(sp2) + (1360938912236929/50000000000000 : ℝ)*(sp3) + (22859584423/100000000000000 : ℝ)*(sp4) + (55347579/100000000000000 : ℝ)*(sp5) + (2627279021/100000000000000 : ℝ)*(sp7) + (34023505646911/1250000000000 : ℝ)*(f.failure) + (561335387499889/10000000000000 : ℝ)*(f.sum) + (57397742816083/8716000000000000000000000000 : ℝ)*base65 + (11987729925033177061/1089500000000000000000000000000000 : ℝ)*base68 + (46819979463124563/17432000000000000000000000000000 : ℝ)*base70 + (6251691658678177061/1089500000000000000000000000000000 : ℝ)*base72 + (5043827079207/8716000000000000000000000000 : ℝ)*base73 + (112800280546740563/17432000000000000000000000000000 : ℝ)*base76 + (2439908139075052061/1089500000000000000000000000000000 : ℝ)*base78 + (19892314111271552061/1089500000000000000000000000000000 : ℝ)*base80 + (2816232938769/2179000000000000000000000000 : ℝ)*base81 + (1017213/62500000000000000000 : ℝ)*base89 + (1017213/62500000000000000000 : ℝ)*base91 + (392213/62500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4935168272219060695629536667/544750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1976566799/100000000000000 : ℝ)*(base19) + (895276129/50000000000000 : ℝ)*(base23) + (228629019/100000000000000 : ℝ)*(upper3) + (50349743/100000000000000 : ℝ)*(lower4) + (58380489/50000000000000 : ℝ)*(upper5) + (4198798623085787/100000000000000 : ℝ)*(major0) + (4198798623085787/100000000000000 : ℝ)*(major1) + (4198798623085787/100000000000000 : ℝ)*(major2) + (4302862197/12500000000000 : ℝ)*(sp1) + (39684134177/100000000000000 : ℝ)*(sp2) + (1131070368628099/20000000000000 : ℝ)*(sp4) + (141382886091903/2500000000000 : ℝ)*(sp5) + (282765518422703/5000000000000 : ℝ)*(sp6) + (1371122550523697/50000000000000 : ℝ)*(sp7) + (1371122550523697/50000000000000 : ℝ)*(f.failure) + (1131070368628099/20000000000000 : ℝ)*(f.sum) + (617584295441/174320000000000000000000000 : ℝ)*base65 + (2980653049275196111/2179000000000000000000000000000000 : ℝ)*base68 + (49946358284472196111/2179000000000000000000000000000000 : ℝ)*base70 + (2601318000128803889/2179000000000000000000000000000000 : ℝ)*base71 + (20910741177381/4358000000000000000000000000 : ℝ)*base73 + (18086922078629196111/2179000000000000000000000000000000 : ℝ)*base76 + (1621916783288196111/2179000000000000000000000000000000 : ℝ)*base78 + (29156895314502196111/2179000000000000000000000000000000 : ℝ)*base80 + (14421055524457/4358000000000000000000000000 : ℝ)*base82 + (3914051/2500000000000000000000 : ℝ)*base89 + (3914051/2500000000000000000000 : ℝ)*base91 + (3914051/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1301_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76557683/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3011/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10697/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5491/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (461/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1301_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1301_s5_0 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-259982209/1250000000 : ℝ)*x 0 + (5415380831/10000000000 : ℝ)*x 1 + (5242746279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (259982209/1250000000 : ℝ)^4261 ≤ (791004264453/6250000000000 : ℝ)^3237 := by
    have hnat : (259982209 : ℕ)^4261*6250000000000^3237 ≤ 791004264453^3237*1250000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259982209 1250000000 791004264453 6250000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415380831/10000000000 : ℝ)^4261 ≤ (44603053539423/100000000000000 : ℝ)^3237 := by
    have hnat : (5415380831 : ℕ)^4261*100000000000000^3237 ≤ 44603053539423^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415380831 10000000000 44603053539423 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242746279/10000000000 : ℝ)^4261 ≤ (42740878210111/100000000000000 : ℝ)^3237 := by
    have hnat : (5242746279 : ℕ)^4261*100000000000000^3237 ≤ 42740878210111^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242746279 10000000000 42740878210111 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-259982209/1250000000 : ℝ), (5415380831/10000000000 : ℝ), (5242746279/10000000000 : ℝ)] ![(791004264453/6250000000000 : ℝ), (44603053539423/100000000000000 : ℝ), (42740878210111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-259982209/1250000000 : ℝ)|^4261 ≤ (791004264453/6250000000000 : ℝ)^3237
        have hw : |(-259982209/1250000000 : ℝ)|=(259982209/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415380831/10000000000 : ℝ)|^4261 ≤ (44603053539423/100000000000000 : ℝ)^3237
        have hw : |(5415380831/10000000000 : ℝ)|=(5415380831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242746279/10000000000 : ℝ)|^4261 ≤ (42740878210111/100000000000000 : ℝ)^3237
        have hw : |(5242746279/10000000000 : ℝ)|=(5242746279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s5_1 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349806461/10000000000 : ℝ)*x 0 + (-216786123/1000000000 : ℝ)*x 1 + (262137313/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349806461/10000000000 : ℝ)^4261 ≤ (8778693963159/20000000000000 : ℝ)^3237 := by
    have hnat : (5349806461 : ℕ)^4261*20000000000000^3237 ≤ 8778693963159^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349806461 10000000000 8778693963159 20000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216786123/1000000000 : ℝ)^4261 ≤ (2673130432029/20000000000000 : ℝ)^3237 := by
    have hnat : (216786123 : ℕ)^4261*20000000000000^3237 ≤ 2673130432029^3237*1000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216786123 1000000000 2673130432029 20000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262137313/500000000 : ℝ)^4261 ≤ (5342609750777/12500000000000 : ℝ)^3237 := by
    have hnat : (262137313 : ℕ)^4261*12500000000000^3237 ≤ 5342609750777^3237*500000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262137313 500000000 5342609750777 12500000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349806461/10000000000 : ℝ), (-216786123/1000000000 : ℝ), (262137313/500000000 : ℝ)] ![(8778693963159/20000000000000 : ℝ), (2673130432029/20000000000000 : ℝ), (5342609750777/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349806461/10000000000 : ℝ)|^4261 ≤ (8778693963159/20000000000000 : ℝ)^3237
        have hw : |(5349806461/10000000000 : ℝ)|=(5349806461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-216786123/1000000000 : ℝ)|^4261 ≤ (2673130432029/20000000000000 : ℝ)^3237
        have hw : |(-216786123/1000000000 : ℝ)|=(216786123/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262137313/500000000 : ℝ)|^4261 ≤ (5342609750777/12500000000000 : ℝ)^3237
        have hw : |(262137313/500000000 : ℝ)|=(262137313/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s5_2 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349806321/10000000000 : ℝ)*x 0 + (2621373229/5000000000 : ℝ)*x 1 + (-433572231/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349806321/10000000000 : ℝ)^4261 ≤ (43893468303771/100000000000000 : ℝ)^3237 := by
    have hnat : (5349806321 : ℕ)^4261*100000000000000^3237 ≤ 43893468303771^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349806321 10000000000 43893468303771 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621373229/5000000000 : ℝ)^4261 ≤ (42740880131019/100000000000000 : ℝ)^3237 := by
    have hnat : (2621373229 : ℕ)^4261*100000000000000^3237 ≤ 42740880131019^3237*5000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621373229 5000000000 42740880131019 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (433572231/2000000000 : ℝ)^4261 ≤ (2673130310293/20000000000000 : ℝ)^3237 := by
    have hnat : (433572231 : ℕ)^4261*20000000000000^3237 ≤ 2673130310293^3237*2000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433572231 2000000000 2673130310293 20000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349806321/10000000000 : ℝ), (2621373229/5000000000 : ℝ), (-433572231/2000000000 : ℝ)] ![(43893468303771/100000000000000 : ℝ), (42740880131019/100000000000000 : ℝ), (2673130310293/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349806321/10000000000 : ℝ)|^4261 ≤ (43893468303771/100000000000000 : ℝ)^3237
        have hw : |(5349806321/10000000000 : ℝ)|=(5349806321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621373229/5000000000 : ℝ)|^4261 ≤ (42740880131019/100000000000000 : ℝ)^3237
        have hw : |(2621373229/5000000000 : ℝ)|=(2621373229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-433572231/2000000000 : ℝ)|^4261 ≤ (2673130310293/20000000000000 : ℝ)^3237
        have hw : |(-433572231/2000000000 : ℝ)|=(433572231/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s5_3 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1084353773/2500000000 : ℝ)*x 0 + (4162880333/10000000000 : ℝ)*x 1 + (1129726397/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1084353773/2500000000 : ℝ)^4261 ≤ (33302114133147/100000000000000 : ℝ)^3237 := by
    have hnat : (1084353773 : ℕ)^4261*100000000000000^3237 ≤ 33302114133147^3237*2500000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084353773 2500000000 33302114133147 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4162880333/10000000000 : ℝ)^4261 ≤ (985921076371/3125000000000 : ℝ)^3237 := by
    have hnat : (4162880333 : ℕ)^4261*3125000000000^3237 ≤ 985921076371^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4162880333 10000000000 985921076371 3125000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1129726397/2500000000 : ℝ)^4261 ≤ (35148411402751/100000000000000 : ℝ)^3237 := by
    have hnat : (1129726397 : ℕ)^4261*100000000000000^3237 ≤ 35148411402751^3237*2500000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129726397 2500000000 35148411402751 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1084353773/2500000000 : ℝ), (4162880333/10000000000 : ℝ), (1129726397/2500000000 : ℝ)] ![(33302114133147/100000000000000 : ℝ), (985921076371/3125000000000 : ℝ), (35148411402751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1084353773/2500000000 : ℝ)|^4261 ≤ (33302114133147/100000000000000 : ℝ)^3237
        have hw : |(1084353773/2500000000 : ℝ)|=(1084353773/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4162880333/10000000000 : ℝ)|^4261 ≤ (985921076371/3125000000000 : ℝ)^3237
        have hw : |(4162880333/10000000000 : ℝ)|=(4162880333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1129726397/2500000000 : ℝ)|^4261 ≤ (35148411402751/100000000000000 : ℝ)^3237
        have hw : |(1129726397/2500000000 : ℝ)|=(1129726397/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s5_4 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-519967673/2500000000 : ℝ)*x 0 + (5243366221/10000000000 : ℝ)*x 1 + (84605587/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (519967673/2500000000 : ℝ)^4261 ≤ (6328086260957/50000000000000 : ℝ)^3237 := by
    have hnat : (519967673 : ℕ)^4261*50000000000000^3237 ≤ 6328086260957^3237*2500000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519967673 2500000000 6328086260957 50000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243366221/10000000000 : ℝ)^4261 ≤ (42747531134967/100000000000000 : ℝ)^3237 := by
    have hnat : (5243366221 : ℕ)^4261*100000000000000^3237 ≤ 42747531134967^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243366221 10000000000 42747531134967 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84605587/156250000 : ℝ)^4261 ≤ (1783851852899/4000000000000 : ℝ)^3237 := by
    have hnat : (84605587 : ℕ)^4261*4000000000000^3237 ≤ 1783851852899^3237*156250000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84605587 156250000 1783851852899 4000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-519967673/2500000000 : ℝ), (5243366221/10000000000 : ℝ), (84605587/156250000 : ℝ)] ![(6328086260957/50000000000000 : ℝ), (42747531134967/100000000000000 : ℝ), (1783851852899/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-519967673/2500000000 : ℝ)|^4261 ≤ (6328086260957/50000000000000 : ℝ)^3237
        have hw : |(-519967673/2500000000 : ℝ)|=(519967673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243366221/10000000000 : ℝ)|^4261 ≤ (42747531134967/100000000000000 : ℝ)^3237
        have hw : |(5243366221/10000000000 : ℝ)|=(5243366221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84605587/156250000 : ℝ)|^4261 ≤ (1783851852899/4000000000000 : ℝ)^3237
        have hw : |(84605587/156250000 : ℝ)|=(84605587/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s5_5 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326389379/2500000000 : ℝ)*x 0 + (-997924989/5000000000 : ℝ)*x 1 + (5414757583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326389379/2500000000 : ℝ)^4261 ≤ (43416199985233/100000000000000 : ℝ)^3237 := by
    have hnat : (1326389379 : ℕ)^4261*100000000000000^3237 ≤ 43416199985233^3237*2500000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326389379 2500000000 43416199985233 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (997924989/5000000000 : ℝ)^4261 ≤ (11987503504749/100000000000000 : ℝ)^3237 := by
    have hnat : (997924989 : ℕ)^4261*100000000000000^3237 ≤ 11987503504749^3237*5000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      997924989 5000000000 11987503504749 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414757583/10000000000 : ℝ)^4261 ≤ (44596296485097/100000000000000 : ℝ)^3237 := by
    have hnat : (5414757583 : ℕ)^4261*100000000000000^3237 ≤ 44596296485097^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414757583 10000000000 44596296485097 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326389379/2500000000 : ℝ), (-997924989/5000000000 : ℝ), (5414757583/10000000000 : ℝ)] ![(43416199985233/100000000000000 : ℝ), (11987503504749/100000000000000 : ℝ), (44596296485097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326389379/2500000000 : ℝ)|^4261 ≤ (43416199985233/100000000000000 : ℝ)^3237
        have hw : |(1326389379/2500000000 : ℝ)|=(1326389379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-997924989/5000000000 : ℝ)|^4261 ≤ (11987503504749/100000000000000 : ℝ)^3237
        have hw : |(-997924989/5000000000 : ℝ)|=(997924989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414757583/10000000000 : ℝ)|^4261 ≤ (44596296485097/100000000000000 : ℝ)^3237
        have hw : |(5414757583/10000000000 : ℝ)|=(5414757583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s5_6 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (212222301/400000000 : ℝ)*x 0 + (1353689393/2500000000 : ℝ)*x 1 + (-1995849983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212222301/400000000 : ℝ)^4261 ≤ (2170810004109/5000000000000 : ℝ)^3237 := by
    have hnat : (212222301 : ℕ)^4261*5000000000000^3237 ≤ 2170810004109^3237*400000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212222301 400000000 2170810004109 5000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353689393/2500000000 : ℝ)^4261 ≤ (44596296365841/100000000000000 : ℝ)^3237 := by
    have hnat : (1353689393 : ℕ)^4261*100000000000000^3237 ≤ 44596296365841^3237*2500000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353689393 2500000000 44596296365841 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1995849983/10000000000 : ℝ)^4261 ≤ (299687588607/2500000000000 : ℝ)^3237 := by
    have hnat : (1995849983 : ℕ)^4261*2500000000000^3237 ≤ 299687588607^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1995849983 10000000000 299687588607 2500000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212222301/400000000 : ℝ), (1353689393/2500000000 : ℝ), (-1995849983/10000000000 : ℝ)] ![(2170810004109/5000000000000 : ℝ), (44596296365841/100000000000000 : ℝ), (299687588607/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212222301/400000000 : ℝ)|^4261 ≤ (2170810004109/5000000000000 : ℝ)^3237
        have hw : |(212222301/400000000 : ℝ)|=(212222301/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353689393/2500000000 : ℝ)|^4261 ≤ (44596296365841/100000000000000 : ℝ)^3237
        have hw : |(1353689393/2500000000 : ℝ)|=(1353689393/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1995849983/10000000000 : ℝ)|^4261 ≤ (299687588607/2500000000000 : ℝ)^3237
        have hw : |(-1995849983/10000000000 : ℝ)|=(1995849983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1301_s5_7 (p : ℝ) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4337441881/10000000000 : ℝ)*x 0 + (4517626953/10000000000 : ℝ)*x 1 + (832833067/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4337441881/10000000000 : ℝ)^4261 ≤ (33302384881971/100000000000000 : ℝ)^3237 := by
    have hnat : (4337441881 : ℕ)^4261*100000000000000^3237 ≤ 33302384881971^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4337441881 10000000000 33302384881971 100000000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4517626953/10000000000 : ℝ)^4261 ≤ (2195957533471/6250000000000 : ℝ)^3237 := by
    have hnat : (4517626953 : ℕ)^4261*6250000000000^3237 ≤ 2195957533471^3237*10000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4517626953 10000000000 2195957533471 6250000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (832833067/2000000000 : ℝ)^4261 ≤ (3945286820309/12500000000000 : ℝ)^3237 := by
    have hnat : (832833067 : ℕ)^4261*12500000000000^3237 ≤ 3945286820309^3237*2000000000^4261 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      832833067 2000000000 3945286820309 12500000000000 4261 3237 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4261/1024 : ℝ)) 4261 3237 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4337441881/10000000000 : ℝ), (4517626953/10000000000 : ℝ), (832833067/2000000000 : ℝ)] ![(33302384881971/100000000000000 : ℝ), (2195957533471/6250000000000 : ℝ), (3945286820309/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4337441881/10000000000 : ℝ)|^4261 ≤ (33302384881971/100000000000000 : ℝ)^3237
        have hw : |(4337441881/10000000000 : ℝ)|=(4337441881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4517626953/10000000000 : ℝ)|^4261 ≤ (2195957533471/6250000000000 : ℝ)^3237
        have hw : |(4517626953/10000000000 : ℝ)|=(4517626953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(832833067/2000000000 : ℝ)|^4261 ≤ (3945286820309/12500000000000 : ℝ)^3237
        have hw : |(832833067/2000000000 : ℝ)|=(832833067/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1301_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76557683/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (461/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5491/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5519/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3673/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (461/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5491/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (461/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5491/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (461/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5491/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (461/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5491/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (461/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5491/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (461/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5491/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5491/50000 : ℝ) ^ (1065/256 : ℝ) ≤ (10211390726629387/100000000000000000000 : ℝ) := by
    have hpowers : (5491/50000 : ℝ)^1065 ≤ (10211390726629387/100000000000000000000 : ℝ)^256 := by
      have hnat : (5491 : ℕ)^1065*100000000000000000000^256 ≤ 10211390726629387^256*50000^1065 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5491 50000 10211390726629387 100000000000000000000 1065 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5491/50000 : ℝ)) (X := (10211390726629387/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have hpowhi : (461/3125 : ℝ) ^ (1065/256 : ℝ) ≤ (34856990847016357/100000000000000000000 : ℝ) := by
    have hpowers : (461/3125 : ℝ)^1065 ≤ (34856990847016357/100000000000000000000 : ℝ)^256 := by
      have hnat : (461 : ℕ)^1065*100000000000000000000^256 ≤ 34856990847016357^256*3125^1065 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        461 3125 34856990847016357 100000000000000000000 1065 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (461/3125 : ℝ)) (X := (34856990847016357/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010211390726629387/50000000000000000000 : ℝ) ≤ (2000098175146591/2000000000000000 : ℝ) ^ (1065/256 : ℝ) := by
    have hpowers : (50010211390726629387/50000000000000000000 : ℝ)^256 ≤ (2000098175146591/2000000000000000 : ℝ)^1065 := by
      have hnat : (50010211390726629387 : ℕ)^256*2000000000000000^1065 ≤ 2000098175146591^1065*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010211390726629387 50000000000000000000 2000098175146591 2000000000000000 256 1065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000098175146591/2000000000000000 : ℝ)) (X := (50010211390726629387/50000000000000000000 : ℝ)) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252816773848352859/6250000000000000000 : ℝ) ≤ (10001083148476033/10000000000000000 : ℝ) ^ (1065/256 : ℝ) := by
    have hpowers : (6252816773848352859/6250000000000000000 : ℝ)^256 ≤ (10001083148476033/10000000000000000 : ℝ)^1065 := by
      have hnat : (6252816773848352859 : ℕ)^256*10000000000000000^1065 ≤ 10001083148476033^1065*6250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252816773848352859 6250000000000000000 10001083148476033 10000000000000000 256 1065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001083148476033/10000000000000000 : ℝ)) (X := (6252816773848352859/6250000000000000000 : ℝ)) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034856990847016357/50000000000000000000 : ℝ) ≤ (10001675421219111/10000000000000000 : ℝ) ^ (1065/256 : ℝ) := by
    have hpowers : (50034856990847016357/50000000000000000000 : ℝ)^256 ≤ (10001675421219111/10000000000000000 : ℝ)^1065 := by
      have hnat : (50034856990847016357 : ℕ)^256*10000000000000000^1065 ≤ 10001675421219111^1065*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034856990847016357 50000000000000000000 10001675421219111 10000000000000000 256 1065 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001675421219111/10000000000000000 : ℝ)) (X := (50034856990847016357/50000000000000000000 : ℝ)) (by norm_num) 1065 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10211390726629387/100000000000000000000 : ℝ) ≤ ((18844420961492137579/18850000000000000000 : ℝ)+2*(296136371539/188500000000000 : ℝ)*(5491/50000 : ℝ))^(1065/256 : ℝ) := by
    rw [show (18844420961492137579/18850000000000000000 : ℝ)+2*(296136371539/188500000000000 : ℝ)*(5491/50000 : ℝ)=(2000098175146591/2000000000000000 : ℝ) by norm_num, show 1+2*(10211390726629387/100000000000000000000 : ℝ)=(50010211390726629387/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34856990847016357/100000000000000000000 : ℝ)+(10211390726629387/100000000000000000000 : ℝ) ≤ ((18844420961492137579/18850000000000000000 : ℝ)+(296136371539/188500000000000 : ℝ)*((461/3125 : ℝ)+(5491/50000 : ℝ)))^(1065/256 : ℝ) := by
    rw [show (18844420961492137579/18850000000000000000 : ℝ)+(296136371539/188500000000000 : ℝ)*((461/3125 : ℝ)+(5491/50000 : ℝ))=(10001083148476033/10000000000000000 : ℝ) by norm_num, show 1+(34856990847016357/100000000000000000000 : ℝ)+(10211390726629387/100000000000000000000 : ℝ)=(6252816773848352859/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34856990847016357/100000000000000000000 : ℝ) ≤ ((18844420961492137579/18850000000000000000 : ℝ)+2*(296136371539/188500000000000 : ℝ)*(461/3125 : ℝ))^(1065/256 : ℝ) := by
    rw [show (18844420961492137579/18850000000000000000 : ℝ)+2*(296136371539/188500000000000 : ℝ)*(461/3125 : ℝ)=(10001675421219111/10000000000000000 : ℝ) by norm_num, show 1+2*(34856990847016357/100000000000000000000 : ℝ)=(50034856990847016357/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18844420961492137579/18850000000000000000 : ℝ)*(X 1 0+X 2 0)+(296136371539/188500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1065/256 : ℝ)) (lo := (5491/50000 : ℝ)) (hi := (461/3125 : ℝ)) (c := (18844420961492137579/18850000000000000000 : ℝ)) (alpha := (296136371539/188500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18844420961492137579/18850000000000000000 : ℝ)*(X 0 1+X 2 1)+(296136371539/188500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1065/256 : ℝ)) (lo := (5491/50000 : ℝ)) (hi := (461/3125 : ℝ)) (c := (18844420961492137579/18850000000000000000 : ℝ)) (alpha := (296136371539/188500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18844420961492137579/18850000000000000000 : ℝ)*(X 0 2+X 1 2)+(296136371539/188500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1065/256 : ℝ)) (lo := (5491/50000 : ℝ)) (hi := (461/3125 : ℝ)) (c := (18844420961492137579/18850000000000000000 : ℝ)) (alpha := (296136371539/188500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-259982209/1250000000 : ℝ)*X 0 0+(5415380831/10000000000 : ℝ)*X 0 1+(5242746279/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349806461/10000000000 : ℝ)*X 1 0+(-216786123/1000000000 : ℝ)*X 1 1+(262137313/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349806321/10000000000 : ℝ)*X 2 0+(2621373229/5000000000 : ℝ)*X 2 1+(-433572231/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1084353773/2500000000 : ℝ)*X 0 0+(4162880333/10000000000 : ℝ)*X 0 1+(1129726397/2500000000 : ℝ)*X 0 2+(1084353773/2500000000 : ℝ)*X 1 0+(4162880333/10000000000 : ℝ)*X 1 1+(1129726397/2500000000 : ℝ)*X 1 2+(1084353773/2500000000 : ℝ)*X 2 0+(4162880333/10000000000 : ℝ)*X 2 1+(1129726397/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-519967673/2500000000 : ℝ)*X 0 0+(5243366221/10000000000 : ℝ)*X 0 1+(84605587/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326389379/2500000000 : ℝ)*X 1 0+(-997924989/5000000000 : ℝ)*X 1 1+(5414757583/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((212222301/400000000 : ℝ)*X 2 0+(1353689393/2500000000 : ℝ)*X 2 1+(-1995849983/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4337441881/10000000000 : ℝ)*X 0 0+(4517626953/10000000000 : ℝ)*X 0 1+(832833067/2000000000 : ℝ)*X 0 2+(4337441881/10000000000 : ℝ)*X 1 0+(4517626953/10000000000 : ℝ)*X 1 1+(832833067/2000000000 : ℝ)*X 1 2+(4337441881/10000000000 : ℝ)*X 2 0+(4517626953/10000000000 : ℝ)*X 2 1+(832833067/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1301_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (30459874900055343036824649/3770000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1259337119/100000000000000 : ℝ)*(base19) + (481577817/50000000000000 : ℝ)*(base23) + (4834651/6250000000000 : ℝ)*(lower2) + (106793701/100000000000000 : ℝ)*(upper3) + (61660709/100000000000000 : ℝ)*(upper5) + (34405822252423/800000000000 : ℝ)*(major0) + (34405822252423/800000000000 : ℝ)*(major1) + (1075181945388219/25000000000000 : ℝ)*(major2) + (5792612042719249/100000000000000 : ℝ)*(sp0) + (1448159691010019/25000000000000 : ℝ)*(sp1) + (5792639060221561/100000000000000 : ℝ)*(sp2) + (702200499502723/25000000000000 : ℝ)*(sp3) + (13990328973/50000000000000 : ℝ)*(sp4) + (6636199787/50000000000000 : ℝ)*(sp7) + (1404407635205233/50000000000000 : ℝ)*(f.failure) + (1158528004675439/20000000000000 : ℝ)*(f.sum) + (114017045528489/18850000000000000000000000000 : ℝ)*base65 + (7267034160815009/1160000000000000000000000000000 : ℝ)*base67 + (1909498508498156801/471250000000000000000000000000000 : ℝ)*base69 + (9341800009655009/1160000000000000000000000000000 : ℝ)*base71 + (96114111375489/18850000000000000000000000000 : ℝ)*base73 + (2086633613123093199/471250000000000000000000000000000 : ℝ)*base76 + (216956105869683917/15080000000000000000000000000000 : ℝ)*base77 + (123383828862123917/15080000000000000000000000000000 : ℝ)*base79 + (903549197849/188500000000000000000000000 : ℝ)*base81 + (7044861/2500000000000000000000 : ℝ)*base90 + (7044861/2500000000000000000000 : ℝ)*base92 + (32044861/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (81209073224617548938181/9425000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1481637149/100000000000000 : ℝ)*(base19) + (1630245967/100000000000000 : ℝ)*(base23) + (86687401/50000000000000 : ℝ)*(upper3) + (63622773/100000000000000 : ℝ)*(lower4) + (178009853/100000000000000 : ℝ)*(upper5) + (2165940128993891/50000000000000 : ℝ)*(major0) + (2165940128993891/50000000000000 : ℝ)*(major1) + (2165940128993891/50000000000000 : ℝ)*(major2) + (29924986131/100000000000000 : ℝ)*(sp1) + (6435712241/20000000000000 : ℝ)*(sp2) + (2917299601937609/50000000000000 : ℝ)*(sp4) + (2917283898625969/50000000000000 : ℝ)*(sp5) + (2917282697534023/50000000000000 : ℝ)*(sp6) + (707290256222191/25000000000000 : ℝ)*(sp7) + (707290256222191/25000000000000 : ℝ)*(f.failure) + (2917299601937609/50000000000000 : ℝ)*(f.sum) + (1892392718799/4712500000000000000000000000 : ℝ)*base65 + (9691155922927570111/942500000000000000000000000000000 : ℝ)*base68 + (16215456096477429889/942500000000000000000000000000000 : ℝ)*base69 + (4580464953680070111/942500000000000000000000000000000 : ℝ)*base72 + (8187296331163/2356250000000000000000000000 : ℝ)*base74 + (1978130181652429889/942500000000000000000000000000000 : ℝ)*base75 + (6254405797710070111/942500000000000000000000000000000 : ℝ)*base78 + (5178200016952429889/942500000000000000000000000000000 : ℝ)*base79 + (44493747611023/9425000000000000000000000000 : ℝ)*base81 + (1143453/1250000000000000000000 : ℝ)*base89 + (1143453/1250000000000000000000 : ℝ)*base91 + (1143453/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1301_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76557683/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (461/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5491/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5519/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3673/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1301_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1301_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76557683/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16277/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (957/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5519/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3673/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1301_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1301_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1301_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1065/256 : ℝ) ≤ p) (hpb : p ≤ (4261/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76557683/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16277/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (957/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5519/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3673/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1301_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
