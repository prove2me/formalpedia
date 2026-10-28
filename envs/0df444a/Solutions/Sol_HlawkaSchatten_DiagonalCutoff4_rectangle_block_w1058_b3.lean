-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1058_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:01:23.018077+00:00
-- url     : https://prove2.me/submissions/08da4364-c551-4ae3-9844-c540bfddd861

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
theorem support_rectangle_w1058_s9_0 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1103858233/5000000000 : ℝ)*x 0 + (5394472087/10000000000 : ℝ)*x 1 + (2632163597/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1103858233/5000000000 : ℝ)^8251 ≤ (6703594979037/50000000000000 : ℝ)^6203 := by
    have hnat : (1103858233 : ℕ)^8251*50000000000000^6203 ≤ 6703594979037^6203*5000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103858233 5000000000 6703594979037 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394472087/10000000000 : ℝ)^8251 ≤ (10999893166921/25000000000000 : ℝ)^6203 := by
    have hnat : (5394472087 : ℕ)^8251*25000000000000^6203 ≤ 10999893166921^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394472087 10000000000 10999893166921 25000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632163597/5000000000 : ℝ)^8251 ≤ (4259323735571/10000000000000 : ℝ)^6203 := by
    have hnat : (2632163597 : ℕ)^8251*10000000000000^6203 ≤ 4259323735571^6203*5000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632163597 5000000000 4259323735571 10000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1103858233/5000000000 : ℝ), (5394472087/10000000000 : ℝ), (2632163597/5000000000 : ℝ)] ![(6703594979037/50000000000000 : ℝ), (10999893166921/25000000000000 : ℝ), (4259323735571/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1103858233/5000000000 : ℝ)|^8251 ≤ (6703594979037/50000000000000 : ℝ)^6203
        have hw : |(-1103858233/5000000000 : ℝ)|=(1103858233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394472087/10000000000 : ℝ)|^8251 ≤ (10999893166921/25000000000000 : ℝ)^6203
        have hw : |(5394472087/10000000000 : ℝ)|=(5394472087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632163597/5000000000 : ℝ)|^8251 ≤ (4259323735571/10000000000000 : ℝ)^6203
        have hw : |(2632163597/5000000000 : ℝ)|=(2632163597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s9_1 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336247667/2500000000 : ℝ)*x 0 + (-454749939/2000000000 : ℝ)*x 1 + (1316081803/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336247667/2500000000 : ℝ)^8251 ≤ (10865886318043/25000000000000 : ℝ)^6203 := by
    have hnat : (1336247667 : ℕ)^8251*25000000000000^6203 ≤ 10865886318043^6203*2500000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336247667 2500000000 10865886318043 25000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (454749939/2000000000 : ℝ)^8251 ≤ (1394321716561/10000000000000 : ℝ)^6203 := by
    have hnat : (454749939 : ℕ)^8251*10000000000000^6203 ≤ 1394321716561^6203*2000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454749939 2000000000 1394321716561 10000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316081803/2500000000 : ℝ)^8251 ≤ (42593237549431/100000000000000 : ℝ)^6203 := by
    have hnat : (1316081803 : ℕ)^8251*100000000000000^6203 ≤ 42593237549431^6203*2500000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316081803 2500000000 42593237549431 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336247667/2500000000 : ℝ), (-454749939/2000000000 : ℝ), (1316081803/2500000000 : ℝ)] ![(10865886318043/25000000000000 : ℝ), (1394321716561/10000000000000 : ℝ), (42593237549431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336247667/2500000000 : ℝ)|^8251 ≤ (10865886318043/25000000000000 : ℝ)^6203
        have hw : |(1336247667/2500000000 : ℝ)|=(1336247667/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-454749939/2000000000 : ℝ)|^8251 ≤ (1394321716561/10000000000000 : ℝ)^6203
        have hw : |(-454749939/2000000000 : ℝ)|=(454749939/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316081803/2500000000 : ℝ)|^8251 ≤ (42593237549431/100000000000000 : ℝ)^6203
        have hw : |(1316081803/2500000000 : ℝ)|=(1316081803/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s9_2 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344990679/10000000000 : ℝ)*x 0 + (1316081799/2500000000 : ℝ)*x 1 + (-2273749701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344990679/10000000000 : ℝ)^8251 ≤ (2716471586947/6250000000000 : ℝ)^6203 := by
    have hnat : (5344990679 : ℕ)^8251*6250000000000^6203 ≤ 2716471586947^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344990679 10000000000 2716471586947 6250000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316081799/2500000000 : ℝ)^8251 ≤ (8518647475447/20000000000000 : ℝ)^6203 := by
    have hnat : (1316081799 : ℕ)^8251*20000000000000^6203 ≤ 8518647475447^6203*2500000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316081799 2500000000 8518647475447 20000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2273749701/10000000000 : ℝ)^8251 ≤ (1742902151819/12500000000000 : ℝ)^6203 := by
    have hnat : (2273749701 : ℕ)^8251*12500000000000^6203 ≤ 1742902151819^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2273749701 10000000000 1742902151819 12500000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344990679/10000000000 : ℝ), (1316081799/2500000000 : ℝ), (-2273749701/10000000000 : ℝ)] ![(2716471586947/6250000000000 : ℝ), (8518647475447/20000000000000 : ℝ), (1742902151819/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344990679/10000000000 : ℝ)|^8251 ≤ (2716471586947/6250000000000 : ℝ)^6203
        have hw : |(5344990679/10000000000 : ℝ)|=(5344990679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316081799/2500000000 : ℝ)|^8251 ≤ (8518647475447/20000000000000 : ℝ)^6203
        have hw : |(1316081799/2500000000 : ℝ)|=(1316081799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2273749701/10000000000 : ℝ)|^8251 ≤ (1742902151819/12500000000000 : ℝ)^6203
        have hw : |(-2273749701/10000000000 : ℝ)|=(2273749701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s9_3 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (136770163/312500000 : ℝ)*x 0 + (85023897/200000000 : ℝ)*x 1 + (901171131/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136770163/312500000 : ℝ)^8251 ≤ (16658257051089/50000000000000 : ℝ)^6203 := by
    have hnat : (136770163 : ℕ)^8251*50000000000000^6203 ≤ 16658257051089^6203*312500000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136770163 312500000 16658257051089 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (85023897/200000000 : ℝ)^8251 ≤ (16026148454709/50000000000000 : ℝ)^6203 := by
    have hnat : (85023897 : ℕ)^8251*50000000000000^6203 ≤ 16026148454709^6203*200000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85023897 200000000 16026148454709 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (901171131/2000000000 : ℝ)^8251 ≤ (8657797243857/25000000000000 : ℝ)^6203 := by
    have hnat : (901171131 : ℕ)^8251*25000000000000^6203 ≤ 8657797243857^6203*2000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901171131 2000000000 8657797243857 25000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(136770163/312500000 : ℝ), (85023897/200000000 : ℝ), (901171131/2000000000 : ℝ)] ![(16658257051089/50000000000000 : ℝ), (16026148454709/50000000000000 : ℝ), (8657797243857/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(136770163/312500000 : ℝ)|^8251 ≤ (16658257051089/50000000000000 : ℝ)^6203
        have hw : |(136770163/312500000 : ℝ)|=(136770163/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(85023897/200000000 : ℝ)|^8251 ≤ (16026148454709/50000000000000 : ℝ)^6203
        have hw : |(85023897/200000000 : ℝ)|=(85023897/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(901171131/2000000000 : ℝ)|^8251 ≤ (8657797243857/25000000000000 : ℝ)^6203
        have hw : |(901171131/2000000000 : ℝ)|=(901171131/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s9_4 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2207721359/10000000000 : ℝ)*x 0 + (5264653353/10000000000 : ℝ)*x 1 + (5394144897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2207721359/10000000000 : ℝ)^8251 ≤ (6703614741663/50000000000000 : ℝ)^6203 := by
    have hnat : (2207721359 : ℕ)^8251*50000000000000^6203 ≤ 6703614741663^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2207721359 10000000000 6703614741663 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264653353/10000000000 : ℝ)^8251 ≤ (42596747592317/100000000000000 : ℝ)^6203 := by
    have hnat : (5264653353 : ℕ)^8251*100000000000000^6203 ≤ 42596747592317^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264653353 10000000000 42596747592317 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394144897/10000000000 : ℝ)^8251 ≤ (43996022899541/100000000000000 : ℝ)^6203 := by
    have hnat : (5394144897 : ℕ)^8251*100000000000000^6203 ≤ 43996022899541^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394144897 10000000000 43996022899541 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2207721359/10000000000 : ℝ), (5264653353/10000000000 : ℝ), (5394144897/10000000000 : ℝ)] ![(6703614741663/50000000000000 : ℝ), (42596747592317/100000000000000 : ℝ), (43996022899541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2207721359/10000000000 : ℝ)|^8251 ≤ (6703614741663/50000000000000 : ℝ)^6203
        have hw : |(-2207721359/10000000000 : ℝ)|=(2207721359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264653353/10000000000 : ℝ)|^8251 ≤ (42596747592317/100000000000000 : ℝ)^6203
        have hw : |(5264653353/10000000000 : ℝ)|=(5264653353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394144897/10000000000 : ℝ)|^8251 ≤ (43996022899541/100000000000000 : ℝ)^6203
        have hw : |(5394144897/10000000000 : ℝ)|=(5394144897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s9_5 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312230441/10000000000 : ℝ)*x 0 + (-535982957/2500000000 : ℝ)*x 1 + (2697072639/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312230441/10000000000 : ℝ)^8251 ≤ (21554778180927/50000000000000 : ℝ)^6203 := by
    have hnat : (5312230441 : ℕ)^8251*50000000000000^6203 ≤ 21554778180927^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312230441 10000000000 21554778180927 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (535982957/2500000000 : ℝ)^8251 ≤ (2578883317777/20000000000000 : ℝ)^6203 := by
    have hnat : (535982957 : ℕ)^8251*20000000000000^6203 ≤ 2578883317777^6203*2500000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535982957 2500000000 2578883317777 20000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697072639/5000000000 : ℝ)^8251 ≤ (43996027033067/100000000000000 : ℝ)^6203 := by
    have hnat : (2697072639 : ℕ)^8251*100000000000000^6203 ≤ 43996027033067^6203*5000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697072639 5000000000 43996027033067 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312230441/10000000000 : ℝ), (-535982957/2500000000 : ℝ), (2697072639/5000000000 : ℝ)] ![(21554778180927/50000000000000 : ℝ), (2578883317777/20000000000000 : ℝ), (43996027033067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312230441/10000000000 : ℝ)|^8251 ≤ (21554778180927/50000000000000 : ℝ)^6203
        have hw : |(5312230441/10000000000 : ℝ)|=(5312230441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-535982957/2500000000 : ℝ)|^8251 ≤ (2578883317777/20000000000000 : ℝ)^6203
        have hw : |(-535982957/2500000000 : ℝ)|=(535982957/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697072639/5000000000 : ℝ)|^8251 ≤ (43996027033067/100000000000000 : ℝ)^6203
        have hw : |(2697072639/5000000000 : ℝ)|=(2697072639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s9_6 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312230629/10000000000 : ℝ)*x 0 + (2697072601/5000000000 : ℝ)*x 1 + (-2143931677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312230629/10000000000 : ℝ)^8251 ≤ (8621911678243/20000000000000 : ℝ)^6203 := by
    have hnat : (5312230629 : ℕ)^8251*20000000000000^6203 ≤ 8621911678243^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312230629 10000000000 8621911678243 20000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697072601/5000000000 : ℝ)^8251 ≤ (43996026208531/100000000000000 : ℝ)^6203 := by
    have hnat : (2697072601 : ℕ)^8251*100000000000000^6203 ≤ 43996026208531^6203*5000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697072601 5000000000 43996026208531 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2143931677/10000000000 : ℝ)^8251 ≤ (1289441538087/10000000000000 : ℝ)^6203 := by
    have hnat : (2143931677 : ℕ)^8251*10000000000000^6203 ≤ 1289441538087^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143931677 10000000000 1289441538087 10000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312230629/10000000000 : ℝ), (2697072601/5000000000 : ℝ), (-2143931677/10000000000 : ℝ)] ![(8621911678243/20000000000000 : ℝ), (43996026208531/100000000000000 : ℝ), (1289441538087/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312230629/10000000000 : ℝ)|^8251 ≤ (8621911678243/20000000000000 : ℝ)^6203
        have hw : |(5312230629/10000000000 : ℝ)|=(5312230629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697072601/5000000000 : ℝ)|^8251 ≤ (43996026208531/100000000000000 : ℝ)^6203
        have hw : |(2697072601/5000000000 : ℝ)|=(2697072601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2143931677/10000000000 : ℝ)|^8251 ≤ (1289441538087/10000000000000 : ℝ)^6203
        have hw : |(-2143931677/10000000000 : ℝ)|=(2143931677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_s9_7 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4376655683/10000000000 : ℝ)*x 0 + (2252609033/5000000000 : ℝ)*x 1 + (1062958551/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4376655683/10000000000 : ℝ)^8251 ≤ (1332664803497/4000000000000 : ℝ)^6203 := by
    have hnat : (4376655683 : ℕ)^8251*4000000000000^6203 ≤ 1332664803497^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4376655683 10000000000 1332664803497 4000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2252609033/5000000000 : ℝ)^8251 ≤ (1731233540331/5000000000000 : ℝ)^6203 := by
    have hnat : (2252609033 : ℕ)^8251*5000000000000^6203 ≤ 1731233540331^6203*5000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252609033 5000000000 1731233540331 5000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1062958551/2500000000 : ℝ)^8251 ≤ (16029354540393/50000000000000 : ℝ)^6203 := by
    have hnat : (1062958551 : ℕ)^8251*50000000000000^6203 ≤ 16029354540393^6203*2500000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062958551 2500000000 16029354540393 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4376655683/10000000000 : ℝ), (2252609033/5000000000 : ℝ), (1062958551/2500000000 : ℝ)] ![(1332664803497/4000000000000 : ℝ), (1731233540331/5000000000000 : ℝ), (16029354540393/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4376655683/10000000000 : ℝ)|^8251 ≤ (1332664803497/4000000000000 : ℝ)^6203
        have hw : |(4376655683/10000000000 : ℝ)|=(4376655683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2252609033/5000000000 : ℝ)|^8251 ≤ (1731233540331/5000000000000 : ℝ)^6203
        have hw : |(2252609033/5000000000 : ℝ)|=(2252609033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1062958551/2500000000 : ℝ)|^8251 ≤ (16029354540393/50000000000000 : ℝ)^6203
        have hw : |(1062958551/2500000000 : ℝ)|=(1062958551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1058_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29567487/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6999/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (281/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (11241/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13997/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6999/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (281/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6999/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (281/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6999/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (281/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6999/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (281/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6999/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (281/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6999/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (281/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (281/2500 : ℝ) ^ (4125/1024 : ℝ) ≤ (15003156871508543/100000000000000000000 : ℝ) := by
    have hpowers : (281/2500 : ℝ)^4125 ≤ (15003156871508543/100000000000000000000 : ℝ)^1024 := by
      have hnat : (281 : ℕ)^4125*100000000000000000000^1024 ≤ 15003156871508543^1024*2500^4125 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        281 2500 15003156871508543 100000000000000000000 4125 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (281/2500 : ℝ)) (X := (15003156871508543/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4125 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (6999/50000 : ℝ) ^ (4125/1024 : ℝ) ≤ (36314517539489353/100000000000000000000 : ℝ) := by
    have hpowers : (6999/50000 : ℝ)^4125 ≤ (36314517539489353/100000000000000000000 : ℝ)^1024 := by
      have hnat : (6999 : ℕ)^4125*100000000000000000000^1024 ≤ 36314517539489353^1024*50000^4125 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6999 50000 36314517539489353 100000000000000000000 4125 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6999/50000 : ℝ)) (X := (36314517539489353/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4125 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50015003156871508543/50000000000000000000 : ℝ) ≤ (400029792000313/400000000000000 : ℝ) ^ (4125/1024 : ℝ) := by
    have hpowers : (50015003156871508543/50000000000000000000 : ℝ)^1024 ≤ (400029792000313/400000000000000 : ℝ)^4125 := by
      have hnat : (50015003156871508543 : ℕ)^1024*400000000000000^4125 ≤ 400029792000313^4125*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015003156871508543 50000000000000000000 400029792000313 400000000000000 1024 4125 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400029792000313/400000000000000 : ℝ)) (X := (50015003156871508543/50000000000000000000 : ℝ)) (by norm_num) 4125 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506414709301374737/12500000000000000000 : ℝ) ≤ (2500318419183519/2500000000000000 : ℝ) ^ (4125/1024 : ℝ) := by
    have hpowers : (12506414709301374737/12500000000000000000 : ℝ)^1024 ≤ (2500318419183519/2500000000000000 : ℝ)^4125 := by
      have hnat : (12506414709301374737 : ℕ)^1024*2500000000000000^4125 ≤ 2500318419183519^4125*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506414709301374737 12500000000000000000 2500318419183519 2500000000000000 1024 4125 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500318419183519/2500000000000000 : ℝ)) (X := (12506414709301374737/12500000000000000000 : ℝ)) (by norm_num) 4125 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036314517539489353/50000000000000000000 : ℝ) ≤ (10001802553460327/10000000000000000 : ℝ) ^ (4125/1024 : ℝ) := by
    have hpowers : (50036314517539489353/50000000000000000000 : ℝ)^1024 ≤ (10001802553460327/10000000000000000 : ℝ)^4125 := by
      have hnat : (50036314517539489353 : ℕ)^1024*10000000000000000^4125 ≤ 10001802553460327^4125*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036314517539489353 50000000000000000000 10001802553460327 10000000000000000 1024 4125 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001802553460327/10000000000000000 : ℝ)) (X := (50036314517539489353/50000000000000000000 : ℝ)) (by norm_num) 4125 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15003156871508543/100000000000000000000 : ℝ) ≤ ((2757016500961545887/2758000000000000000 : ℝ)+2*(528876726251/275800000000000 : ℝ)*(281/2500 : ℝ))^(4125/1024 : ℝ) := by
    rw [show (2757016500961545887/2758000000000000000 : ℝ)+2*(528876726251/275800000000000 : ℝ)*(281/2500 : ℝ)=(400029792000313/400000000000000 : ℝ) by norm_num, show 1+2*(15003156871508543/100000000000000000000 : ℝ)=(50015003156871508543/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36314517539489353/100000000000000000000 : ℝ)+(15003156871508543/100000000000000000000 : ℝ) ≤ ((2757016500961545887/2758000000000000000 : ℝ)+(528876726251/275800000000000 : ℝ)*((6999/50000 : ℝ)+(281/2500 : ℝ)))^(4125/1024 : ℝ) := by
    rw [show (2757016500961545887/2758000000000000000 : ℝ)+(528876726251/275800000000000 : ℝ)*((6999/50000 : ℝ)+(281/2500 : ℝ))=(2500318419183519/2500000000000000 : ℝ) by norm_num, show 1+(36314517539489353/100000000000000000000 : ℝ)+(15003156871508543/100000000000000000000 : ℝ)=(12506414709301374737/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36314517539489353/100000000000000000000 : ℝ) ≤ ((2757016500961545887/2758000000000000000 : ℝ)+2*(528876726251/275800000000000 : ℝ)*(6999/50000 : ℝ))^(4125/1024 : ℝ) := by
    rw [show (2757016500961545887/2758000000000000000 : ℝ)+2*(528876726251/275800000000000 : ℝ)*(6999/50000 : ℝ)=(10001802553460327/10000000000000000 : ℝ) by norm_num, show 1+2*(36314517539489353/100000000000000000000 : ℝ)=(50036314517539489353/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2757016500961545887/2758000000000000000 : ℝ)*(X 1 0+X 2 0)+(528876726251/275800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4125/1024 : ℝ)) (lo := (281/2500 : ℝ)) (hi := (6999/50000 : ℝ)) (c := (2757016500961545887/2758000000000000000 : ℝ)) (alpha := (528876726251/275800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2757016500961545887/2758000000000000000 : ℝ)*(X 0 1+X 2 1)+(528876726251/275800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4125/1024 : ℝ)) (lo := (281/2500 : ℝ)) (hi := (6999/50000 : ℝ)) (c := (2757016500961545887/2758000000000000000 : ℝ)) (alpha := (528876726251/275800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2757016500961545887/2758000000000000000 : ℝ)*(X 0 2+X 1 2)+(528876726251/275800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4125/1024 : ℝ)) (lo := (281/2500 : ℝ)) (hi := (6999/50000 : ℝ)) (c := (2757016500961545887/2758000000000000000 : ℝ)) (alpha := (528876726251/275800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1103858233/5000000000 : ℝ)*X 0 0+(5394472087/10000000000 : ℝ)*X 0 1+(2632163597/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336247667/2500000000 : ℝ)*X 1 0+(-454749939/2000000000 : ℝ)*X 1 1+(1316081803/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344990679/10000000000 : ℝ)*X 2 0+(1316081799/2500000000 : ℝ)*X 2 1+(-2273749701/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((136770163/312500000 : ℝ)*X 0 0+(85023897/200000000 : ℝ)*X 0 1+(901171131/2000000000 : ℝ)*X 0 2+(136770163/312500000 : ℝ)*X 1 0+(85023897/200000000 : ℝ)*X 1 1+(901171131/2000000000 : ℝ)*X 1 2+(136770163/312500000 : ℝ)*X 2 0+(85023897/200000000 : ℝ)*X 2 1+(901171131/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2207721359/10000000000 : ℝ)*X 0 0+(5264653353/10000000000 : ℝ)*X 0 1+(5394144897/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312230441/10000000000 : ℝ)*X 1 0+(-535982957/2500000000 : ℝ)*X 1 1+(2697072639/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s9_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312230629/10000000000 : ℝ)*X 2 0+(2697072601/5000000000 : ℝ)*X 2 1+(-2143931677/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s9_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4376655683/10000000000 : ℝ)*X 0 0+(2252609033/5000000000 : ℝ)*X 0 1+(1062958551/2500000000 : ℝ)*X 0 2+(4376655683/10000000000 : ℝ)*X 1 0+(2252609033/5000000000 : ℝ)*X 1 1+(1062958551/2500000000 : ℝ)*X 1 2+(4376655683/10000000000 : ℝ)*X 2 0+(2252609033/5000000000 : ℝ)*X 2 1+(1062958551/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_s9_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21410583083174459861219097/4925000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (227860253/25000000000000 : ℝ)*(base19) + (435747809/50000000000000 : ℝ)*(base23) + (596059/2000000000000 : ℝ)*(lower2) + (118760911/100000000000000 : ℝ)*(upper3) + (17610883/25000000000000 : ℝ)*(upper5) + (1451326626544061/25000000000000 : ℝ)*(major0) + (1451326626544061/25000000000000 : ℝ)*(major1) + (1451326626544061/25000000000000 : ℝ)*(major2) + (7683770041151519/100000000000000 : ℝ)*(sp0) + (1920948573914711/25000000000000 : ℝ)*(sp1) + (7683794335604237/100000000000000 : ℝ)*(sp2) + (785360818639203/20000000000000 : ℝ)*(sp3) + (1572871771/6250000000000 : ℝ)*(sp4) + (13567145727/100000000000000 : ℝ)*(sp7) + (1963408830170871/50000000000000 : ℝ)*(f.failure) + (1536759041419971/20000000000000 : ℝ)*(f.sum) + (17128526651437/6895000000000000000000000000 : ℝ)*base65 + (252620974310412893/68950000000000000000000000000000 : ℝ)*base68 + (497647231283487107/68950000000000000000000000000000 : ℝ)*base69 + (64600663723587107/68950000000000000000000000000000 : ℝ)*base71 + (16887342456291/3447500000000000000000000000 : ℝ)*base73 + (456862351325987107/68950000000000000000000000000000 : ℝ)*base75 + (719195475641137107/68950000000000000000000000000000 : ℝ)*base77 + (32091893554862893/68950000000000000000000000000000 : ℝ)*base80 + (19017004295899/3447500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (3928823/1000000000000000000000 : ℝ)*base90 + (3928823/1000000000000000000000 : ℝ)*base92 + (3928823/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (37533954540728815799081163/17237500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5369473/1000000000000 : ℝ)*(base23) + (122718537/100000000000000 : ℝ)*(lower1) + (148353957/100000000000000 : ℝ)*(lower2) + (42877143/25000000000000 : ℝ)*(upper3) + (108872371/50000000000000 : ℝ)*(lower4) + (1458636535964883/25000000000000 : ℝ)*(major0) + (1458636535964883/25000000000000 : ℝ)*(major1) + (1458636535964883/25000000000000 : ℝ)*(major2) + (2696312803/12500000000000 : ℝ)*(sp2) + (7293031567/100000000000000 : ℝ)*(sp3) + (482656019886971/6250000000000 : ℝ)*(sp4) + (482656019886971/6250000000000 : ℝ)*(sp5) + (7722474210741811/100000000000000 : ℝ)*(sp6) + (493323575489247/12500000000000 : ℝ)*(sp7) + (1973297948472771/50000000000000 : ℝ)*(f.failure) + (482656019886971/6250000000000 : ℝ)*(f.sum) + (6490186365427/3447500000000000000000000000 : ℝ)*base66 + (1268362839315883779/68950000000000000000000000000000 : ℝ)*base68 + (324523666286466221/68950000000000000000000000000000 : ℝ)*base69 + (1072742441879783779/68950000000000000000000000000000 : ℝ)*base72 + (553344662509/430937500000000000000000000 : ℝ)*base74 + (174052074856733779/68950000000000000000000000000000 : ℝ)*base76 + (881357074588833779/68950000000000000000000000000000 : ℝ)*base78 + (841903208671983779/68950000000000000000000000000000 : ℝ)*base80 + (617774438539/1723750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (6396477/1000000000000000000000 : ℝ)*base89 + (6396477/1000000000000000000000 : ℝ)*base91 + (6396477/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1058_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29567487/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6999/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (281/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11241/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13997/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1058_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1058_box_0 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2077983197/10000000000 : ℝ)*x 0 + (5377472731/10000000000 : ℝ)*x 1 + (2688736757/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2077983197/10000000000 : ℝ)^8251 ≤ (12369518579631/100000000000000 : ℝ)^6203 := by
    have hnat : (2077983197 : ℕ)^8251*100000000000000^6203 ≤ 12369518579631^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077983197 10000000000 12369518579631 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377472731/10000000000 : ℝ)^8251 ≤ (21907618231969/50000000000000 : ℝ)^6203 := by
    have hnat : (5377472731 : ℕ)^8251*50000000000000^6203 ≤ 21907618231969^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377472731 10000000000 21907618231969 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688736757/5000000000 : ℝ)^8251 ≤ (43815244950143/100000000000000 : ℝ)^6203 := by
    have hnat : (2688736757 : ℕ)^8251*100000000000000^6203 ≤ 43815244950143^6203*5000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688736757 5000000000 43815244950143 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2077983197/10000000000 : ℝ), (5377472731/10000000000 : ℝ), (2688736757/5000000000 : ℝ)] ![(12369518579631/100000000000000 : ℝ), (21907618231969/50000000000000 : ℝ), (43815244950143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2077983197/10000000000 : ℝ)|^8251 ≤ (12369518579631/100000000000000 : ℝ)^6203
        have hw : |(-2077983197/10000000000 : ℝ)|=(2077983197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377472731/10000000000 : ℝ)|^8251 ≤ (21907618231969/50000000000000 : ℝ)^6203
        have hw : |(5377472731/10000000000 : ℝ)|=(5377472731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688736757/5000000000 : ℝ)|^8251 ≤ (43815244950143/100000000000000 : ℝ)^6203
        have hw : |(2688736757/5000000000 : ℝ)|=(2688736757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_box_1 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5295113209/10000000000 : ℝ)*x 0 + (-2189455093/10000000000 : ℝ)*x 1 + (5377472949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295113209/10000000000 : ℝ)^8251 ≤ (42924883215761/100000000000000 : ℝ)^6203 := by
    have hnat : (5295113209 : ℕ)^8251*100000000000000^6203 ≤ 42924883215761^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295113209 10000000000 42924883215761 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2189455093/10000000000 : ℝ)^8251 ≤ (13259877943473/100000000000000 : ℝ)^6203 := by
    have hnat : (2189455093 : ℕ)^8251*100000000000000^6203 ≤ 13259877943473^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189455093 10000000000 13259877943473 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5377472949/10000000000 : ℝ)^8251 ≤ (43815238826637/100000000000000 : ℝ)^6203 := by
    have hnat : (5377472949 : ℕ)^8251*100000000000000^6203 ≤ 43815238826637^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377472949 10000000000 43815238826637 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295113209/10000000000 : ℝ), (-2189455093/10000000000 : ℝ), (5377472949/10000000000 : ℝ)] ![(42924883215761/100000000000000 : ℝ), (13259877943473/100000000000000 : ℝ), (43815238826637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295113209/10000000000 : ℝ)|^8251 ≤ (42924883215761/100000000000000 : ℝ)^6203
        have hw : |(5295113209/10000000000 : ℝ)|=(5295113209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2189455093/10000000000 : ℝ)|^8251 ≤ (13259877943473/100000000000000 : ℝ)^6203
        have hw : |(-2189455093/10000000000 : ℝ)|=(2189455093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5377472949/10000000000 : ℝ)|^8251 ≤ (43815238826637/100000000000000 : ℝ)^6203
        have hw : |(5377472949/10000000000 : ℝ)|=(5377472949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_box_2 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5295113387/10000000000 : ℝ)*x 0 + (1344368289/2500000000 : ℝ)*x 1 + (-136840911/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295113387/10000000000 : ℝ)^8251 ≤ (42924885135131/100000000000000 : ℝ)^6203 := by
    have hnat : (5295113387 : ℕ)^8251*100000000000000^6203 ≤ 42924885135131^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295113387 10000000000 42924885135131 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1344368289/2500000000 : ℝ)^8251 ≤ (10953810267529/25000000000000 : ℝ)^6203 := by
    have hnat : (1344368289 : ℕ)^8251*25000000000000^6203 ≤ 10953810267529^6203*2500000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344368289 2500000000 10953810267529 25000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (136840911/625000000 : ℝ)^8251 ≤ (3314968444657/25000000000000 : ℝ)^6203 := by
    have hnat : (136840911 : ℕ)^8251*25000000000000^6203 ≤ 3314968444657^6203*625000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136840911 625000000 3314968444657 25000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295113387/10000000000 : ℝ), (1344368289/2500000000 : ℝ), (-136840911/625000000 : ℝ)] ![(42924885135131/100000000000000 : ℝ), (10953810267529/25000000000000 : ℝ), (3314968444657/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295113387/10000000000 : ℝ)|^8251 ≤ (42924885135131/100000000000000 : ℝ)^6203
        have hw : |(5295113387/10000000000 : ℝ)|=(5295113387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1344368289/2500000000 : ℝ)|^8251 ≤ (10953810267529/25000000000000 : ℝ)^6203
        have hw : |(1344368289/2500000000 : ℝ)|=(1344368289/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-136840911/625000000 : ℝ)|^8251 ≤ (3314968444657/25000000000000 : ℝ)^6203
        have hw : |(-136840911/625000000 : ℝ)|=(136840911/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_box_3 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2242559607/5000000000 : ℝ)*x 0 + (4324576507/10000000000 : ℝ)*x 1 + (2162288311/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2242559607/5000000000 : ℝ)^8251 ≤ (6883870694827/20000000000000 : ℝ)^6203 := by
    have hnat : (2242559607 : ℕ)^8251*20000000000000^6203 ≤ 6883870694827^6203*5000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242559607 5000000000 6883870694827 20000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4324576507/10000000000 : ℝ)^8251 ≤ (3279032267423/10000000000000 : ℝ)^6203 := by
    have hnat : (4324576507 : ℕ)^8251*10000000000000^6203 ≤ 3279032267423^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4324576507 10000000000 3279032267423 10000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2162288311/5000000000 : ℝ)^8251 ≤ (4098790479261/12500000000000 : ℝ)^6203 := by
    have hnat : (2162288311 : ℕ)^8251*12500000000000^6203 ≤ 4098790479261^6203*5000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162288311 5000000000 4098790479261 12500000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2242559607/5000000000 : ℝ), (4324576507/10000000000 : ℝ), (2162288311/5000000000 : ℝ)] ![(6883870694827/20000000000000 : ℝ), (3279032267423/10000000000000 : ℝ), (4098790479261/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2242559607/5000000000 : ℝ)|^8251 ≤ (6883870694827/20000000000000 : ℝ)^6203
        have hw : |(2242559607/5000000000 : ℝ)|=(2242559607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4324576507/10000000000 : ℝ)|^8251 ≤ (3279032267423/10000000000000 : ℝ)^6203
        have hw : |(4324576507/10000000000 : ℝ)|=(4324576507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2162288311/5000000000 : ℝ)|^8251 ≤ (4098790479261/12500000000000 : ℝ)^6203
        have hw : |(2162288311/5000000000 : ℝ)|=(2162288311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_box_4 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-467767331/2000000000 : ℝ)*x 0 + (211198873/400000000 : ℝ)*x 1 + (5279971801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (467767331/2000000000 : ℝ)^8251 ≤ (2895323593057/20000000000000 : ℝ)^6203 := by
    have hnat : (467767331 : ℕ)^8251*20000000000000^6203 ≤ 2895323593057^6203*2000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467767331 2000000000 2895323593057 20000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211198873/400000000 : ℝ)^8251 ≤ (668151424079/1562500000000 : ℝ)^6203 := by
    have hnat : (211198873 : ℕ)^8251*1562500000000^6203 ≤ 668151424079^6203*400000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211198873 400000000 668151424079 1562500000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5279971801/10000000000 : ℝ)^8251 ≤ (42761690882509/100000000000000 : ℝ)^6203 := by
    have hnat : (5279971801 : ℕ)^8251*100000000000000^6203 ≤ 42761690882509^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279971801 10000000000 42761690882509 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-467767331/2000000000 : ℝ), (211198873/400000000 : ℝ), (5279971801/10000000000 : ℝ)] ![(2895323593057/20000000000000 : ℝ), (668151424079/1562500000000 : ℝ), (42761690882509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-467767331/2000000000 : ℝ)|^8251 ≤ (2895323593057/20000000000000 : ℝ)^6203
        have hw : |(-467767331/2000000000 : ℝ)|=(467767331/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(211198873/400000000 : ℝ)|^8251 ≤ (668151424079/1562500000000 : ℝ)^6203
        have hw : |(211198873/400000000 : ℝ)|=(211198873/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5279971801/10000000000 : ℝ)|^8251 ≤ (42761690882509/100000000000000 : ℝ)^6203
        have hw : |(5279971801/10000000000 : ℝ)|=(5279971801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_box_5 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2682064567/5000000000 : ℝ)*x 0 + (-222754891/1000000000 : ℝ)*x 1 + (5279971827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2682064567/5000000000 : ℝ)^8251 ≤ (43670676966273/100000000000000 : ℝ)^6203 := by
    have hnat : (2682064567 : ℕ)^8251*100000000000000^6203 ≤ 43670676966273^6203*5000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2682064567 5000000000 43670676966273 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (222754891/1000000000 : ℝ)^8251 ≤ (13567631855779/100000000000000 : ℝ)^6203 := by
    have hnat : (222754891 : ℕ)^8251*100000000000000^6203 ≤ 13567631855779^6203*1000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222754891 1000000000 13567631855779 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5279971827/10000000000 : ℝ)^8251 ≤ (21380845581301/50000000000000 : ℝ)^6203 := by
    have hnat : (5279971827 : ℕ)^8251*50000000000000^6203 ≤ 21380845581301^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279971827 10000000000 21380845581301 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2682064567/5000000000 : ℝ), (-222754891/1000000000 : ℝ), (5279971827/10000000000 : ℝ)] ![(43670676966273/100000000000000 : ℝ), (13567631855779/100000000000000 : ℝ), (21380845581301/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2682064567/5000000000 : ℝ)|^8251 ≤ (43670676966273/100000000000000 : ℝ)^6203
        have hw : |(2682064567/5000000000 : ℝ)|=(2682064567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-222754891/1000000000 : ℝ)|^8251 ≤ (13567631855779/100000000000000 : ℝ)^6203
        have hw : |(-222754891/1000000000 : ℝ)|=(222754891/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5279971827/10000000000 : ℝ)|^8251 ≤ (21380845581301/50000000000000 : ℝ)^6203
        have hw : |(5279971827/10000000000 : ℝ)|=(5279971827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_box_6 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1341032281/2500000000 : ℝ)*x 0 + (5279971833/10000000000 : ℝ)*x 1 + (-445509783/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1341032281/2500000000 : ℝ)^8251 ≤ (43670676857981/100000000000000 : ℝ)^6203 := by
    have hnat : (1341032281 : ℕ)^8251*100000000000000^6203 ≤ 43670676857981^6203*2500000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1341032281 2500000000 43670676857981 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5279971833/10000000000 : ℝ)^8251 ≤ (42761691227239/100000000000000 : ℝ)^6203 := by
    have hnat : (5279971833 : ℕ)^8251*100000000000000^6203 ≤ 42761691227239^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279971833 10000000000 42761691227239 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (445509783/2000000000 : ℝ)^8251 ≤ (423988496759/3125000000000 : ℝ)^6203 := by
    have hnat : (445509783 : ℕ)^8251*3125000000000^6203 ≤ 423988496759^6203*2000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445509783 2000000000 423988496759 3125000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1341032281/2500000000 : ℝ), (5279971833/10000000000 : ℝ), (-445509783/2000000000 : ℝ)] ![(43670676857981/100000000000000 : ℝ), (42761691227239/100000000000000 : ℝ), (423988496759/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1341032281/2500000000 : ℝ)|^8251 ≤ (43670676857981/100000000000000 : ℝ)^6203
        have hw : |(1341032281/2500000000 : ℝ)|=(1341032281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5279971833/10000000000 : ℝ)|^8251 ≤ (42761691227239/100000000000000 : ℝ)^6203
        have hw : |(5279971833/10000000000 : ℝ)|=(5279971833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-445509783/2000000000 : ℝ)|^8251 ≤ (423988496759/3125000000000 : ℝ)^6203
        have hw : |(-445509783/2000000000 : ℝ)|=(445509783/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_box_7 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4267845713/10000000000 : ℝ)*x 0 + (4433191861/10000000000 : ℝ)*x 1 + (2216595857/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4267845713/10000000000 : ℝ)^8251 ≤ (16109697246787/50000000000000 : ℝ)^6203 := by
    have hnat : (4267845713 : ℕ)^8251*50000000000000^6203 ≤ 16109697246787^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4267845713 10000000000 16109697246787 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4433191861/10000000000 : ℝ)^8251 ≤ (33890303493399/100000000000000 : ℝ)^6203 := by
    have hnat : (4433191861 : ℕ)^8251*100000000000000^6203 ≤ 33890303493399^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4433191861 10000000000 33890303493399 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2216595857/5000000000 : ℝ)^8251 ≤ (16945150999303/50000000000000 : ℝ)^6203 := by
    have hnat : (2216595857 : ℕ)^8251*50000000000000^6203 ≤ 16945150999303^6203*5000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2216595857 5000000000 16945150999303 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4267845713/10000000000 : ℝ), (4433191861/10000000000 : ℝ), (2216595857/5000000000 : ℝ)] ![(16109697246787/50000000000000 : ℝ), (33890303493399/100000000000000 : ℝ), (16945150999303/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4267845713/10000000000 : ℝ)|^8251 ≤ (16109697246787/50000000000000 : ℝ)^6203
        have hw : |(4267845713/10000000000 : ℝ)|=(4267845713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4433191861/10000000000 : ℝ)|^8251 ≤ (33890303493399/100000000000000 : ℝ)^6203
        have hw : |(4433191861/10000000000 : ℝ)|=(4433191861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2216595857/5000000000 : ℝ)|^8251 ≤ (16945150999303/50000000000000 : ℝ)^6203
        have hw : |(2216595857/5000000000 : ℝ)|=(2216595857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_box_8 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1142195649/5000000000 : ℝ)*x 0 + (1042765429/2000000000 : ℝ)*x 1 + (2693536109/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1142195649/5000000000 : ℝ)^8251 ≤ (7015043326559/50000000000000 : ℝ)^6203 := by
    have hnat : (1142195649 : ℕ)^8251*50000000000000^6203 ≤ 7015043326559^6203*5000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1142195649 5000000000 7015043326559 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042765429/2000000000 : ℝ)^8251 ≤ (21025303175989/50000000000000 : ℝ)^6203 := by
    have hnat : (1042765429 : ℕ)^8251*50000000000000^6203 ≤ 21025303175989^6203*2000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042765429 2000000000 21025303175989 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693536109/5000000000 : ℝ)^8251 ≤ (43919306974943/100000000000000 : ℝ)^6203 := by
    have hnat : (2693536109 : ℕ)^8251*100000000000000^6203 ≤ 43919306974943^6203*5000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693536109 5000000000 43919306974943 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1142195649/5000000000 : ℝ), (1042765429/2000000000 : ℝ), (2693536109/5000000000 : ℝ)] ![(7015043326559/50000000000000 : ℝ), (21025303175989/50000000000000 : ℝ), (43919306974943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1142195649/5000000000 : ℝ)|^8251 ≤ (7015043326559/50000000000000 : ℝ)^6203
        have hw : |(-1142195649/5000000000 : ℝ)|=(1142195649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1042765429/2000000000 : ℝ)|^8251 ≤ (21025303175989/50000000000000 : ℝ)^6203
        have hw : |(1042765429/2000000000 : ℝ)|=(1042765429/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693536109/5000000000 : ℝ)|^8251 ≤ (43919306974943/100000000000000 : ℝ)^6203
        have hw : |(2693536109/5000000000 : ℝ)|=(2693536109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_box_9 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1322078659/2500000000 : ℝ)*x 0 + (-34150529/156250000 : ℝ)*x 1 + (2693536081/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322078659/2500000000 : ℝ)^8251 ≤ (2142579495103/5000000000000 : ℝ)^6203 := by
    have hnat : (1322078659 : ℕ)^8251*5000000000000^6203 ≤ 2142579495103^6203*2500000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322078659 2500000000 2142579495103 5000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34150529/156250000 : ℝ)^8251 ≤ (6614551861141/50000000000000 : ℝ)^6203 := by
    have hnat : (34150529 : ℕ)^8251*50000000000000^6203 ≤ 6614551861141^6203*156250000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34150529 156250000 6614551861141 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693536081/5000000000 : ℝ)^8251 ≤ (21959653183827/50000000000000 : ℝ)^6203 := by
    have hnat : (2693536081 : ℕ)^8251*50000000000000^6203 ≤ 21959653183827^6203*5000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693536081 5000000000 21959653183827 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322078659/2500000000 : ℝ), (-34150529/156250000 : ℝ), (2693536081/5000000000 : ℝ)] ![(2142579495103/5000000000000 : ℝ), (6614551861141/50000000000000 : ℝ), (21959653183827/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322078659/2500000000 : ℝ)|^8251 ≤ (2142579495103/5000000000000 : ℝ)^6203
        have hw : |(1322078659/2500000000 : ℝ)|=(1322078659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-34150529/156250000 : ℝ)|^8251 ≤ (6614551861141/50000000000000 : ℝ)^6203
        have hw : |(-34150529/156250000 : ℝ)|=(34150529/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693536081/5000000000 : ℝ)|^8251 ≤ (21959653183827/50000000000000 : ℝ)^6203
        have hw : |(2693536081/5000000000 : ℝ)|=(2693536081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_box_10 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2644157353/5000000000 : ℝ)*x 0 + (2693536089/5000000000 : ℝ)*x 1 + (-109281687/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644157353/5000000000 : ℝ)^8251 ≤ (10712897664137/25000000000000 : ℝ)^6203 := by
    have hnat : (2644157353 : ℕ)^8251*25000000000000^6203 ≤ 10712897664137^6203*5000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644157353 5000000000 10712897664137 25000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2693536089/5000000000 : ℝ)^8251 ≤ (8783861308233/20000000000000 : ℝ)^6203 := by
    have hnat : (2693536089 : ℕ)^8251*20000000000000^6203 ≤ 8783861308233^6203*5000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693536089 5000000000 8783861308233 20000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (109281687/500000000 : ℝ)^8251 ≤ (3307275697087/25000000000000 : ℝ)^6203 := by
    have hnat : (109281687 : ℕ)^8251*25000000000000^6203 ≤ 3307275697087^6203*500000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109281687 500000000 3307275697087 25000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644157353/5000000000 : ℝ), (2693536089/5000000000 : ℝ), (-109281687/500000000 : ℝ)] ![(10712897664137/25000000000000 : ℝ), (8783861308233/20000000000000 : ℝ), (3307275697087/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644157353/5000000000 : ℝ)|^8251 ≤ (10712897664137/25000000000000 : ℝ)^6203
        have hw : |(2644157353/5000000000 : ℝ)|=(2644157353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2693536089/5000000000 : ℝ)|^8251 ≤ (8783861308233/20000000000000 : ℝ)^6203
        have hw : |(2693536089/5000000000 : ℝ)|=(2693536089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-109281687/500000000 : ℝ)|^8251 ≤ (3307275697087/25000000000000 : ℝ)^6203
        have hw : |(-109281687/500000000 : ℝ)|=(109281687/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_box_11 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (281639819/625000000 : ℝ)*x 0 + (4313877047/10000000000 : ℝ)*x 1 + (269617323/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (281639819/625000000 : ℝ)^8251 ≤ (1731754436593/5000000000000 : ℝ)^6203 := by
    have hnat : (281639819 : ℕ)^8251*5000000000000^6203 ≤ 1731754436593^6203*625000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281639819 625000000 1731754436593 5000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4313877047/10000000000 : ℝ)^8251 ≤ (16341227507023/50000000000000 : ℝ)^6203 := by
    have hnat : (4313877047 : ℕ)^8251*50000000000000^6203 ≤ 16341227507023^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4313877047 10000000000 16341227507023 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269617323/625000000 : ℝ)^8251 ≤ (32682456233421/100000000000000 : ℝ)^6203 := by
    have hnat : (269617323 : ℕ)^8251*100000000000000^6203 ≤ 32682456233421^6203*625000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269617323 625000000 32682456233421 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(281639819/625000000 : ℝ), (4313877047/10000000000 : ℝ), (269617323/625000000 : ℝ)] ![(1731754436593/5000000000000 : ℝ), (16341227507023/50000000000000 : ℝ), (32682456233421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(281639819/625000000 : ℝ)|^8251 ≤ (1731754436593/5000000000000 : ℝ)^6203
        have hw : |(281639819/625000000 : ℝ)|=(281639819/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4313877047/10000000000 : ℝ)|^8251 ≤ (16341227507023/50000000000000 : ℝ)^6203
        have hw : |(4313877047/10000000000 : ℝ)|=(4313877047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269617323/625000000 : ℝ)|^8251 ≤ (32682456233421/100000000000000 : ℝ)^6203
        have hw : |(269617323/625000000 : ℝ)|=(269617323/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_box_12 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-133300181/625000000 : ℝ)*x 0 + (1360568967/2500000000 : ℝ)*x 1 + (1054395083/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133300181/625000000 : ℝ)^8251 ≤ (12805460378759/100000000000000 : ℝ)^6203 := by
    have hnat : (133300181 : ℕ)^8251*100000000000000^6203 ≤ 12805460378759^6203*625000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133300181 625000000 12805460378759 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1360568967/2500000000 : ℝ)^8251 ≤ (5564871318407/12500000000000 : ℝ)^6203 := by
    have hnat : (1360568967 : ℕ)^8251*12500000000000^6203 ≤ 5564871318407^6203*2500000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360568967 2500000000 5564871318407 12500000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054395083/2000000000 : ℝ)^8251 ≤ (21337784531791/50000000000000 : ℝ)^6203 := by
    have hnat : (1054395083 : ℕ)^8251*50000000000000^6203 ≤ 21337784531791^6203*2000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054395083 2000000000 21337784531791 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-133300181/625000000 : ℝ), (1360568967/2500000000 : ℝ), (1054395083/2000000000 : ℝ)] ![(12805460378759/100000000000000 : ℝ), (5564871318407/12500000000000 : ℝ), (21337784531791/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-133300181/625000000 : ℝ)|^8251 ≤ (12805460378759/100000000000000 : ℝ)^6203
        have hw : |(-133300181/625000000 : ℝ)|=(133300181/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1360568967/2500000000 : ℝ)|^8251 ≤ (5564871318407/12500000000000 : ℝ)^6203
        have hw : |(1360568967/2500000000 : ℝ)|=(1360568967/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1054395083/2000000000 : ℝ)|^8251 ≤ (21337784531791/50000000000000 : ℝ)^6203
        have hw : |(1054395083/2000000000 : ℝ)|=(1054395083/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_box_13 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (671223411/1250000000 : ℝ)*x 0 + (-22306139/100000000 : ℝ)*x 1 + (5271975479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671223411/1250000000 : ℝ)^8251 ≤ (10932990197997/25000000000000 : ℝ)^6203 := by
    have hnat : (671223411 : ℕ)^8251*25000000000000^6203 ≤ 10932990197997^6203*1250000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671223411 1250000000 10932990197997 25000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (22306139/100000000 : ℝ)^8251 ≤ (33981173589/250000000000 : ℝ)^6203 := by
    have hnat : (22306139 : ℕ)^8251*250000000000^6203 ≤ 33981173589^6203*100000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22306139 100000000 33981173589 250000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5271975479/10000000000 : ℝ)^8251 ≤ (8535113950539/20000000000000 : ℝ)^6203 := by
    have hnat : (5271975479 : ℕ)^8251*20000000000000^6203 ≤ 8535113950539^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271975479 10000000000 8535113950539 20000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671223411/1250000000 : ℝ), (-22306139/100000000 : ℝ), (5271975479/10000000000 : ℝ)] ![(10932990197997/25000000000000 : ℝ), (33981173589/250000000000 : ℝ), (8535113950539/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671223411/1250000000 : ℝ)|^8251 ≤ (10932990197997/25000000000000 : ℝ)^6203
        have hw : |(671223411/1250000000 : ℝ)|=(671223411/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-22306139/100000000 : ℝ)|^8251 ≤ (33981173589/250000000000 : ℝ)^6203
        have hw : |(-22306139/100000000 : ℝ)|=(22306139/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5271975479/10000000000 : ℝ)|^8251 ≤ (8535113950539/20000000000000 : ℝ)^6203
        have hw : |(5271975479/10000000000 : ℝ)|=(5271975479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_box_14 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5369787003/10000000000 : ℝ)*x 0 + (5271975577/10000000000 : ℝ)*x 1 + (-2230614151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369787003/10000000000 : ℝ)^8251 ≤ (21865978852299/50000000000000 : ℝ)^6203 := by
    have hnat : (5369787003 : ℕ)^8251*50000000000000^6203 ≤ 21865978852299^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369787003 10000000000 21865978852299 50000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5271975577/10000000000 : ℝ)^8251 ≤ (426755708079/1000000000000 : ℝ)^6203 := by
    have hnat : (5271975577 : ℕ)^8251*1000000000000^6203 ≤ 426755708079^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271975577 10000000000 426755708079 1000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2230614151/10000000000 : ℝ)^8251 ≤ (3398117867519/25000000000000 : ℝ)^6203 := by
    have hnat : (2230614151 : ℕ)^8251*25000000000000^6203 ≤ 3398117867519^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2230614151 10000000000 3398117867519 25000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369787003/10000000000 : ℝ), (5271975577/10000000000 : ℝ), (-2230614151/10000000000 : ℝ)] ![(21865978852299/50000000000000 : ℝ), (426755708079/1000000000000 : ℝ), (3398117867519/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369787003/10000000000 : ℝ)|^8251 ≤ (21865978852299/50000000000000 : ℝ)^6203
        have hw : |(5369787003/10000000000 : ℝ)|=(5369787003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5271975577/10000000000 : ℝ)|^8251 ≤ (426755708079/1000000000000 : ℝ)^6203
        have hw : |(5271975577/10000000000 : ℝ)|=(5271975577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2230614151/10000000000 : ℝ)|^8251 ≤ (3398117867519/25000000000000 : ℝ)^6203
        have hw : |(-2230614151/10000000000 : ℝ)|=(2230614151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1058_box_15 (p : ℝ) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2124898073/5000000000 : ℝ)*x 0 + (4442094271/10000000000 : ℝ)*x 1 + (2221047707/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2124898073/5000000000 : ℝ)^8251 ≤ (8009567555021/25000000000000 : ℝ)^6203 := by
    have hnat : (2124898073 : ℕ)^8251*25000000000000^6203 ≤ 8009567555021^6203*5000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124898073 5000000000 8009567555021 25000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4442094271/10000000000 : ℝ)^8251 ≤ (33980859072193/100000000000000 : ℝ)^6203 := by
    have hnat : (4442094271 : ℕ)^8251*100000000000000^6203 ≤ 33980859072193^6203*10000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4442094271 10000000000 33980859072193 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2221047707/5000000000 : ℝ)^8251 ≤ (33980870702673/100000000000000 : ℝ)^6203 := by
    have hnat : (2221047707 : ℕ)^8251*100000000000000^6203 ≤ 33980870702673^6203*5000000000^8251 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2221047707 5000000000 33980870702673 100000000000000 8251 6203 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8251/2048 : ℝ)) 8251 6203 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2124898073/5000000000 : ℝ), (4442094271/10000000000 : ℝ), (2221047707/5000000000 : ℝ)] ![(8009567555021/25000000000000 : ℝ), (33980859072193/100000000000000 : ℝ), (33980870702673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2124898073/5000000000 : ℝ)|^8251 ≤ (8009567555021/25000000000000 : ℝ)^6203
        have hw : |(2124898073/5000000000 : ℝ)|=(2124898073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4442094271/10000000000 : ℝ)|^8251 ≤ (33980859072193/100000000000000 : ℝ)^6203
        have hw : |(4442094271/10000000000 : ℝ)|=(4442094271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2221047707/5000000000 : ℝ)|^8251 ≤ (33980870702673/100000000000000 : ℝ)^6203
        have hw : |(2221047707/5000000000 : ℝ)|=(2221047707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1058_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29567487/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13997/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11241/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(3889/6250 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11847/20000 : ℝ) ∧ (79547/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (41467/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13997/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11241/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13997/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11241/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13997/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11241/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13997/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11241/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13997/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11241/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13997/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11241/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11241/100000 : ℝ) ^ (4125/1024 : ℝ) ≤ (7504267299798383/50000000000000000000 : ℝ) := by
    have hpowers : (11241/100000 : ℝ)^4125 ≤ (7504267299798383/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11241 : ℕ)^4125*50000000000000000000^1024 ≤ 7504267299798383^1024*100000^4125 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11241 100000 7504267299798383 50000000000000000000 4125 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11241/100000 : ℝ)) (X := (7504267299798383/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4125 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (13997/100000 : ℝ) ^ (4125/1024 : ℝ) ≤ (36304068140601497/100000000000000000000 : ℝ) := by
    have hpowers : (13997/100000 : ℝ)^4125 ≤ (36304068140601497/100000000000000000000 : ℝ)^1024 := by
      have hnat : (13997 : ℕ)^4125*100000000000000000000^1024 ≤ 36304068140601497^1024*100000^4125 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13997 100000 36304068140601497 100000000000000000000 4125 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13997/100000 : ℝ)) (X := (36304068140601497/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4125 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007504267299798383/25000000000000000000 : ℝ) ≤ (5000372533471827/5000000000000000 : ℝ) ^ (4125/1024 : ℝ) := by
    have hpowers : (25007504267299798383/25000000000000000000 : ℝ)^1024 ≤ (5000372533471827/5000000000000000 : ℝ)^4125 := by
      have hnat : (25007504267299798383 : ℕ)^1024*5000000000000000^4125 ≤ 5000372533471827^4125*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007504267299798383 25000000000000000000 5000372533471827 5000000000000000 1024 4125 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000372533471827/5000000000000000 : ℝ)) (X := (25007504267299798383/25000000000000000000 : ℝ)) (by norm_num) 4125 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051312602740198263/100000000000000000000 : ℝ) ≤ (10001273550882237/10000000000000000 : ℝ) ^ (4125/1024 : ℝ) := by
    have hpowers : (100051312602740198263/100000000000000000000 : ℝ)^1024 ≤ (10001273550882237/10000000000000000 : ℝ)^4125 := by
      have hnat : (100051312602740198263 : ℕ)^1024*10000000000000000^4125 ≤ 10001273550882237^4125*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051312602740198263 100000000000000000000 10001273550882237 10000000000000000 1024 4125 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001273550882237/10000000000000000 : ℝ)) (X := (100051312602740198263/100000000000000000000 : ℝ)) (by norm_num) 4125 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036304068140601497/50000000000000000000 : ℝ) ≤ (500090101741041/500000000000000 : ℝ) ^ (4125/1024 : ℝ) := by
    have hpowers : (50036304068140601497/50000000000000000000 : ℝ)^1024 ≤ (500090101741041/500000000000000 : ℝ)^4125 := by
      have hnat : (50036304068140601497 : ℕ)^1024*500000000000000^4125 ≤ 500090101741041^4125*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036304068140601497 50000000000000000000 500090101741041 500000000000000 1024 4125 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500090101741041/500000000000000 : ℝ)) (X := (50036304068140601497/50000000000000000000 : ℝ)) (by norm_num) 4125 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7504267299798383/50000000000000000000 : ℝ) ≤ ((13775086014294743709/13780000000000000000 : ℝ)+2*(528483938583/275600000000000 : ℝ)*(11241/100000 : ℝ))^(4125/1024 : ℝ) := by
    rw [show (13775086014294743709/13780000000000000000 : ℝ)+2*(528483938583/275600000000000 : ℝ)*(11241/100000 : ℝ)=(5000372533471827/5000000000000000 : ℝ) by norm_num, show 1+2*(7504267299798383/50000000000000000000 : ℝ)=(25007504267299798383/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36304068140601497/100000000000000000000 : ℝ)+(7504267299798383/50000000000000000000 : ℝ) ≤ ((13775086014294743709/13780000000000000000 : ℝ)+(528483938583/275600000000000 : ℝ)*((13997/100000 : ℝ)+(11241/100000 : ℝ)))^(4125/1024 : ℝ) := by
    rw [show (13775086014294743709/13780000000000000000 : ℝ)+(528483938583/275600000000000 : ℝ)*((13997/100000 : ℝ)+(11241/100000 : ℝ))=(10001273550882237/10000000000000000 : ℝ) by norm_num, show 1+(36304068140601497/100000000000000000000 : ℝ)+(7504267299798383/50000000000000000000 : ℝ)=(100051312602740198263/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36304068140601497/100000000000000000000 : ℝ) ≤ ((13775086014294743709/13780000000000000000 : ℝ)+2*(528483938583/275600000000000 : ℝ)*(13997/100000 : ℝ))^(4125/1024 : ℝ) := by
    rw [show (13775086014294743709/13780000000000000000 : ℝ)+2*(528483938583/275600000000000 : ℝ)*(13997/100000 : ℝ)=(500090101741041/500000000000000 : ℝ) by norm_num, show 1+2*(36304068140601497/100000000000000000000 : ℝ)=(50036304068140601497/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13775086014294743709/13780000000000000000 : ℝ)*(X 1 0+X 2 0)+(528483938583/275600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4125/1024 : ℝ)) (lo := (11241/100000 : ℝ)) (hi := (13997/100000 : ℝ)) (c := (13775086014294743709/13780000000000000000 : ℝ)) (alpha := (528483938583/275600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13775086014294743709/13780000000000000000 : ℝ)*(X 0 1+X 2 1)+(528483938583/275600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4125/1024 : ℝ)) (lo := (11241/100000 : ℝ)) (hi := (13997/100000 : ℝ)) (c := (13775086014294743709/13780000000000000000 : ℝ)) (alpha := (528483938583/275600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13775086014294743709/13780000000000000000 : ℝ)*(X 0 2+X 1 2)+(528483938583/275600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4125/1024 : ℝ)) (lo := (11241/100000 : ℝ)) (hi := (13997/100000 : ℝ)) (c := (13775086014294743709/13780000000000000000 : ℝ)) (alpha := (528483938583/275600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2077983197/10000000000 : ℝ)*X 0 0+(5377472731/10000000000 : ℝ)*X 0 1+(2688736757/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5295113209/10000000000 : ℝ)*X 1 0+(-2189455093/10000000000 : ℝ)*X 1 1+(5377472949/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5295113387/10000000000 : ℝ)*X 2 0+(1344368289/2500000000 : ℝ)*X 2 1+(-136840911/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2242559607/5000000000 : ℝ)*X 0 0+(4324576507/10000000000 : ℝ)*X 0 1+(2162288311/5000000000 : ℝ)*X 0 2+(2242559607/5000000000 : ℝ)*X 1 0+(4324576507/10000000000 : ℝ)*X 1 1+(2162288311/5000000000 : ℝ)*X 1 2+(2242559607/5000000000 : ℝ)*X 2 0+(4324576507/10000000000 : ℝ)*X 2 1+(2162288311/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-467767331/2000000000 : ℝ)*X 0 0+(211198873/400000000 : ℝ)*X 0 1+(5279971801/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2682064567/5000000000 : ℝ)*X 1 0+(-222754891/1000000000 : ℝ)*X 1 1+(5279971827/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1341032281/2500000000 : ℝ)*X 2 0+(5279971833/10000000000 : ℝ)*X 2 1+(-445509783/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4267845713/10000000000 : ℝ)*X 0 0+(4433191861/10000000000 : ℝ)*X 0 1+(2216595857/5000000000 : ℝ)*X 0 2+(4267845713/10000000000 : ℝ)*X 1 0+(4433191861/10000000000 : ℝ)*X 1 1+(2216595857/5000000000 : ℝ)*X 1 2+(4267845713/10000000000 : ℝ)*X 2 0+(4433191861/10000000000 : ℝ)*X 2 1+(2216595857/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1142195649/5000000000 : ℝ)*X 0 0+(1042765429/2000000000 : ℝ)*X 0 1+(2693536109/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1322078659/2500000000 : ℝ)*X 1 0+(-34150529/156250000 : ℝ)*X 1 1+(2693536081/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2644157353/5000000000 : ℝ)*X 2 0+(2693536089/5000000000 : ℝ)*X 2 1+(-109281687/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((281639819/625000000 : ℝ)*X 0 0+(4313877047/10000000000 : ℝ)*X 0 1+(269617323/625000000 : ℝ)*X 0 2+(281639819/625000000 : ℝ)*X 1 0+(4313877047/10000000000 : ℝ)*X 1 1+(269617323/625000000 : ℝ)*X 1 2+(281639819/625000000 : ℝ)*X 2 0+(4313877047/10000000000 : ℝ)*X 2 1+(269617323/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-133300181/625000000 : ℝ)*X 0 0+(1360568967/2500000000 : ℝ)*X 0 1+(1054395083/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((671223411/1250000000 : ℝ)*X 1 0+(-22306139/100000000 : ℝ)*X 1 1+(5271975479/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5369787003/10000000000 : ℝ)*X 2 0+(5271975577/10000000000 : ℝ)*X 2 1+(-2230614151/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2124898073/5000000000 : ℝ)*X 0 0+(4442094271/10000000000 : ℝ)*X 0 1+(2221047707/5000000000 : ℝ)*X 0 2+(2124898073/5000000000 : ℝ)*X 1 0+(4442094271/10000000000 : ℝ)*X 1 1+(2221047707/5000000000 : ℝ)*X 1 2+(2124898073/5000000000 : ℝ)*X 2 0+(4442094271/10000000000 : ℝ)*X 2 1+(2221047707/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1058_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-3889/6250 : ℝ) ≤ (-53588336731692702573679565179407/86125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (87512601/100000000000000 : ℝ)*(upper0) + (30022043/25000000000000 : ℝ)*(upper1) + (54955831/50000000000000 : ℝ)*(upper3) + (98875471/100000000000000 : ℝ)*(upper5) + (962499045423359/25000000000000 : ℝ)*(major0) + (962499045423359/25000000000000 : ℝ)*(major1) + (962499045423359/25000000000000 : ℝ)*(major2) + (6277708999/50000000000000 : ℝ)*(sp3) + (5116521431592437/100000000000000 : ℝ)*(sp4) + (1023304724775623/20000000000000 : ℝ)*(sp5) + (1023302916139037/20000000000000 : ℝ)*(sp6) + (651049177781919/25000000000000 : ℝ)*(sp7) + (1096142839/50000000000000 : ℝ)*(sp8) + (904318293/10000000000000 : ℝ)*(sp14) + (1302104633272837/50000000000000 : ℝ)*(f.failure) + (1023304724775623/20000000000000 : ℝ)*(f.sum) + (2590938054437/861250000000000000000000000 : ℝ)*base66 + (19549954663914751469/344500000000000000000000000000000 : ℝ)*base68 + (9850125644592751469/344500000000000000000000000000000 : ℝ)*base70 + (2059081315843251469/344500000000000000000000000000000 : ℝ)*base72 + (24956273006243/3445000000000000000000000000 : ℝ)*base74 + (11201910319040751469/344500000000000000000000000000000 : ℝ)*base76 + (1560942694083251469/344500000000000000000000000000000 : ℝ)*base78 + (8744585521425248531/344500000000000000000000000000000 : ℝ)*base79 + (80252119896439/1722500000000000000000000000 : ℝ)*base82 + (15450619/1000000000000000000000 : ℝ)*base89 + (15450619/1000000000000000000000 : ℝ)*base91 + (15450619/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (11847/20000 : ℝ) ≤ (204072766172212634130010668325287/344500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10692419/50000000000000 : ℝ)*(lower0) + (68923367/25000000000000 : ℝ)*(lower3) + (42367843/25000000000000 : ℝ)*(upper4) + (1956383749784027/50000000000000 : ℝ)*(major0) + (1956383749784027/50000000000000 : ℝ)*(major1) + (1956383749784027/50000000000000 : ℝ)*(major2) + (2579557071446809/50000000000000 : ℝ)*(sp0) + (5159115262229871/100000000000000 : ℝ)*(sp1) + (5159104012748503/100000000000000 : ℝ)*(sp2) + (1323331289561891/50000000000000 : ℝ)*(sp3) + (498693547/10000000000000 : ℝ)*(sp5) + (16236416839/100000000000000 : ℝ)*(sp6) + (3189140359/50000000000000 : ℝ)*(sp7) + (1526567931/25000000000000 : ℝ)*(sp12) + (2646668957404499/100000000000000 : ℝ)*(f.failure) + (2579560124582671/50000000000000 : ℝ)*(f.sum) + (50207192828739/6890000000000000000000000000 : ℝ)*base66 + (5358688991164013857/689000000000000000000000000000000 : ℝ)*base68 + (9060121910998013857/689000000000000000000000000000000 : ℝ)*base70 + (266941398635013857/689000000000000000000000000000000 : ℝ)*base72 + (282880736822669/6890000000000000000000000000 : ℝ)*base74 + (1506590215171013857/689000000000000000000000000000000 : ℝ)*base76 + (27155396777013857/689000000000000000000000000000000 : ℝ)*base78 + (33072814270849013857/689000000000000000000000000000000 : ℝ)*base80 + (45835872366529/6890000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (2075987/2000000000000000000000 : ℝ)*base90 + (2075987/2000000000000000000000 : ℝ)*base92 + (2075987/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (79547/100000 : ℝ) ≤ (548096653298451548710104296706573/689000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3657711/10000000000000 : ℝ)*(upper0) + (56533193/100000000000000 : ℝ)*(lower3) + (11535119/20000000000000 : ℝ)*(upper4) + (4381059921774967/100000000000000 : ℝ)*(major0) + (4381059921774967/100000000000000 : ℝ)*(major1) + (4381059921774967/100000000000000 : ℝ)*(major2) + (16360868329/50000000000000 : ℝ)*(sp1) + (58123771627/100000000000000 : ℝ)*(sp2) + (31209379279/100000000000000 : ℝ)*(sp3) + (168096133/25000000000000 : ℝ)*(sp4) + (721521493885793/12500000000000 : ℝ)*(sp8) + (5772139901734217/100000000000000 : ℝ)*(sp9) + (5772114499699249/100000000000000 : ℝ)*(sp10) + (296339948175451/10000000000000 : ℝ)*(sp11) + (296343069113379/10000000000000 : ℝ)*(f.failure) + (46177380987767/800000000000 : ℝ)*(f.sum) + (61917851186041/13780000000000000000000000000 : ℝ)*base65 + (1904187282490982603/1378000000000000000000000000000000 : ℝ)*base67 + (10507775564948982603/1378000000000000000000000000000000 : ℝ)*base69 + (13269556360384982603/1378000000000000000000000000000000 : ℝ)*base71 + (490735883878701/13780000000000000000000000000 : ℝ)*base73 + (8371794990532982603/1378000000000000000000000000000000 : ℝ)*base75 + (5850527127782982603/1378000000000000000000000000000000 : ℝ)*base77 + (20906090234678982603/1378000000000000000000000000000000 : ℝ)*base79 + (74008202265081/13780000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (1108573/200000000000000000000 : ℝ)*base89 + (1108573/200000000000000000000 : ℝ)*base91 + (1108573/200000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-41467/50000 : ℝ) ≤ (-285699417962466610106849586411717/344500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (72058899/50000000000000 : ℝ)*(lower1) + (138702303/50000000000000 : ℝ)*(lower4) + (10947909/10000000000000 : ℝ)*(upper5) + (2207782040307171/50000000000000 : ℝ)*(major0) + (2207782040307171/50000000000000 : ℝ)*(major1) + (2207782040307171/50000000000000 : ℝ)*(major2) + (2510644449/20000000000000 : ℝ)*(sp0) + (149425145663/50000000000000 : ℝ)*(sp5) + (246688418553/50000000000000 : ℝ)*(sp6) + (294524822981/100000000000000 : ℝ)*(sp7) + (73399869149913/1250000000000 : ℝ)*(sp12) + (5871703234923959/100000000000000 : ℝ)*(sp13) + (5871508708378179/100000000000000 : ℝ)*(sp14) + (1493237711635963/50000000000000 : ℝ)*(sp15) + (2986769948094907/100000000000000 : ℝ)*(f.failure) + (1174400417043057/20000000000000 : ℝ)*(f.sum) + (14788450009467/6890000000000000000000000000 : ℝ)*base66 + (8476771947036487239/689000000000000000000000000000000 : ℝ)*base67 + (4721305842022487239/689000000000000000000000000000000 : ℝ)*base69 + (11069812948710512761/689000000000000000000000000000000 : ℝ)*base72 + (40996832660663/6890000000000000000000000000 : ℝ)*base73 + (4979099716685487239/689000000000000000000000000000000 : ℝ)*base75 + (5029045276355512761/689000000000000000000000000000000 : ℝ)*base78 + (4982915118262487239/689000000000000000000000000000000 : ℝ)*base79 + (51235600361383/6890000000000000000000000000 : ℝ)*base81 + (2511291/2000000000000000000000 : ℝ)*base90 + (2511291/2000000000000000000000 : ℝ)*base92 + (2511291/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1058_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29567487/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13997/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11241/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(11847/20000 : ℝ) else (79547/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41467/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1058_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1058_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29567487/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6999/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (281/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(11847/20000 : ℝ) else (79547/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41467/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1058_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1058_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4125/1024 : ℝ) ≤ p) (hpb : p ≤ (8251/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29567487/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6999/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (281/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(11847/20000 : ℝ) else (79547/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41467/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1058_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
