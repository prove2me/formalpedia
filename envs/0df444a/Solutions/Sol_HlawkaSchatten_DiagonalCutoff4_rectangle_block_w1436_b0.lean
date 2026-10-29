-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1436_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:55:52.360301+00:00
-- url     : https://prove2.me/submissions/c2ab526a-5468-408b-8640-fd5018383798

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
theorem support_rectangle_w1436_s0_0 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-438714359/2500000000 : ℝ)*x 0 + (2978648797/5000000000 : ℝ)*x 1 + (4832836361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (438714359/2500000000 : ℝ)^1099 ≤ (2586278081533/25000000000000 : ℝ)^843 := by
    have hnat : (438714359 : ℕ)^1099*25000000000000^843 ≤ 2586278081533^843*2500000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438714359 2500000000 2586278081533 25000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2978648797/5000000000 : ℝ)^1099 ≤ (50902236385097/100000000000000 : ℝ)^843 := by
    have hnat : (2978648797 : ℕ)^1099*100000000000000^843 ≤ 50902236385097^843*5000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2978648797 5000000000 50902236385097 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4832836361/10000000000 : ℝ)^1099 ≤ (38752651265757/100000000000000 : ℝ)^843 := by
    have hnat : (4832836361 : ℕ)^1099*100000000000000^843 ≤ 38752651265757^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4832836361 10000000000 38752651265757 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-438714359/2500000000 : ℝ), (2978648797/5000000000 : ℝ), (4832836361/10000000000 : ℝ)] ![(2586278081533/25000000000000 : ℝ), (50902236385097/100000000000000 : ℝ), (38752651265757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-438714359/2500000000 : ℝ)|^1099 ≤ (2586278081533/25000000000000 : ℝ)^843
        have hw : |(-438714359/2500000000 : ℝ)|=(438714359/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2978648797/5000000000 : ℝ)|^1099 ≤ (50902236385097/100000000000000 : ℝ)^843
        have hw : |(2978648797/5000000000 : ℝ)|=(2978648797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4832836361/10000000000 : ℝ)|^1099 ≤ (38752651265757/100000000000000 : ℝ)^843
        have hw : |(4832836361/10000000000 : ℝ)|=(4832836361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s0_1 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2745660533/5000000000 : ℝ)*x 0 + (-2389754421/10000000000 : ℝ)*x 1 + (2416418259/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2745660533/5000000000 : ℝ)^1099 ≤ (45774392607329/100000000000000 : ℝ)^843 := by
    have hnat : (2745660533 : ℕ)^1099*100000000000000^843 ≤ 45774392607329^843*5000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2745660533 5000000000 45774392607329 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2389754421/10000000000 : ℝ)^1099 ≤ (241764913649/1562500000000 : ℝ)^843 := by
    have hnat : (2389754421 : ℕ)^1099*1562500000000^843 ≤ 241764913649^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2389754421 10000000000 241764913649 1562500000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2416418259/5000000000 : ℝ)^1099 ≤ (7750530581397/20000000000000 : ℝ)^843 := by
    have hnat : (2416418259 : ℕ)^1099*20000000000000^843 ≤ 7750530581397^843*5000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2416418259 5000000000 7750530581397 20000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2745660533/5000000000 : ℝ), (-2389754421/10000000000 : ℝ), (2416418259/5000000000 : ℝ)] ![(45774392607329/100000000000000 : ℝ), (241764913649/1562500000000 : ℝ), (7750530581397/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2745660533/5000000000 : ℝ)|^1099 ≤ (45774392607329/100000000000000 : ℝ)^843
        have hw : |(2745660533/5000000000 : ℝ)|=(2745660533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2389754421/10000000000 : ℝ)|^1099 ≤ (241764913649/1562500000000 : ℝ)^843
        have hw : |(-2389754421/10000000000 : ℝ)|=(2389754421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2416418259/5000000000 : ℝ)|^1099 ≤ (7750530581397/20000000000000 : ℝ)^843
        have hw : |(2416418259/5000000000 : ℝ)|=(2416418259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s0_2 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5491321177/10000000000 : ℝ)*x 0 + (4832836531/10000000000 : ℝ)*x 1 + (-1194877131/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5491321177/10000000000 : ℝ)^1099 ≤ (45774393813583/100000000000000 : ℝ)^843 := by
    have hnat : (5491321177 : ℕ)^1099*100000000000000^843 ≤ 45774393813583^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5491321177 10000000000 45774393813583 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4832836531/10000000000 : ℝ)^1099 ≤ (38752653042883/100000000000000 : ℝ)^843 := by
    have hnat : (4832836531 : ℕ)^1099*100000000000000^843 ≤ 38752653042883^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4832836531 10000000000 38752653042883 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1194877131/5000000000 : ℝ)^1099 ≤ (15472953131429/100000000000000 : ℝ)^843 := by
    have hnat : (1194877131 : ℕ)^1099*100000000000000^843 ≤ 15472953131429^843*5000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1194877131 5000000000 15472953131429 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5491321177/10000000000 : ℝ), (4832836531/10000000000 : ℝ), (-1194877131/5000000000 : ℝ)] ![(45774393813583/100000000000000 : ℝ), (38752653042883/100000000000000 : ℝ), (15472953131429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5491321177/10000000000 : ℝ)|^1099 ≤ (45774393813583/100000000000000 : ℝ)^843
        have hw : |(5491321177/10000000000 : ℝ)|=(5491321177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4832836531/10000000000 : ℝ)|^1099 ≤ (38752653042883/100000000000000 : ℝ)^843
        have hw : |(4832836531/10000000000 : ℝ)|=(4832836531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1194877131/5000000000 : ℝ)|^1099 ≤ (15472953131429/100000000000000 : ℝ)^843
        have hw : |(-1194877131/5000000000 : ℝ)|=(1194877131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s0_3 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4164998439/10000000000 : ℝ)*x 0 + (3103191251/10000000000 : ℝ)*x 1 + (1108403357/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4164998439/10000000000 : ℝ)^1099 ≤ (7980691036503/25000000000000 : ℝ)^843 := by
    have hnat : (4164998439 : ℕ)^1099*25000000000000^843 ≤ 7980691036503^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4164998439 10000000000 7980691036503 25000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3103191251/10000000000 : ℝ)^1099 ≤ (169930893503/781250000000 : ℝ)^843 := by
    have hnat : (3103191251 : ℕ)^1099*781250000000^843 ≤ 169930893503^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3103191251 10000000000 169930893503 781250000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1108403357/2000000000 : ℝ)^1099 ≤ (46326081468413/100000000000000 : ℝ)^843 := by
    have hnat : (1108403357 : ℕ)^1099*100000000000000^843 ≤ 46326081468413^843*2000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108403357 2000000000 46326081468413 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4164998439/10000000000 : ℝ), (3103191251/10000000000 : ℝ), (1108403357/2000000000 : ℝ)] ![(7980691036503/25000000000000 : ℝ), (169930893503/781250000000 : ℝ), (46326081468413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4164998439/10000000000 : ℝ)|^1099 ≤ (7980691036503/25000000000000 : ℝ)^843
        have hw : |(4164998439/10000000000 : ℝ)|=(4164998439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3103191251/10000000000 : ℝ)|^1099 ≤ (169930893503/781250000000 : ℝ)^843
        have hw : |(3103191251/10000000000 : ℝ)|=(3103191251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1108403357/2000000000 : ℝ)|^1099 ≤ (46326081468413/100000000000000 : ℝ)^843
        have hw : |(1108403357/2000000000 : ℝ)|=(1108403357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s0_4 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1758841087/10000000000 : ℝ)*x 0 + (4861591229/10000000000 : ℝ)*x 1 + (296375809/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1758841087/10000000000 : ℝ)^1099 ≤ (5187869307053/50000000000000 : ℝ)^843 := by
    have hnat : (1758841087 : ℕ)^1099*50000000000000^843 ≤ 5187869307053^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1758841087 10000000000 5187869307053 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4861591229/10000000000 : ℝ)^1099 ≤ (610211200229/1562500000000 : ℝ)^843 := by
    have hnat : (4861591229 : ℕ)^1099*1562500000000^843 ≤ 610211200229^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4861591229 10000000000 610211200229 1562500000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (296375809/500000000 : ℝ)^1099 ≤ (50570744551877/100000000000000 : ℝ)^843 := by
    have hnat : (296375809 : ℕ)^1099*100000000000000^843 ≤ 50570744551877^843*500000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      296375809 500000000 50570744551877 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1758841087/10000000000 : ℝ), (4861591229/10000000000 : ℝ), (296375809/500000000 : ℝ)] ![(5187869307053/50000000000000 : ℝ), (610211200229/1562500000000 : ℝ), (50570744551877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1758841087/10000000000 : ℝ)|^1099 ≤ (5187869307053/50000000000000 : ℝ)^843
        have hw : |(-1758841087/10000000000 : ℝ)|=(1758841087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4861591229/10000000000 : ℝ)|^1099 ≤ (610211200229/1562500000000 : ℝ)^843
        have hw : |(4861591229/10000000000 : ℝ)|=(4861591229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(296375809/500000000 : ℝ)|^1099 ≤ (50570744551877/100000000000000 : ℝ)^843
        have hw : |(296375809/500000000 : ℝ)|=(296375809/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s0_5 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1296094957/2500000000 : ℝ)*x 0 + (-1295074307/10000000000 : ℝ)*x 1 + (5927516251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1296094957/2500000000 : ℝ)^1099 ≤ (21233750132023/50000000000000 : ℝ)^843 := by
    have hnat : (1296094957 : ℕ)^1099*50000000000000^843 ≤ 21233750132023^843*2500000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296094957 2500000000 21233750132023 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1295074307/10000000000 : ℝ)^1099 ≤ (6961754383899/100000000000000 : ℝ)^843 := by
    have hnat : (1295074307 : ℕ)^1099*100000000000000^843 ≤ 6961754383899^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295074307 10000000000 6961754383899 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5927516251/10000000000 : ℝ)^1099 ≤ (12642686335391/25000000000000 : ℝ)^843 := by
    have hnat : (5927516251 : ℕ)^1099*25000000000000^843 ≤ 12642686335391^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5927516251 10000000000 12642686335391 25000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1296094957/2500000000 : ℝ), (-1295074307/10000000000 : ℝ), (5927516251/10000000000 : ℝ)] ![(21233750132023/50000000000000 : ℝ), (6961754383899/100000000000000 : ℝ), (12642686335391/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1296094957/2500000000 : ℝ)|^1099 ≤ (21233750132023/50000000000000 : ℝ)^843
        have hw : |(1296094957/2500000000 : ℝ)|=(1296094957/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1295074307/10000000000 : ℝ)|^1099 ≤ (6961754383899/100000000000000 : ℝ)^843
        have hw : |(-1295074307/10000000000 : ℝ)|=(1295074307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5927516251/10000000000 : ℝ)|^1099 ≤ (12642686335391/25000000000000 : ℝ)^843
        have hw : |(5927516251/10000000000 : ℝ)|=(5927516251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s0_6 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1296094963/2500000000 : ℝ)*x 0 + (2963758047/5000000000 : ℝ)*x 1 + (-647537259/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1296094963/2500000000 : ℝ)^1099 ≤ (21233750260171/50000000000000 : ℝ)^843 := by
    have hnat : (1296094963 : ℕ)^1099*50000000000000^843 ≤ 21233750260171^843*2500000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296094963 2500000000 21233750260171 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2963758047/5000000000 : ℝ)^1099 ≤ (25285371797677/50000000000000 : ℝ)^843 := by
    have hnat : (2963758047 : ℕ)^1099*50000000000000^843 ≤ 25285371797677^843*5000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2963758047 5000000000 25285371797677 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (647537259/5000000000 : ℝ)^1099 ≤ (6961755862587/100000000000000 : ℝ)^843 := by
    have hnat : (647537259 : ℕ)^1099*100000000000000^843 ≤ 6961755862587^843*5000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647537259 5000000000 6961755862587 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1296094963/2500000000 : ℝ), (2963758047/5000000000 : ℝ), (-647537259/5000000000 : ℝ)] ![(21233750260171/50000000000000 : ℝ), (25285371797677/50000000000000 : ℝ), (6961755862587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1296094963/2500000000 : ℝ)|^1099 ≤ (21233750260171/50000000000000 : ℝ)^843
        have hw : |(1296094963/2500000000 : ℝ)|=(1296094963/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2963758047/5000000000 : ℝ)|^1099 ≤ (25285371797677/50000000000000 : ℝ)^843
        have hw : |(2963758047/5000000000 : ℝ)|=(2963758047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-647537259/5000000000 : ℝ)|^1099 ≤ (6961755862587/100000000000000 : ℝ)^843
        have hw : |(-647537259/5000000000 : ℝ)|=(647537259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s0_7 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4173640093/10000000000 : ℝ)*x 0 + (5479651101/10000000000 : ℝ)*x 1 + (791945913/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4173640093/10000000000 : ℝ)^1099 ≤ (32009139406517/100000000000000 : ℝ)^843 := by
    have hnat : (4173640093 : ℕ)^1099*100000000000000^843 ≤ 32009139406517^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4173640093 10000000000 32009139406517 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5479651101/10000000000 : ℝ)^1099 ≤ (45647614228523/100000000000000 : ℝ)^843 := by
    have hnat : (5479651101 : ℕ)^1099*100000000000000^843 ≤ 45647614228523^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5479651101 10000000000 45647614228523 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (791945913/2500000000 : ℝ)^1099 ≤ (4468649270981/20000000000000 : ℝ)^843 := by
    have hnat : (791945913 : ℕ)^1099*20000000000000^843 ≤ 4468649270981^843*2500000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      791945913 2500000000 4468649270981 20000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4173640093/10000000000 : ℝ), (5479651101/10000000000 : ℝ), (791945913/2500000000 : ℝ)] ![(32009139406517/100000000000000 : ℝ), (45647614228523/100000000000000 : ℝ), (4468649270981/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4173640093/10000000000 : ℝ)|^1099 ≤ (32009139406517/100000000000000 : ℝ)^843
        have hw : |(4173640093/10000000000 : ℝ)|=(4173640093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5479651101/10000000000 : ℝ)|^1099 ≤ (45647614228523/100000000000000 : ℝ)^843
        have hw : |(5479651101/10000000000 : ℝ)|=(5479651101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(791945913/2500000000 : ℝ)|^1099 ≤ (4468649270981/20000000000000 : ℝ)^843
        have hw : |(791945913/2500000000 : ℝ)|=(791945913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1436_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158444201/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2097/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2621/10000 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4395/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4395 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4395*1^1024 ≤ 0^1024*1^4395 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4395 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4395/1024 : ℝ) ≤ (1959045810463866073/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4395 ≤ (1959045810463866073/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4395*100000000000000000000^1024 ≤ 1959045810463866073^1024*5^4395 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1959045810463866073 100000000000000000000 4395 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1959045810463866073/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4395/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4395 := by
      have hnat : (1 : ℕ)^1024*1^4395 ≤ 1^4395*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101959045810463866073/100000000000000000000 : ℝ) ≤ (1255663148201913/1250000000000000 : ℝ) ^ (4395/1024 : ℝ) := by
    have hpowers : (101959045810463866073/100000000000000000000 : ℝ)^1024 ≤ (1255663148201913/1250000000000000 : ℝ)^4395 := by
      have hnat : (101959045810463866073 : ℕ)^1024*1250000000000000^4395 ≤ 1255663148201913^4395*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101959045810463866073 100000000000000000000 1255663148201913 1250000000000000 1024 4395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1255663148201913/1250000000000000 : ℝ)) (X := (101959045810463866073/100000000000000000000 : ℝ)) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51959045810463866073/50000000000000000000 : ℝ) ≤ (630663148201913/625000000000000 : ℝ) ^ (4395/1024 : ℝ) := by
    have hpowers : (51959045810463866073/50000000000000000000 : ℝ)^1024 ≤ (630663148201913/625000000000000 : ℝ)^4395 := by
      have hnat : (51959045810463866073 : ℕ)^1024*625000000000000^4395 ≤ 630663148201913^4395*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51959045810463866073 50000000000000000000 630663148201913 625000000000000 1024 4395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (630663148201913/625000000000000 : ℝ)) (X := (51959045810463866073/50000000000000000000 : ℝ)) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(5663148201913/500000000000000 : ℝ)*(0 : ℝ))^(4395/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(5663148201913/500000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1959045810463866073/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(5663148201913/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4395/1024 : ℝ) := by
    rw [show (1 : ℝ)+(5663148201913/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1255663148201913/1250000000000000 : ℝ) by norm_num, show 1+(1959045810463866073/100000000000000000000 : ℝ)+(0 : ℝ)=(101959045810463866073/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1959045810463866073/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(5663148201913/500000000000000 : ℝ)*(2/5 : ℝ))^(4395/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(5663148201913/500000000000000 : ℝ)*(2/5 : ℝ)=(630663148201913/625000000000000 : ℝ) by norm_num, show 1+2*(1959045810463866073/100000000000000000000 : ℝ)=(51959045810463866073/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(5663148201913/500000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4395/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5663148201913/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(5663148201913/500000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4395/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5663148201913/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(5663148201913/500000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4395/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5663148201913/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-438714359/2500000000 : ℝ)*X 0 0+(2978648797/5000000000 : ℝ)*X 0 1+(4832836361/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2745660533/5000000000 : ℝ)*X 1 0+(-2389754421/10000000000 : ℝ)*X 1 1+(2416418259/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5491321177/10000000000 : ℝ)*X 2 0+(4832836531/10000000000 : ℝ)*X 2 1+(-1194877131/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4164998439/10000000000 : ℝ)*X 0 0+(3103191251/10000000000 : ℝ)*X 0 1+(1108403357/2000000000 : ℝ)*X 0 2+(4164998439/10000000000 : ℝ)*X 1 0+(3103191251/10000000000 : ℝ)*X 1 1+(1108403357/2000000000 : ℝ)*X 1 2+(4164998439/10000000000 : ℝ)*X 2 0+(3103191251/10000000000 : ℝ)*X 2 1+(1108403357/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1758841087/10000000000 : ℝ)*X 0 0+(4861591229/10000000000 : ℝ)*X 0 1+(296375809/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1296094957/2500000000 : ℝ)*X 1 0+(-1295074307/10000000000 : ℝ)*X 1 1+(5927516251/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1296094963/2500000000 : ℝ)*X 2 0+(2963758047/5000000000 : ℝ)*X 2 1+(-647537259/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4173640093/10000000000 : ℝ)*X 0 0+(5479651101/10000000000 : ℝ)*X 0 1+(791945913/2500000000 : ℝ)*X 0 2+(4173640093/10000000000 : ℝ)*X 1 0+(5479651101/10000000000 : ℝ)*X 1 1+(791945913/2500000000 : ℝ)*X 1 2+(4173640093/10000000000 : ℝ)*X 2 0+(5479651101/10000000000 : ℝ)*X 2 1+(791945913/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (28607692839264206336211/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (222132151/20000000000000 : ℝ)*(base19) + (1101981183/100000000000000 : ℝ)*(base23) + (69271151/50000000000000 : ℝ)*(upper3) + (146377/1000000000000 : ℝ)*(upper4) + (162862847/100000000000000 : ℝ)*(upper5) + (324839920756683/50000000000000 : ℝ)*(major0) + (324839920756683/50000000000000 : ℝ)*(major1) + (324839920756683/50000000000000 : ℝ)*(major2) + (444659215142337/50000000000000 : ℝ)*(sp0) + (889321424172333/100000000000000 : ℝ)*(sp1) + (177864286570381/20000000000000 : ℝ)*(sp2) + (410035191197147/100000000000000 : ℝ)*(sp3) + (2052274207/50000000000000 : ℝ)*(sp4) + (1804422129/100000000000000 : ℝ)*(sp7) + (102509248904819/25000000000000 : ℝ)*(f.failure) + (13895664606767/1562500000000 : ℝ)*(f.sum) + (31730292465421/12500000000000000000000000000 : ℝ)*base66 + (236604924065421/25000000000000000000000000000 : ℝ)*base68 + (182710105290421/25000000000000000000000000000 : ℝ)*base70 + (226870634565421/25000000000000000000000000000 : ℝ)*base72 + (48981431027921/12500000000000000000000000000 : ℝ)*base74 + (112237271790421/25000000000000000000000000000 : ℝ)*base76 + (117221264740421/25000000000000000000000000000 : ℝ)*base78 + (144940083890421/25000000000000000000000000000 : ℝ)*base80 + (75296901777921/12500000000000000000000000000 : ℝ)*base82 + (21504619/2500000000000000000000 : ℝ)*base89 + (21504619/2500000000000000000000 : ℝ)*base91 + (21504619/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21849701862874849061169/3125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1596426521/100000000000000 : ℝ)*(base19) + (100593339/6250000000000 : ℝ)*(base23) + (15717557/10000000000000 : ℝ)*(base32) + (241434777/100000000000000 : ℝ)*(upper3) + (141817733/100000000000000 : ℝ)*(upper5) + (85668900051127/12500000000000 : ℝ)*(major0) + (85668900051127/12500000000000 : ℝ)*(major1) + (85668900051127/12500000000000 : ℝ)*(major2) + (3794426751/100000000000000 : ℝ)*(sp1) + (788355383/20000000000000 : ℝ)*(sp2) + (9381516571751/1000000000000 : ℝ)*(sp4) + (938146266321827/100000000000000 : ℝ)*(sp5) + (938146105904761/100000000000000 : ℝ)*(sp6) + (432550353403871/100000000000000 : ℝ)*(sp7) + (432550510579441/100000000000000 : ℝ)*(f.failure) + (9381516571751/1000000000000 : ℝ)*(f.sum) + (1086596997731/781250000000000000000000000 : ℝ)*base66 + (5008757512201/6250000000000000000000000000 : ℝ)*base67 + (20318601130951/6250000000000000000000000000 : ℝ)*base69 + (17870429674701/6250000000000000000000000000 : ℝ)*base71 + (403183410231/781250000000000000000000000 : ℝ)*base74 + (68416816162201/6250000000000000000000000000 : ℝ)*base75 + (1036917143451/6250000000000000000000000000 : ℝ)*base77 + (4721210643451/6250000000000000000000000000 : ℝ)*base79 + (6487334943451/3125000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (23728359/10000000000000000000000 : ℝ)*base90 + (23728359/10000000000000000000000 : ℝ)*base92 + (23728359/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1436_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158444201/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2097/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2621/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1436_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1436_s1_0 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1926220647/10000000000 : ℝ)*x 0 + (1120487341/2000000000 : ℝ)*x 1 + (1269457021/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1926220647/10000000000 : ℝ)^1099 ≤ (730075004903/6250000000000 : ℝ)^843 := by
    have hnat : (1926220647 : ℕ)^1099*6250000000000^843 ≤ 730075004903^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1926220647 10000000000 730075004903 6250000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1120487341/2000000000 : ℝ)^1099 ≤ (939711924239/2000000000000 : ℝ)^843 := by
    have hnat : (1120487341 : ℕ)^1099*2000000000000^843 ≤ 939711924239^843*2000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120487341 2000000000 939711924239 2000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1269457021/2500000000 : ℝ)^1099 ≤ (41333203690787/100000000000000 : ℝ)^843 := by
    have hnat : (1269457021 : ℕ)^1099*100000000000000^843 ≤ 41333203690787^843*2500000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1269457021 2500000000 41333203690787 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1926220647/10000000000 : ℝ), (1120487341/2000000000 : ℝ), (1269457021/2500000000 : ℝ)] ![(730075004903/6250000000000 : ℝ), (939711924239/2000000000000 : ℝ), (41333203690787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1926220647/10000000000 : ℝ)|^1099 ≤ (730075004903/6250000000000 : ℝ)^843
        have hw : |(-1926220647/10000000000 : ℝ)|=(1926220647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1120487341/2000000000 : ℝ)|^1099 ≤ (939711924239/2000000000000 : ℝ)^843
        have hw : |(1120487341/2000000000 : ℝ)|=(1120487341/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1269457021/2500000000 : ℝ)|^1099 ≤ (41333203690787/100000000000000 : ℝ)^843
        have hw : |(1269457021/2500000000 : ℝ)|=(1269457021/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s1_1 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2698054853/5000000000 : ℝ)*x 0 + (-1102028213/5000000000 : ℝ)*x 1 + (158682171/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2698054853/5000000000 : ℝ)^1099 ≤ (44742450969729/100000000000000 : ℝ)^843 := by
    have hnat : (2698054853 : ℕ)^1099*100000000000000^843 ≤ 44742450969729^843*5000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698054853 5000000000 44742450969729 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1102028213/5000000000 : ℝ)^1099 ≤ (13924330600379/100000000000000 : ℝ)^843 := by
    have hnat : (1102028213 : ℕ)^1099*100000000000000^843 ≤ 13924330600379^843*5000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102028213 5000000000 13924330600379 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (158682171/312500000 : ℝ)^1099 ≤ (41333218420039/100000000000000 : ℝ)^843 := by
    have hnat : (158682171 : ℕ)^1099*100000000000000^843 ≤ 41333218420039^843*312500000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158682171 312500000 41333218420039 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2698054853/5000000000 : ℝ), (-1102028213/5000000000 : ℝ), (158682171/312500000 : ℝ)] ![(44742450969729/100000000000000 : ℝ), (13924330600379/100000000000000 : ℝ), (41333218420039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2698054853/5000000000 : ℝ)|^1099 ≤ (44742450969729/100000000000000 : ℝ)^843
        have hw : |(2698054853/5000000000 : ℝ)|=(2698054853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1102028213/5000000000 : ℝ)|^1099 ≤ (13924330600379/100000000000000 : ℝ)^843
        have hw : |(-1102028213/5000000000 : ℝ)|=(1102028213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(158682171/312500000 : ℝ)|^1099 ≤ (41333218420039/100000000000000 : ℝ)^843
        have hw : |(158682171/312500000 : ℝ)|=(158682171/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s1_2 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5396110821/10000000000 : ℝ)*x 0 + (2538914101/5000000000 : ℝ)*x 1 + (-2204056599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5396110821/10000000000 : ℝ)^1099 ≤ (44742463022419/100000000000000 : ℝ)^843 := by
    have hnat : (5396110821 : ℕ)^1099*100000000000000^843 ≤ 44742463022419^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396110821 10000000000 44742463022419 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2538914101/5000000000 : ℝ)^1099 ≤ (20666602471493/50000000000000 : ℝ)^843 := by
    have hnat : (2538914101 : ℕ)^1099*50000000000000^843 ≤ 20666602471493^843*5000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2538914101 5000000000 20666602471493 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2204056599/10000000000 : ℝ)^1099 ≤ (556973281009/4000000000000 : ℝ)^843 := by
    have hnat : (2204056599 : ℕ)^1099*4000000000000^843 ≤ 556973281009^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2204056599 10000000000 556973281009 4000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5396110821/10000000000 : ℝ), (2538914101/5000000000 : ℝ), (-2204056599/10000000000 : ℝ)] ![(44742463022419/100000000000000 : ℝ), (20666602471493/50000000000000 : ℝ), (556973281009/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5396110821/10000000000 : ℝ)|^1099 ≤ (44742463022419/100000000000000 : ℝ)^843
        have hw : |(5396110821/10000000000 : ℝ)|=(5396110821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2538914101/5000000000 : ℝ)|^1099 ≤ (20666602471493/50000000000000 : ℝ)^843
        have hw : |(2538914101/5000000000 : ℝ)|=(2538914101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2204056599/10000000000 : ℝ)|^1099 ≤ (556973281009/4000000000000 : ℝ)^843
        have hw : |(-2204056599/10000000000 : ℝ)|=(2204056599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s1_3 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (427536479/1000000000 : ℝ)*x 0 + (1870074113/5000000000 : ℝ)*x 1 + (2438980177/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (427536479/1000000000 : ℝ)^1099 ≤ (3302996328923/10000000000000 : ℝ)^843 := by
    have hnat : (427536479 : ℕ)^1099*10000000000000^843 ≤ 3302996328923^843*1000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427536479 1000000000 3302996328923 10000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1870074113/5000000000 : ℝ)^1099 ≤ (13872503031661/50000000000000 : ℝ)^843 := by
    have hnat : (1870074113 : ℕ)^1099*50000000000000^843 ≤ 13872503031661^843*5000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1870074113 5000000000 13872503031661 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2438980177/5000000000 : ℝ)^1099 ≤ (39225030624069/100000000000000 : ℝ)^843 := by
    have hnat : (2438980177 : ℕ)^1099*100000000000000^843 ≤ 39225030624069^843*5000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2438980177 5000000000 39225030624069 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(427536479/1000000000 : ℝ), (1870074113/5000000000 : ℝ), (2438980177/5000000000 : ℝ)] ![(3302996328923/10000000000000 : ℝ), (13872503031661/50000000000000 : ℝ), (39225030624069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(427536479/1000000000 : ℝ)|^1099 ≤ (3302996328923/10000000000000 : ℝ)^843
        have hw : |(427536479/1000000000 : ℝ)|=(427536479/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1870074113/5000000000 : ℝ)|^1099 ≤ (13872503031661/50000000000000 : ℝ)^843
        have hw : |(1870074113/5000000000 : ℝ)|=(1870074113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2438980177/5000000000 : ℝ)|^1099 ≤ (39225030624069/100000000000000 : ℝ)^843
        have hw : |(2438980177/5000000000 : ℝ)|=(2438980177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s1_4 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1926609283/10000000000 : ℝ)*x 0 + (1016789241/2000000000 : ℝ)*x 1 + (5596215389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1926609283/10000000000 : ℝ)^1099 ≤ (233685453831/2000000000000 : ℝ)^843 := by
    have hnat : (1926609283 : ℕ)^1099*2000000000000^843 ≤ 233685453831^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1926609283 10000000000 233685453831 2000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1016789241/2000000000 : ℝ)^1099 ≤ (5174767520123/12500000000000 : ℝ)^843 := by
    have hnat : (1016789241 : ℕ)^1099*12500000000000^843 ≤ 5174767520123^843*2000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016789241 2000000000 5174767520123 12500000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5596215389/10000000000 : ℝ)^1099 ≤ (46917587130357/100000000000000 : ℝ)^843 := by
    have hnat : (5596215389 : ℕ)^1099*100000000000000^843 ≤ 46917587130357^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5596215389 10000000000 46917587130357 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1926609283/10000000000 : ℝ), (1016789241/2000000000 : ℝ), (5596215389/10000000000 : ℝ)] ![(233685453831/2000000000000 : ℝ), (5174767520123/12500000000000 : ℝ), (46917587130357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1926609283/10000000000 : ℝ)|^1099 ≤ (233685453831/2000000000000 : ℝ)^843
        have hw : |(-1926609283/10000000000 : ℝ)|=(1926609283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1016789241/2000000000 : ℝ)|^1099 ≤ (5174767520123/12500000000000 : ℝ)^843
        have hw : |(1016789241/2000000000 : ℝ)|=(1016789241/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5596215389/10000000000 : ℝ)|^1099 ≤ (46917587130357/100000000000000 : ℝ)^843
        have hw : |(5596215389/10000000000 : ℝ)|=(5596215389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s1_5 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5258973223/10000000000 : ℝ)*x 0 + (-210708757/1250000000 : ℝ)*x 1 + (5596215409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5258973223/10000000000 : ℝ)^1099 ≤ (1730632662107/4000000000000 : ℝ)^843 := by
    have hnat : (5258973223 : ℕ)^1099*4000000000000^843 ≤ 1730632662107^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258973223 10000000000 1730632662107 4000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210708757/1250000000 : ℝ)^1099 ≤ (613537254783/6250000000000 : ℝ)^843 := by
    have hnat : (210708757 : ℕ)^1099*6250000000000^843 ≤ 613537254783^843*1250000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210708757 1250000000 613537254783 6250000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5596215409/10000000000 : ℝ)^1099 ≤ (5864698418619/12500000000000 : ℝ)^843 := by
    have hnat : (5596215409 : ℕ)^1099*12500000000000^843 ≤ 5864698418619^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5596215409 10000000000 5864698418619 12500000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5258973223/10000000000 : ℝ), (-210708757/1250000000 : ℝ), (5596215409/10000000000 : ℝ)] ![(1730632662107/4000000000000 : ℝ), (613537254783/6250000000000 : ℝ), (5864698418619/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5258973223/10000000000 : ℝ)|^1099 ≤ (1730632662107/4000000000000 : ℝ)^843
        have hw : |(5258973223/10000000000 : ℝ)|=(5258973223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-210708757/1250000000 : ℝ)|^1099 ≤ (613537254783/6250000000000 : ℝ)^843
        have hw : |(-210708757/1250000000 : ℝ)|=(210708757/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5596215409/10000000000 : ℝ)|^1099 ≤ (5864698418619/12500000000000 : ℝ)^843
        have hw : |(5596215409/10000000000 : ℝ)|=(5596215409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s1_6 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5258973159/10000000000 : ℝ)*x 0 + (559621537/1000000000 : ℝ)*x 1 + (-1685670203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5258973159/10000000000 : ℝ)^1099 ≤ (43265815866249/100000000000000 : ℝ)^843 := by
    have hnat : (5258973159 : ℕ)^1099*100000000000000^843 ≤ 43265815866249^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258973159 10000000000 43265815866249 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (559621537/1000000000 : ℝ)^1099 ≤ (46917586922691/100000000000000 : ℝ)^843 := by
    have hnat : (559621537 : ℕ)^1099*100000000000000^843 ≤ 46917586922691^843*1000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559621537 1000000000 46917586922691 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1685670203/10000000000 : ℝ)^1099 ≤ (4908298596279/50000000000000 : ℝ)^843 := by
    have hnat : (1685670203 : ℕ)^1099*50000000000000^843 ≤ 4908298596279^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1685670203 10000000000 4908298596279 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5258973159/10000000000 : ℝ), (559621537/1000000000 : ℝ), (-1685670203/10000000000 : ℝ)] ![(43265815866249/100000000000000 : ℝ), (46917586922691/100000000000000 : ℝ), (4908298596279/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5258973159/10000000000 : ℝ)|^1099 ≤ (43265815866249/100000000000000 : ℝ)^843
        have hw : |(5258973159/10000000000 : ℝ)|=(5258973159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(559621537/1000000000 : ℝ)|^1099 ≤ (46917586922691/100000000000000 : ℝ)^843
        have hw : |(559621537/1000000000 : ℝ)|=(559621537/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1685670203/10000000000 : ℝ)|^1099 ≤ (4908298596279/50000000000000 : ℝ)^843
        have hw : |(-1685670203/10000000000 : ℝ)|=(1685670203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s1_7 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (855241623/2000000000 : ℝ)*x 0 + (121617303/250000000 : ℝ)*x 1 + (3753639349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (855241623/2000000000 : ℝ)^1099 ≤ (8259614326011/25000000000000 : ℝ)^843 := by
    have hnat : (855241623 : ℕ)^1099*25000000000000^843 ≤ 8259614326011^843*2000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      855241623 2000000000 8259614326011 25000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (121617303/250000000 : ℝ)^1099 ≤ (39085994149243/100000000000000 : ℝ)^843 := by
    have hnat : (121617303 : ℕ)^1099*100000000000000^843 ≤ 39085994149243^843*250000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121617303 250000000 39085994149243 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3753639349/10000000000 : ℝ)^1099 ≤ (13937774267037/50000000000000 : ℝ)^843 := by
    have hnat : (3753639349 : ℕ)^1099*50000000000000^843 ≤ 13937774267037^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3753639349 10000000000 13937774267037 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(855241623/2000000000 : ℝ), (121617303/250000000 : ℝ), (3753639349/10000000000 : ℝ)] ![(8259614326011/25000000000000 : ℝ), (39085994149243/100000000000000 : ℝ), (13937774267037/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(855241623/2000000000 : ℝ)|^1099 ≤ (8259614326011/25000000000000 : ℝ)^843
        have hw : |(855241623/2000000000 : ℝ)|=(855241623/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(121617303/250000000 : ℝ)|^1099 ≤ (39085994149243/100000000000000 : ℝ)^843
        have hw : |(121617303/250000000 : ℝ)|=(121617303/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3753639349/10000000000 : ℝ)|^1099 ≤ (13937774267037/50000000000000 : ℝ)^843
        have hw : |(3753639349/10000000000 : ℝ)|=(3753639349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1436_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158444201/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2621/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2097/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (7709/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (47/250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2621/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2097/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2621/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2097/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2621/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2097/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2621/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2097/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2621/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2097/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2621/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2097/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2097/100000 : ℝ) ^ (4395/1024 : ℝ) ≤ (6256242527071/100000000000000000000 : ℝ) := by
    have hpowers : (2097/100000 : ℝ)^4395 ≤ (6256242527071/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2097 : ℕ)^4395*100000000000000000000^1024 ≤ 6256242527071^1024*100000^4395 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2097 100000 6256242527071 100000000000000000000 4395 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2097/100000 : ℝ)) (X := (6256242527071/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2621/10000 : ℝ) ^ (4395/1024 : ℝ) ≤ (159600777046768873/50000000000000000000 : ℝ) := by
    have hpowers : (2621/10000 : ℝ)^4395 ≤ (159600777046768873/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2621 : ℕ)^4395*50000000000000000000^1024 ≤ 159600777046768873^1024*10000^4395 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2621 10000 159600777046768873 50000000000000000000 4395 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2621/10000 : ℝ)) (X := (159600777046768873/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000006256242527071/50000000000000000000 : ℝ) ≤ (2500000072882731/2500000000000000 : ℝ) ^ (4395/1024 : ℝ) := by
    have hpowers : (50000006256242527071/50000000000000000000 : ℝ)^1024 ≤ (2500000072882731/2500000000000000 : ℝ)^4395 := by
      have hnat : (50000006256242527071 : ℕ)^1024*2500000000000000^4395 ≤ 2500000072882731^4395*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000006256242527071 50000000000000000000 2500000072882731 2500000000000000 1024 4395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000072882731/2500000000000000 : ℝ)) (X := (50000006256242527071/50000000000000000000 : ℝ)) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100319207810336064817/100000000000000000000 : ℝ) ≤ (5003714100158763/5000000000000000 : ℝ) ^ (4395/1024 : ℝ) := by
    have hpowers : (100319207810336064817/100000000000000000000 : ℝ)^1024 ≤ (5003714100158763/5000000000000000 : ℝ)^4395 := by
      have hnat : (100319207810336064817 : ℕ)^1024*5000000000000000^4395 ≤ 5003714100158763^4395*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100319207810336064817 100000000000000000000 5003714100158763 5000000000000000 1024 4395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003714100158763/5000000000000000 : ℝ)) (X := (100319207810336064817/100000000000000000000 : ℝ)) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25159600777046768873/25000000000000000000 : ℝ) ≤ (9780132919047/9765625000000 : ℝ) ^ (4395/1024 : ℝ) := by
    have hpowers : (25159600777046768873/25000000000000000000 : ℝ)^1024 ≤ (9780132919047/9765625000000 : ℝ)^4395 := by
      have hnat : (25159600777046768873 : ℕ)^1024*9765625000000^4395 ≤ 9780132919047^4395*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25159600777046768873 25000000000000000000 9780132919047 9765625000000 1024 4395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (9780132919047/9765625000000 : ℝ)) (X := (25159600777046768873/25000000000000000000 : ℝ)) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6256242527071/100000000000000000000 : ℝ) ≤ ((30137356797529270203/30141250000000000000 : ℝ)+2*(3713954393301/1205650000000000 : ℝ)*(2097/100000 : ℝ))^(4395/1024 : ℝ) := by
    rw [show (30137356797529270203/30141250000000000000 : ℝ)+2*(3713954393301/1205650000000000 : ℝ)*(2097/100000 : ℝ)=(2500000072882731/2500000000000000 : ℝ) by norm_num, show 1+2*(6256242527071/100000000000000000000 : ℝ)=(50000006256242527071/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(159600777046768873/50000000000000000000 : ℝ)+(6256242527071/100000000000000000000 : ℝ) ≤ ((30137356797529270203/30141250000000000000 : ℝ)+(3713954393301/1205650000000000 : ℝ)*((2621/10000 : ℝ)+(2097/100000 : ℝ)))^(4395/1024 : ℝ) := by
    rw [show (30137356797529270203/30141250000000000000 : ℝ)+(3713954393301/1205650000000000 : ℝ)*((2621/10000 : ℝ)+(2097/100000 : ℝ))=(5003714100158763/5000000000000000 : ℝ) by norm_num, show 1+(159600777046768873/50000000000000000000 : ℝ)+(6256242527071/100000000000000000000 : ℝ)=(100319207810336064817/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(159600777046768873/50000000000000000000 : ℝ) ≤ ((30137356797529270203/30141250000000000000 : ℝ)+2*(3713954393301/1205650000000000 : ℝ)*(2621/10000 : ℝ))^(4395/1024 : ℝ) := by
    rw [show (30137356797529270203/30141250000000000000 : ℝ)+2*(3713954393301/1205650000000000 : ℝ)*(2621/10000 : ℝ)=(9780132919047/9765625000000 : ℝ) by norm_num, show 1+2*(159600777046768873/50000000000000000000 : ℝ)=(25159600777046768873/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (30137356797529270203/30141250000000000000 : ℝ)*(X 1 0+X 2 0)+(3713954393301/1205650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4395/1024 : ℝ)) (lo := (2097/100000 : ℝ)) (hi := (2621/10000 : ℝ)) (c := (30137356797529270203/30141250000000000000 : ℝ)) (alpha := (3713954393301/1205650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (30137356797529270203/30141250000000000000 : ℝ)*(X 0 1+X 2 1)+(3713954393301/1205650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4395/1024 : ℝ)) (lo := (2097/100000 : ℝ)) (hi := (2621/10000 : ℝ)) (c := (30137356797529270203/30141250000000000000 : ℝ)) (alpha := (3713954393301/1205650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (30137356797529270203/30141250000000000000 : ℝ)*(X 0 2+X 1 2)+(3713954393301/1205650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4395/1024 : ℝ)) (lo := (2097/100000 : ℝ)) (hi := (2621/10000 : ℝ)) (c := (30137356797529270203/30141250000000000000 : ℝ)) (alpha := (3713954393301/1205650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1926220647/10000000000 : ℝ)*X 0 0+(1120487341/2000000000 : ℝ)*X 0 1+(1269457021/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2698054853/5000000000 : ℝ)*X 1 0+(-1102028213/5000000000 : ℝ)*X 1 1+(158682171/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5396110821/10000000000 : ℝ)*X 2 0+(2538914101/5000000000 : ℝ)*X 2 1+(-2204056599/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((427536479/1000000000 : ℝ)*X 0 0+(1870074113/5000000000 : ℝ)*X 0 1+(2438980177/5000000000 : ℝ)*X 0 2+(427536479/1000000000 : ℝ)*X 1 0+(1870074113/5000000000 : ℝ)*X 1 1+(2438980177/5000000000 : ℝ)*X 1 2+(427536479/1000000000 : ℝ)*X 2 0+(1870074113/5000000000 : ℝ)*X 2 1+(2438980177/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1926609283/10000000000 : ℝ)*X 0 0+(1016789241/2000000000 : ℝ)*X 0 1+(5596215389/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5258973223/10000000000 : ℝ)*X 1 0+(-210708757/1250000000 : ℝ)*X 1 1+(5596215409/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5258973159/10000000000 : ℝ)*X 2 0+(559621537/1000000000 : ℝ)*X 2 1+(-1685670203/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((855241623/2000000000 : ℝ)*X 0 0+(121617303/250000000 : ℝ)*X 0 1+(3753639349/10000000000 : ℝ)*X 0 2+(855241623/2000000000 : ℝ)*X 1 0+(121617303/250000000 : ℝ)*X 1 1+(3753639349/10000000000 : ℝ)*X 1 2+(855241623/2000000000 : ℝ)*X 2 0+(121617303/250000000 : ℝ)*X 2 1+(3753639349/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1970037994426951052419559499/376765625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (424801439/50000000000000 : ℝ)*(base19) + (15225783/1250000000000 : ℝ)*(base23) + (15478707/20000000000000 : ℝ)*(upper3) + (6858401/50000000000000 : ℝ)*(upper4) + (32667999/50000000000000 : ℝ)*(upper5) + (87034151777459/6250000000000 : ℝ)*(major0) + (87034151777459/6250000000000 : ℝ)*(major1) + (87034151777459/6250000000000 : ℝ)*(major2) + (1906193408967811/100000000000000 : ℝ)*(sp0) + (1906204237443283/100000000000000 : ℝ)*(sp1) + (953101934491761/50000000000000 : ℝ)*(sp2) + (109860417603979/12500000000000 : ℝ)*(sp3) + (11678078351/100000000000000 : ℝ)*(sp4) + (425470683/10000000000000 : ℝ)*(sp7) + (878887595538661/100000000000000 : ℝ)*(f.failure) + (953102543523081/50000000000000 : ℝ)*(f.sum) + (65861675340639/15070625000000000000000000000 : ℝ)*base66 + (476043784206403651/94191406250000000000000000000000 : ℝ)*base67 + (3529414193043869771/376765625000000000000000000000000 : ℝ)*base70 + (383999667915458323/188382812500000000000000000000000 : ℝ)*base72 + (48079490476139/60282500000000000000000000000 : ℝ)*base73 + (211765451898528651/94191406250000000000000000000000 : ℝ)*base75 + (631551028386802073/188382812500000000000000000000000 : ℝ)*base78 + (237715054141427073/188382812500000000000000000000000 : ℝ)*base80 + (99717621003089/15070625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (93245139/10000000000000000000000 : ℝ)*base90 + (93245139/10000000000000000000000 : ℝ)*base92 + (93245139/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (170257150385924856806598201/30141250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (41303809/100000000000000 : ℝ)*(base1) + (7691427/625000000000 : ℝ)*(base19) + (598682757/50000000000000 : ℝ)*(base23) + (141259/100000000000 : ℝ)*(upper3) + (115831877/100000000000000 : ℝ)*(upper5) + (28521457898589/2000000000000 : ℝ)*(major0) + (28521457898589/2000000000000 : ℝ)*(major1) + (28521457898589/2000000000000 : ℝ)*(major2) + (367942947/5000000000000 : ℝ)*(sp1) + (3497121151/50000000000000 : ℝ)*(sp2) + (976049126682631/50000000000000 : ℝ)*(sp4) + (122005601410887/6250000000000 : ℝ)*(sp5) + (488022505113409/25000000000000 : ℝ)*(sp6) + (450023674102771/50000000000000 : ℝ)*(sp7) + (112505923688669/12500000000000 : ℝ)*(f.failure) + (1952098212061453/100000000000000 : ℝ)*(f.sum) + (11300685802747/6028250000000000000000000000 : ℝ)*base65 + (425336973418706433/60282500000000000000000000000000 : ℝ)*base68 + (309897753763301433/60282500000000000000000000000000 : ℝ)*base70 + (11476273083876433/60282500000000000000000000000000 : ℝ)*base72 + (17941991226761/6028250000000000000000000000 : ℝ)*base74 + (106269279427273567/60282500000000000000000000000000 : ℝ)*base75 + (9569755228701433/60282500000000000000000000000000 : ℝ)*base78 + (620633388030338567/60282500000000000000000000000000 : ℝ)*base79 + (64777622099/6028250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (7458469/1250000000000000000000 : ℝ)*base89 + (7458469/1250000000000000000000 : ℝ)*base91 + (7458469/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1436_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158444201/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2621/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2097/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7709/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (47/250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1436_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1436_s2_0 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1958834721/10000000000 : ℝ)*x 0 + (1091323587/2000000000 : ℝ)*x 1 + (2601322833/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1958834721/10000000000 : ℝ)^1099 ≤ (11939704120809/100000000000000 : ℝ)^843 := by
    have hnat : (1958834721 : ℕ)^1099*100000000000000^843 ≤ 11939704120809^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1958834721 10000000000 11939704120809 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1091323587/2000000000 : ℝ)^1099 ≤ (45397630702647/100000000000000 : ℝ)^843 := by
    have hnat : (1091323587 : ℕ)^1099*100000000000000^843 ≤ 45397630702647^843*2000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091323587 2000000000 45397630702647 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2601322833/5000000000 : ℝ)^1099 ≤ (21331332575843/50000000000000 : ℝ)^843 := by
    have hnat : (2601322833 : ℕ)^1099*50000000000000^843 ≤ 21331332575843^843*5000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2601322833 5000000000 21331332575843 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1958834721/10000000000 : ℝ), (1091323587/2000000000 : ℝ), (2601322833/5000000000 : ℝ)] ![(11939704120809/100000000000000 : ℝ), (45397630702647/100000000000000 : ℝ), (21331332575843/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1958834721/10000000000 : ℝ)|^1099 ≤ (11939704120809/100000000000000 : ℝ)^843
        have hw : |(-1958834721/10000000000 : ℝ)|=(1958834721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1091323587/2000000000 : ℝ)|^1099 ≤ (45397630702647/100000000000000 : ℝ)^843
        have hw : |(1091323587/2000000000 : ℝ)|=(1091323587/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2601322833/5000000000 : ℝ)|^1099 ≤ (21331332575843/50000000000000 : ℝ)^843
        have hw : |(2601322833/5000000000 : ℝ)|=(2601322833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s2_1 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (53596991/100000000 : ℝ)*x 0 + (-104473119/500000000 : ℝ)*x 1 + (2601322763/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53596991/100000000 : ℝ)^1099 ≤ (11087317804319/25000000000000 : ℝ)^843 := by
    have hnat : (53596991 : ℕ)^1099*25000000000000^843 ≤ 11087317804319^843*100000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53596991 100000000 11087317804319 25000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104473119/500000000 : ℝ)^1099 ≤ (12988065108783/100000000000000 : ℝ)^843 := by
    have hnat : (104473119 : ℕ)^1099*100000000000000^843 ≤ 12988065108783^843*500000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104473119 500000000 12988065108783 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2601322763/5000000000 : ℝ)^1099 ≤ (42662663655031/100000000000000 : ℝ)^843 := by
    have hnat : (2601322763 : ℕ)^1099*100000000000000^843 ≤ 42662663655031^843*5000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2601322763 5000000000 42662663655031 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53596991/100000000 : ℝ), (-104473119/500000000 : ℝ), (2601322763/5000000000 : ℝ)] ![(11087317804319/25000000000000 : ℝ), (12988065108783/100000000000000 : ℝ), (42662663655031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53596991/100000000 : ℝ)|^1099 ≤ (11087317804319/25000000000000 : ℝ)^843
        have hw : |(53596991/100000000 : ℝ)|=(53596991/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-104473119/500000000 : ℝ)|^1099 ≤ (12988065108783/100000000000000 : ℝ)^843
        have hw : |(-104473119/500000000 : ℝ)|=(104473119/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2601322763/5000000000 : ℝ)|^1099 ≤ (42662663655031/100000000000000 : ℝ)^843
        have hw : |(2601322763/5000000000 : ℝ)|=(2601322763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s2_2 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1339924667/2500000000 : ℝ)*x 0 + (5202645999/10000000000 : ℝ)*x 1 + (-2089462331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1339924667/2500000000 : ℝ)^1099 ≤ (354794132457/800000000000 : ℝ)^843 := by
    have hnat : (1339924667 : ℕ)^1099*800000000000^843 ≤ 354794132457^843*2500000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1339924667 2500000000 354794132457 800000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5202645999/10000000000 : ℝ)^1099 ≤ (42662668711589/100000000000000 : ℝ)^843 := by
    have hnat : (5202645999 : ℕ)^1099*100000000000000^843 ≤ 42662668711589^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5202645999 10000000000 42662668711589 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2089462331/10000000000 : ℝ)^1099 ≤ (1623508088963/12500000000000 : ℝ)^843 := by
    have hnat : (2089462331 : ℕ)^1099*12500000000000^843 ≤ 1623508088963^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089462331 10000000000 1623508088963 12500000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1339924667/2500000000 : ℝ), (5202645999/10000000000 : ℝ), (-2089462331/10000000000 : ℝ)] ![(354794132457/800000000000 : ℝ), (42662668711589/100000000000000 : ℝ), (1623508088963/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1339924667/2500000000 : ℝ)|^1099 ≤ (354794132457/800000000000 : ℝ)^843
        have hw : |(1339924667/2500000000 : ℝ)|=(1339924667/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5202645999/10000000000 : ℝ)|^1099 ≤ (42662668711589/100000000000000 : ℝ)^843
        have hw : |(5202645999/10000000000 : ℝ)|=(5202645999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2089462331/10000000000 : ℝ)|^1099 ≤ (1623508088963/12500000000000 : ℝ)^843
        have hw : |(-2089462331/10000000000 : ℝ)|=(2089462331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s2_3 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (429840441/1000000000 : ℝ)*x 0 + (403088293/1000000000 : ℝ)*x 1 + (286357489/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (429840441/1000000000 : ℝ)^1099 ≤ (16631101134833/50000000000000 : ℝ)^843 := by
    have hnat : (429840441 : ℕ)^1099*50000000000000^843 ≤ 16631101134833^843*1000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429840441 1000000000 16631101134833 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (403088293/1000000000 : ℝ)^1099 ≤ (15294636720599/50000000000000 : ℝ)^843 := by
    have hnat : (403088293 : ℕ)^1099*50000000000000^843 ≤ 15294636720599^843*1000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403088293 1000000000 15294636720599 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (286357489/625000000 : ℝ)^1099 ≤ (18074262135873/50000000000000 : ℝ)^843 := by
    have hnat : (286357489 : ℕ)^1099*50000000000000^843 ≤ 18074262135873^843*625000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      286357489 625000000 18074262135873 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(429840441/1000000000 : ℝ), (403088293/1000000000 : ℝ), (286357489/625000000 : ℝ)] ![(16631101134833/50000000000000 : ℝ), (15294636720599/50000000000000 : ℝ), (18074262135873/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(429840441/1000000000 : ℝ)|^1099 ≤ (16631101134833/50000000000000 : ℝ)^843
        have hw : |(429840441/1000000000 : ℝ)|=(429840441/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(403088293/1000000000 : ℝ)|^1099 ≤ (15294636720599/50000000000000 : ℝ)^843
        have hw : |(403088293/1000000000 : ℝ)|=(403088293/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(286357489/625000000 : ℝ)|^1099 ≤ (18074262135873/50000000000000 : ℝ)^843
        have hw : |(286357489/625000000 : ℝ)|=(286357489/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s2_4 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1958878899/10000000000 : ℝ)*x 0 + (5204088633/10000000000 : ℝ)*x 1 + (5455163219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1958878899/10000000000 : ℝ)^1099 ≤ (5970027587203/50000000000000 : ℝ)^843 := by
    have hnat : (1958878899 : ℕ)^1099*50000000000000^843 ≤ 5970027587203^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1958878899 10000000000 5970027587203 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5204088633/10000000000 : ℝ)^1099 ≤ (8535618338401/20000000000000 : ℝ)^843 := by
    have hnat : (5204088633 : ℕ)^1099*20000000000000^843 ≤ 8535618338401^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5204088633 10000000000 8535618338401 20000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5455163219/10000000000 : ℝ)^1099 ≤ (2215910797/4882812500 : ℝ)^843 := by
    have hnat : (5455163219 : ℕ)^1099*4882812500^843 ≤ 2215910797^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5455163219 10000000000 2215910797 4882812500 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1958878899/10000000000 : ℝ), (5204088633/10000000000 : ℝ), (5455163219/10000000000 : ℝ)] ![(5970027587203/50000000000000 : ℝ), (8535618338401/20000000000000 : ℝ), (2215910797/4882812500 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1958878899/10000000000 : ℝ)|^1099 ≤ (5970027587203/50000000000000 : ℝ)^843
        have hw : |(-1958878899/10000000000 : ℝ)|=(1958878899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5204088633/10000000000 : ℝ)|^1099 ≤ (8535618338401/20000000000000 : ℝ)^843
        have hw : |(5204088633/10000000000 : ℝ)|=(5204088633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5455163219/10000000000 : ℝ)|^1099 ≤ (2215910797/4882812500 : ℝ)^843
        have hw : |(5455163219/10000000000 : ℝ)|=(5455163219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s2_5 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2646807233/5000000000 : ℝ)*x 0 + (-91847209/500000000 : ℝ)*x 1 + (43641311/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646807233/5000000000 : ℝ)^1099 ≤ (5454716157839/12500000000000 : ℝ)^843 := by
    have hnat : (2646807233 : ℕ)^1099*12500000000000^843 ≤ 5454716157839^843*5000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646807233 5000000000 5454716157839 12500000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (91847209/500000000 : ℝ)^1099 ≤ (10980410484493/100000000000000 : ℝ)^843 := by
    have hnat : (91847209 : ℕ)^1099*100000000000000^843 ≤ 10980410484493^843*500000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91847209 500000000 10980410484493 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43641311/80000000 : ℝ)^1099 ≤ (22690930118563/50000000000000 : ℝ)^843 := by
    have hnat : (43641311 : ℕ)^1099*50000000000000^843 ≤ 22690930118563^843*80000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43641311 80000000 22690930118563 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646807233/5000000000 : ℝ), (-91847209/500000000 : ℝ), (43641311/80000000 : ℝ)] ![(5454716157839/12500000000000 : ℝ), (10980410484493/100000000000000 : ℝ), (22690930118563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646807233/5000000000 : ℝ)|^1099 ≤ (5454716157839/12500000000000 : ℝ)^843
        have hw : |(2646807233/5000000000 : ℝ)|=(2646807233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-91847209/500000000 : ℝ)|^1099 ≤ (10980410484493/100000000000000 : ℝ)^843
        have hw : |(-91847209/500000000 : ℝ)|=(91847209/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(43641311/80000000 : ℝ)|^1099 ≤ (22690930118563/50000000000000 : ℝ)^843
        have hw : |(43641311/80000000 : ℝ)|=(43641311/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s2_6 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1058722839/2000000000 : ℝ)*x 0 + (2727581913/5000000000 : ℝ)*x 1 + (-1836944621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058722839/2000000000 : ℝ)^1099 ≤ (43637726350323/100000000000000 : ℝ)^843 := by
    have hnat : (1058722839 : ℕ)^1099*100000000000000^843 ≤ 43637726350323^843*2000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058722839 2000000000 43637726350323 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2727581913/5000000000 : ℝ)^1099 ≤ (45381859705703/100000000000000 : ℝ)^843 := by
    have hnat : (2727581913 : ℕ)^1099*100000000000000^843 ≤ 45381859705703^843*5000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2727581913 5000000000 45381859705703 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1836944621/10000000000 : ℝ)^1099 ≤ (1372551740139/12500000000000 : ℝ)^843 := by
    have hnat : (1836944621 : ℕ)^1099*12500000000000^843 ≤ 1372551740139^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1836944621 10000000000 1372551740139 12500000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058722839/2000000000 : ℝ), (2727581913/5000000000 : ℝ), (-1836944621/10000000000 : ℝ)] ![(43637726350323/100000000000000 : ℝ), (45381859705703/100000000000000 : ℝ), (1372551740139/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058722839/2000000000 : ℝ)|^1099 ≤ (43637726350323/100000000000000 : ℝ)^843
        have hw : |(1058722839/2000000000 : ℝ)|=(1058722839/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2727581913/5000000000 : ℝ)|^1099 ≤ (45381859705703/100000000000000 : ℝ)^843
        have hw : |(2727581913/5000000000 : ℝ)|=(2727581913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1836944621/10000000000 : ℝ)|^1099 ≤ (1372551740139/12500000000000 : ℝ)^843
        have hw : |(-1836944621/10000000000 : ℝ)|=(1836944621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s2_7 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4298500249/10000000000 : ℝ)*x 0 + (1144647707/2500000000 : ℝ)*x 1 + (1008509399/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4298500249/10000000000 : ℝ)^1099 ≤ (16631584558149/50000000000000 : ℝ)^843 := by
    have hnat : (4298500249 : ℕ)^1099*50000000000000^843 ≤ 16631584558149^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4298500249 10000000000 16631584558149 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1144647707/2500000000 : ℝ)^1099 ≤ (18058171910379/50000000000000 : ℝ)^843 := by
    have hnat : (1144647707 : ℕ)^1099*50000000000000^843 ≤ 18058171910379^843*2500000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1144647707 2500000000 18058171910379 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1008509399/2500000000 : ℝ)^1099 ≤ (7655121764161/25000000000000 : ℝ)^843 := by
    have hnat : (1008509399 : ℕ)^1099*25000000000000^843 ≤ 7655121764161^843*2500000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008509399 2500000000 7655121764161 25000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4298500249/10000000000 : ℝ), (1144647707/2500000000 : ℝ), (1008509399/2500000000 : ℝ)] ![(16631584558149/50000000000000 : ℝ), (18058171910379/50000000000000 : ℝ), (7655121764161/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4298500249/10000000000 : ℝ)|^1099 ≤ (16631584558149/50000000000000 : ℝ)^843
        have hw : |(4298500249/10000000000 : ℝ)|=(4298500249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1144647707/2500000000 : ℝ)|^1099 ≤ (18058171910379/50000000000000 : ℝ)^843
        have hw : |(1144647707/2500000000 : ℝ)|=(1144647707/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1008509399/2500000000 : ℝ)|^1099 ≤ (7655121764161/25000000000000 : ℝ)^843
        have hw : |(1008509399/2500000000 : ℝ)|=(1008509399/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1436_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158444201/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (47/250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7709/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2081/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7889/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (47/250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7709/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (47/250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7709/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (47/250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7709/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (47/250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7709/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (47/250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7709/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (47/250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7709/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7709/100000 : ℝ) ^ (4395/1024 : ℝ) ≤ (41777679708227/2500000000000000000 : ℝ) := by
    have hpowers : (7709/100000 : ℝ)^4395 ≤ (41777679708227/2500000000000000000 : ℝ)^1024 := by
      have hnat : (7709 : ℕ)^4395*2500000000000000000^1024 ≤ 41777679708227^1024*100000^4395 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7709 100000 41777679708227 2500000000000000000 4395 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7709/100000 : ℝ)) (X := (41777679708227/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (47/250 : ℝ) ^ (4395/1024 : ℝ) ≤ (76681598871569579/100000000000000000000 : ℝ) := by
    have hpowers : (47/250 : ℝ)^4395 ≤ (76681598871569579/100000000000000000000 : ℝ)^1024 := by
      have hnat : (47 : ℕ)^4395*100000000000000000000^1024 ≤ 76681598871569579^1024*250^4395 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        47 250 76681598871569579 100000000000000000000 4395 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (47/250 : ℝ)) (X := (76681598871569579/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250041777679708227/1250000000000000000 : ℝ) ≤ (10000077869935279/10000000000000000 : ℝ) ^ (4395/1024 : ℝ) := by
    have hpowers : (1250041777679708227/1250000000000000000 : ℝ)^1024 ≤ (10000077869935279/10000000000000000 : ℝ)^4395 := by
      have hnat : (1250041777679708227 : ℕ)^1024*10000000000000000^4395 ≤ 10000077869935279^4395*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250041777679708227 1250000000000000000 10000077869935279 10000000000000000 1024 4395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000077869935279/10000000000000000 : ℝ)) (X := (1250041777679708227/1250000000000000000 : ℝ)) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100078352706059898659/100000000000000000000 : ℝ) ≤ (10001825007353839/10000000000000000 : ℝ) ^ (4395/1024 : ℝ) := by
    have hpowers : (100078352706059898659/100000000000000000000 : ℝ)^1024 ≤ (10001825007353839/10000000000000000 : ℝ)^4395 := by
      have hnat : (100078352706059898659 : ℕ)^1024*10000000000000000^4395 ≤ 10001825007353839^4395*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100078352706059898659 100000000000000000000 10001825007353839 10000000000000000 1024 4395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001825007353839/10000000000000000 : ℝ)) (X := (100078352706059898659/100000000000000000000 : ℝ)) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50076681598871569579/50000000000000000000 : ℝ) ≤ (10003572144772399/10000000000000000 : ℝ) ^ (4395/1024 : ℝ) := by
    have hpowers : (50076681598871569579/50000000000000000000 : ℝ)^1024 ≤ (10003572144772399/10000000000000000 : ℝ)^4395 := by
      have hnat : (50076681598871569579 : ℕ)^1024*10000000000000000^4395 ≤ 10003572144772399^4395*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50076681598871569579 50000000000000000000 10003572144772399 10000000000000000 1024 4395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003572144772399/10000000000000000 : ℝ)) (X := (50076681598871569579/50000000000000000000 : ℝ)) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(41777679708227/2500000000000000000 : ℝ) ≤ ((36961308763577607103/36970000000000000000 : ℝ)+2*(1819934811/1155312500000 : ℝ)*(7709/100000 : ℝ))^(4395/1024 : ℝ) := by
    rw [show (36961308763577607103/36970000000000000000 : ℝ)+2*(1819934811/1155312500000 : ℝ)*(7709/100000 : ℝ)=(10000077869935279/10000000000000000 : ℝ) by norm_num, show 1+2*(41777679708227/2500000000000000000 : ℝ)=(1250041777679708227/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(76681598871569579/100000000000000000000 : ℝ)+(41777679708227/2500000000000000000 : ℝ) ≤ ((36961308763577607103/36970000000000000000 : ℝ)+(1819934811/1155312500000 : ℝ)*((47/250 : ℝ)+(7709/100000 : ℝ)))^(4395/1024 : ℝ) := by
    rw [show (36961308763577607103/36970000000000000000 : ℝ)+(1819934811/1155312500000 : ℝ)*((47/250 : ℝ)+(7709/100000 : ℝ))=(10001825007353839/10000000000000000 : ℝ) by norm_num, show 1+(76681598871569579/100000000000000000000 : ℝ)+(41777679708227/2500000000000000000 : ℝ)=(100078352706059898659/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(76681598871569579/100000000000000000000 : ℝ) ≤ ((36961308763577607103/36970000000000000000 : ℝ)+2*(1819934811/1155312500000 : ℝ)*(47/250 : ℝ))^(4395/1024 : ℝ) := by
    rw [show (36961308763577607103/36970000000000000000 : ℝ)+2*(1819934811/1155312500000 : ℝ)*(47/250 : ℝ)=(10003572144772399/10000000000000000 : ℝ) by norm_num, show 1+2*(76681598871569579/100000000000000000000 : ℝ)=(50076681598871569579/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (36961308763577607103/36970000000000000000 : ℝ)*(X 1 0+X 2 0)+(1819934811/1155312500000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4395/1024 : ℝ)) (lo := (7709/100000 : ℝ)) (hi := (47/250 : ℝ)) (c := (36961308763577607103/36970000000000000000 : ℝ)) (alpha := (1819934811/1155312500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (36961308763577607103/36970000000000000000 : ℝ)*(X 0 1+X 2 1)+(1819934811/1155312500000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4395/1024 : ℝ)) (lo := (7709/100000 : ℝ)) (hi := (47/250 : ℝ)) (c := (36961308763577607103/36970000000000000000 : ℝ)) (alpha := (1819934811/1155312500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (36961308763577607103/36970000000000000000 : ℝ)*(X 0 2+X 1 2)+(1819934811/1155312500000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4395/1024 : ℝ)) (lo := (7709/100000 : ℝ)) (hi := (47/250 : ℝ)) (c := (36961308763577607103/36970000000000000000 : ℝ)) (alpha := (1819934811/1155312500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1958834721/10000000000 : ℝ)*X 0 0+(1091323587/2000000000 : ℝ)*X 0 1+(2601322833/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((53596991/100000000 : ℝ)*X 1 0+(-104473119/500000000 : ℝ)*X 1 1+(2601322763/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1339924667/2500000000 : ℝ)*X 2 0+(5202645999/10000000000 : ℝ)*X 2 1+(-2089462331/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((429840441/1000000000 : ℝ)*X 0 0+(403088293/1000000000 : ℝ)*X 0 1+(286357489/625000000 : ℝ)*X 0 2+(429840441/1000000000 : ℝ)*X 1 0+(403088293/1000000000 : ℝ)*X 1 1+(286357489/625000000 : ℝ)*X 1 2+(429840441/1000000000 : ℝ)*X 2 0+(403088293/1000000000 : ℝ)*X 2 1+(286357489/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1958878899/10000000000 : ℝ)*X 0 0+(5204088633/10000000000 : ℝ)*X 0 1+(5455163219/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2646807233/5000000000 : ℝ)*X 1 0+(-91847209/500000000 : ℝ)*X 1 1+(43641311/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1058722839/2000000000 : ℝ)*X 2 0+(2727581913/5000000000 : ℝ)*X 2 1+(-1836944621/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4298500249/10000000000 : ℝ)*X 0 0+(1144647707/2500000000 : ℝ)*X 0 1+(1008509399/2500000000 : ℝ)*X 0 2+(4298500249/10000000000 : ℝ)*X 1 0+(1144647707/2500000000 : ℝ)*X 1 1+(1008509399/2500000000 : ℝ)*X 1 2+(4298500249/10000000000 : ℝ)*X 2 0+(1144647707/2500000000 : ℝ)*X 2 1+(1008509399/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2884979109890667998224559079/924250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (105307/250000000000 : ℝ)*(base21) + (8569189/50000000000000 : ℝ)*(upper2) + (8777411/100000000000000 : ℝ)*(upper3) + (29824001/25000000000000 : ℝ)*(lower4) + (48796587/50000000000000 : ℝ)*(upper5) + (2876430108483469/100000000000000 : ℝ)*(major0) + (2876430108483469/100000000000000 : ℝ)*(major1) + (2876430108483469/100000000000000 : ℝ)*(major2) + (3937438601542319/100000000000000 : ℝ)*(sp0) + (3937436070971693/100000000000000 : ℝ)*(sp1) + (393743816500537/10000000000000 : ℝ)*(sp2) + (453855377844259/25000000000000 : ℝ)*(sp3) + (1265285313/50000000000000 : ℝ)*(sp5) + (394414149/100000000000000 : ℝ)*(sp6) + (453855377844259/25000000000000 : ℝ)*(f.failure) + (3937438601542319/100000000000000 : ℝ)*(f.sum) + (42223832315559/3697000000000000000000000000 : ℝ)*base65 + (20118167322475480307/3697000000000000000000000000000000 : ℝ)*base67 + (26769756585494480307/3697000000000000000000000000000000 : ℝ)*base69 + (92440012489868480307/3697000000000000000000000000000000 : ℝ)*base71 + (369559726339/924250000000000000000000000 : ℝ)*base73 + (18305505349136480307/3697000000000000000000000000000000 : ℝ)*base75 + (49809017474165480307/3697000000000000000000000000000000 : ℝ)*base77 + (22820629709507519693/3697000000000000000000000000000000 : ℝ)*base80 + (17110366763471/3697000000000000000000000000 : ℝ)*base81 + (5307941/2500000000000000000000 : ℝ)*base90 + (5307941/2500000000000000000000 : ℝ)*base92 + (5307941/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2379347233978791628701148413/462125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (369671/5000000000000 : ℝ)*(base19) + (10634377/100000000000000 : ℝ)*(base23) + (148279759/100000000000000 : ℝ)*(upper3) + (30094321/25000000000000 : ℝ)*(lower4) + (727405446219419/25000000000000 : ℝ)*(major0) + (727405446219419/25000000000000 : ℝ)*(major1) + (727405446219419/25000000000000 : ℝ)*(major2) + (1151965023/25000000000000 : ℝ)*(sp1) + (596966183/20000000000000 : ℝ)*(sp2) + (123274539/12500000000000 : ℝ)*(sp3) + (199143669560281/5000000000000 : ℝ)*(sp4) + (3982868775952109/100000000000000 : ℝ)*(sp5) + (497858799467541/12500000000000 : ℝ)*(sp6) + (1836369020729771/100000000000000 : ℝ)*(sp7) + (918185003463041/50000000000000 : ℝ)*(f.failure) + (199143669560281/5000000000000 : ℝ)*(f.sum) + (15045112960361/3697000000000000000000000000 : ℝ)*base65 + (6429873296595066843/924250000000000000000000000000000 : ℝ)*base68 + (715825565613066843/924250000000000000000000000000000 : ℝ)*base70 + (2040668168056316843/924250000000000000000000000000000 : ℝ)*base72 + (46189732169/115531250000000000000000000 : ℝ)*base73 + (18770605663597816843/924250000000000000000000000000000 : ℝ)*base76 + (3909086851716816843/924250000000000000000000000000000 : ℝ)*base78 + (6617973470705316843/924250000000000000000000000000000 : ℝ)*base80 + (6749471845557/3697000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (35724759/5000000000000000000000 : ℝ)*base90 + (35724759/5000000000000000000000 : ℝ)*base92 + (35724759/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1436_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158444201/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (47/250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7709/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2081/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7889/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1436_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1436_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158444201/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2081/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7889/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1436_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1436_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1436_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158444201/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2081/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7889/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1436_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
