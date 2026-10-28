-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1066_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:06:50.775858+00:00
-- url     : https://prove2.me/submissions/567356cb-e758-47ea-9469-44854b6a579a

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
theorem support_rectangle_w1066_s3_0 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-219902749/1000000000 : ℝ)*x 0 + (339845959/625000000 : ℝ)*x 1 + (2612187319/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (219902749/1000000000 : ℝ)^8259 ≤ (3336409951499/25000000000000 : ℝ)^6211 := by
    have hnat : (219902749 : ℕ)^8259*25000000000000^6211 ≤ 3336409951499^6211*1000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219902749 1000000000 3336409951499 25000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339845959/625000000 : ℝ)^8259 ≤ (22239459511323/50000000000000 : ℝ)^6211 := by
    have hnat : (339845959 : ℕ)^8259*50000000000000^6211 ≤ 22239459511323^6211*625000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339845959 625000000 22239459511323 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2612187319/5000000000 : ℝ)^8259 ≤ (42175441154921/100000000000000 : ℝ)^6211 := by
    have hnat : (2612187319 : ℕ)^8259*100000000000000^6211 ≤ 42175441154921^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612187319 5000000000 42175441154921 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-219902749/1000000000 : ℝ), (339845959/625000000 : ℝ), (2612187319/5000000000 : ℝ)] ![(3336409951499/25000000000000 : ℝ), (22239459511323/50000000000000 : ℝ), (42175441154921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-219902749/1000000000 : ℝ)|^8259 ≤ (3336409951499/25000000000000 : ℝ)^6211
        have hw : |(-219902749/1000000000 : ℝ)|=(219902749/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339845959/625000000 : ℝ)|^8259 ≤ (22239459511323/50000000000000 : ℝ)^6211
        have hw : |(339845959/625000000 : ℝ)|=(339845959/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2612187319/5000000000 : ℝ)|^8259 ≤ (42175441154921/100000000000000 : ℝ)^6211
        have hw : |(2612187319/5000000000 : ℝ)|=(2612187319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s3_1 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5355691619/10000000000 : ℝ)*x 0 + (-2308182853/10000000000 : ℝ)*x 1 + (2612187281/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355691619/10000000000 : ℝ)^8259 ≤ (21795451563801/50000000000000 : ℝ)^6211 := by
    have hnat : (5355691619 : ℕ)^8259*50000000000000^6211 ≤ 21795451563801^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355691619 10000000000 21795451563801 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2308182853/10000000000 : ℝ)^8259 ≤ (14233656529187/100000000000000 : ℝ)^6211 := by
    have hnat : (2308182853 : ℕ)^8259*100000000000000^6211 ≤ 14233656529187^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2308182853 10000000000 14233656529187 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2612187281/5000000000 : ℝ)^8259 ≤ (42175440339081/100000000000000 : ℝ)^6211 := by
    have hnat : (2612187281 : ℕ)^8259*100000000000000^6211 ≤ 42175440339081^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612187281 5000000000 42175440339081 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355691619/10000000000 : ℝ), (-2308182853/10000000000 : ℝ), (2612187281/5000000000 : ℝ)] ![(21795451563801/50000000000000 : ℝ), (14233656529187/100000000000000 : ℝ), (42175440339081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355691619/10000000000 : ℝ)|^8259 ≤ (21795451563801/50000000000000 : ℝ)^6211
        have hw : |(5355691619/10000000000 : ℝ)|=(5355691619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2308182853/10000000000 : ℝ)|^8259 ≤ (14233656529187/100000000000000 : ℝ)^6211
        have hw : |(-2308182853/10000000000 : ℝ)|=(2308182853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2612187281/5000000000 : ℝ)|^8259 ≤ (42175440339081/100000000000000 : ℝ)^6211
        have hw : |(2612187281/5000000000 : ℝ)|=(2612187281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s3_2 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (167365361/312500000 : ℝ)*x 0 + (2612187199/5000000000 : ℝ)*x 1 + (-1154091577/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167365361/312500000 : ℝ)^8259 ≤ (43590902402463/100000000000000 : ℝ)^6211 := by
    have hnat : (167365361 : ℕ)^8259*100000000000000^6211 ≤ 43590902402463^6211*312500000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167365361 312500000 43590902402463 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2612187199/5000000000 : ℝ)^8259 ≤ (8435087715717/20000000000000 : ℝ)^6211 := by
    have hnat : (2612187199 : ℕ)^8259*20000000000000^6211 ≤ 8435087715717^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612187199 5000000000 8435087715717 20000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1154091577/5000000000 : ℝ)^8259 ≤ (7116829498689/50000000000000 : ℝ)^6211 := by
    have hnat : (1154091577 : ℕ)^8259*50000000000000^6211 ≤ 7116829498689^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1154091577 5000000000 7116829498689 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167365361/312500000 : ℝ), (2612187199/5000000000 : ℝ), (-1154091577/5000000000 : ℝ)] ![(43590902402463/100000000000000 : ℝ), (8435087715717/20000000000000 : ℝ), (7116829498689/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167365361/312500000 : ℝ)|^8259 ≤ (43590902402463/100000000000000 : ℝ)^6211
        have hw : |(167365361/312500000 : ℝ)|=(167365361/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2612187199/5000000000 : ℝ)|^8259 ≤ (8435087715717/20000000000000 : ℝ)^6211
        have hw : |(2612187199/5000000000 : ℝ)|=(2612187199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1154091577/5000000000 : ℝ)|^8259 ≤ (7116829498689/50000000000000 : ℝ)^6211
        have hw : |(-1154091577/5000000000 : ℝ)|=(1154091577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s3_3 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4372689347/10000000000 : ℝ)*x 0 + (208442647/500000000 : ℝ)*x 1 + (573327397/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4372689347/10000000000 : ℝ)^8259 ≤ (33288172368739/100000000000000 : ℝ)^6211 := by
    have hnat : (4372689347 : ℕ)^8259*100000000000000^6211 ≤ 33288172368739^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4372689347 10000000000 33288172368739 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208442647/500000000 : ℝ)^8259 ≤ (6248154540069/20000000000000 : ℝ)^6211 := by
    have hnat : (208442647 : ℕ)^8259*20000000000000^6211 ≤ 6248154540069^6211*500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208442647 500000000 6248154540069 20000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (573327397/1250000000 : ℝ)^8259 ≤ (35471054918689/100000000000000 : ℝ)^6211 := by
    have hnat : (573327397 : ℕ)^8259*100000000000000^6211 ≤ 35471054918689^6211*1250000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      573327397 1250000000 35471054918689 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4372689347/10000000000 : ℝ), (208442647/500000000 : ℝ), (573327397/1250000000 : ℝ)] ![(33288172368739/100000000000000 : ℝ), (6248154540069/20000000000000 : ℝ), (35471054918689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4372689347/10000000000 : ℝ)|^8259 ≤ (33288172368739/100000000000000 : ℝ)^6211
        have hw : |(4372689347/10000000000 : ℝ)|=(4372689347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(208442647/500000000 : ℝ)|^8259 ≤ (6248154540069/20000000000000 : ℝ)^6211
        have hw : |(208442647/500000000 : ℝ)|=(208442647/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(573327397/1250000000 : ℝ)|^8259 ≤ (35471054918689/100000000000000 : ℝ)^6211
        have hw : |(573327397/1250000000 : ℝ)|=(573327397/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s3_4 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-549762441/2500000000 : ℝ)*x 0 + (1306311899/2500000000 : ℝ)*x 1 + (5436657249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (549762441/2500000000 : ℝ)^8259 ≤ (13345819557949/100000000000000 : ℝ)^6211 := by
    have hnat : (549762441 : ℕ)^8259*100000000000000^6211 ≤ 13345819557949^6211*2500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549762441 2500000000 13345819557949 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1306311899/2500000000 : ℝ)^8259 ≤ (8436962476873/20000000000000 : ℝ)^6211 := by
    have hnat : (1306311899 : ℕ)^8259*20000000000000^6211 ≤ 8436962476873^6211*2500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306311899 2500000000 8436962476873 20000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5436657249/10000000000 : ℝ)^8259 ≤ (44469368041037/100000000000000 : ℝ)^6211 := by
    have hnat : (5436657249 : ℕ)^8259*100000000000000^6211 ≤ 44469368041037^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436657249 10000000000 44469368041037 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-549762441/2500000000 : ℝ), (1306311899/2500000000 : ℝ), (5436657249/10000000000 : ℝ)] ![(13345819557949/100000000000000 : ℝ), (8436962476873/20000000000000 : ℝ), (44469368041037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-549762441/2500000000 : ℝ)|^8259 ≤ (13345819557949/100000000000000 : ℝ)^6211
        have hw : |(-549762441/2500000000 : ℝ)|=(549762441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1306311899/2500000000 : ℝ)|^8259 ≤ (8436962476873/20000000000000 : ℝ)^6211
        have hw : |(1306311899/2500000000 : ℝ)|=(1306311899/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5436657249/10000000000 : ℝ)|^8259 ≤ (44469368041037/100000000000000 : ℝ)^6211
        have hw : |(5436657249/10000000000 : ℝ)|=(5436657249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s3_5 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (132549923/250000000 : ℝ)*x 0 + (-2095900757/10000000000 : ℝ)*x 1 + (5436656661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132549923/250000000 : ℝ)^8259 ≤ (10752682508397/25000000000000 : ℝ)^6211 := by
    have hnat : (132549923 : ℕ)^8259*25000000000000^6211 ≤ 10752682508397^6211*250000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132549923 250000000 10752682508397 25000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2095900757/10000000000 : ℝ)^8259 ≤ (12519908305529/100000000000000 : ℝ)^6211 := by
    have hnat : (2095900757 : ℕ)^8259*100000000000000^6211 ≤ 12519908305529^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095900757 10000000000 12519908305529 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5436656661/10000000000 : ℝ)^8259 ≤ (4446936164557/10000000000000 : ℝ)^6211 := by
    have hnat : (5436656661 : ℕ)^8259*10000000000000^6211 ≤ 4446936164557^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436656661 10000000000 4446936164557 10000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132549923/250000000 : ℝ), (-2095900757/10000000000 : ℝ), (5436656661/10000000000 : ℝ)] ![(10752682508397/25000000000000 : ℝ), (12519908305529/100000000000000 : ℝ), (4446936164557/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132549923/250000000 : ℝ)|^8259 ≤ (10752682508397/25000000000000 : ℝ)^6211
        have hw : |(132549923/250000000 : ℝ)|=(132549923/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2095900757/10000000000 : ℝ)|^8259 ≤ (12519908305529/100000000000000 : ℝ)^6211
        have hw : |(-2095900757/10000000000 : ℝ)|=(2095900757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5436656661/10000000000 : ℝ)|^8259 ≤ (4446936164557/10000000000000 : ℝ)^6211
        have hw : |(5436656661/10000000000 : ℝ)|=(5436656661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s3_6 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5301996681/10000000000 : ℝ)*x 0 + (679582133/1250000000 : ℝ)*x 1 + (-209590053/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301996681/10000000000 : ℝ)^8259 ≤ (43010727455479/100000000000000 : ℝ)^6211 := by
    have hnat : (5301996681 : ℕ)^8259*100000000000000^6211 ≤ 43010727455479^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301996681 10000000000 43010727455479 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (679582133/1250000000 : ℝ)^8259 ≤ (44469366028857/100000000000000 : ℝ)^6211 := by
    have hnat : (679582133 : ℕ)^8259*100000000000000^6211 ≤ 44469366028857^6211*1250000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679582133 1250000000 44469366028857 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209590053/1000000000 : ℝ)^8259 ≤ (12519906502419/100000000000000 : ℝ)^6211 := by
    have hnat : (209590053 : ℕ)^8259*100000000000000^6211 ≤ 12519906502419^6211*1000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209590053 1000000000 12519906502419 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301996681/10000000000 : ℝ), (679582133/1250000000 : ℝ), (-209590053/1000000000 : ℝ)] ![(43010727455479/100000000000000 : ℝ), (44469366028857/100000000000000 : ℝ), (12519906502419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301996681/10000000000 : ℝ)|^8259 ≤ (43010727455479/100000000000000 : ℝ)^6211
        have hw : |(5301996681/10000000000 : ℝ)|=(5301996681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(679582133/1250000000 : ℝ)|^8259 ≤ (44469366028857/100000000000000 : ℝ)^6211
        have hw : |(679582133/1250000000 : ℝ)|=(679582133/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-209590053/1000000000 : ℝ)|^8259 ≤ (12519906502419/100000000000000 : ℝ)^6211
        have hw : |(-209590053/1000000000 : ℝ)|=(209590053/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s3_7 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4372733101/10000000000 : ℝ)*x 0 + (286556687/625000000 : ℝ)*x 1 + (2085287613/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4372733101/10000000000 : ℝ)^8259 ≤ (83221538223/250000000000 : ℝ)^6211 := by
    have hnat : (4372733101 : ℕ)^8259*250000000000^6211 ≤ 83221538223^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4372733101 10000000000 83221538223 250000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (286556687/625000000 : ℝ)^8259 ≤ (35453448498533/100000000000000 : ℝ)^6211 := by
    have hnat : (286556687 : ℕ)^8259*100000000000000^6211 ≤ 35453448498533^6211*625000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      286556687 625000000 35453448498533 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2085287613/5000000000 : ℝ)^8259 ≤ (15628968102599/50000000000000 : ℝ)^6211 := by
    have hnat : (2085287613 : ℕ)^8259*50000000000000^6211 ≤ 15628968102599^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085287613 5000000000 15628968102599 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4372733101/10000000000 : ℝ), (286556687/625000000 : ℝ), (2085287613/5000000000 : ℝ)] ![(83221538223/250000000000 : ℝ), (35453448498533/100000000000000 : ℝ), (15628968102599/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4372733101/10000000000 : ℝ)|^8259 ≤ (83221538223/250000000000 : ℝ)^6211
        have hw : |(4372733101/10000000000 : ℝ)|=(4372733101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(286556687/625000000 : ℝ)|^8259 ≤ (35453448498533/100000000000000 : ℝ)^6211
        have hw : |(286556687/625000000 : ℝ)|=(286556687/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2085287613/5000000000 : ℝ)|^8259 ≤ (15628968102599/50000000000000 : ℝ)^6211
        have hw : |(2085287613/5000000000 : ℝ)|=(2085287613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1066_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73996519/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16741/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1089/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (2599/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7453/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16741/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1089/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16741/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1089/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16741/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1089/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16741/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1089/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16741/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1089/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16741/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1089/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1089/12500 : ℝ) ^ (4129/1024 : ℝ) ≤ (5324944788668013/100000000000000000000 : ℝ) := by
    have hpowers : (1089/12500 : ℝ)^4129 ≤ (5324944788668013/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1089 : ℕ)^4129*100000000000000000000^1024 ≤ 5324944788668013^1024*12500^4129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1089 12500 5324944788668013 100000000000000000000 4129 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1089/12500 : ℝ)) (X := (5324944788668013/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16741/100000 : ℝ) ^ (4129/1024 : ℝ) ≤ (74149927077077911/100000000000000000000 : ℝ) := by
    have hpowers : (16741/100000 : ℝ)^4129 ≤ (74149927077077911/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16741 : ℕ)^4129*100000000000000000000^1024 ≤ 74149927077077911^1024*100000^4129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16741 100000 74149927077077911 100000000000000000000 4129 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16741/100000 : ℝ)) (X := (74149927077077911/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005324944788668013/50000000000000000000 : ℝ) ≤ (10000264108749351/10000000000000000 : ℝ) ^ (4129/1024 : ℝ) := by
    have hpowers : (50005324944788668013/50000000000000000000 : ℝ)^1024 ≤ (10000264108749351/10000000000000000 : ℝ)^4129 := by
      have hnat : (50005324944788668013 : ℕ)^1024*10000000000000000^4129 ≤ 10000264108749351^4129*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005324944788668013 50000000000000000000 10000264108749351 10000000000000000 1024 4129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000264108749351/10000000000000000 : ℝ)) (X := (50005324944788668013/50000000000000000000 : ℝ)) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25019868717966436481/25000000000000000000 : ℝ) ≤ (1000197040351261/1000000000000000 : ℝ) ^ (4129/1024 : ℝ) := by
    have hpowers : (25019868717966436481/25000000000000000000 : ℝ)^1024 ≤ (1000197040351261/1000000000000000 : ℝ)^4129 := by
      have hnat : (25019868717966436481 : ℕ)^1024*1000000000000000^4129 ≤ 1000197040351261^4129*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25019868717966436481 25000000000000000000 1000197040351261 1000000000000000 1024 4129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000197040351261/1000000000000000 : ℝ)) (X := (25019868717966436481/25000000000000000000 : ℝ)) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50074149927077077911/50000000000000000000 : ℝ) ≤ (10003676698275869/10000000000000000 : ℝ) ^ (4129/1024 : ℝ) := by
    have hpowers : (50074149927077077911/50000000000000000000 : ℝ)^1024 ≤ (10003676698275869/10000000000000000 : ℝ)^4129 := by
      have hnat : (50074149927077077911 : ℕ)^1024*10000000000000000^4129 ≤ 10003676698275869^4129*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50074149927077077911 50000000000000000000 10003676698275869 10000000000000000 1024 4129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003676698275869/10000000000000000 : ℝ)) (X := (50074149927077077911/50000000000000000000 : ℝ)) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5324944788668013/100000000000000000000 : ℝ) ≤ ((80262390049193514363/80290000000000000000 : ℝ)+2*(1706294763259/802900000000000 : ℝ)*(1089/12500 : ℝ))^(4129/1024 : ℝ) := by
    rw [show (80262390049193514363/80290000000000000000 : ℝ)+2*(1706294763259/802900000000000 : ℝ)*(1089/12500 : ℝ)=(10000264108749351/10000000000000000 : ℝ) by norm_num, show 1+2*(5324944788668013/100000000000000000000 : ℝ)=(50005324944788668013/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(74149927077077911/100000000000000000000 : ℝ)+(5324944788668013/100000000000000000000 : ℝ) ≤ ((80262390049193514363/80290000000000000000 : ℝ)+(1706294763259/802900000000000 : ℝ)*((16741/100000 : ℝ)+(1089/12500 : ℝ)))^(4129/1024 : ℝ) := by
    rw [show (80262390049193514363/80290000000000000000 : ℝ)+(1706294763259/802900000000000 : ℝ)*((16741/100000 : ℝ)+(1089/12500 : ℝ))=(1000197040351261/1000000000000000 : ℝ) by norm_num, show 1+(74149927077077911/100000000000000000000 : ℝ)+(5324944788668013/100000000000000000000 : ℝ)=(25019868717966436481/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(74149927077077911/100000000000000000000 : ℝ) ≤ ((80262390049193514363/80290000000000000000 : ℝ)+2*(1706294763259/802900000000000 : ℝ)*(16741/100000 : ℝ))^(4129/1024 : ℝ) := by
    rw [show (80262390049193514363/80290000000000000000 : ℝ)+2*(1706294763259/802900000000000 : ℝ)*(16741/100000 : ℝ)=(10003676698275869/10000000000000000 : ℝ) by norm_num, show 1+2*(74149927077077911/100000000000000000000 : ℝ)=(50074149927077077911/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (80262390049193514363/80290000000000000000 : ℝ)*(X 1 0+X 2 0)+(1706294763259/802900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4129/1024 : ℝ)) (lo := (1089/12500 : ℝ)) (hi := (16741/100000 : ℝ)) (c := (80262390049193514363/80290000000000000000 : ℝ)) (alpha := (1706294763259/802900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (80262390049193514363/80290000000000000000 : ℝ)*(X 0 1+X 2 1)+(1706294763259/802900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4129/1024 : ℝ)) (lo := (1089/12500 : ℝ)) (hi := (16741/100000 : ℝ)) (c := (80262390049193514363/80290000000000000000 : ℝ)) (alpha := (1706294763259/802900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (80262390049193514363/80290000000000000000 : ℝ)*(X 0 2+X 1 2)+(1706294763259/802900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4129/1024 : ℝ)) (lo := (1089/12500 : ℝ)) (hi := (16741/100000 : ℝ)) (c := (80262390049193514363/80290000000000000000 : ℝ)) (alpha := (1706294763259/802900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-219902749/1000000000 : ℝ)*X 0 0+(339845959/625000000 : ℝ)*X 0 1+(2612187319/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5355691619/10000000000 : ℝ)*X 1 0+(-2308182853/10000000000 : ℝ)*X 1 1+(2612187281/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((167365361/312500000 : ℝ)*X 2 0+(2612187199/5000000000 : ℝ)*X 2 1+(-1154091577/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4372689347/10000000000 : ℝ)*X 0 0+(208442647/500000000 : ℝ)*X 0 1+(573327397/1250000000 : ℝ)*X 0 2+(4372689347/10000000000 : ℝ)*X 1 0+(208442647/500000000 : ℝ)*X 1 1+(573327397/1250000000 : ℝ)*X 1 2+(4372689347/10000000000 : ℝ)*X 2 0+(208442647/500000000 : ℝ)*X 2 1+(573327397/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-549762441/2500000000 : ℝ)*X 0 0+(1306311899/2500000000 : ℝ)*X 0 1+(5436657249/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((132549923/250000000 : ℝ)*X 1 0+(-2095900757/10000000000 : ℝ)*X 1 1+(5436656661/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5301996681/10000000000 : ℝ)*X 2 0+(679582133/1250000000 : ℝ)*X 2 1+(-209590053/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4372733101/10000000000 : ℝ)*X 0 0+(286556687/625000000 : ℝ)*X 0 1+(2085287613/5000000000 : ℝ)*X 0 2+(4372733101/10000000000 : ℝ)*X 1 0+(286556687/625000000 : ℝ)*X 1 1+(2085287613/5000000000 : ℝ)*X 1 2+(4372733101/10000000000 : ℝ)*X 2 0+(286556687/625000000 : ℝ)*X 2 1+(2085287613/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11777830577837990001575948187/2007250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (570679749/50000000000000 : ℝ)*(base19) + (44660491/4000000000000 : ℝ)*(base23) + (18669307/100000000000000 : ℝ)*(upper2) + (140864873/50000000000000 : ℝ)*(upper3) + (1771257757021239/50000000000000 : ℝ)*(major0) + (1771257757021239/50000000000000 : ℝ)*(major1) + (1771257757021239/50000000000000 : ℝ)*(major2) + (469131594217531/10000000000000 : ℝ)*(sp0) + (2345662763228629/50000000000000 : ℝ)*(sp1) + (4691325449836113/100000000000000 : ℝ)*(sp2) + (2393691968553623/100000000000000 : ℝ)*(sp3) + (5362820723/50000000000000 : ℝ)*(sp4) + (6341773/6250000000000 : ℝ)*(sp6) + (1524515799/12500000000000 : ℝ)*(sp7) + (149606510292501/6250000000000 : ℝ)*(f.failure) + (4691326667816757/100000000000000 : ℝ)*(f.sum) + (67917356112097/40145000000000000000000000000 : ℝ)*base65 + (47074957414002655757/4014500000000000000000000000000000 : ℝ)*base67 + (56061358923059655757/4014500000000000000000000000000000 : ℝ)*base69 + (46265146311745155757/4014500000000000000000000000000000 : ℝ)*base71 + (2816818298919/5018125000000000000000000000 : ℝ)*base73 + (76170225628210655757/4014500000000000000000000000000000 : ℝ)*base75 + (81958935826156155757/4014500000000000000000000000000000 : ℝ)*base77 + (38748217725987655757/4014500000000000000000000000000000 : ℝ)*base79 + (30880562261273/10036250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2054019/312500000000000000000 : ℝ)*base89 + (2054019/312500000000000000000 : ℝ)*base91 + (2054019/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7958554811140195135545815631/1003625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (389969643/25000000000000 : ℝ)*(base19) + (1352329419/100000000000000 : ℝ)*(base23) + (624781/50000000000000 : ℝ)*(upper3) + (10028423/50000000000000 : ℝ)*(lower4) + (176487919/50000000000000 : ℝ)*(upper5) + (892960206609479/25000000000000 : ℝ)*(major0) + (892960206609479/25000000000000 : ℝ)*(major1) + (892960206609479/25000000000000 : ℝ)*(major2) + (10185575511/50000000000000 : ℝ)*(sp1) + (1719601397/10000000000000 : ℝ)*(sp2) + (4730161891477701/100000000000000 : ℝ)*(sp4) + (1182534990112027/25000000000000 : ℝ)*(sp5) + (591267917891789/12500000000000 : ℝ)*(sp6) + (48270389941423/2000000000000 : ℝ)*(sp7) + (48270389941423/2000000000000 : ℝ)*(f.failure) + (4730161891477701/100000000000000 : ℝ)*(f.sum) + (56708463265863/20072500000000000000000000000 : ℝ)*base66 + (10182189196353546877/2007250000000000000000000000000000 : ℝ)*base67 + (7084369711830703123/2007250000000000000000000000000000 : ℝ)*base70 + (32073455319003453123/2007250000000000000000000000000000 : ℝ)*base72 + (13055242901467/20072500000000000000000000000 : ℝ)*base73 + (20140674204447546877/2007250000000000000000000000000000 : ℝ)*base75 + (2405673924524953123/2007250000000000000000000000000000 : ℝ)*base78 + (1291378726078453123/2007250000000000000000000000000000 : ℝ)*base80 + (45444556032489/10036250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (93463/100000000000000000000 : ℝ)*base90 + (93463/100000000000000000000 : ℝ)*base92 + (93463/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1066_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73996519/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16741/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1089/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2599/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7453/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1066_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1066_s4_0 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2202705963/10000000000 : ℝ)*x 0 + (337863499/625000000 : ℝ)*x 1 + (5253690877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2202705963/10000000000 : ℝ)^8259 ≤ (13375333345031/100000000000000 : ℝ)^6211 := by
    have hnat : (2202705963 : ℕ)^8259*100000000000000^6211 ≤ 13375333345031^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2202705963 10000000000 13375333345031 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337863499/625000000 : ℝ)^8259 ≤ (22067116348121/50000000000000 : ℝ)^6211 := by
    have hnat : (337863499 : ℕ)^8259*50000000000000^6211 ≤ 22067116348121^6211*625000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337863499 625000000 22067116348121 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5253690877/10000000000 : ℝ)^8259 ≤ (42490433944017/100000000000000 : ℝ)^6211 := by
    have hnat : (5253690877 : ℕ)^8259*100000000000000^6211 ≤ 42490433944017^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253690877 10000000000 42490433944017 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2202705963/10000000000 : ℝ), (337863499/625000000 : ℝ), (5253690877/10000000000 : ℝ)] ![(13375333345031/100000000000000 : ℝ), (22067116348121/50000000000000 : ℝ), (42490433944017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2202705963/10000000000 : ℝ)|^8259 ≤ (13375333345031/100000000000000 : ℝ)^6211
        have hw : |(-2202705963/10000000000 : ℝ)|=(2202705963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337863499/625000000 : ℝ)|^8259 ≤ (22067116348121/50000000000000 : ℝ)^6211
        have hw : |(337863499/625000000 : ℝ)|=(337863499/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5253690877/10000000000 : ℝ)|^8259 ≤ (42490433944017/100000000000000 : ℝ)^6211
        have hw : |(5253690877/10000000000 : ℝ)|=(5253690877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s4_1 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5347833903/10000000000 : ℝ)*x 0 + (-2280081053/10000000000 : ℝ)*x 1 + (5253690847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347833903/10000000000 : ℝ)^8259 ≤ (43505879922861/100000000000000 : ℝ)^6211 := by
    have hnat : (5347833903 : ℕ)^8259*100000000000000^6211 ≤ 43505879922861^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347833903 10000000000 43505879922861 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2280081053/10000000000 : ℝ)^8259 ≤ (560147457823/4000000000000 : ℝ)^6211 := by
    have hnat : (2280081053 : ℕ)^8259*4000000000000^6211 ≤ 560147457823^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2280081053 10000000000 560147457823 4000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5253690847/10000000000 : ℝ)^8259 ≤ (42490433621381/100000000000000 : ℝ)^6211 := by
    have hnat : (5253690847 : ℕ)^8259*100000000000000^6211 ≤ 42490433621381^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253690847 10000000000 42490433621381 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347833903/10000000000 : ℝ), (-2280081053/10000000000 : ℝ), (5253690847/10000000000 : ℝ)] ![(43505879922861/100000000000000 : ℝ), (560147457823/4000000000000 : ℝ), (42490433621381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347833903/10000000000 : ℝ)|^8259 ≤ (43505879922861/100000000000000 : ℝ)^6211
        have hw : |(5347833903/10000000000 : ℝ)|=(5347833903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2280081053/10000000000 : ℝ)|^8259 ≤ (560147457823/4000000000000 : ℝ)^6211
        have hw : |(-2280081053/10000000000 : ℝ)|=(2280081053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5253690847/10000000000 : ℝ)|^8259 ≤ (42490433621381/100000000000000 : ℝ)^6211
        have hw : |(5253690847/10000000000 : ℝ)|=(5253690847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s4_2 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5347833997/10000000000 : ℝ)*x 0 + (1313422701/2500000000 : ℝ)*x 1 + (-456016197/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347833997/10000000000 : ℝ)^8259 ≤ (43505880939727/100000000000000 : ℝ)^6211 := by
    have hnat : (5347833997 : ℕ)^8259*100000000000000^6211 ≤ 43505880939727^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347833997 10000000000 43505880939727 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1313422701/2500000000 : ℝ)^8259 ≤ (8498086631787/20000000000000 : ℝ)^6211 := by
    have hnat : (1313422701 : ℕ)^8259*20000000000000^6211 ≤ 8498086631787^6211*2500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313422701 2500000000 8498086631787 20000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (456016197/2000000000 : ℝ)^8259 ≤ (560147435609/4000000000000 : ℝ)^6211 := by
    have hnat : (456016197 : ℕ)^8259*4000000000000^6211 ≤ 560147435609^6211*2000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456016197 2000000000 560147435609 4000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347833997/10000000000 : ℝ), (1313422701/2500000000 : ℝ), (-456016197/2000000000 : ℝ)] ![(43505880939727/100000000000000 : ℝ), (8498086631787/20000000000000 : ℝ), (560147435609/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347833997/10000000000 : ℝ)|^8259 ≤ (43505880939727/100000000000000 : ℝ)^6211
        have hw : |(5347833997/10000000000 : ℝ)|=(5347833997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1313422701/2500000000 : ℝ)|^8259 ≤ (8498086631787/20000000000000 : ℝ)^6211
        have hw : |(1313422701/2500000000 : ℝ)|=(1313422701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-456016197/2000000000 : ℝ)|^8259 ≤ (560147435609/4000000000000 : ℝ)^6211
        have hw : |(-456016197/2000000000 : ℝ)|=(456016197/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s4_3 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2187438561/5000000000 : ℝ)*x 0 + (1057094243/2500000000 : ℝ)*x 1 + (2263260533/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187438561/5000000000 : ℝ)^8259 ≤ (33310320941103/100000000000000 : ℝ)^6211 := by
    have hnat : (2187438561 : ℕ)^8259*100000000000000^6211 ≤ 33310320941103^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187438561 5000000000 33310320941103 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1057094243/2500000000 : ℝ)^8259 ≤ (3979414139371/12500000000000 : ℝ)^6211 := by
    have hnat : (1057094243 : ℕ)^8259*12500000000000^6211 ≤ 3979414139371^6211*2500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057094243 2500000000 3979414139371 12500000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2263260533/5000000000 : ℝ)^8259 ≤ (34854365920287/100000000000000 : ℝ)^6211 := by
    have hnat : (2263260533 : ℕ)^8259*100000000000000^6211 ≤ 34854365920287^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2263260533 5000000000 34854365920287 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2187438561/5000000000 : ℝ), (1057094243/2500000000 : ℝ), (2263260533/5000000000 : ℝ)] ![(33310320941103/100000000000000 : ℝ), (3979414139371/12500000000000 : ℝ), (34854365920287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2187438561/5000000000 : ℝ)|^8259 ≤ (33310320941103/100000000000000 : ℝ)^6211
        have hw : |(2187438561/5000000000 : ℝ)|=(2187438561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1057094243/2500000000 : ℝ)|^8259 ≤ (3979414139371/12500000000000 : ℝ)^6211
        have hw : |(1057094243/2500000000 : ℝ)|=(1057094243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2263260533/5000000000 : ℝ)|^8259 ≤ (34854365920287/100000000000000 : ℝ)^6211
        have hw : |(2263260533/5000000000 : ℝ)|=(2263260533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s4_4 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2202714349/10000000000 : ℝ)*x 0 + (5254136661/10000000000 : ℝ)*x 1 + (5405368127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2202714349/10000000000 : ℝ)^8259 ≤ (13375401057579/100000000000000 : ℝ)^6211 := by
    have hnat : (2202714349 : ℕ)^8259*100000000000000^6211 ≤ 13375401057579^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2202714349 10000000000 13375401057579 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5254136661/10000000000 : ℝ)^8259 ≤ (21247614110603/50000000000000 : ℝ)^6211 := by
    have hnat : (5254136661 : ℕ)^8259*50000000000000^6211 ≤ 21247614110603^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254136661 10000000000 21247614110603 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5405368127/10000000000 : ℝ)^8259 ≤ (44129370710357/100000000000000 : ℝ)^6211 := by
    have hnat : (5405368127 : ℕ)^8259*100000000000000^6211 ≤ 44129370710357^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405368127 10000000000 44129370710357 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2202714349/10000000000 : ℝ), (5254136661/10000000000 : ℝ), (5405368127/10000000000 : ℝ)] ![(13375401057579/100000000000000 : ℝ), (21247614110603/50000000000000 : ℝ), (44129370710357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2202714349/10000000000 : ℝ)|^8259 ≤ (13375401057579/100000000000000 : ℝ)^6211
        have hw : |(-2202714349/10000000000 : ℝ)|=(2202714349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5254136661/10000000000 : ℝ)|^8259 ≤ (21247614110603/50000000000000 : ℝ)^6211
        have hw : |(5254136661/10000000000 : ℝ)|=(5254136661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5405368127/10000000000 : ℝ)|^8259 ≤ (44129370710357/100000000000000 : ℝ)^6211
        have hw : |(5405368127/10000000000 : ℝ)|=(5405368127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s4_5 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2654759661/5000000000 : ℝ)*x 0 + (-425680567/2000000000 : ℝ)*x 1 + (5405367989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2654759661/5000000000 : ℝ)^8259 ≤ (1346621676399/3125000000000 : ℝ)^6211 := by
    have hnat : (2654759661 : ℕ)^8259*3125000000000^6211 ≤ 1346621676399^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2654759661 5000000000 1346621676399 3125000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (425680567/2000000000 : ℝ)^8259 ≤ (1277873712257/10000000000000 : ℝ)^6211 := by
    have hnat : (425680567 : ℕ)^8259*10000000000000^6211 ≤ 1277873712257^6211*2000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425680567 2000000000 1277873712257 10000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5405367989/10000000000 : ℝ)^8259 ≤ (22064684606117/50000000000000 : ℝ)^6211 := by
    have hnat : (5405367989 : ℕ)^8259*50000000000000^6211 ≤ 22064684606117^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405367989 10000000000 22064684606117 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2654759661/5000000000 : ℝ), (-425680567/2000000000 : ℝ), (5405367989/10000000000 : ℝ)] ![(1346621676399/3125000000000 : ℝ), (1277873712257/10000000000000 : ℝ), (22064684606117/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2654759661/5000000000 : ℝ)|^8259 ≤ (1346621676399/3125000000000 : ℝ)^6211
        have hw : |(2654759661/5000000000 : ℝ)|=(2654759661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-425680567/2000000000 : ℝ)|^8259 ≤ (1277873712257/10000000000000 : ℝ)^6211
        have hw : |(-425680567/2000000000 : ℝ)|=(425680567/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5405367989/10000000000 : ℝ)|^8259 ≤ (22064684606117/50000000000000 : ℝ)^6211
        have hw : |(5405367989/10000000000 : ℝ)|=(5405367989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s4_6 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5309518707/10000000000 : ℝ)*x 0 + (5405368109/10000000000 : ℝ)*x 1 + (-133025219/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309518707/10000000000 : ℝ)^8259 ≤ (21545943503811/50000000000000 : ℝ)^6211 := by
    have hnat : (5309518707 : ℕ)^8259*50000000000000^6211 ≤ 21545943503811^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309518707 10000000000 21545943503811 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5405368109/10000000000 : ℝ)^8259 ≤ (44129370514949/100000000000000 : ℝ)^6211 := by
    have hnat : (5405368109 : ℕ)^8259*100000000000000^6211 ≤ 44129370514949^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405368109 10000000000 44129370514949 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (133025219/625000000 : ℝ)^8259 ≤ (6389371231807/50000000000000 : ℝ)^6211 := by
    have hnat : (133025219 : ℕ)^8259*50000000000000^6211 ≤ 6389371231807^6211*625000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133025219 625000000 6389371231807 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309518707/10000000000 : ℝ), (5405368109/10000000000 : ℝ), (-133025219/625000000 : ℝ)] ![(21545943503811/50000000000000 : ℝ), (44129370514949/100000000000000 : ℝ), (6389371231807/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309518707/10000000000 : ℝ)|^8259 ≤ (21545943503811/50000000000000 : ℝ)^6211
        have hw : |(5309518707/10000000000 : ℝ)|=(5309518707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5405368109/10000000000 : ℝ)|^8259 ≤ (44129370514949/100000000000000 : ℝ)^6211
        have hw : |(5405368109/10000000000 : ℝ)|=(5405368109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-133025219/625000000 : ℝ)|^8259 ≤ (6389371231807/50000000000000 : ℝ)^6211
        have hw : |(-133025219/625000000 : ℝ)|=(133025219/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s4_7 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (874978537/2000000000 : ℝ)*x 0 + (2262823627/5000000000 : ℝ)*x 1 + (2114627421/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (874978537/2000000000 : ℝ)^8259 ≤ (8327619627679/25000000000000 : ℝ)^6211 := by
    have hnat : (874978537 : ℕ)^8259*25000000000000^6211 ≤ 8327619627679^6211*2000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874978537 2000000000 8327619627679 25000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2262823627/5000000000 : ℝ)^8259 ≤ (8711354805669/25000000000000 : ℝ)^6211 := by
    have hnat : (2262823627 : ℕ)^8259*25000000000000^6211 ≤ 8711354805669^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262823627 5000000000 8711354805669 25000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2114627421/5000000000 : ℝ)^8259 ≤ (6368820451211/20000000000000 : ℝ)^6211 := by
    have hnat : (2114627421 : ℕ)^8259*20000000000000^6211 ≤ 6368820451211^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114627421 5000000000 6368820451211 20000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(874978537/2000000000 : ℝ), (2262823627/5000000000 : ℝ), (2114627421/5000000000 : ℝ)] ![(8327619627679/25000000000000 : ℝ), (8711354805669/25000000000000 : ℝ), (6368820451211/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(874978537/2000000000 : ℝ)|^8259 ≤ (8327619627679/25000000000000 : ℝ)^6211
        have hw : |(874978537/2000000000 : ℝ)|=(874978537/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2262823627/5000000000 : ℝ)|^8259 ≤ (8711354805669/25000000000000 : ℝ)^6211
        have hw : |(2262823627/5000000000 : ℝ)|=(2262823627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2114627421/5000000000 : ℝ)|^8259 ≤ (6368820451211/20000000000000 : ℝ)^6211
        have hw : |(2114627421/5000000000 : ℝ)|=(2114627421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1066_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73996519/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7453/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2599/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5511/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14243/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7453/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2599/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7453/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2599/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7453/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2599/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7453/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2599/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7453/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2599/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7453/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2599/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2599/25000 : ℝ) ^ (4129/1024 : ℝ) ≤ (5429402856455391/50000000000000000000 : ℝ) := by
    have hpowers : (2599/25000 : ℝ)^4129 ≤ (5429402856455391/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2599 : ℕ)^4129*50000000000000000000^1024 ≤ 5429402856455391^1024*25000^4129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2599 25000 5429402856455391 50000000000000000000 4129 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2599/25000 : ℝ)) (X := (5429402856455391/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7453/50000 : ℝ) ^ (4129/1024 : ℝ) ≤ (928612945232523/2000000000000000000 : ℝ) := by
    have hpowers : (7453/50000 : ℝ)^4129 ≤ (928612945232523/2000000000000000000 : ℝ)^1024 := by
      have hnat : (7453 : ℕ)^4129*2000000000000000000^1024 ≤ 928612945232523^1024*50000^4129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7453 50000 928612945232523 2000000000000000000 4129 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7453/50000 : ℝ)) (X := (928612945232523/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005429402856455391/25000000000000000000 : ℝ) ≤ (2500134639248919/2500000000000000 : ℝ) ^ (4129/1024 : ℝ) := by
    have hpowers : (25005429402856455391/25000000000000000000 : ℝ)^1024 ≤ (2500134639248919/2500000000000000 : ℝ)^4129 := by
      have hnat : (25005429402856455391 : ℕ)^1024*2500000000000000^4129 ≤ 2500134639248919^4129*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005429402856455391 25000000000000000000 2500134639248919 2500000000000000 1024 4129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500134639248919/2500000000000000 : ℝ)) (X := (25005429402856455391/25000000000000000000 : ℝ)) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25014322363243634233/25000000000000000000 : ℝ) ≤ (10001420483586911/10000000000000000 : ℝ) ^ (4129/1024 : ℝ) := by
    have hpowers : (25014322363243634233/25000000000000000000 : ℝ)^1024 ≤ (10001420483586911/10000000000000000 : ℝ)^4129 := by
      have hnat : (25014322363243634233 : ℕ)^1024*10000000000000000^4129 ≤ 10001420483586911^4129*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014322363243634233 25000000000000000000 10001420483586911 10000000000000000 1024 4129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001420483586911/10000000000000000 : ℝ)) (X := (25014322363243634233/25000000000000000000 : ℝ)) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1000928612945232523/1000000000000000000 : ℝ) ≤ (5001151205089073/5000000000000000 : ℝ) ^ (4129/1024 : ℝ) := by
    have hpowers : (1000928612945232523/1000000000000000000 : ℝ)^1024 ≤ (5001151205089073/5000000000000000 : ℝ)^4129 := by
      have hnat : (1000928612945232523 : ℕ)^1024*5000000000000000^4129 ≤ 5001151205089073^4129*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000928612945232523 1000000000000000000 5001151205089073 5000000000000000 1024 4129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001151205089073/5000000000000000 : ℝ)) (X := (1000928612945232523/1000000000000000000 : ℝ)) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5429402856455391/50000000000000000000 : ℝ) ≤ ((281775574214784629/281875000000000000 : ℝ)+2*(176385318247/90200000000000 : ℝ)*(2599/25000 : ℝ))^(4129/1024 : ℝ) := by
    rw [show (281775574214784629/281875000000000000 : ℝ)+2*(176385318247/90200000000000 : ℝ)*(2599/25000 : ℝ)=(2500134639248919/2500000000000000 : ℝ) by norm_num, show 1+2*(5429402856455391/50000000000000000000 : ℝ)=(25005429402856455391/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(928612945232523/2000000000000000000 : ℝ)+(5429402856455391/50000000000000000000 : ℝ) ≤ ((281775574214784629/281875000000000000 : ℝ)+(176385318247/90200000000000 : ℝ)*((7453/50000 : ℝ)+(2599/25000 : ℝ)))^(4129/1024 : ℝ) := by
    rw [show (281775574214784629/281875000000000000 : ℝ)+(176385318247/90200000000000 : ℝ)*((7453/50000 : ℝ)+(2599/25000 : ℝ))=(10001420483586911/10000000000000000 : ℝ) by norm_num, show 1+(928612945232523/2000000000000000000 : ℝ)+(5429402856455391/50000000000000000000 : ℝ)=(25014322363243634233/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(928612945232523/2000000000000000000 : ℝ) ≤ ((281775574214784629/281875000000000000 : ℝ)+2*(176385318247/90200000000000 : ℝ)*(7453/50000 : ℝ))^(4129/1024 : ℝ) := by
    rw [show (281775574214784629/281875000000000000 : ℝ)+2*(176385318247/90200000000000 : ℝ)*(7453/50000 : ℝ)=(5001151205089073/5000000000000000 : ℝ) by norm_num, show 1+2*(928612945232523/2000000000000000000 : ℝ)=(1000928612945232523/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (281775574214784629/281875000000000000 : ℝ)*(X 1 0+X 2 0)+(176385318247/90200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4129/1024 : ℝ)) (lo := (2599/25000 : ℝ)) (hi := (7453/50000 : ℝ)) (c := (281775574214784629/281875000000000000 : ℝ)) (alpha := (176385318247/90200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (281775574214784629/281875000000000000 : ℝ)*(X 0 1+X 2 1)+(176385318247/90200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4129/1024 : ℝ)) (lo := (2599/25000 : ℝ)) (hi := (7453/50000 : ℝ)) (c := (281775574214784629/281875000000000000 : ℝ)) (alpha := (176385318247/90200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (281775574214784629/281875000000000000 : ℝ)*(X 0 2+X 1 2)+(176385318247/90200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4129/1024 : ℝ)) (lo := (2599/25000 : ℝ)) (hi := (7453/50000 : ℝ)) (c := (281775574214784629/281875000000000000 : ℝ)) (alpha := (176385318247/90200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2202705963/10000000000 : ℝ)*X 0 0+(337863499/625000000 : ℝ)*X 0 1+(5253690877/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347833903/10000000000 : ℝ)*X 1 0+(-2280081053/10000000000 : ℝ)*X 1 1+(5253690847/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347833997/10000000000 : ℝ)*X 2 0+(1313422701/2500000000 : ℝ)*X 2 1+(-456016197/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2187438561/5000000000 : ℝ)*X 0 0+(1057094243/2500000000 : ℝ)*X 0 1+(2263260533/5000000000 : ℝ)*X 0 2+(2187438561/5000000000 : ℝ)*X 1 0+(1057094243/2500000000 : ℝ)*X 1 1+(2263260533/5000000000 : ℝ)*X 1 2+(2187438561/5000000000 : ℝ)*X 2 0+(1057094243/2500000000 : ℝ)*X 2 1+(2263260533/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2202714349/10000000000 : ℝ)*X 0 0+(5254136661/10000000000 : ℝ)*X 0 1+(5405368127/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2654759661/5000000000 : ℝ)*X 1 0+(-425680567/2000000000 : ℝ)*X 1 1+(5405367989/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5309518707/10000000000 : ℝ)*X 2 0+(5405368109/10000000000 : ℝ)*X 2 1+(-133025219/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((874978537/2000000000 : ℝ)*X 0 0+(2262823627/5000000000 : ℝ)*X 0 1+(2114627421/5000000000 : ℝ)*X 0 2+(874978537/2000000000 : ℝ)*X 1 0+(2262823627/5000000000 : ℝ)*X 1 1+(2114627421/5000000000 : ℝ)*X 1 2+(874978537/2000000000 : ℝ)*X 2 0+(2262823627/5000000000 : ℝ)*X 2 1+(2114627421/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2227655636882447604605631/320312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (228599539/20000000000000 : ℝ)*(base19) + (963191097/100000000000000 : ℝ)*(base23) + (78974633/50000000000000 : ℝ)*(lower2) + (20021563/12500000000000 : ℝ)*(upper3) + (50311917/100000000000000 : ℝ)*(upper5) + (2481923116720443/50000000000000 : ℝ)*(major0) + (2481923116720443/50000000000000 : ℝ)*(major1) + (2481923116720443/50000000000000 : ℝ)*(major2) + (1314712078335321/20000000000000 : ℝ)*(sp0) + (6573583155282289/100000000000000 : ℝ)*(sp1) + (6573583335088887/100000000000000 : ℝ)*(sp2) + (1677046729452523/50000000000000 : ℝ)*(sp3) + (23906603379/100000000000000 : ℝ)*(sp4) + (14477875661/100000000000000 : ℝ)*(sp7) + (1677053968390353/50000000000000 : ℝ)*(f.failure) + (410849018642499/6250000000000 : ℝ)*(f.sum) + (557483316111/51250000000000000000000000 : ℝ)*base66 + (5700161067991249/640625000000000000000000000000 : ℝ)*base68 + (34833625373833/5004882812500000000000000000 : ℝ)*base70 + (495809168975039/40039062500000000000000000000 : ℝ)*base72 + (643036006967/102500000000000000000000000 : ℝ)*base74 + (1460947448866249/640625000000000000000000000000 : ℝ)*base76 + (1064876294072031/160156250000000000000000000000 : ℝ)*base78 + (130022624840313/320312500000000000000000000000 : ℝ)*base79 + (467768622451/51250000000000000000000000 : ℝ)*base82 + (5181207/2500000000000000000000 : ℝ)*base89 + (5181207/2500000000000000000000 : ℝ)*base91 + (5181207/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2587717473220258011420393/1281250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2277037719/100000000000000 : ℝ)*(base19) + (406881433/25000000000000 : ℝ)*(base23) + (171992167/100000000000000 : ℝ)*(upper2) + (13847323/25000000000000 : ℝ)*(upper5) + (4993135328949977/100000000000000 : ℝ)*(major0) + (4993135328949977/100000000000000 : ℝ)*(major1) + (4993135328949977/100000000000000 : ℝ)*(major2) + (49057863/5000000000000 : ℝ)*(sp0) + (63941489041/100000000000000 : ℝ)*(sp1) + (17590639453/50000000000000 : ℝ)*(sp2) + (206636587883389/3125000000000 : ℝ)*(sp4) + (6612305574898947/100000000000000 : ℝ)*(sp5) + (6612334984621069/100000000000000 : ℝ)*(sp6) + (337389879715151/10000000000000 : ℝ)*(sp7) + (337389879715151/10000000000000 : ℝ)*(f.failure) + (6612371793425707/100000000000000 : ℝ)*(f.sum) + (1123612956649/410000000000000000000000000 : ℝ)*base65 + (2358282914261359/320312500000000000000000000000 : ℝ)*base68 + (4187880952917609/320312500000000000000000000000 : ℝ)*base70 + (2501262643992907/640625000000000000000000000000 : ℝ)*base71 + (883559595009/410000000000000000000000000 : ℝ)*base73 + (2594403355966617/160156250000000000000000000000 : ℝ)*base76 + (1054778893944593/640625000000000000000000000000 : ℝ)*base78 + (294621641913343/640625000000000000000000000000 : ℝ)*base80 + (505463904089/410000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (559369/500000000000000000000 : ℝ)*base89 + (559369/500000000000000000000 : ℝ)*base91 + (559369/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1066_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73996519/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7453/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2599/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5511/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14243/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1066_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1066_s5_0 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-550884109/2500000000 : ℝ)*x 0 + (2698498851/5000000000 : ℝ)*x 1 + (2630982227/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (550884109/2500000000 : ℝ)^8259 ≤ (13382039391117/100000000000000 : ℝ)^6211 := by
    have hnat : (550884109 : ℕ)^8259*100000000000000^6211 ≤ 13382039391117^6211*2500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550884109 2500000000 13382039391117 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698498851/5000000000 : ℝ)^8259 ≤ (11009631221311/25000000000000 : ℝ)^6211 := by
    have hnat : (2698498851 : ℕ)^8259*25000000000000^6211 ≤ 11009631221311^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698498851 5000000000 11009631221311 25000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2630982227/5000000000 : ℝ)^8259 ≤ (42579435706217/100000000000000 : ℝ)^6211 := by
    have hnat : (2630982227 : ℕ)^8259*100000000000000^6211 ≤ 42579435706217^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630982227 5000000000 42579435706217 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-550884109/2500000000 : ℝ), (2698498851/5000000000 : ℝ), (2630982227/5000000000 : ℝ)] ![(13382039391117/100000000000000 : ℝ), (11009631221311/25000000000000 : ℝ), (42579435706217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-550884109/2500000000 : ℝ)|^8259 ≤ (13382039391117/100000000000000 : ℝ)^6211
        have hw : |(-550884109/2500000000 : ℝ)|=(550884109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698498851/5000000000 : ℝ)|^8259 ≤ (11009631221311/25000000000000 : ℝ)^6211
        have hw : |(2698498851/5000000000 : ℝ)|=(2698498851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2630982227/5000000000 : ℝ)|^8259 ≤ (42579435706217/100000000000000 : ℝ)^6211
        have hw : |(2630982227/5000000000 : ℝ)|=(2630982227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s5_1 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (267281887/500000000 : ℝ)*x 0 + (-284010887/1250000000 : ℝ)*x 1 + (5261964639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267281887/500000000 : ℝ)^8259 ≤ (21741062020793/50000000000000 : ℝ)^6211 := by
    have hnat : (267281887 : ℕ)^8259*50000000000000^6211 ≤ 21741062020793^6211*500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267281887 500000000 21741062020793 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (284010887/1250000000 : ℝ)^8259 ≤ (6969219123009/50000000000000 : ℝ)^6211 := by
    have hnat : (284010887 : ℕ)^8259*50000000000000^6211 ≤ 6969219123009^6211*1250000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284010887 1250000000 6969219123009 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261964639/10000000000 : ℝ)^8259 ≤ (42579437696843/100000000000000 : ℝ)^6211 := by
    have hnat : (5261964639 : ℕ)^8259*100000000000000^6211 ≤ 42579437696843^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261964639 10000000000 42579437696843 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267281887/500000000 : ℝ), (-284010887/1250000000 : ℝ), (5261964639/10000000000 : ℝ)] ![(21741062020793/50000000000000 : ℝ), (6969219123009/50000000000000 : ℝ), (42579437696843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267281887/500000000 : ℝ)|^8259 ≤ (21741062020793/50000000000000 : ℝ)^6211
        have hw : |(267281887/500000000 : ℝ)|=(267281887/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-284010887/1250000000 : ℝ)|^8259 ≤ (6969219123009/50000000000000 : ℝ)^6211
        have hw : |(-284010887/1250000000 : ℝ)|=(284010887/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261964639/10000000000 : ℝ)|^8259 ≤ (42579437696843/100000000000000 : ℝ)^6211
        have hw : |(5261964639/10000000000 : ℝ)|=(5261964639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s5_2 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672818741/5000000000 : ℝ)*x 0 + (5261964523/10000000000 : ℝ)*x 1 + (-284010949/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672818741/5000000000 : ℝ)^8259 ≤ (43482121250991/100000000000000 : ℝ)^6211 := by
    have hnat : (2672818741 : ℕ)^8259*100000000000000^6211 ≤ 43482121250991^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672818741 5000000000 43482121250991 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5261964523/10000000000 : ℝ)^8259 ≤ (42579436448667/100000000000000 : ℝ)^6211 := by
    have hnat : (5261964523 : ℕ)^8259*100000000000000^6211 ≤ 42579436448667^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261964523 10000000000 42579436448667 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (284010949/1250000000 : ℝ)^8259 ≤ (13938442292119/100000000000000 : ℝ)^6211 := by
    have hnat : (284010949 : ℕ)^8259*100000000000000^6211 ≤ 13938442292119^6211*1250000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284010949 1250000000 13938442292119 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672818741/5000000000 : ℝ), (5261964523/10000000000 : ℝ), (-284010949/1250000000 : ℝ)] ![(43482121250991/100000000000000 : ℝ), (42579436448667/100000000000000 : ℝ), (13938442292119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672818741/5000000000 : ℝ)|^8259 ≤ (43482121250991/100000000000000 : ℝ)^6211
        have hw : |(2672818741/5000000000 : ℝ)|=(2672818741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5261964523/10000000000 : ℝ)|^8259 ≤ (42579436448667/100000000000000 : ℝ)^6211
        have hw : |(5261964523/10000000000 : ℝ)|=(5261964523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-284010949/1250000000 : ℝ)|^8259 ≤ (13938442292119/100000000000000 : ℝ)^6211
        have hw : |(-284010949/1250000000 : ℝ)|=(284010949/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s5_3 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (43753587/100000000 : ℝ)*x 0 + (265316371/625000000 : ℝ)*x 1 + (1127427417/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43753587/100000000 : ℝ)^8259 ≤ (33315196825663/100000000000000 : ℝ)^6211 := by
    have hnat : (43753587 : ℕ)^8259*100000000000000^6211 ≤ 33315196825663^6211*100000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43753587 100000000 33315196825663 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (265316371/625000000 : ℝ)^8259 ≤ (16001232029457/50000000000000 : ℝ)^6211 := by
    have hnat : (265316371 : ℕ)^8259*50000000000000^6211 ≤ 16001232029457^6211*625000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265316371 625000000 16001232029457 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1127427417/2500000000 : ℝ)^8259 ≤ (17341169546841/50000000000000 : ℝ)^6211 := by
    have hnat : (1127427417 : ℕ)^8259*50000000000000^6211 ≤ 17341169546841^6211*2500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127427417 2500000000 17341169546841 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(43753587/100000000 : ℝ), (265316371/625000000 : ℝ), (1127427417/2500000000 : ℝ)] ![(33315196825663/100000000000000 : ℝ), (16001232029457/50000000000000 : ℝ), (17341169546841/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(43753587/100000000 : ℝ)|^8259 ≤ (33315196825663/100000000000000 : ℝ)^6211
        have hw : |(43753587/100000000 : ℝ)|=(43753587/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(265316371/625000000 : ℝ)|^8259 ≤ (16001232029457/50000000000000 : ℝ)^6211
        have hw : |(265316371/625000000 : ℝ)|=(265316371/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1127427417/2500000000 : ℝ)|^8259 ≤ (17341169546841/50000000000000 : ℝ)^6211
        have hw : |(1127427417/2500000000 : ℝ)|=(1127427417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s5_4 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2203542291/10000000000 : ℝ)*x 0 + (164447369/312500000 : ℝ)*x 1 + (2698322453/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2203542291/10000000000 : ℝ)^8259 ≤ (3345521668259/25000000000000 : ℝ)^6211 := by
    have hnat : (2203542291 : ℕ)^8259*25000000000000^6211 ≤ 3345521668259^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203542291 10000000000 3345521668259 25000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164447369/312500000 : ℝ)^8259 ≤ (21291608183061/50000000000000 : ℝ)^6211 := by
    have hnat : (164447369 : ℕ)^8259*50000000000000^6211 ≤ 21291608183061^6211*312500000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164447369 312500000 21291608183061 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698322453/5000000000 : ℝ)^8259 ≤ (880693938849/2000000000000 : ℝ)^6211 := by
    have hnat : (2698322453 : ℕ)^8259*2000000000000^6211 ≤ 880693938849^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698322453 5000000000 880693938849 2000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2203542291/10000000000 : ℝ), (164447369/312500000 : ℝ), (2698322453/5000000000 : ℝ)] ![(3345521668259/25000000000000 : ℝ), (21291608183061/50000000000000 : ℝ), (880693938849/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2203542291/10000000000 : ℝ)|^8259 ≤ (3345521668259/25000000000000 : ℝ)^6211
        have hw : |(-2203542291/10000000000 : ℝ)|=(2203542291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164447369/312500000 : ℝ)|^8259 ≤ (21291608183061/50000000000000 : ℝ)^6211
        have hw : |(164447369/312500000 : ℝ)|=(164447369/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698322453/5000000000 : ℝ)|^8259 ≤ (880693938849/2000000000000 : ℝ)^6211
        have hw : |(2698322453/5000000000 : ℝ)|=(2698322453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s5_5 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (265581299/500000000 : ℝ)*x 0 + (-2137406901/10000000000 : ℝ)*x 1 + (5396644937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265581299/500000000 : ℝ)^8259 ≤ (43114630413973/100000000000000 : ℝ)^6211 := by
    have hnat : (265581299 : ℕ)^8259*100000000000000^6211 ≤ 43114630413973^6211*500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265581299 500000000 43114630413973 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2137406901/10000000000 : ℝ)^8259 ≤ (1285067228501/10000000000000 : ℝ)^6211 := by
    have hnat : (2137406901 : ℕ)^8259*10000000000000^6211 ≤ 1285067228501^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2137406901 10000000000 1285067228501 10000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396644937/10000000000 : ℝ)^8259 ≤ (22017348639403/50000000000000 : ℝ)^6211 := by
    have hnat : (5396644937 : ℕ)^8259*50000000000000^6211 ≤ 22017348639403^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396644937 10000000000 22017348639403 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265581299/500000000 : ℝ), (-2137406901/10000000000 : ℝ), (5396644937/10000000000 : ℝ)] ![(43114630413973/100000000000000 : ℝ), (1285067228501/10000000000000 : ℝ), (22017348639403/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265581299/500000000 : ℝ)|^8259 ≤ (43114630413973/100000000000000 : ℝ)^6211
        have hw : |(265581299/500000000 : ℝ)|=(265581299/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2137406901/10000000000 : ℝ)|^8259 ≤ (1285067228501/10000000000000 : ℝ)^6211
        have hw : |(-2137406901/10000000000 : ℝ)|=(2137406901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396644937/10000000000 : ℝ)|^8259 ≤ (22017348639403/50000000000000 : ℝ)^6211
        have hw : |(5396644937/10000000000 : ℝ)|=(5396644937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s5_6 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311625983/10000000000 : ℝ)*x 0 + (5396644927/10000000000 : ℝ)*x 1 + (-33396983/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311625983/10000000000 : ℝ)^8259 ≤ (21557315223177/50000000000000 : ℝ)^6211 := by
    have hnat : (5311625983 : ℕ)^8259*50000000000000^6211 ≤ 21557315223177^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311625983 10000000000 21557315223177 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396644927/10000000000 : ℝ)^8259 ≤ (344021071643/781250000000 : ℝ)^6211 := by
    have hnat : (5396644927 : ℕ)^8259*781250000000^6211 ≤ 344021071643^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396644927 10000000000 344021071643 781250000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33396983/156250000 : ℝ)^8259 ≤ (1606334046619/12500000000000 : ℝ)^6211 := by
    have hnat : (33396983 : ℕ)^8259*12500000000000^6211 ≤ 1606334046619^6211*156250000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33396983 156250000 1606334046619 12500000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311625983/10000000000 : ℝ), (5396644927/10000000000 : ℝ), (-33396983/156250000 : ℝ)] ![(21557315223177/50000000000000 : ℝ), (344021071643/781250000000 : ℝ), (1606334046619/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311625983/10000000000 : ℝ)|^8259 ≤ (21557315223177/50000000000000 : ℝ)^6211
        have hw : |(5311625983/10000000000 : ℝ)|=(5311625983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396644927/10000000000 : ℝ)|^8259 ≤ (344021071643/781250000000 : ℝ)^6211
        have hw : |(5396644927/10000000000 : ℝ)|=(5396644927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-33396983/156250000 : ℝ)|^8259 ≤ (1606334046619/12500000000000 : ℝ)^6211
        have hw : |(-33396983/156250000 : ℝ)|=(33396983/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s5_7 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1093842493/2500000000 : ℝ)*x 0 + (2254510099/5000000000 : ℝ)*x 1 + (265359617/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093842493/2500000000 : ℝ)^8259 ≤ (33315310954613/100000000000000 : ℝ)^6211 := by
    have hnat : (1093842493 : ℕ)^8259*100000000000000^6211 ≤ 33315310954613^6211*2500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093842493 2500000000 33315310954613 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2254510099/5000000000 : ℝ)^8259 ≤ (34675288427383/100000000000000 : ℝ)^6211 := by
    have hnat : (2254510099 : ℕ)^8259*100000000000000^6211 ≤ 34675288427383^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254510099 5000000000 34675288427383 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (265359617/625000000 : ℝ)^8259 ≤ (16004700299667/50000000000000 : ℝ)^6211 := by
    have hnat : (265359617 : ℕ)^8259*50000000000000^6211 ≤ 16004700299667^6211*625000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265359617 625000000 16004700299667 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1093842493/2500000000 : ℝ), (2254510099/5000000000 : ℝ), (265359617/625000000 : ℝ)] ![(33315310954613/100000000000000 : ℝ), (34675288427383/100000000000000 : ℝ), (16004700299667/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1093842493/2500000000 : ℝ)|^8259 ≤ (33315310954613/100000000000000 : ℝ)^6211
        have hw : |(1093842493/2500000000 : ℝ)|=(1093842493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2254510099/5000000000 : ℝ)|^8259 ≤ (34675288427383/100000000000000 : ℝ)^6211
        have hw : |(2254510099/5000000000 : ℝ)|=(2254510099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(265359617/625000000 : ℝ)|^8259 ≤ (16004700299667/50000000000000 : ℝ)^6211
        have hw : |(265359617/625000000 : ℝ)|=(265359617/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1066_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73996519/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14243/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5511/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5599/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7029/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14243/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5511/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14243/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5511/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14243/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5511/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14243/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5511/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14243/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5511/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14243/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5511/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5511/50000 : ℝ) ^ (4129/1024 : ℝ) ≤ (13746020013856777/100000000000000000000 : ℝ) := by
    have hpowers : (5511/50000 : ℝ)^4129 ≤ (13746020013856777/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5511 : ℕ)^4129*100000000000000000000^1024 ≤ 13746020013856777^1024*50000^4129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5511 50000 13746020013856777 100000000000000000000 4129 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5511/50000 : ℝ)) (X := (13746020013856777/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14243/100000 : ℝ) ^ (4129/1024 : ℝ) ≤ (38648209811812533/100000000000000000000 : ℝ) := by
    have hpowers : (14243/100000 : ℝ)^4129 ≤ (38648209811812533/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14243 : ℕ)^4129*100000000000000000000^1024 ≤ 38648209811812533^1024*100000^4129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14243 100000 38648209811812533 100000000000000000000 4129 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14243/100000 : ℝ)) (X := (38648209811812533/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013746020013856777/50000000000000000000 : ℝ) ≤ (5000340868726137/5000000000000000 : ℝ) ^ (4129/1024 : ℝ) := by
    have hpowers : (50013746020013856777/50000000000000000000 : ℝ)^1024 ≤ (5000340868726137/5000000000000000 : ℝ)^4129 := by
      have hnat : (50013746020013856777 : ℕ)^1024*5000000000000000^4129 ≤ 5000340868726137^4129*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013746020013856777 50000000000000000000 5000340868726137 5000000000000000 1024 4129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000340868726137/5000000000000000 : ℝ)) (X := (50013746020013856777/50000000000000000000 : ℝ)) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10005239422982566931/10000000000000000000 : ℝ) ≤ (2500324782786963/2500000000000000 : ℝ) ^ (4129/1024 : ℝ) := by
    have hpowers : (10005239422982566931/10000000000000000000 : ℝ)^1024 ≤ (2500324782786963/2500000000000000 : ℝ)^4129 := by
      have hnat : (10005239422982566931 : ℕ)^1024*2500000000000000^4129 ≤ 2500324782786963^4129*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005239422982566931 10000000000000000000 2500324782786963 2500000000000000 1024 4129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500324782786963/2500000000000000 : ℝ)) (X := (10005239422982566931/10000000000000000000 : ℝ)) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50038648209811812533/50000000000000000000 : ℝ) ≤ (1000191652484343/1000000000000000 : ℝ) ^ (4129/1024 : ℝ) := by
    have hpowers : (50038648209811812533/50000000000000000000 : ℝ)^1024 ≤ (1000191652484343/1000000000000000 : ℝ)^4129 := by
      have hnat : (50038648209811812533 : ℕ)^1024*1000000000000000^4129 ≤ 1000191652484343^4129*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50038648209811812533 50000000000000000000 1000191652484343 1000000000000000 1024 4129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000191652484343/1000000000000000 : ℝ)) (X := (50038648209811812533/50000000000000000000 : ℝ)) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13746020013856777/100000000000000000000 : ℝ) ≤ ((16099293024854226561/16105000000000000000 : ℝ)+2*(308696847789/161050000000000 : ℝ)*(5511/50000 : ℝ))^(4129/1024 : ℝ) := by
    rw [show (16099293024854226561/16105000000000000000 : ℝ)+2*(308696847789/161050000000000 : ℝ)*(5511/50000 : ℝ)=(5000340868726137/5000000000000000 : ℝ) by norm_num, show 1+2*(13746020013856777/100000000000000000000 : ℝ)=(50013746020013856777/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38648209811812533/100000000000000000000 : ℝ)+(13746020013856777/100000000000000000000 : ℝ) ≤ ((16099293024854226561/16105000000000000000 : ℝ)+(308696847789/161050000000000 : ℝ)*((14243/100000 : ℝ)+(5511/50000 : ℝ)))^(4129/1024 : ℝ) := by
    rw [show (16099293024854226561/16105000000000000000 : ℝ)+(308696847789/161050000000000 : ℝ)*((14243/100000 : ℝ)+(5511/50000 : ℝ))=(2500324782786963/2500000000000000 : ℝ) by norm_num, show 1+(38648209811812533/100000000000000000000 : ℝ)+(13746020013856777/100000000000000000000 : ℝ)=(10005239422982566931/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38648209811812533/100000000000000000000 : ℝ) ≤ ((16099293024854226561/16105000000000000000 : ℝ)+2*(308696847789/161050000000000 : ℝ)*(14243/100000 : ℝ))^(4129/1024 : ℝ) := by
    rw [show (16099293024854226561/16105000000000000000 : ℝ)+2*(308696847789/161050000000000 : ℝ)*(14243/100000 : ℝ)=(1000191652484343/1000000000000000 : ℝ) by norm_num, show 1+2*(38648209811812533/100000000000000000000 : ℝ)=(50038648209811812533/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16099293024854226561/16105000000000000000 : ℝ)*(X 1 0+X 2 0)+(308696847789/161050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4129/1024 : ℝ)) (lo := (5511/50000 : ℝ)) (hi := (14243/100000 : ℝ)) (c := (16099293024854226561/16105000000000000000 : ℝ)) (alpha := (308696847789/161050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16099293024854226561/16105000000000000000 : ℝ)*(X 0 1+X 2 1)+(308696847789/161050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4129/1024 : ℝ)) (lo := (5511/50000 : ℝ)) (hi := (14243/100000 : ℝ)) (c := (16099293024854226561/16105000000000000000 : ℝ)) (alpha := (308696847789/161050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16099293024854226561/16105000000000000000 : ℝ)*(X 0 2+X 1 2)+(308696847789/161050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4129/1024 : ℝ)) (lo := (5511/50000 : ℝ)) (hi := (14243/100000 : ℝ)) (c := (16099293024854226561/16105000000000000000 : ℝ)) (alpha := (308696847789/161050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-550884109/2500000000 : ℝ)*X 0 0+(2698498851/5000000000 : ℝ)*X 0 1+(2630982227/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267281887/500000000 : ℝ)*X 1 0+(-284010887/1250000000 : ℝ)*X 1 1+(5261964639/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672818741/5000000000 : ℝ)*X 2 0+(5261964523/10000000000 : ℝ)*X 2 1+(-284010949/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((43753587/100000000 : ℝ)*X 0 0+(265316371/625000000 : ℝ)*X 0 1+(1127427417/2500000000 : ℝ)*X 0 2+(43753587/100000000 : ℝ)*X 1 0+(265316371/625000000 : ℝ)*X 1 1+(1127427417/2500000000 : ℝ)*X 1 2+(43753587/100000000 : ℝ)*X 2 0+(265316371/625000000 : ℝ)*X 2 1+(1127427417/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2203542291/10000000000 : ℝ)*X 0 0+(164447369/312500000 : ℝ)*X 0 1+(2698322453/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((265581299/500000000 : ℝ)*X 1 0+(-2137406901/10000000000 : ℝ)*X 1 1+(5396644937/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311625983/10000000000 : ℝ)*X 2 0+(5396644927/10000000000 : ℝ)*X 2 1+(-33396983/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1093842493/2500000000 : ℝ)*X 0 0+(2254510099/5000000000 : ℝ)*X 0 1+(265359617/625000000 : ℝ)*X 0 2+(1093842493/2500000000 : ℝ)*X 1 0+(2254510099/5000000000 : ℝ)*X 1 1+(265359617/625000000 : ℝ)*X 1 2+(1093842493/2500000000 : ℝ)*X 2 0+(2254510099/5000000000 : ℝ)*X 2 1+(265359617/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9104168611536820959091375317/805250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1609843437/100000000000000 : ℝ)*(base19) + (1469722127/100000000000000 : ℝ)*(base23) + (299553877/100000000000000 : ℝ)*(upper3) + (38880423/25000000000000 : ℝ)*(lower4) + (5592189832934999/100000000000000 : ℝ)*(major0) + (5592189832934999/100000000000000 : ℝ)*(major1) + (5592189832934999/100000000000000 : ℝ)*(major2) + (740565032895281/10000000000000 : ℝ)*(sp0) + (925711660490987/12500000000000 : ℝ)*(sp1) + (185142046297771/2500000000000 : ℝ)*(sp2) + (377864496147903/10000000000000 : ℝ)*(sp3) + (44564818523/100000000000000 : ℝ)*(sp4) + (2314427673/20000000000000 : ℝ)*(sp6) + (19716876227/50000000000000 : ℝ)*(sp7) + (1889342197615741/50000000000000 : ℝ)*(f.failure) + (7405694893771333/100000000000000 : ℝ)*(f.sum) + (62979703973753/16105000000000000000000000000 : ℝ)*base66 + (2924841472994591561/1610500000000000000000000000000000 : ℝ)*base68 + (319106010040408439/1610500000000000000000000000000000 : ℝ)*base69 + (9680317490290591561/1610500000000000000000000000000000 : ℝ)*base72 + (9558924773479/8052500000000000000000000000 : ℝ)*base74 + (21506164465202591561/1610500000000000000000000000000000 : ℝ)*base76 + (12474289606458091561/1610500000000000000000000000000000 : ℝ)*base78 + (315646428959908439/1610500000000000000000000000000000 : ℝ)*base79 + (20569509134609/8052500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (41394421/2500000000000000000000 : ℝ)*base90 + (41394421/2500000000000000000000 : ℝ)*base92 + (41394421/2500000000000000000000 : ℝ)*base94 + (1/50000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (583126381401043968347423667/201312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (139238789/25000000000000 : ℝ)*(base19) + (297425589/50000000000000 : ℝ)*(base23) + (63238933/100000000000000 : ℝ)*(upper3) + (17011679/100000000000000 : ℝ)*(lower4) + (32220959/50000000000000 : ℝ)*(upper5) + (1405354732912551/25000000000000 : ℝ)*(major0) + (1405354732912551/25000000000000 : ℝ)*(major1) + (1405354732912551/25000000000000 : ℝ)*(major2) + (16054683259/100000000000000 : ℝ)*(sp1) + (8157351869/50000000000000 : ℝ)*(sp2) + (7444403051425303/100000000000000 : ℝ)*(sp4) + (930548304973361/12500000000000 : ℝ)*(sp5) + (3722193070935193/50000000000000 : ℝ)*(sp6) + (3798434715321003/100000000000000 : ℝ)*(sp7) + (3798434715321003/100000000000000 : ℝ)*(f.failure) + (7444403051425303/100000000000000 : ℝ)*(f.sum) + (2824124771897/16105000000000000000000000000 : ℝ)*base65 + (727627166631117111/402625000000000000000000000000000 : ℝ)*base67 + (582603851773382889/402625000000000000000000000000000 : ℝ)*base70 + (2763557720863632889/402625000000000000000000000000000 : ℝ)*base72 + (64383853284251/8052500000000000000000000000 : ℝ)*base73 + (8994633786524242111/402625000000000000000000000000000 : ℝ)*base75 + (33316196619617111/402625000000000000000000000000000 : ℝ)*base77 + (6927315776779617111/402625000000000000000000000000000 : ℝ)*base79 + (3532315835959/2013125000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (10411443/5000000000000000000000 : ℝ)*base90 + (10411443/5000000000000000000000 : ℝ)*base92 + (10411443/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1066_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73996519/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14243/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5511/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5599/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7029/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1066_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1066_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73996519/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16741/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1089/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5599/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7029/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1066_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1066_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1066_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73996519/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16741/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1089/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5599/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7029/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1066_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
