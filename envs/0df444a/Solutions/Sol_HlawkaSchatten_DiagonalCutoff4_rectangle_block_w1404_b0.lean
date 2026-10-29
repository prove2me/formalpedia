-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1404_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:47:17.293364+00:00
-- url     : https://prove2.me/submissions/3ccac020-52c8-4659-a865-f72817526ff5

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
theorem support_rectangle_w1404_s0_0 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-35461107/200000000 : ℝ)*x 0 + (597056617/1000000000 : ℝ)*x 1 + (2412742287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (35461107/200000000 : ℝ)^1091 ≤ (10432549295837/100000000000000 : ℝ)^835 := by
    have hnat : (35461107 : ℕ)^1091*100000000000000^835 ≤ 10432549295837^835*200000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35461107 200000000 10432549295837 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (597056617/1000000000 : ℝ)^1091 ≤ (25486771660053/50000000000000 : ℝ)^835 := by
    have hnat : (597056617 : ℕ)^1091*50000000000000^835 ≤ 25486771660053^835*1000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      597056617 1000000000 25486771660053 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2412742287/5000000000 : ℝ)^1091 ≤ (38593907371777/100000000000000 : ℝ)^835 := by
    have hnat : (2412742287 : ℕ)^1091*100000000000000^835 ≤ 38593907371777^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2412742287 5000000000 38593907371777 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-35461107/200000000 : ℝ), (597056617/1000000000 : ℝ), (2412742287/5000000000 : ℝ)] ![(10432549295837/100000000000000 : ℝ), (25486771660053/50000000000000 : ℝ), (38593907371777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-35461107/200000000 : ℝ)|^1091 ≤ (10432549295837/100000000000000 : ℝ)^835
        have hw : |(-35461107/200000000 : ℝ)|=(35461107/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(597056617/1000000000 : ℝ)|^1091 ≤ (25486771660053/50000000000000 : ℝ)^835
        have hw : |(597056617/1000000000 : ℝ)|=(597056617/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2412742287/5000000000 : ℝ)|^1091 ≤ (38593907371777/100000000000000 : ℝ)^835
        have hw : |(2412742287/5000000000 : ℝ)|=(2412742287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s0_1 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1098976657/2000000000 : ℝ)*x 0 + (-151314841/625000000 : ℝ)*x 1 + (2412742419/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1098976657/2000000000 : ℝ)^1091 ≤ (45733365847219/100000000000000 : ℝ)^835 := by
    have hnat : (1098976657 : ℕ)^1091*100000000000000^835 ≤ 45733365847219^835*2000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098976657 2000000000 45733365847219 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (151314841/625000000 : ℝ)^1091 ≤ (3134544802141/20000000000000 : ℝ)^835 := by
    have hnat : (151314841 : ℕ)^1091*20000000000000^835 ≤ 3134544802141^835*625000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151314841 625000000 3134544802141 20000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2412742419/5000000000 : ℝ)^1091 ≤ (2412119383161/6250000000000 : ℝ)^835 := by
    have hnat : (2412742419 : ℕ)^1091*6250000000000^835 ≤ 2412119383161^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2412742419 5000000000 2412119383161 6250000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1098976657/2000000000 : ℝ), (-151314841/625000000 : ℝ), (2412742419/5000000000 : ℝ)] ![(45733365847219/100000000000000 : ℝ), (3134544802141/20000000000000 : ℝ), (2412119383161/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1098976657/2000000000 : ℝ)|^1091 ≤ (45733365847219/100000000000000 : ℝ)^835
        have hw : |(1098976657/2000000000 : ℝ)|=(1098976657/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-151314841/625000000 : ℝ)|^1091 ≤ (3134544802141/20000000000000 : ℝ)^835
        have hw : |(-151314841/625000000 : ℝ)|=(151314841/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2412742419/5000000000 : ℝ)|^1091 ≤ (2412119383161/6250000000000 : ℝ)^835
        have hw : |(2412742419/5000000000 : ℝ)|=(2412742419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s0_2 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2747441737/5000000000 : ℝ)*x 0 + (1206371183/2500000000 : ℝ)*x 1 + (-75657417/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2747441737/5000000000 : ℝ)^1091 ≤ (45733367902517/100000000000000 : ℝ)^835 := by
    have hnat : (2747441737 : ℕ)^1091*100000000000000^835 ≤ 45733367902517^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2747441737 5000000000 45733367902517 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1206371183/2500000000 : ℝ)^1091 ≤ (9648477255719/25000000000000 : ℝ)^835 := by
    have hnat : (1206371183 : ℕ)^1091*25000000000000^835 ≤ 9648477255719^835*2500000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1206371183 2500000000 9648477255719 25000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (75657417/312500000 : ℝ)^1091 ≤ (15672723063379/100000000000000 : ℝ)^835 := by
    have hnat : (75657417 : ℕ)^1091*100000000000000^835 ≤ 15672723063379^835*312500000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75657417 312500000 15672723063379 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2747441737/5000000000 : ℝ), (1206371183/2500000000 : ℝ), (-75657417/312500000 : ℝ)] ![(45733367902517/100000000000000 : ℝ), (9648477255719/25000000000000 : ℝ), (15672723063379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2747441737/5000000000 : ℝ)|^1091 ≤ (45733367902517/100000000000000 : ℝ)^835
        have hw : |(2747441737/5000000000 : ℝ)|=(2747441737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1206371183/2500000000 : ℝ)|^1091 ≤ (9648477255719/25000000000000 : ℝ)^835
        have hw : |(1206371183/2500000000 : ℝ)|=(1206371183/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-75657417/312500000 : ℝ)|^1091 ≤ (15672723063379/100000000000000 : ℝ)^835
        have hw : |(-75657417/312500000 : ℝ)|=(75657417/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s0_3 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4169608063/10000000000 : ℝ)*x 0 + (1552029347/5000000000 : ℝ)*x 1 + (5558581353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4169608063/10000000000 : ℝ)^1091 ≤ (6377514180583/20000000000000 : ℝ)^835 := by
    have hnat : (4169608063 : ℕ)^1091*20000000000000^835 ≤ 6377514180583^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169608063 10000000000 6377514180583 20000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1552029347/5000000000 : ℝ)^1091 ≤ (5421286277879/25000000000000 : ℝ)^835 := by
    have hnat : (1552029347 : ℕ)^1091*25000000000000^835 ≤ 5421286277879^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1552029347 5000000000 5421286277879 25000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5558581353/10000000000 : ℝ)^1091 ≤ (46427283982321/100000000000000 : ℝ)^835 := by
    have hnat : (5558581353 : ℕ)^1091*100000000000000^835 ≤ 46427283982321^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5558581353 10000000000 46427283982321 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4169608063/10000000000 : ℝ), (1552029347/5000000000 : ℝ), (5558581353/10000000000 : ℝ)] ![(6377514180583/20000000000000 : ℝ), (5421286277879/25000000000000 : ℝ), (46427283982321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4169608063/10000000000 : ℝ)|^1091 ≤ (6377514180583/20000000000000 : ℝ)^835
        have hw : |(4169608063/10000000000 : ℝ)|=(4169608063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1552029347/5000000000 : ℝ)|^1091 ≤ (5421286277879/25000000000000 : ℝ)^835
        have hw : |(1552029347/5000000000 : ℝ)|=(1552029347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5558581353/10000000000 : ℝ)|^1091 ≤ (46427283982321/100000000000000 : ℝ)^835
        have hw : |(5558581353/10000000000 : ℝ)|=(5558581353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s0_4 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-888597601/5000000000 : ℝ)*x 0 + (4854836717/10000000000 : ℝ)*x 1 + (1188033091/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (888597601/5000000000 : ℝ)^1091 ≤ (327012104817/3125000000000 : ℝ)^835 := by
    have hnat : (888597601 : ℕ)^1091*3125000000000^835 ≤ 327012104817^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      888597601 5000000000 327012104817 3125000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4854836717/10000000000 : ℝ)^1091 ≤ (3890092273413/10000000000000 : ℝ)^835 := by
    have hnat : (4854836717 : ℕ)^1091*10000000000000^835 ≤ 3890092273413^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4854836717 10000000000 3890092273413 10000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1188033091/2000000000 : ℝ)^1091 ≤ (50634689905087/100000000000000 : ℝ)^835 := by
    have hnat : (1188033091 : ℕ)^1091*100000000000000^835 ≤ 50634689905087^835*2000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1188033091 2000000000 50634689905087 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-888597601/5000000000 : ℝ), (4854836717/10000000000 : ℝ), (1188033091/2000000000 : ℝ)] ![(327012104817/3125000000000 : ℝ), (3890092273413/10000000000000 : ℝ), (50634689905087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-888597601/5000000000 : ℝ)|^1091 ≤ (327012104817/3125000000000 : ℝ)^835
        have hw : |(-888597601/5000000000 : ℝ)|=(888597601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4854836717/10000000000 : ℝ)|^1091 ≤ (3890092273413/10000000000000 : ℝ)^835
        have hw : |(4854836717/10000000000 : ℝ)|=(4854836717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1188033091/2000000000 : ℝ)|^1091 ≤ (50634689905087/100000000000000 : ℝ)^835
        have hw : |(1188033091/2000000000 : ℝ)|=(1188033091/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s0_5 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5182464751/10000000000 : ℝ)*x 0 + (-81647311/625000000 : ℝ)*x 1 + (594016569/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5182464751/10000000000 : ℝ)^1091 ≤ (16549199797/39062500000 : ℝ)^835 := by
    have hnat : (5182464751 : ℕ)^1091*39062500000^835 ≤ 16549199797^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182464751 10000000000 16549199797 39062500000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81647311/625000000 : ℝ)^1091 ≤ (6999355989309/100000000000000 : ℝ)^835 := by
    have hnat : (81647311 : ℕ)^1091*100000000000000^835 ≤ 6999355989309^835*625000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81647311 625000000 6999355989309 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (594016569/1000000000 : ℝ)^1091 ≤ (50634692522401/100000000000000 : ℝ)^835 := by
    have hnat : (594016569 : ℕ)^1091*100000000000000^835 ≤ 50634692522401^835*1000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      594016569 1000000000 50634692522401 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5182464751/10000000000 : ℝ), (-81647311/625000000 : ℝ), (594016569/1000000000 : ℝ)] ![(16549199797/39062500000 : ℝ), (6999355989309/100000000000000 : ℝ), (50634692522401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5182464751/10000000000 : ℝ)|^1091 ≤ (16549199797/39062500000 : ℝ)^835
        have hw : |(5182464751/10000000000 : ℝ)|=(5182464751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-81647311/625000000 : ℝ)|^1091 ≤ (6999355989309/100000000000000 : ℝ)^835
        have hw : |(-81647311/625000000 : ℝ)|=(81647311/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(594016569/1000000000 : ℝ)|^1091 ≤ (50634692522401/100000000000000 : ℝ)^835
        have hw : |(594016569/1000000000 : ℝ)|=(594016569/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s0_6 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (32390407/62500000 : ℝ)*x 0 + (742520691/1250000000 : ℝ)*x 1 + (-1306356669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (32390407/62500000 : ℝ)^1091 ≤ (5295744427709/12500000000000 : ℝ)^835 := by
    have hnat : (32390407 : ℕ)^1091*12500000000000^835 ≤ 5295744427709^835*62500000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32390407 62500000 5295744427709 12500000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (742520691/1250000000 : ℝ)^1091 ≤ (81015505149/160000000000 : ℝ)^835 := by
    have hnat : (742520691 : ℕ)^1091*160000000000^835 ≤ 81015505149^835*1250000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      742520691 1250000000 81015505149 160000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1306356669/10000000000 : ℝ)^1091 ≤ (6999353840129/100000000000000 : ℝ)^835 := by
    have hnat : (1306356669 : ℕ)^1091*100000000000000^835 ≤ 6999353840129^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306356669 10000000000 6999353840129 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(32390407/62500000 : ℝ), (742520691/1250000000 : ℝ), (-1306356669/10000000000 : ℝ)] ![(5295744427709/12500000000000 : ℝ), (81015505149/160000000000 : ℝ), (6999353840129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(32390407/62500000 : ℝ)|^1091 ≤ (5295744427709/12500000000000 : ℝ)^835
        have hw : |(32390407/62500000 : ℝ)|=(32390407/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(742520691/1250000000 : ℝ)|^1091 ≤ (81015505149/160000000000 : ℝ)^835
        have hw : |(742520691/1250000000 : ℝ)|=(742520691/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1306356669/10000000000 : ℝ)|^1091 ≤ (6999353840129/100000000000000 : ℝ)^835
        have hw : |(-1306356669/10000000000 : ℝ)|=(1306356669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s0_7 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (835696467/2000000000 : ℝ)*x 0 + (5495663953/10000000000 : ℝ)*x 1 + (1584611903/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (835696467/2000000000 : ℝ)^1091 ≤ (3997034250769/12500000000000 : ℝ)^835 := by
    have hnat : (835696467 : ℕ)^1091*12500000000000^835 ≤ 3997034250769^835*2000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      835696467 2000000000 3997034250769 12500000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5495663953/10000000000 : ℝ)^1091 ≤ (22870927739011/50000000000000 : ℝ)^835 := by
    have hnat : (5495663953 : ℕ)^1091*50000000000000^835 ≤ 22870927739011^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5495663953 10000000000 22870927739011 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1584611903/5000000000 : ℝ)^1091 ≤ (22281870501447/100000000000000 : ℝ)^835 := by
    have hnat : (1584611903 : ℕ)^1091*100000000000000^835 ≤ 22281870501447^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1584611903 5000000000 22281870501447 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(835696467/2000000000 : ℝ), (5495663953/10000000000 : ℝ), (1584611903/5000000000 : ℝ)] ![(3997034250769/12500000000000 : ℝ), (22870927739011/50000000000000 : ℝ), (22281870501447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(835696467/2000000000 : ℝ)|^1091 ≤ (3997034250769/12500000000000 : ℝ)^835
        have hw : |(835696467/2000000000 : ℝ)|=(835696467/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5495663953/10000000000 : ℝ)|^1091 ≤ (22870927739011/50000000000000 : ℝ)^835
        have hw : |(5495663953/10000000000 : ℝ)|=(5495663953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1584611903/5000000000 : ℝ)|^1091 ≤ (22281870501447/100000000000000 : ℝ)^835
        have hw : |(1584611903/5000000000 : ℝ)|=(1584611903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1404_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39294187/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (187/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (826/3125 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4363/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4363 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4363*1^1024 ≤ 0^1024*1^4363 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4363 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4363/1024 : ℝ) ≤ (50398803440966419/2500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4363 ≤ (50398803440966419/2500000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4363*2500000000000000000^1024 ≤ 50398803440966419^1024*5^4363 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 50398803440966419 2500000000000000000 4363 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (50398803440966419/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4363/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4363 := by
      have hnat : (1 : ℕ)^1024*1^4363 ≤ 1^4363*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2550398803440966419/2500000000000000000 : ℝ) ≤ (10046953860938413/10000000000000000 : ℝ) ^ (4363/1024 : ℝ) := by
    have hpowers : (2550398803440966419/2500000000000000000 : ℝ)^1024 ≤ (10046953860938413/10000000000000000 : ℝ)^4363 := by
      have hnat : (2550398803440966419 : ℕ)^1024*10000000000000000^4363 ≤ 10046953860938413^4363*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2550398803440966419 2500000000000000000 10046953860938413 10000000000000000 1024 4363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10046953860938413/10000000000000000 : ℝ)) (X := (2550398803440966419/2500000000000000000 : ℝ)) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1300398803440966419/1250000000000000000 : ℝ) ≤ (5046953860938413/5000000000000000 : ℝ) ^ (4363/1024 : ℝ) := by
    have hpowers : (1300398803440966419/1250000000000000000 : ℝ)^1024 ≤ (5046953860938413/5000000000000000 : ℝ)^4363 := by
      have hnat : (1300398803440966419 : ℕ)^1024*5000000000000000^4363 ≤ 5046953860938413^4363*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1300398803440966419 1250000000000000000 5046953860938413 5000000000000000 1024 4363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5046953860938413/5000000000000000 : ℝ)) (X := (1300398803440966419/1250000000000000000 : ℝ)) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(46953860938413/4000000000000000 : ℝ)*(0 : ℝ))^(4363/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(46953860938413/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(50398803440966419/2500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(46953860938413/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4363/1024 : ℝ) := by
    rw [show (1 : ℝ)+(46953860938413/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10046953860938413/10000000000000000 : ℝ) by norm_num, show 1+(50398803440966419/2500000000000000000 : ℝ)+(0 : ℝ)=(2550398803440966419/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(50398803440966419/2500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(46953860938413/4000000000000000 : ℝ)*(2/5 : ℝ))^(4363/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(46953860938413/4000000000000000 : ℝ)*(2/5 : ℝ)=(5046953860938413/5000000000000000 : ℝ) by norm_num, show 1+2*(50398803440966419/2500000000000000000 : ℝ)=(1300398803440966419/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(46953860938413/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4363/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (46953860938413/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(46953860938413/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4363/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (46953860938413/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(46953860938413/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4363/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (46953860938413/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-35461107/200000000 : ℝ)*X 0 0+(597056617/1000000000 : ℝ)*X 0 1+(2412742287/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1098976657/2000000000 : ℝ)*X 1 0+(-151314841/625000000 : ℝ)*X 1 1+(2412742419/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2747441737/5000000000 : ℝ)*X 2 0+(1206371183/2500000000 : ℝ)*X 2 1+(-75657417/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4169608063/10000000000 : ℝ)*X 0 0+(1552029347/5000000000 : ℝ)*X 0 1+(5558581353/10000000000 : ℝ)*X 0 2+(4169608063/10000000000 : ℝ)*X 1 0+(1552029347/5000000000 : ℝ)*X 1 1+(5558581353/10000000000 : ℝ)*X 1 2+(4169608063/10000000000 : ℝ)*X 2 0+(1552029347/5000000000 : ℝ)*X 2 1+(5558581353/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-888597601/5000000000 : ℝ)*X 0 0+(4854836717/10000000000 : ℝ)*X 0 1+(1188033091/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5182464751/10000000000 : ℝ)*X 1 0+(-81647311/625000000 : ℝ)*X 1 1+(594016569/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((32390407/62500000 : ℝ)*X 2 0+(742520691/1250000000 : ℝ)*X 2 1+(-1306356669/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((835696467/2000000000 : ℝ)*X 0 0+(5495663953/10000000000 : ℝ)*X 0 1+(1584611903/5000000000 : ℝ)*X 0 2+(835696467/2000000000 : ℝ)*X 1 0+(5495663953/10000000000 : ℝ)*X 1 1+(1584611903/5000000000 : ℝ)*X 1 2+(835696467/2000000000 : ℝ)*X 2 0+(5495663953/10000000000 : ℝ)*X 2 1+(1584611903/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (931236528599586417/500000000000000000000000 : ℝ) := by norm_num
    linear_combination (247030121/50000000000000 : ℝ)*(base19) + (96607897/20000000000000 : ℝ)*(base23) + (13236809/20000000000000 : ℝ)*(upper3) + (2256121/10000000000000 : ℝ)*(upper4) + (68146699/100000000000000 : ℝ)*(upper5) + (640358380295517/100000000000000 : ℝ)*(major0) + (640358380295517/100000000000000 : ℝ)*(major1) + (640358380295517/100000000000000 : ℝ)*(major2) + (34932074833481/4000000000000 : ℝ)*(sp0) + (436651641680941/50000000000000 : ℝ)*(sp1) + (873303294382639/100000000000000 : ℝ)*(sp2) + (203706011064953/50000000000000 : ℝ)*(sp3) + (19065851/1000000000000 : ℝ)*(sp4) + (449478281/50000000000000 : ℝ)*(sp7) + (101853230271617/25000000000000 : ℝ)*(f.failure) + (218325944355531/25000000000000 : ℝ)*(f.sum) + (239694202605479/200000000000000000000000000000 : ℝ)*base66 + (3638015443005479/400000000000000000000000000000 : ℝ)*base68 + (2161041620994521/400000000000000000000000000000 : ℝ)*base69 + (406748810205479/400000000000000000000000000000 : ℝ)*base72 + (965078154605479/200000000000000000000000000000 : ℝ)*base74 + (3515092714594521/400000000000000000000000000000 : ℝ)*base75 + (1166984983394521/400000000000000000000000000000 : ℝ)*base77 + (1463261837794521/400000000000000000000000000000 : ℝ)*base79 + (844316482194521/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (2059621/625000000000000000000 : ℝ)*base90 + (2059621/625000000000000000000 : ℝ)*base92 + (2059621/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (367823924938731853884147/40000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2007283627/100000000000000 : ℝ)*(base19) + (262701031/12500000000000 : ℝ)*(base23) + (41028233/50000000000000 : ℝ)*(base32) + (303616533/100000000000000 : ℝ)*(upper3) + (116609931/50000000000000 : ℝ)*(upper5) + (675610504039627/100000000000000 : ℝ)*(major0) + (675610504039627/100000000000000 : ℝ)*(major1) + (675610504039627/100000000000000 : ℝ)*(major2) + (478127687/10000000000000 : ℝ)*(sp1) + (2628855309/50000000000000 : ℝ)*(sp2) + (92137944791559/10000000000000 : ℝ)*(sp4) + (921372659355093/100000000000000 : ℝ)*(sp5) + (921372088596723/100000000000000 : ℝ)*(sp6) + (429841171587251/100000000000000 : ℝ)*(sp7) + (429841253643717/100000000000000 : ℝ)*(f.failure) + (92137944791559/10000000000000 : ℝ)*(f.sum) + (407395177491951/200000000000000000000000000000 : ℝ)*base65 + (1135025065291951/400000000000000000000000000000 : ℝ)*base67 + (500841256091951/400000000000000000000000000000 : ℝ)*base69 + (1360675207291951/400000000000000000000000000000 : ℝ)*base71 + (573149215491951/200000000000000000000000000000 : ℝ)*base73 + (1081763855908049/400000000000000000000000000000 : ℝ)*base76 + (1828121647691951/400000000000000000000000000000 : ℝ)*base77 + (3997852629291951/400000000000000000000000000000 : ℝ)*base79 + (38660953091951/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (27826921/2500000000000000000000 : ℝ)*base90 + (27826921/2500000000000000000000 : ℝ)*base92 + (27826921/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1404_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39294187/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (187/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (826/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1404_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1404_s1_0 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1948964267/10000000000 : ℝ)*x 0 + (2807705941/5000000000 : ℝ)*x 1 + (1013581617/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1948964267/10000000000 : ℝ)^1091 ≤ (2951257541219/25000000000000 : ℝ)^835 := by
    have hnat : (1948964267 : ℕ)^1091*25000000000000^835 ≤ 2951257541219^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1948964267 10000000000 2951257541219 25000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2807705941/5000000000 : ℝ)^1091 ≤ (47048450168327/100000000000000 : ℝ)^835 := by
    have hnat : (2807705941 : ℕ)^1091*100000000000000^835 ≤ 47048450168327^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2807705941 5000000000 47048450168327 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1013581617/2000000000 : ℝ)^1091 ≤ (41146519650907/100000000000000 : ℝ)^835 := by
    have hnat : (1013581617 : ℕ)^1091*100000000000000^835 ≤ 41146519650907^835*2000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1013581617 2000000000 41146519650907 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1948964267/10000000000 : ℝ), (2807705941/5000000000 : ℝ), (1013581617/2000000000 : ℝ)] ![(2951257541219/25000000000000 : ℝ), (47048450168327/100000000000000 : ℝ), (41146519650907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1948964267/10000000000 : ℝ)|^1091 ≤ (2951257541219/25000000000000 : ℝ)^835
        have hw : |(-1948964267/10000000000 : ℝ)|=(1948964267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2807705941/5000000000 : ℝ)|^1091 ≤ (47048450168327/100000000000000 : ℝ)^835
        have hw : |(2807705941/5000000000 : ℝ)|=(2807705941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1013581617/2000000000 : ℝ)|^1091 ≤ (41146519650907/100000000000000 : ℝ)^835
        have hw : |(1013581617/2000000000 : ℝ)|=(1013581617/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s1_1 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5399335267/10000000000 : ℝ)*x 0 + (-1119820991/5000000000 : ℝ)*x 1 + (5067908923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5399335267/10000000000 : ℝ)^1091 ≤ (44697100984979/100000000000000 : ℝ)^835 := by
    have hnat : (5399335267 : ℕ)^1091*100000000000000^835 ≤ 44697100984979^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399335267 10000000000 44697100984979 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1119820991/5000000000 : ℝ)^1091 ≤ (2831274090079/20000000000000 : ℝ)^835 := by
    have hnat : (1119820991 : ℕ)^1091*20000000000000^835 ≤ 2831274090079^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119820991 5000000000 2831274090079 20000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5067908923/10000000000 : ℝ)^1091 ≤ (20573264270299/50000000000000 : ℝ)^835 := by
    have hnat : (5067908923 : ℕ)^1091*50000000000000^835 ≤ 20573264270299^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5067908923 10000000000 20573264270299 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5399335267/10000000000 : ℝ), (-1119820991/5000000000 : ℝ), (5067908923/10000000000 : ℝ)] ![(44697100984979/100000000000000 : ℝ), (2831274090079/20000000000000 : ℝ), (20573264270299/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5399335267/10000000000 : ℝ)|^1091 ≤ (44697100984979/100000000000000 : ℝ)^835
        have hw : |(5399335267/10000000000 : ℝ)|=(5399335267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1119820991/5000000000 : ℝ)|^1091 ≤ (2831274090079/20000000000000 : ℝ)^835
        have hw : |(-1119820991/5000000000 : ℝ)|=(1119820991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5067908923/10000000000 : ℝ)|^1091 ≤ (20573264270299/50000000000000 : ℝ)^835
        have hw : |(5067908923/10000000000 : ℝ)|=(5067908923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s1_2 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5272789/9765625 : ℝ)*x 0 + (2533954203/5000000000 : ℝ)*x 1 + (-2239641771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5272789/9765625 : ℝ)^1091 ≤ (44697108221061/100000000000000 : ℝ)^835 := by
    have hnat : (5272789 : ℕ)^1091*100000000000000^835 ≤ 44697108221061^835*9765625^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272789 9765625 44697108221061 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2533954203/5000000000 : ℝ)^1091 ≤ (41146523056147/100000000000000 : ℝ)^835 := by
    have hnat : (2533954203 : ℕ)^1091*100000000000000^835 ≤ 41146523056147^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2533954203 5000000000 41146523056147 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2239641771/10000000000 : ℝ)^1091 ≤ (14156368707809/100000000000000 : ℝ)^835 := by
    have hnat : (2239641771 : ℕ)^1091*100000000000000^835 ≤ 14156368707809^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239641771 10000000000 14156368707809 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5272789/9765625 : ℝ), (2533954203/5000000000 : ℝ), (-2239641771/10000000000 : ℝ)] ![(44697108221061/100000000000000 : ℝ), (41146523056147/100000000000000 : ℝ), (14156368707809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5272789/9765625 : ℝ)|^1091 ≤ (44697108221061/100000000000000 : ℝ)^835
        have hw : |(5272789/9765625 : ℝ)|=(5272789/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2533954203/5000000000 : ℝ)|^1091 ≤ (41146523056147/100000000000000 : ℝ)^835
        have hw : |(2533954203/5000000000 : ℝ)|=(2533954203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2239641771/10000000000 : ℝ)|^1091 ≤ (14156368707809/100000000000000 : ℝ)^835
        have hw : |(-2239641771/10000000000 : ℝ)|=(2239641771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s1_3 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2140585841/5000000000 : ℝ)*x 0 + (186532913/500000000 : ℝ)*x 1 + (1226062599/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2140585841/5000000000 : ℝ)^1091 ≤ (4125861236843/12500000000000 : ℝ)^835 := by
    have hnat : (2140585841 : ℕ)^1091*12500000000000^835 ≤ 4125861236843^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140585841 5000000000 4125861236843 12500000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (186532913/500000000 : ℝ)^1091 ≤ (3446756051929/12500000000000 : ℝ)^835 := by
    have hnat : (186532913 : ℕ)^1091*12500000000000^835 ≤ 3446756051929^835*500000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      186532913 500000000 3446756051929 12500000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1226062599/2500000000 : ℝ)^1091 ≤ (39419061680747/100000000000000 : ℝ)^835 := by
    have hnat : (1226062599 : ℕ)^1091*100000000000000^835 ≤ 39419061680747^835*2500000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1226062599 2500000000 39419061680747 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2140585841/5000000000 : ℝ), (186532913/500000000 : ℝ), (1226062599/2500000000 : ℝ)] ![(4125861236843/12500000000000 : ℝ), (3446756051929/12500000000000 : ℝ), (39419061680747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2140585841/5000000000 : ℝ)|^1091 ≤ (4125861236843/12500000000000 : ℝ)^835
        have hw : |(2140585841/5000000000 : ℝ)|=(2140585841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(186532913/500000000 : ℝ)|^1091 ≤ (3446756051929/12500000000000 : ℝ)^835
        have hw : |(186532913/500000000 : ℝ)|=(186532913/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1226062599/2500000000 : ℝ)|^1091 ≤ (39419061680747/100000000000000 : ℝ)^835
        have hw : |(1226062599/2500000000 : ℝ)|=(1226062599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s1_4 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-487349479/2500000000 : ℝ)*x 0 + (5074455251/10000000000 : ℝ)*x 1 + (5608751453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (487349479/2500000000 : ℝ)^1091 ≤ (1180846222321/10000000000000 : ℝ)^835 := by
    have hnat : (487349479 : ℕ)^1091*10000000000000^835 ≤ 1180846222321^835*2500000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487349479 2500000000 1180846222321 10000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5074455251/10000000000 : ℝ)^1091 ≤ (41215987200057/100000000000000 : ℝ)^835 := by
    have hnat : (5074455251 : ℕ)^1091*100000000000000^835 ≤ 41215987200057^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5074455251 10000000000 41215987200057 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5608751453/10000000000 : ℝ)^1091 ≤ (23487775280357/50000000000000 : ℝ)^835 := by
    have hnat : (5608751453 : ℕ)^1091*50000000000000^835 ≤ 23487775280357^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5608751453 10000000000 23487775280357 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-487349479/2500000000 : ℝ), (5074455251/10000000000 : ℝ), (5608751453/10000000000 : ℝ)] ![(1180846222321/10000000000000 : ℝ), (41215987200057/100000000000000 : ℝ), (23487775280357/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-487349479/2500000000 : ℝ)|^1091 ≤ (1180846222321/10000000000000 : ℝ)^835
        have hw : |(-487349479/2500000000 : ℝ)|=(487349479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5074455251/10000000000 : ℝ)|^1091 ≤ (41215987200057/100000000000000 : ℝ)^835
        have hw : |(5074455251/10000000000 : ℝ)|=(5074455251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5608751453/10000000000 : ℝ)|^1091 ≤ (23487775280357/50000000000000 : ℝ)^835
        have hw : |(5608751453/10000000000 : ℝ)|=(5608751453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s1_5 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (328534803/625000000 : ℝ)*x 0 + (-1698799423/10000000000 : ℝ)*x 1 + (5608751353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328534803/625000000 : ℝ)^1091 ≤ (33718023883/78125000000 : ℝ)^835 := by
    have hnat : (328534803 : ℕ)^1091*78125000000^835 ≤ 33718023883^835*625000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328534803 625000000 33718023883 78125000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1698799423/10000000000 : ℝ)^1091 ≤ (4932689973727/50000000000000 : ℝ)^835 := by
    have hnat : (1698799423 : ℕ)^1091*50000000000000^835 ≤ 4932689973727^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1698799423 10000000000 4932689973727 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5608751353/10000000000 : ℝ)^1091 ≤ (9395109893279/20000000000000 : ℝ)^835 := by
    have hnat : (5608751353 : ℕ)^1091*20000000000000^835 ≤ 9395109893279^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5608751353 10000000000 9395109893279 20000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(328534803/625000000 : ℝ), (-1698799423/10000000000 : ℝ), (5608751353/10000000000 : ℝ)] ![(33718023883/78125000000 : ℝ), (4932689973727/50000000000000 : ℝ), (9395109893279/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(328534803/625000000 : ℝ)|^1091 ≤ (33718023883/78125000000 : ℝ)^835
        have hw : |(328534803/625000000 : ℝ)|=(328534803/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1698799423/10000000000 : ℝ)|^1091 ≤ (4932689973727/50000000000000 : ℝ)^835
        have hw : |(-1698799423/10000000000 : ℝ)|=(1698799423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5608751353/10000000000 : ℝ)|^1091 ≤ (9395109893279/20000000000000 : ℝ)^835
        have hw : |(5608751353/10000000000 : ℝ)|=(5608751353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s1_6 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5256557419/10000000000 : ℝ)*x 0 + (2804375907/5000000000 : ℝ)*x 1 + (-1698797951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256557419/10000000000 : ℝ)^1091 ≤ (4315907669579/10000000000000 : ℝ)^835 := by
    have hnat : (5256557419 : ℕ)^1091*10000000000000^835 ≤ 4315907669579^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256557419 10000000000 4315907669579 10000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2804375907/5000000000 : ℝ)^1091 ≤ (23487777255603/50000000000000 : ℝ)^835 := by
    have hnat : (2804375907 : ℕ)^1091*50000000000000^835 ≤ 23487777255603^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2804375907 5000000000 23487777255603 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1698797951/10000000000 : ℝ)^1091 ≤ (4932684389183/50000000000000 : ℝ)^835 := by
    have hnat : (1698797951 : ℕ)^1091*50000000000000^835 ≤ 4932684389183^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1698797951 10000000000 4932684389183 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256557419/10000000000 : ℝ), (2804375907/5000000000 : ℝ), (-1698797951/10000000000 : ℝ)] ![(4315907669579/10000000000000 : ℝ), (23487777255603/50000000000000 : ℝ), (4932684389183/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256557419/10000000000 : ℝ)|^1091 ≤ (4315907669579/10000000000000 : ℝ)^835
        have hw : |(5256557419/10000000000 : ℝ)|=(5256557419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2804375907/5000000000 : ℝ)|^1091 ≤ (23487777255603/50000000000000 : ℝ)^835
        have hw : |(2804375907/5000000000 : ℝ)|=(2804375907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1698797951/10000000000 : ℝ)|^1091 ≤ (4932684389183/50000000000000 : ℝ)^835
        have hw : |(-1698797951/10000000000 : ℝ)|=(1698797951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s1_7 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (535262853/1250000000 : ℝ)*x 0 + (195608617/400000000 : ℝ)*x 1 + (1872467269/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535262853/1250000000 : ℝ)^1091 ≤ (33016270063043/100000000000000 : ℝ)^835 := by
    have hnat : (535262853 : ℕ)^1091*100000000000000^835 ≤ 33016270063043^835*1250000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535262853 1250000000 33016270063043 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (195608617/400000000 : ℝ)^1091 ≤ (39271731151/100000000000 : ℝ)^835 := by
    have hnat : (195608617 : ℕ)^1091*100000000000^835 ≤ 39271731151^835*400000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195608617 400000000 39271731151 100000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1872467269/5000000000 : ℝ)^1091 ≤ (27711998763671/100000000000000 : ℝ)^835 := by
    have hnat : (1872467269 : ℕ)^1091*100000000000000^835 ≤ 27711998763671^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1872467269 5000000000 27711998763671 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535262853/1250000000 : ℝ), (195608617/400000000 : ℝ), (1872467269/5000000000 : ℝ)] ![(33016270063043/100000000000000 : ℝ), (39271731151/100000000000 : ℝ), (27711998763671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535262853/1250000000 : ℝ)|^1091 ≤ (33016270063043/100000000000000 : ℝ)^835
        have hw : |(535262853/1250000000 : ℝ)|=(535262853/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(195608617/400000000 : ℝ)|^1091 ≤ (39271731151/100000000000 : ℝ)^835
        have hw : |(195608617/400000000 : ℝ)|=(195608617/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1872467269/5000000000 : ℝ)|^1091 ≤ (27711998763671/100000000000000 : ℝ)^835
        have hw : |(1872467269/5000000000 : ℝ)|=(1872467269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1404_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39294187/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (826/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (187/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (3721/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2377/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (826/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (187/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (826/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (187/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (826/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (187/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (826/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (187/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (826/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (187/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (826/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (187/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (187/10000 : ℝ) ^ (4363/1024 : ℝ) ≤ (4332739977143/100000000000000000000 : ℝ) := by
    have hpowers : (187/10000 : ℝ)^4363 ≤ (4332739977143/100000000000000000000 : ℝ)^1024 := by
      have hnat : (187 : ℕ)^4363*100000000000000000000^1024 ≤ 4332739977143^1024*10000^4363 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        187 10000 4332739977143 100000000000000000000 4363 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (187/10000 : ℝ)) (X := (4332739977143/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (826/3125 : ℝ) ^ (4363/1024 : ℝ) ≤ (172510298121336731/50000000000000000000 : ℝ) := by
    have hpowers : (826/3125 : ℝ)^4363 ≤ (172510298121336731/50000000000000000000 : ℝ)^1024 := by
      have hnat : (826 : ℕ)^4363*50000000000000000000^1024 ≤ 172510298121336731^1024*3125^4363 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        826 3125 172510298121336731 50000000000000000000 4363 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (826/3125 : ℝ)) (X := (172510298121336731/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000004332739977143/50000000000000000000 : ℝ) ≤ (10000000203379583/10000000000000000 : ℝ) ^ (4363/1024 : ℝ) := by
    have hpowers : (50000004332739977143/50000000000000000000 : ℝ)^1024 ≤ (10000000203379583/10000000000000000 : ℝ)^4363 := by
      have hnat : (50000004332739977143 : ℕ)^1024*10000000000000000^4363 ≤ 10000000203379583^4363*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000004332739977143 50000000000000000000 10000000203379583 10000000000000000 1024 4363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000203379583/10000000000000000 : ℝ)) (X := (50000004332739977143/50000000000000000000 : ℝ)) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20069004985796530121/20000000000000000000 : ℝ) ≤ (10008087096613001/10000000000000000 : ℝ) ^ (4363/1024 : ℝ) := by
    have hpowers : (20069004985796530121/20000000000000000000 : ℝ)^1024 ≤ (10008087096613001/10000000000000000 : ℝ)^4363 := by
      have hnat : (20069004985796530121 : ℕ)^1024*10000000000000000^4363 ≤ 10008087096613001^4363*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20069004985796530121 20000000000000000000 10008087096613001 10000000000000000 1024 4363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008087096613001/10000000000000000 : ℝ)) (X := (20069004985796530121/20000000000000000000 : ℝ)) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25172510298121336731/25000000000000000000 : ℝ) ≤ (10016173989846419/10000000000000000 : ℝ) ^ (4363/1024 : ℝ) := by
    have hpowers : (25172510298121336731/25000000000000000000 : ℝ)^1024 ≤ (10016173989846419/10000000000000000 : ℝ)^4363 := by
      have hnat : (25172510298121336731 : ℕ)^1024*10000000000000000^4363 ≤ 10016173989846419^4363*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25172510298121336731 25000000000000000000 10016173989846419 10000000000000000 1024 4363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10016173989846419/10000000000000000 : ℝ)) (X := (25172510298121336731/25000000000000000000 : ℝ)) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4332739977143/100000000000000000000 : ℝ) ≤ ((122794880007358167163/122810000000000000000 : ℝ)+2*(4043446616709/1228100000000000 : ℝ)*(187/10000 : ℝ))^(4363/1024 : ℝ) := by
    rw [show (122794880007358167163/122810000000000000000 : ℝ)+2*(4043446616709/1228100000000000 : ℝ)*(187/10000 : ℝ)=(10000000203379583/10000000000000000 : ℝ) by norm_num, show 1+2*(4332739977143/100000000000000000000 : ℝ)=(50000004332739977143/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(172510298121336731/50000000000000000000 : ℝ)+(4332739977143/100000000000000000000 : ℝ) ≤ ((122794880007358167163/122810000000000000000 : ℝ)+(4043446616709/1228100000000000 : ℝ)*((826/3125 : ℝ)+(187/10000 : ℝ)))^(4363/1024 : ℝ) := by
    rw [show (122794880007358167163/122810000000000000000 : ℝ)+(4043446616709/1228100000000000 : ℝ)*((826/3125 : ℝ)+(187/10000 : ℝ))=(10008087096613001/10000000000000000 : ℝ) by norm_num, show 1+(172510298121336731/50000000000000000000 : ℝ)+(4332739977143/100000000000000000000 : ℝ)=(20069004985796530121/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(172510298121336731/50000000000000000000 : ℝ) ≤ ((122794880007358167163/122810000000000000000 : ℝ)+2*(4043446616709/1228100000000000 : ℝ)*(826/3125 : ℝ))^(4363/1024 : ℝ) := by
    rw [show (122794880007358167163/122810000000000000000 : ℝ)+2*(4043446616709/1228100000000000 : ℝ)*(826/3125 : ℝ)=(10016173989846419/10000000000000000 : ℝ) by norm_num, show 1+2*(172510298121336731/50000000000000000000 : ℝ)=(25172510298121336731/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (122794880007358167163/122810000000000000000 : ℝ)*(X 1 0+X 2 0)+(4043446616709/1228100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4363/1024 : ℝ)) (lo := (187/10000 : ℝ)) (hi := (826/3125 : ℝ)) (c := (122794880007358167163/122810000000000000000 : ℝ)) (alpha := (4043446616709/1228100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (122794880007358167163/122810000000000000000 : ℝ)*(X 0 1+X 2 1)+(4043446616709/1228100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4363/1024 : ℝ)) (lo := (187/10000 : ℝ)) (hi := (826/3125 : ℝ)) (c := (122794880007358167163/122810000000000000000 : ℝ)) (alpha := (4043446616709/1228100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (122794880007358167163/122810000000000000000 : ℝ)*(X 0 2+X 1 2)+(4043446616709/1228100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4363/1024 : ℝ)) (lo := (187/10000 : ℝ)) (hi := (826/3125 : ℝ)) (c := (122794880007358167163/122810000000000000000 : ℝ)) (alpha := (4043446616709/1228100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1948964267/10000000000 : ℝ)*X 0 0+(2807705941/5000000000 : ℝ)*X 0 1+(1013581617/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5399335267/10000000000 : ℝ)*X 1 0+(-1119820991/5000000000 : ℝ)*X 1 1+(5067908923/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5272789/9765625 : ℝ)*X 2 0+(2533954203/5000000000 : ℝ)*X 2 1+(-2239641771/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2140585841/5000000000 : ℝ)*X 0 0+(186532913/500000000 : ℝ)*X 0 1+(1226062599/2500000000 : ℝ)*X 0 2+(2140585841/5000000000 : ℝ)*X 1 0+(186532913/500000000 : ℝ)*X 1 1+(1226062599/2500000000 : ℝ)*X 1 2+(2140585841/5000000000 : ℝ)*X 2 0+(186532913/500000000 : ℝ)*X 2 1+(1226062599/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-487349479/2500000000 : ℝ)*X 0 0+(5074455251/10000000000 : ℝ)*X 0 1+(5608751453/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((328534803/625000000 : ℝ)*X 1 0+(-1698799423/10000000000 : ℝ)*X 1 1+(5608751353/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5256557419/10000000000 : ℝ)*X 2 0+(2804375907/5000000000 : ℝ)*X 2 1+(-1698797951/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((535262853/1250000000 : ℝ)*X 0 0+(195608617/400000000 : ℝ)*X 0 1+(1872467269/5000000000 : ℝ)*X 0 2+(535262853/1250000000 : ℝ)*X 1 0+(195608617/400000000 : ℝ)*X 1 1+(1872467269/5000000000 : ℝ)*X 1 2+(535262853/1250000000 : ℝ)*X 2 0+(195608617/400000000 : ℝ)*X 2 1+(1872467269/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9391887124054988879326892691/1535125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10339003/100000000000000 : ℝ)*(base1) + (22832823/2000000000000 : ℝ)*(base19) + (1367950961/100000000000000 : ℝ)*(base23) + (34585517/50000000000000 : ℝ)*(upper3) + (106908217/50000000000000 : ℝ)*(upper5) + (334823296639619/25000000000000 : ℝ)*(major0) + (334823296639619/25000000000000 : ℝ)*(major1) + (334823296639619/25000000000000 : ℝ)*(major2) + (1826480602323843/100000000000000 : ℝ)*(sp0) + (365298263092697/20000000000000 : ℝ)*(sp1) + (73059643566147/4000000000000 : ℝ)*(sp2) + (26627794584231/3125000000000 : ℝ)*(sp3) + (2373023959/20000000000000 : ℝ)*(sp4) + (855008949/20000000000000 : ℝ)*(sp7) + (42604685603957/5000000000000 : ℝ)*(f.failure) + (456623114276159/25000000000000 : ℝ)*(f.sum) + (52927750883669/61405000000000000000000000000 : ℝ)*base65 + (14419587915366269103/3070250000000000000000000000000000 : ℝ)*base68 + (5851015537709730897/3070250000000000000000000000000000 : ℝ)*base69 + (17282132748852019103/3070250000000000000000000000000000 : ℝ)*base72 + (113493207020891/61405000000000000000000000000 : ℝ)*base74 + (7205321648693480897/3070250000000000000000000000000000 : ℝ)*base75 + (18027403100028269103/3070250000000000000000000000000000 : ℝ)*base78 + (22655214169891019103/3070250000000000000000000000000000 : ℝ)*base80 + (241045917093599/61405000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (702041/125000000000000000000 : ℝ)*base90 + (702041/125000000000000000000 : ℝ)*base92 + (702041/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (52801303587874370368004202861/6140500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (259310133/100000000000000 : ℝ)*(base1) + (1019836133/50000000000000 : ℝ)*(base19) + (2356440833/100000000000000 : ℝ)*(base23) + (184430501/100000000000000 : ℝ)*(upper3) + (162118293/50000000000000 : ℝ)*(upper5) + (1372385929329149/100000000000000 : ℝ)*(major0) + (1372385929329149/100000000000000 : ℝ)*(major1) + (1372385929329149/100000000000000 : ℝ)*(major2) + (5057697337/50000000000000 : ℝ)*(sp1) + (14292601439/100000000000000 : ℝ)*(sp2) + (467905910483447/25000000000000 : ℝ)*(sp4) + (467902806889179/25000000000000 : ℝ)*(sp5) + (1871606733581383/100000000000000 : ℝ)*(sp6) + (174629586019163/20000000000000 : ℝ)*(sp7) + (218287047351487/25000000000000 : ℝ)*(f.failure) + (233952922827957/12500000000000 : ℝ)*(f.sum) + (200983819500919/61405000000000000000000000000 : ℝ)*base66 + (68713658030948365713/12281000000000000000000000000000000 : ℝ)*base68 + (78735893155900634287/12281000000000000000000000000000000 : ℝ)*base69 + (49601640666911365713/12281000000000000000000000000000000 : ℝ)*base72 + (147954041361077/30702500000000000000000000000 : ℝ)*base74 + (100636940483065365713/12281000000000000000000000000000000 : ℝ)*base76 + (37524299621566365713/12281000000000000000000000000000000 : ℝ)*base78 + (71010297540603634287/12281000000000000000000000000000000 : ℝ)*base79 + (142478415276601/61405000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (3656069/625000000000000000000 : ℝ)*base89 + (3656069/625000000000000000000 : ℝ)*base91 + (3656069/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1404_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39294187/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (826/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (187/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3721/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2377/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1404_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1404_s2_0 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1984004077/10000000000 : ℝ)*x 0 + (2731971913/5000000000 : ℝ)*x 1 + (20787411/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1984004077/10000000000 : ℝ)^1091 ≤ (6041549908797/50000000000000 : ℝ)^835 := by
    have hnat : (1984004077 : ℕ)^1091*50000000000000^835 ≤ 6041549908797^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1984004077 10000000000 6041549908797 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2731971913/5000000000 : ℝ)^1091 ≤ (907944052799/2000000000000 : ℝ)^835 := by
    have hnat : (2731971913 : ℕ)^1091*2000000000000^835 ≤ 907944052799^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731971913 5000000000 907944052799 2000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20787411/40000000 : ℝ)^1091 ≤ (42519697525671/100000000000000 : ℝ)^835 := by
    have hnat : (20787411 : ℕ)^1091*100000000000000^835 ≤ 42519697525671^835*40000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20787411 40000000 42519697525671 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1984004077/10000000000 : ℝ), (2731971913/5000000000 : ℝ), (20787411/40000000 : ℝ)] ![(6041549908797/50000000000000 : ℝ), (907944052799/2000000000000 : ℝ), (42519697525671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1984004077/10000000000 : ℝ)|^1091 ≤ (6041549908797/50000000000000 : ℝ)^835
        have hw : |(-1984004077/10000000000 : ℝ)|=(1984004077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2731971913/5000000000 : ℝ)|^1091 ≤ (907944052799/2000000000000 : ℝ)^835
        have hw : |(2731971913/5000000000 : ℝ)|=(2731971913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(20787411/40000000 : ℝ)|^1091 ≤ (42519697525671/100000000000000 : ℝ)^835
        have hw : |(20787411/40000000 : ℝ)|=(20787411/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s2_1 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2680875371/5000000000 : ℝ)*x 0 + (-530394441/2500000000 : ℝ)*x 1 + (2598426369/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2680875371/5000000000 : ℝ)^1091 ≤ (22145505638073/50000000000000 : ℝ)^835 := by
    have hnat : (2680875371 : ℕ)^1091*50000000000000^835 ≤ 22145505638073^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2680875371 5000000000 22145505638073 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (530394441/2500000000 : ℝ)^1091 ≤ (3297322830151/25000000000000 : ℝ)^835 := by
    have hnat : (530394441 : ℕ)^1091*25000000000000^835 ≤ 3297322830151^835*2500000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530394441 2500000000 3297322830151 25000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2598426369/5000000000 : ℝ)^1091 ≤ (10629924349347/25000000000000 : ℝ)^835 := by
    have hnat : (2598426369 : ℕ)^1091*25000000000000^835 ≤ 10629924349347^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598426369 5000000000 10629924349347 25000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2680875371/5000000000 : ℝ), (-530394441/2500000000 : ℝ), (2598426369/5000000000 : ℝ)] ![(22145505638073/50000000000000 : ℝ), (3297322830151/25000000000000 : ℝ), (10629924349347/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2680875371/5000000000 : ℝ)|^1091 ≤ (22145505638073/50000000000000 : ℝ)^835
        have hw : |(2680875371/5000000000 : ℝ)|=(2680875371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-530394441/2500000000 : ℝ)|^1091 ≤ (3297322830151/25000000000000 : ℝ)^835
        have hw : |(-530394441/2500000000 : ℝ)|=(530394441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2598426369/5000000000 : ℝ)|^1091 ≤ (10629924349347/25000000000000 : ℝ)^835
        have hw : |(2598426369/5000000000 : ℝ)|=(2598426369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s2_2 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1340437633/2500000000 : ℝ)*x 0 + (207874119/400000000 : ℝ)*x 1 + (-212157773/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1340437633/2500000000 : ℝ)^1091 ≤ (44291009009589/100000000000000 : ℝ)^835 := by
    have hnat : (1340437633 : ℕ)^1091*100000000000000^835 ≤ 44291009009589^835*2500000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340437633 2500000000 44291009009589 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207874119/400000000 : ℝ)^1091 ≤ (21259849965489/50000000000000 : ℝ)^835 := by
    have hnat : (207874119 : ℕ)^1091*50000000000000^835 ≤ 21259849965489^835*400000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207874119 400000000 21259849965489 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (212157773/1000000000 : ℝ)^1091 ≤ (824330690277/6250000000000 : ℝ)^835 := by
    have hnat : (212157773 : ℕ)^1091*6250000000000^835 ≤ 824330690277^835*1000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212157773 1000000000 824330690277 6250000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1340437633/2500000000 : ℝ), (207874119/400000000 : ℝ), (-212157773/1000000000 : ℝ)] ![(44291009009589/100000000000000 : ℝ), (21259849965489/50000000000000 : ℝ), (824330690277/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1340437633/2500000000 : ℝ)|^1091 ≤ (44291009009589/100000000000000 : ℝ)^835
        have hw : |(1340437633/2500000000 : ℝ)|=(1340437633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207874119/400000000 : ℝ)|^1091 ≤ (21259849965489/50000000000000 : ℝ)^835
        have hw : |(207874119/400000000 : ℝ)|=(207874119/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-212157773/1000000000 : ℝ)|^1091 ≤ (824330690277/6250000000000 : ℝ)^835
        have hw : |(-212157773/1000000000 : ℝ)|=(212157773/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s2_3 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2152920871/5000000000 : ℝ)*x 0 + (2014108071/5000000000 : ℝ)*x 1 + (460073527/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2152920871/5000000000 : ℝ)^1091 ≤ (16627811443671/50000000000000 : ℝ)^835 := by
    have hnat : (2152920871 : ℕ)^1091*50000000000000^835 ≤ 16627811443671^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152920871 5000000000 16627811443671 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2014108071/5000000000 : ℝ)^1091 ≤ (30482146179209/100000000000000 : ℝ)^835 := by
    have hnat : (2014108071 : ℕ)^1091*100000000000000^835 ≤ 30482146179209^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014108071 5000000000 30482146179209 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (460073527/1000000000 : ℝ)^1091 ≤ (36262230924363/100000000000000 : ℝ)^835 := by
    have hnat : (460073527 : ℕ)^1091*100000000000000^835 ≤ 36262230924363^835*1000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      460073527 1000000000 36262230924363 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2152920871/5000000000 : ℝ), (2014108071/5000000000 : ℝ), (460073527/1000000000 : ℝ)] ![(16627811443671/50000000000000 : ℝ), (30482146179209/100000000000000 : ℝ), (36262230924363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2152920871/5000000000 : ℝ)|^1091 ≤ (16627811443671/50000000000000 : ℝ)^835
        have hw : |(2152920871/5000000000 : ℝ)|=(2152920871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2014108071/5000000000 : ℝ)|^1091 ≤ (30482146179209/100000000000000 : ℝ)^835
        have hw : |(2014108071/5000000000 : ℝ)|=(2014108071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(460073527/1000000000 : ℝ)|^1091 ≤ (36262230924363/100000000000000 : ℝ)^835
        have hw : |(460073527/1000000000 : ℝ)|=(460073527/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s2_4 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1984054233/10000000000 : ℝ)*x 0 + (12996051/25000000 : ℝ)*x 1 + (5462363173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1984054233/10000000000 : ℝ)^1091 ≤ (241669978663/2000000000000 : ℝ)^835 := by
    have hnat : (1984054233 : ℕ)^1091*2000000000000^835 ≤ 241669978663^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1984054233 10000000000 241669978663 2000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (12996051/25000000 : ℝ)^1091 ≤ (10634114219367/25000000000000 : ℝ)^835 := by
    have hnat : (12996051 : ℕ)^1091*25000000000000^835 ≤ 10634114219367^835*25000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12996051 25000000 10634114219367 25000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5462363173/10000000000 : ℝ)^1091 ≤ (5672505521929/12500000000000 : ℝ)^835 := by
    have hnat : (5462363173 : ℕ)^1091*12500000000000^835 ≤ 5672505521929^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462363173 10000000000 5672505521929 12500000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1984054233/10000000000 : ℝ), (12996051/25000000 : ℝ), (5462363173/10000000000 : ℝ)] ![(241669978663/2000000000000 : ℝ), (10634114219367/25000000000000 : ℝ), (5672505521929/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1984054233/10000000000 : ℝ)|^1091 ≤ (241669978663/2000000000000 : ℝ)^835
        have hw : |(-1984054233/10000000000 : ℝ)|=(1984054233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(12996051/25000000 : ℝ)|^1091 ≤ (10634114219367/25000000000000 : ℝ)^835
        have hw : |(12996051/25000000 : ℝ)|=(12996051/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5462363173/10000000000 : ℝ)|^1091 ≤ (5672505521929/12500000000000 : ℝ)^835
        have hw : |(5462363173/10000000000 : ℝ)|=(5462363173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s2_5 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5292465007/10000000000 : ℝ)*x 0 + (-1856067937/10000000000 : ℝ)*x 1 + (1365590721/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5292465007/10000000000 : ℝ)^1091 ≤ (43544687380273/100000000000000 : ℝ)^835 := by
    have hnat : (5292465007 : ℕ)^1091*100000000000000^835 ≤ 43544687380273^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5292465007 10000000000 43544687380273 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1856067937/10000000000 : ℝ)^1091 ≤ (2215054312867/20000000000000 : ℝ)^835 := by
    have hnat : (1856067937 : ℕ)^1091*20000000000000^835 ≤ 2215054312867^835*10000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1856067937 10000000000 2215054312867 20000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1365590721/2500000000 : ℝ)^1091 ≤ (45380041038389/100000000000000 : ℝ)^835 := by
    have hnat : (1365590721 : ℕ)^1091*100000000000000^835 ≤ 45380041038389^835*2500000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365590721 2500000000 45380041038389 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5292465007/10000000000 : ℝ), (-1856067937/10000000000 : ℝ), (1365590721/2500000000 : ℝ)] ![(43544687380273/100000000000000 : ℝ), (2215054312867/20000000000000 : ℝ), (45380041038389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5292465007/10000000000 : ℝ)|^1091 ≤ (43544687380273/100000000000000 : ℝ)^835
        have hw : |(5292465007/10000000000 : ℝ)|=(5292465007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1856067937/10000000000 : ℝ)|^1091 ≤ (2215054312867/20000000000000 : ℝ)^835
        have hw : |(-1856067937/10000000000 : ℝ)|=(1856067937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1365590721/2500000000 : ℝ)|^1091 ≤ (45380041038389/100000000000000 : ℝ)^835
        have hw : |(1365590721/2500000000 : ℝ)|=(1365590721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s2_6 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2646233213/5000000000 : ℝ)*x 0 + (273118143/500000000 : ℝ)*x 1 + (-928033007/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646233213/5000000000 : ℝ)^1091 ≤ (43544702634769/100000000000000 : ℝ)^835 := by
    have hnat : (2646233213 : ℕ)^1091*100000000000000^835 ≤ 43544702634769^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646233213 5000000000 43544702634769 100000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273118143/500000000 : ℝ)^1091 ≤ (22690020388937/50000000000000 : ℝ)^835 := by
    have hnat : (273118143 : ℕ)^1091*50000000000000^835 ≤ 22690020388937^835*500000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273118143 500000000 22690020388937 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (928033007/5000000000 : ℝ)^1091 ≤ (5537628285849/50000000000000 : ℝ)^835 := by
    have hnat : (928033007 : ℕ)^1091*50000000000000^835 ≤ 5537628285849^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      928033007 5000000000 5537628285849 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646233213/5000000000 : ℝ), (273118143/500000000 : ℝ), (-928033007/5000000000 : ℝ)] ![(43544702634769/100000000000000 : ℝ), (22690020388937/50000000000000 : ℝ), (5537628285849/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646233213/5000000000 : ℝ)|^1091 ≤ (43544702634769/100000000000000 : ℝ)^835
        have hw : |(2646233213/5000000000 : ℝ)|=(2646233213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(273118143/500000000 : ℝ)|^1091 ≤ (22690020388937/50000000000000 : ℝ)^835
        have hw : |(273118143/500000000 : ℝ)|=(273118143/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-928033007/5000000000 : ℝ)|^1091 ≤ (5537628285849/50000000000000 : ℝ)^835
        have hw : |(-928033007/5000000000 : ℝ)|=(928033007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1404_s2_7 (p : ℝ) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2152975251/5000000000 : ℝ)*x 0 + (574671931/1250000000 : ℝ)*x 1 + (2015801923/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2152975251/5000000000 : ℝ)^1091 ≤ (16628360208391/50000000000000 : ℝ)^835 := by
    have hnat : (2152975251 : ℕ)^1091*50000000000000^835 ≤ 16628360208391^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152975251 5000000000 16628360208391 50000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (574671931/1250000000 : ℝ)^1091 ≤ (4528454292833/12500000000000 : ℝ)^835 := by
    have hnat : (574671931 : ℕ)^1091*12500000000000^835 ≤ 4528454292833^835*1250000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      574671931 1250000000 4528454292833 12500000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2015801923/5000000000 : ℝ)^1091 ≤ (3051564522853/10000000000000 : ℝ)^835 := by
    have hnat : (2015801923 : ℕ)^1091*10000000000000^835 ≤ 3051564522853^835*5000000000^1091 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015801923 5000000000 3051564522853 10000000000000 1091 835 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1091/256 : ℝ)) 1091 835 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2152975251/5000000000 : ℝ), (574671931/1250000000 : ℝ), (2015801923/5000000000 : ℝ)] ![(16628360208391/50000000000000 : ℝ), (4528454292833/12500000000000 : ℝ), (3051564522853/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2152975251/5000000000 : ℝ)|^1091 ≤ (16628360208391/50000000000000 : ℝ)^835
        have hw : |(2152975251/5000000000 : ℝ)|=(2152975251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(574671931/1250000000 : ℝ)|^1091 ≤ (4528454292833/12500000000000 : ℝ)^835
        have hw : |(574671931/1250000000 : ℝ)|=(574671931/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2015801923/5000000000 : ℝ)|^1091 ≤ (3051564522853/10000000000000 : ℝ)^835
        have hw : |(2015801923/5000000000 : ℝ)|=(2015801923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1404_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39294187/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2377/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3721/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1023/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15879/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2377/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3721/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2377/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3721/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2377/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3721/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2377/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3721/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2377/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3721/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2377/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3721/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3721/50000 : ℝ) ^ (4363/1024 : ℝ) ≤ (31159505273091/2000000000000000000 : ℝ) := by
    have hpowers : (3721/50000 : ℝ)^4363 ≤ (31159505273091/2000000000000000000 : ℝ)^1024 := by
      have hnat : (3721 : ℕ)^4363*2000000000000000000^1024 ≤ 31159505273091^1024*50000^4363 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3721 50000 31159505273091 2000000000000000000 4363 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3721/50000 : ℝ)) (X := (31159505273091/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2377/12500 : ℝ) ^ (4363/1024 : ℝ) ≤ (21205701249400153/25000000000000000000 : ℝ) := by
    have hpowers : (2377/12500 : ℝ)^4363 ≤ (21205701249400153/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2377 : ℕ)^4363*25000000000000000000^1024 ≤ 21205701249400153^1024*12500^4363 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2377 12500 21205701249400153 25000000000000000000 4363 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2377/12500 : ℝ)) (X := (21205701249400153/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1000031159505273091/1000000000000000000 : ℝ) ≤ (500003656538273/500000000000000 : ℝ) ^ (4363/1024 : ℝ) := by
    have hpowers : (1000031159505273091/1000000000000000000 : ℝ)^1024 ≤ (500003656538273/500000000000000 : ℝ)^4363 := by
      have hnat : (1000031159505273091 : ℕ)^1024*500000000000000^4363 ≤ 500003656538273^4363*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000031159505273091 1000000000000000000 500003656538273 500000000000000 1024 4363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500003656538273/500000000000000 : ℝ)) (X := (1000031159505273091/1000000000000000000 : ℝ)) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50043190390130627581/50000000000000000000 : ℝ) ≤ (5001013347429113/5000000000000000 : ℝ) ^ (4363/1024 : ℝ) := by
    have hpowers : (50043190390130627581/50000000000000000000 : ℝ)^1024 ≤ (5001013347429113/5000000000000000 : ℝ)^4363 := by
      have hnat : (50043190390130627581 : ℕ)^1024*5000000000000000^4363 ≤ 5001013347429113^4363*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50043190390130627581 50000000000000000000 5001013347429113 5000000000000000 1024 4363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001013347429113/5000000000000000 : ℝ)) (X := (50043190390130627581/50000000000000000000 : ℝ)) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12521205701249400153/12500000000000000000 : ℝ) ≤ (625248766184437/625000000000000 : ℝ) ^ (4363/1024 : ℝ) := by
    have hpowers : (12521205701249400153/12500000000000000000 : ℝ)^1024 ≤ (625248766184437/625000000000000 : ℝ)^4363 := by
      have hnat : (12521205701249400153 : ℕ)^1024*625000000000000^4363 ≤ 625248766184437^4363*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12521205701249400153 12500000000000000000 625248766184437 625000000000000 1024 4363 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625248766184437/625000000000000 : ℝ)) (X := (12521205701249400153/12500000000000000000 : ℝ)) (by norm_num) 4363 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(31159505273091/2000000000000000000 : ℝ) ≤ ((25111061104063087/25117187500000000 : ℝ)+2*(108531338487/64300000000000 : ℝ)*(3721/50000 : ℝ))^(4363/1024 : ℝ) := by
    rw [show (25111061104063087/25117187500000000 : ℝ)+2*(108531338487/64300000000000 : ℝ)*(3721/50000 : ℝ)=(500003656538273/500000000000000 : ℝ) by norm_num, show 1+2*(31159505273091/2000000000000000000 : ℝ)=(1000031159505273091/1000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21205701249400153/25000000000000000000 : ℝ)+(31159505273091/2000000000000000000 : ℝ) ≤ ((25111061104063087/25117187500000000 : ℝ)+(108531338487/64300000000000 : ℝ)*((2377/12500 : ℝ)+(3721/50000 : ℝ)))^(4363/1024 : ℝ) := by
    rw [show (25111061104063087/25117187500000000 : ℝ)+(108531338487/64300000000000 : ℝ)*((2377/12500 : ℝ)+(3721/50000 : ℝ))=(5001013347429113/5000000000000000 : ℝ) by norm_num, show 1+(21205701249400153/25000000000000000000 : ℝ)+(31159505273091/2000000000000000000 : ℝ)=(50043190390130627581/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21205701249400153/25000000000000000000 : ℝ) ≤ ((25111061104063087/25117187500000000 : ℝ)+2*(108531338487/64300000000000 : ℝ)*(2377/12500 : ℝ))^(4363/1024 : ℝ) := by
    rw [show (25111061104063087/25117187500000000 : ℝ)+2*(108531338487/64300000000000 : ℝ)*(2377/12500 : ℝ)=(625248766184437/625000000000000 : ℝ) by norm_num, show 1+2*(21205701249400153/25000000000000000000 : ℝ)=(12521205701249400153/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (25111061104063087/25117187500000000 : ℝ)*(X 1 0+X 2 0)+(108531338487/64300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4363/1024 : ℝ)) (lo := (3721/50000 : ℝ)) (hi := (2377/12500 : ℝ)) (c := (25111061104063087/25117187500000000 : ℝ)) (alpha := (108531338487/64300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (25111061104063087/25117187500000000 : ℝ)*(X 0 1+X 2 1)+(108531338487/64300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4363/1024 : ℝ)) (lo := (3721/50000 : ℝ)) (hi := (2377/12500 : ℝ)) (c := (25111061104063087/25117187500000000 : ℝ)) (alpha := (108531338487/64300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (25111061104063087/25117187500000000 : ℝ)*(X 0 2+X 1 2)+(108531338487/64300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4363/1024 : ℝ)) (lo := (3721/50000 : ℝ)) (hi := (2377/12500 : ℝ)) (c := (25111061104063087/25117187500000000 : ℝ)) (alpha := (108531338487/64300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1984004077/10000000000 : ℝ)*X 0 0+(2731971913/5000000000 : ℝ)*X 0 1+(20787411/40000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2680875371/5000000000 : ℝ)*X 1 0+(-530394441/2500000000 : ℝ)*X 1 1+(2598426369/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1340437633/2500000000 : ℝ)*X 2 0+(207874119/400000000 : ℝ)*X 2 1+(-212157773/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2152920871/5000000000 : ℝ)*X 0 0+(2014108071/5000000000 : ℝ)*X 0 1+(460073527/1000000000 : ℝ)*X 0 2+(2152920871/5000000000 : ℝ)*X 1 0+(2014108071/5000000000 : ℝ)*X 1 1+(460073527/1000000000 : ℝ)*X 1 2+(2152920871/5000000000 : ℝ)*X 2 0+(2014108071/5000000000 : ℝ)*X 2 1+(460073527/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1984054233/10000000000 : ℝ)*X 0 0+(12996051/25000000 : ℝ)*X 0 1+(5462363173/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5292465007/10000000000 : ℝ)*X 1 0+(-1856067937/10000000000 : ℝ)*X 1 1+(1365590721/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2646233213/5000000000 : ℝ)*X 2 0+(273118143/500000000 : ℝ)*X 2 1+(-928033007/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2152975251/5000000000 : ℝ)*X 0 0+(574671931/1250000000 : ℝ)*X 0 1+(2015801923/5000000000 : ℝ)*X 0 2+(2152975251/5000000000 : ℝ)*X 1 0+(574671931/1250000000 : ℝ)*X 1 1+(2015801923/5000000000 : ℝ)*X 1 2+(2152975251/5000000000 : ℝ)*X 2 0+(574671931/1250000000 : ℝ)*X 2 1+(2015801923/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1404_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12428825186929909066412031/2511718750000000000000000000000 : ℝ) := by norm_num
    linear_combination (354558493/50000000000000 : ℝ)*(base19) + (53542723/12500000000000 : ℝ)*(base23) + (71919477/100000000000000 : ℝ)*(lower2) + (31204461/20000000000000 : ℝ)*(upper3) + (47836829/100000000000000 : ℝ)*(upper5) + (1372682849030049/50000000000000 : ℝ)*(major0) + (1372682849030049/50000000000000 : ℝ)*(major1) + (1372682849030049/50000000000000 : ℝ)*(major2) + (748810050696283/20000000000000 : ℝ)*(sp0) + (1872028163464487/50000000000000 : ℝ)*(sp1) + (149762264308167/4000000000000 : ℝ)*(sp2) + (27291715657579/1562500000000 : ℝ)*(sp3) + (1356512909/20000000000000 : ℝ)*(sp4) + (4393044683/100000000000000 : ℝ)*(sp7) + (1746674195129739/100000000000000 : ℝ)*(f.failure) + (93601425901149/2500000000000 : ℝ)*(f.sum) + (3516776251239/803750000000000000000000000 : ℝ)*base65 + (83827148031849271/10046875000000000000000000000000 : ℝ)*base68 + (7267273791717487/1255859375000000000000000000000 : ℝ)*base70 + (75737991019349271/10046875000000000000000000000000 : ℝ)*base72 + (2381241155137/1607500000000000000000000000 : ℝ)*base74 + (2712835258275729/10046875000000000000000000000000 : ℝ)*base75 + (78189453542275729/10046875000000000000000000000000 : ℝ)*base77 + (719058603404987/1255859375000000000000000000000 : ℝ)*base80 + (6274880053847/1607500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (3527193/2500000000000000000000 : ℝ)*base89 + (3527193/2500000000000000000000 : ℝ)*base91 + (3527193/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23284059045411489827940423/10046875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (97526469/25000000000000 : ℝ)*(base19) + (1735550169/100000000000000 : ℝ)*(base23) + (157435839/100000000000000 : ℝ)*(lower2) + (13504459/20000000000000 : ℝ)*(upper3) + (59132673/50000000000000 : ℝ)*(lower4) + (2778104716743329/100000000000000 : ℝ)*(major0) + (2778104716743329/100000000000000 : ℝ)*(major1) + (2778104716743329/100000000000000 : ℝ)*(major2) + (6166640331/20000000000000 : ℝ)*(sp2) + (953397639/100000000000000 : ℝ)*(sp3) + (3788705732389211/100000000000000 : ℝ)*(sp4) + (1894352671141667/50000000000000 : ℝ)*(sp5) + (1894336581818693/50000000000000 : ℝ)*(sp6) + (1767502670448383/100000000000000 : ℝ)*(sp7) + (1767503623846021/100000000000000 : ℝ)*(f.failure) + (3788705732389211/100000000000000 : ℝ)*(f.sum) + (82125839169/100468750000000000000000000 : ℝ)*base65 + (24260578122192641/20093750000000000000000000000000 : ℝ)*base68 + (81084094548213609/20093750000000000000000000000000 : ℝ)*base69 + (216571354132182359/20093750000000000000000000000000 : ℝ)*base71 + (19641706272037/3215000000000000000000000000 : ℝ)*base74 + (282334077417619859/20093750000000000000000000000000 : ℝ)*base75 + (59288496986380141/20093750000000000000000000000000 : ℝ)*base78 + (294159990691713609/20093750000000000000000000000000 : ℝ)*base79 + (2237530532513/3215000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (16620073/2500000000000000000000 : ℝ)*base90 + (16620073/2500000000000000000000 : ℝ)*base92 + (16620073/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1404_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39294187/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2377/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3721/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1023/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15879/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1404_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1404_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39294187/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1023/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15879/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1404_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1404_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1404_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4363/1024 : ℝ) ≤ p) (hpb : p ≤ (1091/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39294187/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1023/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15879/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1404_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
