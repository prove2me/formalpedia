-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1033_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:41:08.550924+00:00
-- url     : https://prove2.me/submissions/818e5691-1e88-4284-8a49-f8c46b88860c

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
theorem support_rectangle_w1033_s0_0 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5472758991/10000000000 : ℝ)*x 0 + (-1358382523/5000000000 : ℝ)*x 1 + (4791770663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5472758991/10000000000 : ℝ)^4113 ≤ (11203714273417/25000000000000 : ℝ)^3089 := by
    have hnat : (5472758991 : ℕ)^4113*25000000000000^3089 ≤ 11203714273417^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5472758991 10000000000 11203714273417 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358382523/5000000000 : ℝ)^4113 ≤ (8818830417353/50000000000000 : ℝ)^3089 := by
    have hnat : (1358382523 : ℕ)^4113*50000000000000^3089 ≤ 8818830417353^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358382523 5000000000 8818830417353 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4791770663/10000000000 : ℝ)^4113 ≤ (18773741025267/50000000000000 : ℝ)^3089 := by
    have hnat : (4791770663 : ℕ)^4113*50000000000000^3089 ≤ 18773741025267^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4791770663 10000000000 18773741025267 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5472758991/10000000000 : ℝ), (-1358382523/5000000000 : ℝ), (4791770663/10000000000 : ℝ)] ![(11203714273417/25000000000000 : ℝ), (8818830417353/50000000000000 : ℝ), (18773741025267/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5472758991/10000000000 : ℝ)|^4113 ≤ (11203714273417/25000000000000 : ℝ)^3089
        have hw : |(5472758991/10000000000 : ℝ)|=(5472758991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1358382523/5000000000 : ℝ)|^4113 ≤ (8818830417353/50000000000000 : ℝ)^3089
        have hw : |(-1358382523/5000000000 : ℝ)|=(1358382523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4791770663/10000000000 : ℝ)|^4113 ≤ (18773741025267/50000000000000 : ℝ)^3089
        have hw : |(4791770663/10000000000 : ℝ)|=(4791770663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s0_1 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5464344427/10000000000 : ℝ)*x 0 + (74947947/156250000 : ℝ)*x 1 + (-108858473/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5464344427/10000000000 : ℝ)^4113 ≤ (1397597946163/3125000000000 : ℝ)^3089 := by
    have hnat : (5464344427 : ℕ)^4113*3125000000000^3089 ≤ 1397597946163^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5464344427 10000000000 1397597946163 3125000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (74947947/156250000 : ℝ)^4113 ≤ (7519718578973/20000000000000 : ℝ)^3089 := by
    have hnat : (74947947 : ℕ)^4113*20000000000000^3089 ≤ 7519718578973^3089*156250000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74947947 156250000 7519718578973 20000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108858473/400000000 : ℝ)^4113 ≤ (17678272819429/100000000000000 : ℝ)^3089 := by
    have hnat : (108858473 : ℕ)^4113*100000000000000^3089 ≤ 17678272819429^3089*400000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108858473 400000000 17678272819429 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5464344427/10000000000 : ℝ), (74947947/156250000 : ℝ), (-108858473/400000000 : ℝ)] ![(1397597946163/3125000000000 : ℝ), (7519718578973/20000000000000 : ℝ), (17678272819429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5464344427/10000000000 : ℝ)|^4113 ≤ (1397597946163/3125000000000 : ℝ)^3089
        have hw : |(5464344427/10000000000 : ℝ)|=(5464344427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(74947947/156250000 : ℝ)|^4113 ≤ (7519718578973/20000000000000 : ℝ)^3089
        have hw : |(74947947/156250000 : ℝ)|=(74947947/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-108858473/400000000 : ℝ)|^4113 ≤ (17678272819429/100000000000000 : ℝ)^3089
        have hw : |(-108858473/400000000 : ℝ)|=(108858473/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s0_2 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-386453591/2000000000 : ℝ)*x 0 + (240022847/500000000 : ℝ)*x 1 + (6044761559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (386453591/2000000000 : ℝ)^4113 ≤ (11204680765619/100000000000000 : ℝ)^3089 := by
    have hnat : (386453591 : ℕ)^4113*100000000000000^3089 ≤ 11204680765619^3089*2000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      386453591 2000000000 11204680765619 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (240022847/500000000 : ℝ)^4113 ≤ (18819068308641/50000000000000 : ℝ)^3089 := by
    have hnat : (240022847 : ℕ)^4113*50000000000000^3089 ≤ 18819068308641^3089*500000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240022847 500000000 18819068308641 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6044761559/10000000000 : ℝ)^4113 ≤ (51157182604031/100000000000000 : ℝ)^3089 := by
    have hnat : (6044761559 : ℕ)^4113*100000000000000^3089 ≤ 51157182604031^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6044761559 10000000000 51157182604031 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-386453591/2000000000 : ℝ), (240022847/500000000 : ℝ), (6044761559/10000000000 : ℝ)] ![(11204680765619/100000000000000 : ℝ), (18819068308641/50000000000000 : ℝ), (51157182604031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-386453591/2000000000 : ℝ)|^4113 ≤ (11204680765619/100000000000000 : ℝ)^3089
        have hw : |(-386453591/2000000000 : ℝ)|=(386453591/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(240022847/500000000 : ℝ)|^4113 ≤ (18819068308641/50000000000000 : ℝ)^3089
        have hw : |(240022847/500000000 : ℝ)|=(240022847/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6044761559/10000000000 : ℝ)|^4113 ≤ (51157182604031/100000000000000 : ℝ)^3089
        have hw : |(6044761559/10000000000 : ℝ)|=(6044761559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s0_3 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1291664307/2500000000 : ℝ)*x 0 + (-351381751/2500000000 : ℝ)*x 1 + (3022380703/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1291664307/2500000000 : ℝ)^4113 ≤ (41508684896041/100000000000000 : ℝ)^3089 := by
    have hnat : (1291664307 : ℕ)^4113*100000000000000^3089 ≤ 41508684896041^3089*2500000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1291664307 2500000000 41508684896041 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (351381751/2500000000 : ℝ)^4113 ≤ (366706709949/5000000000000 : ℝ)^3089 := by
    have hnat : (351381751 : ℕ)^4113*5000000000000^3089 ≤ 366706709949^3089*2500000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      351381751 2500000000 366706709949 5000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3022380703/5000000000 : ℝ)^4113 ≤ (25578590439971/50000000000000 : ℝ)^3089 := by
    have hnat : (3022380703 : ℕ)^4113*50000000000000^3089 ≤ 25578590439971^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3022380703 5000000000 25578590439971 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1291664307/2500000000 : ℝ), (-351381751/2500000000 : ℝ), (3022380703/5000000000 : ℝ)] ![(41508684896041/100000000000000 : ℝ), (366706709949/5000000000000 : ℝ), (25578590439971/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1291664307/2500000000 : ℝ)|^4113 ≤ (41508684896041/100000000000000 : ℝ)^3089
        have hw : |(1291664307/2500000000 : ℝ)|=(1291664307/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-351381751/2500000000 : ℝ)|^4113 ≤ (366706709949/5000000000000 : ℝ)^3089
        have hw : |(-351381751/2500000000 : ℝ)|=(351381751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3022380703/5000000000 : ℝ)|^4113 ≤ (25578590439971/50000000000000 : ℝ)^3089
        have hw : |(3022380703/5000000000 : ℝ)|=(3022380703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s0_4 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5166657199/10000000000 : ℝ)*x 0 + (1511190357/2500000000 : ℝ)*x 1 + (-702763507/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5166657199/10000000000 : ℝ)^4113 ≤ (41508684585823/100000000000000 : ℝ)^3089 := by
    have hnat : (5166657199 : ℕ)^4113*100000000000000^3089 ≤ 41508684585823^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5166657199 10000000000 41508684585823 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1511190357/2500000000 : ℝ)^4113 ≤ (1023143622557/2000000000000 : ℝ)^3089 := by
    have hnat : (1511190357 : ℕ)^4113*2000000000000^3089 ≤ 1023143622557^3089*2500000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1511190357 2500000000 1023143622557 2000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (702763507/5000000000 : ℝ)^4113 ≤ (3667067134229/50000000000000 : ℝ)^3089 := by
    have hnat : (702763507 : ℕ)^4113*50000000000000^3089 ≤ 3667067134229^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      702763507 5000000000 3667067134229 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5166657199/10000000000 : ℝ), (1511190357/2500000000 : ℝ), (-702763507/5000000000 : ℝ)] ![(41508684585823/100000000000000 : ℝ), (1023143622557/2000000000000 : ℝ), (3667067134229/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5166657199/10000000000 : ℝ)|^4113 ≤ (41508684585823/100000000000000 : ℝ)^3089
        have hw : |(5166657199/10000000000 : ℝ)|=(5166657199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1511190357/2500000000 : ℝ)|^4113 ≤ (1023143622557/2000000000000 : ℝ)^3089
        have hw : |(1511190357/2500000000 : ℝ)|=(1511190357/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-702763507/5000000000 : ℝ)|^4113 ≤ (3667067134229/50000000000000 : ℝ)^3089
        have hw : |(-702763507/5000000000 : ℝ)|=(702763507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s0_5 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4220613529/10000000000 : ℝ)*x 0 + (5617731261/10000000000 : ℝ)*x 1 + (3195033123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4220613529/10000000000 : ℝ)^4113 ≤ (3963674942753/12500000000000 : ℝ)^3089 := by
    have hnat : (4220613529 : ℕ)^4113*12500000000000^3089 ≤ 3963674942753^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4220613529 10000000000 3963674942753 12500000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5617731261/10000000000 : ℝ)^4113 ≤ (46402427584583/100000000000000 : ℝ)^3089 := by
    have hnat : (5617731261 : ℕ)^4113*100000000000000^3089 ≤ 46402427584583^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5617731261 10000000000 46402427584583 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3195033123/10000000000 : ℝ)^4113 ≤ (21888172855489/100000000000000 : ℝ)^3089 := by
    have hnat : (3195033123 : ℕ)^4113*100000000000000^3089 ≤ 21888172855489^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3195033123 10000000000 21888172855489 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4220613529/10000000000 : ℝ), (5617731261/10000000000 : ℝ), (3195033123/10000000000 : ℝ)] ![(3963674942753/12500000000000 : ℝ), (46402427584583/100000000000000 : ℝ), (21888172855489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4220613529/10000000000 : ℝ)|^4113 ≤ (3963674942753/12500000000000 : ℝ)^3089
        have hw : |(4220613529/10000000000 : ℝ)|=(4220613529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5617731261/10000000000 : ℝ)|^4113 ≤ (46402427584583/100000000000000 : ℝ)^3089
        have hw : |(5617731261/10000000000 : ℝ)|=(5617731261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3195033123/10000000000 : ℝ)|^4113 ≤ (21888172855489/100000000000000 : ℝ)^3089
        have hw : |(3195033123/10000000000 : ℝ)|=(3195033123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1033_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18418937/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (0 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14119/50000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
  have base43 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*X 2 1) ≤ (0 : ℝ) := by
    linarith only [sign0]
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
  have hpowlo : (0 : ℝ) ^ (8225/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8225 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8225*1^2048 ≤ 0^2048*1^8225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8225 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8225/2048 : ℝ) ≤ (100899226602081563/4000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8225 ≤ (100899226602081563/4000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8225*4000000000000000000^2048 ≤ 100899226602081563^2048*5^8225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 100899226602081563 4000000000000000000 8225 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (100899226602081563/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8225/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8225 := by
      have hnat : (1 : ℕ)^2048*1^8225 ≤ 1^8225*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (4100899226602081563/4000000000000000000 : ℝ) ≤ (628888917987063/625000000000000 : ℝ) ^ (8225/2048 : ℝ) := by
    have hpowers : (4100899226602081563/4000000000000000000 : ℝ)^2048 ≤ (628888917987063/625000000000000 : ℝ)^8225 := by
      have hnat : (4100899226602081563 : ℕ)^2048*625000000000000^8225 ≤ 628888917987063^8225*4000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4100899226602081563 4000000000000000000 628888917987063 625000000000000 2048 8225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (628888917987063/625000000000000 : ℝ)) (X := (4100899226602081563/4000000000000000000 : ℝ)) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (2100899226602081563/2000000000000000000 : ℝ) ≤ (316388917987063/312500000000000 : ℝ) ^ (8225/2048 : ℝ) := by
    have hpowers : (2100899226602081563/2000000000000000000 : ℝ)^2048 ≤ (316388917987063/312500000000000 : ℝ)^8225 := by
      have hnat : (2100899226602081563 : ℕ)^2048*312500000000000^8225 ≤ 316388917987063^8225*2000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2100899226602081563 2000000000000000000 316388917987063 312500000000000 2048 8225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (316388917987063/312500000000000 : ℝ)) (X := (2100899226602081563/2000000000000000000 : ℝ)) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(3888917987063/250000000000000 : ℝ)*(0 : ℝ))^(8225/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(3888917987063/250000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(100899226602081563/4000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(3888917987063/250000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8225/2048 : ℝ) := by
    rw [show (1 : ℝ)+(3888917987063/250000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(628888917987063/625000000000000 : ℝ) by norm_num, show 1+(100899226602081563/4000000000000000000 : ℝ)+(0 : ℝ)=(4100899226602081563/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(100899226602081563/4000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(3888917987063/250000000000000 : ℝ)*(2/5 : ℝ))^(8225/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(3888917987063/250000000000000 : ℝ)*(2/5 : ℝ)=(316388917987063/312500000000000 : ℝ) by norm_num, show 1+2*(100899226602081563/4000000000000000000 : ℝ)=(2100899226602081563/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(3888917987063/250000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8225/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3888917987063/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(3888917987063/250000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8225/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3888917987063/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(3888917987063/250000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8225/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3888917987063/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5472758991/10000000000 : ℝ)*X 1 0+(-1358382523/5000000000 : ℝ)*X 1 1+(4791770663/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s0_0 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5464344427/10000000000 : ℝ)*X 2 0+(74947947/156250000 : ℝ)*X 2 1+(-108858473/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s0_1 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-386453591/2000000000 : ℝ)*X 0 0+(240022847/500000000 : ℝ)*X 0 1+(6044761559/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s0_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1291664307/2500000000 : ℝ)*X 1 0+(-351381751/2500000000 : ℝ)*X 1 1+(3022380703/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s0_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((5166657199/10000000000 : ℝ)*X 2 0+(1511190357/2500000000 : ℝ)*X 2 1+(-702763507/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s0_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4220613529/10000000000 : ℝ)*X 0 0+(5617731261/10000000000 : ℝ)*X 0 1+(3195033123/10000000000 : ℝ)*X 0 2+(4220613529/10000000000 : ℝ)*X 1 0+(5617731261/10000000000 : ℝ)*X 1 1+(3195033123/10000000000 : ℝ)*X 1 2+(4220613529/10000000000 : ℝ)*X 2 0+(5617731261/10000000000 : ℝ)*X 2 1+(3195033123/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s0_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(base43) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11901145745285901809421/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (257236459/50000000000000 : ℝ)*(base19) + (508148253/100000000000000 : ℝ)*(base23) + (56319/12500000000000 : ℝ)*(base39) + (3239069/5000000000000 : ℝ)*(upper3) + (32432427/50000000000000 : ℝ)*(upper5) + (608212357598739/100000000000000 : ℝ)*(major0) + (608212357598739/100000000000000 : ℝ)*(major1) + (304106178574093/50000000000000 : ℝ)*(major2) + (504428747/50000000000000 : ℝ)*(sp0) + (499154933/50000000000000 : ℝ)*(sp1) + (25114428677197/3125000000000 : ℝ)*(sp2) + (200915048584973/25000000000000 : ℝ)*(sp3) + (803660211662737/100000000000000 : ℝ)*(sp4) + (103190733400959/25000000000000 : ℝ)*(sp5) + (103190733400959/25000000000000 : ℝ)*(f.failure) + (803661718120857/100000000000000 : ℝ)*(f.sum) + (1451890162749/1000000000000000000000000000 : ℝ)*base66 + (53526324008859/12500000000000000000000000000 : ℝ)*base67 + (131268446986443/25000000000000000000000000000 : ℝ)*base70 + (63410846283859/12500000000000000000000000000 : ℝ)*base71 + (2810220142749/1000000000000000000000000000 : ℝ)*base74 + (57510015436443/25000000000000000000000000000 : ℝ)*base76 + (91473954888557/25000000000000000000000000000 : ℝ)*base77 + (215901343113557/25000000000000000000000000000 : ℝ)*base79 + (35762316136443/12500000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (185583/312500000000000000000 : ℝ)*base89 + (185583/312500000000000000000 : ℝ)*base91 + (3310583/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1033_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18418937/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14119/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1033_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1033_s1_0 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-534803749/2500000000 : ℝ)*x 0 + (2865657729/5000000000 : ℝ)*x 1 + (77797601/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534803749/2500000000 : ℝ)^4113 ≤ (6415116424139/50000000000000 : ℝ)^3089 := by
    have hnat : (534803749 : ℕ)^4113*50000000000000^3089 ≤ 6415116424139^3089*2500000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534803749 2500000000 6415116424139 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2865657729/5000000000 : ℝ)^4113 ≤ (23827906991557/50000000000000 : ℝ)^3089 := by
    have hnat : (2865657729 : ℕ)^4113*50000000000000^3089 ≤ 23827906991557^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2865657729 5000000000 23827906991557 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (77797601/156250000 : ℝ)^4113 ≤ (9878488287937/25000000000000 : ℝ)^3089 := by
    have hnat : (77797601 : ℕ)^4113*25000000000000^3089 ≤ 9878488287937^3089*156250000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77797601 156250000 9878488287937 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-534803749/2500000000 : ℝ), (2865657729/5000000000 : ℝ), (77797601/156250000 : ℝ)] ![(6415116424139/50000000000000 : ℝ), (23827906991557/50000000000000 : ℝ), (9878488287937/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-534803749/2500000000 : ℝ)|^4113 ≤ (6415116424139/50000000000000 : ℝ)^3089
        have hw : |(-534803749/2500000000 : ℝ)|=(534803749/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2865657729/5000000000 : ℝ)|^4113 ≤ (23827906991557/50000000000000 : ℝ)^3089
        have hw : |(2865657729/5000000000 : ℝ)|=(2865657729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(77797601/156250000 : ℝ)|^4113 ≤ (9878488287937/25000000000000 : ℝ)^3089
        have hw : |(77797601/156250000 : ℝ)|=(77797601/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s1_1 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2712566269/5000000000 : ℝ)*x 0 + (-2547489467/10000000000 : ℝ)*x 1 + (622380847/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2712566269/5000000000 : ℝ)^4113 ≤ (44296323830577/100000000000000 : ℝ)^3089 := by
    have hnat : (2712566269 : ℕ)^4113*100000000000000^3089 ≤ 44296323830577^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712566269 5000000000 44296323830577 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2547489467/10000000000 : ℝ)^4113 ≤ (404742992371/2500000000000 : ℝ)^3089 := by
    have hnat : (2547489467 : ℕ)^4113*2500000000000^3089 ≤ 404742992371^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2547489467 10000000000 404742992371 2500000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (622380847/1250000000 : ℝ)^4113 ≤ (39513956448601/100000000000000 : ℝ)^3089 := by
    have hnat : (622380847 : ℕ)^4113*100000000000000^3089 ≤ 39513956448601^3089*1250000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      622380847 1250000000 39513956448601 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2712566269/5000000000 : ℝ), (-2547489467/10000000000 : ℝ), (622380847/1250000000 : ℝ)] ![(44296323830577/100000000000000 : ℝ), (404742992371/2500000000000 : ℝ), (39513956448601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2712566269/5000000000 : ℝ)|^4113 ≤ (44296323830577/100000000000000 : ℝ)^3089
        have hw : |(2712566269/5000000000 : ℝ)|=(2712566269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2547489467/10000000000 : ℝ)|^4113 ≤ (404742992371/2500000000000 : ℝ)^3089
        have hw : |(-2547489467/10000000000 : ℝ)|=(2547489467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(622380847/1250000000 : ℝ)|^4113 ≤ (39513956448601/100000000000000 : ℝ)^3089
        have hw : |(622380847/1250000000 : ℝ)|=(622380847/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s1_2 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5425132863/10000000000 : ℝ)*x 0 + (4979046353/10000000000 : ℝ)*x 1 + (-2547489579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5425132863/10000000000 : ℝ)^4113 ≤ (8859265472777/20000000000000 : ℝ)^3089 := by
    have hnat : (5425132863 : ℕ)^4113*20000000000000^3089 ≤ 8859265472777^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425132863 10000000000 8859265472777 20000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4979046353/10000000000 : ℝ)^4113 ≤ (9878487994707/25000000000000 : ℝ)^3089 := by
    have hnat : (4979046353 : ℕ)^4113*25000000000000^3089 ≤ 9878487994707^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4979046353 10000000000 9878487994707 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2547489579/10000000000 : ℝ)^4113 ≤ (16189720642573/100000000000000 : ℝ)^3089 := by
    have hnat : (2547489579 : ℕ)^4113*100000000000000^3089 ≤ 16189720642573^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2547489579 10000000000 16189720642573 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5425132863/10000000000 : ℝ), (4979046353/10000000000 : ℝ), (-2547489579/10000000000 : ℝ)] ![(8859265472777/20000000000000 : ℝ), (9878487994707/25000000000000 : ℝ), (16189720642573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5425132863/10000000000 : ℝ)|^4113 ≤ (8859265472777/20000000000000 : ℝ)^3089
        have hw : |(5425132863/10000000000 : ℝ)|=(5425132863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4979046353/10000000000 : ℝ)|^4113 ≤ (9878487994707/25000000000000 : ℝ)^3089
        have hw : |(4979046353/10000000000 : ℝ)|=(4979046353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2547489579/10000000000 : ℝ)|^4113 ≤ (16189720642573/100000000000000 : ℝ)^3089
        have hw : |(-2547489579/10000000000 : ℝ)|=(2547489579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s1_3 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (86532657/200000000 : ℝ)*x 0 + (3656865937/10000000000 : ℝ)*x 1 + (5121554869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86532657/200000000 : ℝ)^4113 ≤ (3277435812801/10000000000000 : ℝ)^3089 := by
    have hnat : (86532657 : ℕ)^4113*10000000000000^3089 ≤ 3277435812801^3089*200000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86532657 200000000 3277435812801 10000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3656865937/10000000000 : ℝ)^4113 ≤ (26198726469827/100000000000000 : ℝ)^3089 := by
    have hnat : (3656865937 : ℕ)^4113*100000000000000^3089 ≤ 26198726469827^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3656865937 10000000000 26198726469827 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5121554869/10000000000 : ℝ)^4113 ≤ (41026915383109/100000000000000 : ℝ)^3089 := by
    have hnat : (5121554869 : ℕ)^4113*100000000000000^3089 ≤ 41026915383109^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5121554869 10000000000 41026915383109 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(86532657/200000000 : ℝ), (3656865937/10000000000 : ℝ), (5121554869/10000000000 : ℝ)] ![(3277435812801/10000000000000 : ℝ), (26198726469827/100000000000000 : ℝ), (41026915383109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(86532657/200000000 : ℝ)|^4113 ≤ (3277435812801/10000000000000 : ℝ)^3089
        have hw : |(86532657/200000000 : ℝ)|=(86532657/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3656865937/10000000000 : ℝ)|^4113 ≤ (26198726469827/100000000000000 : ℝ)^3089
        have hw : |(3656865937/10000000000 : ℝ)|=(3656865937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5121554869/10000000000 : ℝ)|^4113 ≤ (41026915383109/100000000000000 : ℝ)^3089
        have hw : |(5121554869/10000000000 : ℝ)|=(5121554869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s1_4 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2140187361/10000000000 : ℝ)*x 0 + (4989740083/10000000000 : ℝ)*x 1 + (5720400677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2140187361/10000000000 : ℝ)^4113 ≤ (1283799858993/10000000000000 : ℝ)^3089 := by
    have hnat : (2140187361 : ℕ)^4113*10000000000000^3089 ≤ 1283799858993^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140187361 10000000000 1283799858993 10000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4989740083/10000000000 : ℝ)^4113 ≤ (39626991111419/100000000000000 : ℝ)^3089 := by
    have hnat : (4989740083 : ℕ)^4113*100000000000000^3089 ≤ 39626991111419^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4989740083 10000000000 39626991111419 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5720400677/10000000000 : ℝ)^4113 ≤ (11883752570579/25000000000000 : ℝ)^3089 := by
    have hnat : (5720400677 : ℕ)^4113*25000000000000^3089 ≤ 11883752570579^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5720400677 10000000000 11883752570579 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2140187361/10000000000 : ℝ), (4989740083/10000000000 : ℝ), (5720400677/10000000000 : ℝ)] ![(1283799858993/10000000000000 : ℝ), (39626991111419/100000000000000 : ℝ), (11883752570579/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2140187361/10000000000 : ℝ)|^4113 ≤ (1283799858993/10000000000000 : ℝ)^3089
        have hw : |(-2140187361/10000000000 : ℝ)|=(2140187361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4989740083/10000000000 : ℝ)|^4113 ≤ (39626991111419/100000000000000 : ℝ)^3089
        have hw : |(4989740083/10000000000 : ℝ)|=(4989740083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5720400677/10000000000 : ℝ)|^4113 ≤ (11883752570579/25000000000000 : ℝ)^3089
        have hw : |(5720400677/10000000000 : ℝ)|=(5720400677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s1_5 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2616667911/5000000000 : ℝ)*x 0 + (-1806134187/10000000000 : ℝ)*x 1 + (1430100421/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2616667911/5000000000 : ℝ)^4113 ≤ (42223480560151/100000000000000 : ℝ)^3089 := by
    have hnat : (2616667911 : ℕ)^4113*100000000000000^3089 ≤ 42223480560151^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2616667911 5000000000 42223480560151 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1806134187/10000000000 : ℝ)^4113 ≤ (5120749001431/50000000000000 : ℝ)^3089 := by
    have hnat : (1806134187 : ℕ)^4113*50000000000000^3089 ≤ 5120749001431^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1806134187 10000000000 5120749001431 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1430100421/2500000000 : ℝ)^4113 ≤ (47535021424169/100000000000000 : ℝ)^3089 := by
    have hnat : (1430100421 : ℕ)^4113*100000000000000^3089 ≤ 47535021424169^3089*2500000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1430100421 2500000000 47535021424169 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2616667911/5000000000 : ℝ), (-1806134187/10000000000 : ℝ), (1430100421/2500000000 : ℝ)] ![(42223480560151/100000000000000 : ℝ), (5120749001431/50000000000000 : ℝ), (47535021424169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2616667911/5000000000 : ℝ)|^4113 ≤ (42223480560151/100000000000000 : ℝ)^3089
        have hw : |(2616667911/5000000000 : ℝ)|=(2616667911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1806134187/10000000000 : ℝ)|^4113 ≤ (5120749001431/50000000000000 : ℝ)^3089
        have hw : |(-1806134187/10000000000 : ℝ)|=(1806134187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1430100421/2500000000 : ℝ)|^4113 ≤ (47535021424169/100000000000000 : ℝ)^3089
        have hw : |(1430100421/2500000000 : ℝ)|=(1430100421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s1_6 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2616666993/5000000000 : ℝ)*x 0 + (5720403699/10000000000 : ℝ)*x 1 + (-903066923/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2616666993/5000000000 : ℝ)^4113 ≤ (42223460836429/100000000000000 : ℝ)^3089 := by
    have hnat : (2616666993 : ℕ)^4113*100000000000000^3089 ≤ 42223460836429^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2616666993 5000000000 42223460836429 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5720403699/10000000000 : ℝ)^4113 ≤ (23767521859471/50000000000000 : ℝ)^3089 := by
    have hnat : (5720403699 : ℕ)^4113*50000000000000^3089 ≤ 23767521859471^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5720403699 10000000000 23767521859471 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (903066923/5000000000 : ℝ)^4113 ≤ (2560373857067/25000000000000 : ℝ)^3089 := by
    have hnat : (903066923 : ℕ)^4113*25000000000000^3089 ≤ 2560373857067^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903066923 5000000000 2560373857067 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2616666993/5000000000 : ℝ), (5720403699/10000000000 : ℝ), (-903066923/5000000000 : ℝ)] ![(42223460836429/100000000000000 : ℝ), (23767521859471/50000000000000 : ℝ), (2560373857067/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2616666993/5000000000 : ℝ)|^4113 ≤ (42223460836429/100000000000000 : ℝ)^3089
        have hw : |(2616666993/5000000000 : ℝ)|=(2616666993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5720403699/10000000000 : ℝ)|^4113 ≤ (23767521859471/50000000000000 : ℝ)^3089
        have hw : |(5720403699/10000000000 : ℝ)|=(5720403699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-903066923/5000000000 : ℝ)|^4113 ≤ (2560373857067/25000000000000 : ℝ)^3089
        have hw : |(-903066923/5000000000 : ℝ)|=(903066923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s1_7 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2164261619/5000000000 : ℝ)*x 0 + (1020146163/2000000000 : ℝ)*x 1 + (459764383/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2164261619/5000000000 : ℝ)^4113 ≤ (3279342622497/10000000000000 : ℝ)^3089 := by
    have hnat : (2164261619 : ℕ)^4113*10000000000000^3089 ≤ 3279342622497^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164261619 5000000000 3279342622497 10000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1020146163/2000000000 : ℝ)^4113 ≤ (8160990529437/20000000000000 : ℝ)^3089 := by
    have hnat : (1020146163 : ℕ)^4113*20000000000000^3089 ≤ 8160990529437^3089*2000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020146163 2000000000 8160990529437 20000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (459764383/1250000000 : ℝ)^4113 ≤ (1320081055513/5000000000000 : ℝ)^3089 := by
    have hnat : (459764383 : ℕ)^4113*5000000000000^3089 ≤ 1320081055513^3089*1250000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      459764383 1250000000 1320081055513 5000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2164261619/5000000000 : ℝ), (1020146163/2000000000 : ℝ), (459764383/1250000000 : ℝ)] ![(3279342622497/10000000000000 : ℝ), (8160990529437/20000000000000 : ℝ), (1320081055513/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2164261619/5000000000 : ℝ)|^4113 ≤ (3279342622497/10000000000000 : ℝ)^3089
        have hw : |(2164261619/5000000000 : ℝ)|=(2164261619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1020146163/2000000000 : ℝ)|^4113 ≤ (8160990529437/20000000000000 : ℝ)^3089
        have hw : |(1020146163/2000000000 : ℝ)|=(1020146163/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(459764383/1250000000 : ℝ)|^4113 ≤ (1320081055513/5000000000000 : ℝ)^3089
        have hw : |(459764383/1250000000 : ℝ)|=(459764383/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1033_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18418937/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2513/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20943/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14119/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14119/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14119/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14119/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14119/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14119/50000 : ℝ)*(X 0 2+X 1 2) := by
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
  have hpowlo : (0 : ℝ) ^ (8225/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8225 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8225*1^2048 ≤ 0^2048*1^8225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8225 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14119/50000 : ℝ) ^ (8225/2048 : ℝ) ≤ (311499154808118899/50000000000000000000 : ℝ) := by
    have hpowers : (14119/50000 : ℝ)^8225 ≤ (311499154808118899/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14119 : ℕ)^8225*50000000000000000000^2048 ≤ 311499154808118899^2048*50000^8225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14119 50000 311499154808118899 50000000000000000000 8225 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14119/50000 : ℝ)) (X := (311499154808118899/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8225/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8225 := by
      have hnat : (1 : ℕ)^2048*1^8225 ≤ 1^8225*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50311499154808118899/50000000000000000000 : ℝ) ≤ (5007738155283983/5000000000000000 : ℝ) ^ (8225/2048 : ℝ) := by
    have hpowers : (50311499154808118899/50000000000000000000 : ℝ)^2048 ≤ (5007738155283983/5000000000000000 : ℝ)^8225 := by
      have hnat : (50311499154808118899 : ℕ)^2048*5000000000000000^8225 ≤ 5007738155283983^8225*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50311499154808118899 50000000000000000000 5007738155283983 5000000000000000 2048 8225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5007738155283983/5000000000000000 : ℝ)) (X := (50311499154808118899/50000000000000000000 : ℝ)) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25311499154808118899/25000000000000000000 : ℝ) ≤ (2507738155283983/2500000000000000 : ℝ) ^ (8225/2048 : ℝ) := by
    have hpowers : (25311499154808118899/25000000000000000000 : ℝ)^2048 ≤ (2507738155283983/2500000000000000 : ℝ)^8225 := by
      have hnat : (25311499154808118899 : ℕ)^2048*2500000000000000^8225 ≤ 2507738155283983^8225*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25311499154808118899 25000000000000000000 2507738155283983 2500000000000000 2048 8225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2507738155283983/2500000000000000 : ℝ)) (X := (25311499154808118899/25000000000000000000 : ℝ)) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(7738155283983/1411900000000000 : ℝ)*(0 : ℝ))^(8225/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(7738155283983/1411900000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(311499154808118899/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(7738155283983/1411900000000000 : ℝ)*((14119/50000 : ℝ)+(0 : ℝ)))^(8225/2048 : ℝ) := by
    rw [show (1 : ℝ)+(7738155283983/1411900000000000 : ℝ)*((14119/50000 : ℝ)+(0 : ℝ))=(5007738155283983/5000000000000000 : ℝ) by norm_num, show 1+(311499154808118899/50000000000000000000 : ℝ)+(0 : ℝ)=(50311499154808118899/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(311499154808118899/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(7738155283983/1411900000000000 : ℝ)*(14119/50000 : ℝ))^(8225/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(7738155283983/1411900000000000 : ℝ)*(14119/50000 : ℝ)=(2507738155283983/2500000000000000 : ℝ) by norm_num, show 1+2*(311499154808118899/50000000000000000000 : ℝ)=(25311499154808118899/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(7738155283983/1411900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8225/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (14119/50000 : ℝ)) (c := (1 : ℝ)) (alpha := (7738155283983/1411900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(7738155283983/1411900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8225/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (14119/50000 : ℝ)) (c := (1 : ℝ)) (alpha := (7738155283983/1411900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(7738155283983/1411900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8225/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (14119/50000 : ℝ)) (c := (1 : ℝ)) (alpha := (7738155283983/1411900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-534803749/2500000000 : ℝ)*X 0 0+(2865657729/5000000000 : ℝ)*X 0 1+(77797601/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2712566269/5000000000 : ℝ)*X 1 0+(-2547489467/10000000000 : ℝ)*X 1 1+(622380847/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5425132863/10000000000 : ℝ)*X 2 0+(4979046353/10000000000 : ℝ)*X 2 1+(-2547489579/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((86532657/200000000 : ℝ)*X 0 0+(3656865937/10000000000 : ℝ)*X 0 1+(5121554869/10000000000 : ℝ)*X 0 2+(86532657/200000000 : ℝ)*X 1 0+(3656865937/10000000000 : ℝ)*X 1 1+(5121554869/10000000000 : ℝ)*X 1 2+(86532657/200000000 : ℝ)*X 2 0+(3656865937/10000000000 : ℝ)*X 2 1+(5121554869/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2140187361/10000000000 : ℝ)*X 0 0+(4989740083/10000000000 : ℝ)*X 0 1+(5720400677/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2616667911/5000000000 : ℝ)*X 1 0+(-1806134187/10000000000 : ℝ)*X 1 1+(1430100421/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2616666993/5000000000 : ℝ)*X 2 0+(5720403699/10000000000 : ℝ)*X 2 1+(-903066923/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2164261619/5000000000 : ℝ)*X 0 0+(1020146163/2000000000 : ℝ)*X 0 1+(459764383/1250000000 : ℝ)*X 0 2+(2164261619/5000000000 : ℝ)*X 1 0+(1020146163/2000000000 : ℝ)*X 1 1+(459764383/1250000000 : ℝ)*X 1 2+(2164261619/5000000000 : ℝ)*X 2 0+(1020146163/2000000000 : ℝ)*X 2 1+(459764383/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (31095254829490405193943/14119000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11576269/20000000000000 : ℝ)*(base1) + (527671957/100000000000000 : ℝ)*(base19) + (607306497/100000000000000 : ℝ)*(base23) + (2011819/3125000000000 : ℝ)*(upper3) + (4926227/10000000000000 : ℝ)*(upper5) + (40241170608741/4000000000000 : ℝ)*(major0) + (40241170608741/4000000000000 : ℝ)*(major1) + (40241170608741/4000000000000 : ℝ)*(major2) + (664657255654043/50000000000000 : ℝ)*(sp0) + (664658400912811/50000000000000 : ℝ)*(sp1) + (664658361095541/50000000000000 : ℝ)*(sp2) + (341369929885687/50000000000000 : ℝ)*(sp3) + (1438035419/50000000000000 : ℝ)*(sp4) + (590759/48828125000 : ℝ)*(sp7) + (682741127527151/100000000000000 : ℝ)*(f.failure) + (1329317329497579/100000000000000 : ℝ)*(f.sum) + (5382671625483/14119000000000000000000000000 : ℝ)*base66 + (28810921957693/5647600000000000000000000000 : ℝ)*base68 + (58694705749377/28238000000000000000000000000 : ℝ)*base70 + (36198287239/28238000000000000000000000000 : ℝ)*base71 + (77658333878221/14119000000000000000000000000 : ℝ)*base74 + (107411734732573/28238000000000000000000000000 : ℝ)*base76 + (17173143865701/28238000000000000000000000000 : ℝ)*base78 + (143857819279417/28238000000000000000000000000 : ℝ)*base80 + (61094532058929/14119000000000000000000000000 : ℝ)*base82 + (2441513/1250000000000000000000 : ℝ)*base90 + (2441513/1250000000000000000000 : ℝ)*base92 + (2441513/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33349376257344400410429/8824375000000000000000000000 : ℝ) := by norm_num
    linear_combination (2364021093/100000000000000 : ℝ)*(base19) + (2186061663/100000000000000 : ℝ)*(base23) + (149956713/100000000000000 : ℝ)*(upper2) + (32915567/10000000000000 : ℝ)*(upper3) + (120088171/25000000000000 : ℝ)*(upper5) + (517888431497721/50000000000000 : ℝ)*(major0) + (517888431497721/50000000000000 : ℝ)*(major1) + (517888431497721/50000000000000 : ℝ)*(major2) + (11065831701/100000000000000 : ℝ)*(sp1) + (2873181271/25000000000000 : ℝ)*(sp2) + (273724856796921/20000000000000 : ℝ)*(sp4) + (342152713532953/25000000000000 : ℝ)*(sp5) + (1368610605197859/100000000000000 : ℝ)*(sp6) + (702929316031811/100000000000000 : ℝ)*(sp7) + (702929316031811/100000000000000 : ℝ)*(f.failure) + (273724856796921/20000000000000 : ℝ)*(f.sum) + (273501800539249/70595000000000000000000000000 : ℝ)*base66 + (460807192685643/70595000000000000000000000000 : ℝ)*base67 + (61078371092947/17648750000000000000000000000 : ℝ)*base69 + (27276065933843/70595000000000000000000000000 : ℝ)*base71 + (12152495309433/2206093750000000000000000000 : ℝ)*base73 + (154254576238617/70595000000000000000000000000 : ℝ)*base76 + (171492265390237/70595000000000000000000000000 : ℝ)*base78 + (121522270516767/70595000000000000000000000000 : ℝ)*base80 + (12117133165107/8824375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (8195093/1250000000000000000000 : ℝ)*base90 + (8195093/1250000000000000000000 : ℝ)*base92 + (8195093/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1033_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18418937/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2513/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20943/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1033_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1033_s2_0 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1099308347/5000000000 : ℝ)*x 0 + (5532665381/10000000000 : ℝ)*x 1 + (2570011173/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1099308347/5000000000 : ℝ)^4113 ≤ (3326693897799/25000000000000 : ℝ)^3089 := by
    have hnat : (1099308347 : ℕ)^4113*25000000000000^3089 ≤ 3326693897799^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099308347 5000000000 3326693897799 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5532665381/10000000000 : ℝ)^4113 ≤ (1136730360827/2500000000000 : ℝ)^3089 := by
    have hnat : (5532665381 : ℕ)^4113*2500000000000^3089 ≤ 1136730360827^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5532665381 10000000000 1136730360827 2500000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2570011173/5000000000 : ℝ)^4113 ≤ (20612004981381/50000000000000 : ℝ)^3089 := by
    have hnat : (2570011173 : ℕ)^4113*50000000000000^3089 ≤ 20612004981381^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2570011173 5000000000 20612004981381 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1099308347/5000000000 : ℝ), (5532665381/10000000000 : ℝ), (2570011173/5000000000 : ℝ)] ![(3326693897799/25000000000000 : ℝ), (1136730360827/2500000000000 : ℝ), (20612004981381/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1099308347/5000000000 : ℝ)|^4113 ≤ (3326693897799/25000000000000 : ℝ)^3089
        have hw : |(-1099308347/5000000000 : ℝ)|=(1099308347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5532665381/10000000000 : ℝ)|^4113 ≤ (1136730360827/2500000000000 : ℝ)^3089
        have hw : |(5532665381/10000000000 : ℝ)|=(5532665381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2570011173/5000000000 : ℝ)|^4113 ≤ (20612004981381/50000000000000 : ℝ)^3089
        have hw : |(2570011173/5000000000 : ℝ)|=(2570011173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s2_1 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2689326191/5000000000 : ℝ)*x 0 + (-2403669021/10000000000 : ℝ)*x 1 + (41120183/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2689326191/5000000000 : ℝ)^4113 ≤ (43791723696599/100000000000000 : ℝ)^3089 := by
    have hnat : (2689326191 : ℕ)^4113*100000000000000^3089 ≤ 43791723696599^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689326191 5000000000 43791723696599 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2403669021/10000000000 : ℝ)^4113 ≤ (37460651679/250000000000 : ℝ)^3089 := by
    have hnat : (2403669021 : ℕ)^4113*250000000000^3089 ≤ 37460651679^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2403669021 10000000000 37460651679 250000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41120183/80000000 : ℝ)^4113 ≤ (41224015611893/100000000000000 : ℝ)^3089 := by
    have hnat : (41120183 : ℕ)^4113*100000000000000^3089 ≤ 41224015611893^3089*80000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41120183 80000000 41224015611893 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2689326191/5000000000 : ℝ), (-2403669021/10000000000 : ℝ), (41120183/80000000 : ℝ)] ![(43791723696599/100000000000000 : ℝ), (37460651679/250000000000 : ℝ), (41224015611893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2689326191/5000000000 : ℝ)|^4113 ≤ (43791723696599/100000000000000 : ℝ)^3089
        have hw : |(2689326191/5000000000 : ℝ)|=(2689326191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2403669021/10000000000 : ℝ)|^4113 ≤ (37460651679/250000000000 : ℝ)^3089
        have hw : |(-2403669021/10000000000 : ℝ)|=(2403669021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41120183/80000000 : ℝ)|^4113 ≤ (41224015611893/100000000000000 : ℝ)^3089
        have hw : |(41120183/80000000 : ℝ)|=(41120183/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s2_2 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5378652443/10000000000 : ℝ)*x 0 + (2570011471/5000000000 : ℝ)*x 1 + (-300458607/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378652443/10000000000 : ℝ)^4113 ≤ (8758344871577/20000000000000 : ℝ)^3089 := by
    have hnat : (5378652443 : ℕ)^4113*20000000000000^3089 ≤ 8758344871577^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378652443 10000000000 8758344871577 20000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2570011471/5000000000 : ℝ)^4113 ≤ (41224016327379/100000000000000 : ℝ)^3089 := by
    have hnat : (2570011471 : ℕ)^4113*100000000000000^3089 ≤ 41224016327379^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2570011471 5000000000 41224016327379 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (300458607/1250000000 : ℝ)^4113 ≤ (14984259302027/100000000000000 : ℝ)^3089 := by
    have hnat : (300458607 : ℕ)^4113*100000000000000^3089 ≤ 14984259302027^3089*1250000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300458607 1250000000 14984259302027 100000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378652443/10000000000 : ℝ), (2570011471/5000000000 : ℝ), (-300458607/1250000000 : ℝ)] ![(8758344871577/20000000000000 : ℝ), (41224016327379/100000000000000 : ℝ), (14984259302027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378652443/10000000000 : ℝ)|^4113 ≤ (8758344871577/20000000000000 : ℝ)^3089
        have hw : |(5378652443/10000000000 : ℝ)|=(5378652443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2570011471/5000000000 : ℝ)|^4113 ≤ (41224016327379/100000000000000 : ℝ)^3089
        have hw : |(2570011471/5000000000 : ℝ)|=(2570011471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-300458607/1250000000 : ℝ)|^4113 ≤ (14984259302027/100000000000000 : ℝ)^3089
        have hw : |(-300458607/1250000000 : ℝ)|=(300458607/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s2_3 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (34935309/80000000 : ℝ)*x 0 + (4001671301/10000000000 : ℝ)*x 1 + (4766156829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34935309/80000000 : ℝ)^4113 ≤ (8295315316699/25000000000000 : ℝ)^3089 := by
    have hnat : (34935309 : ℕ)^4113*25000000000000^3089 ≤ 8295315316699^3089*80000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34935309 80000000 8295315316699 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4001671301/10000000000 : ℝ)^4113 ≤ (2953825882353/10000000000000 : ℝ)^3089 := by
    have hnat : (4001671301 : ℕ)^4113*10000000000000^3089 ≤ 2953825882353^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4001671301 10000000000 2953825882353 10000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4766156829/10000000000 : ℝ)^4113 ≤ (3728047989137/10000000000000 : ℝ)^3089 := by
    have hnat : (4766156829 : ℕ)^4113*10000000000000^3089 ≤ 3728047989137^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4766156829 10000000000 3728047989137 10000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34935309/80000000 : ℝ), (4001671301/10000000000 : ℝ), (4766156829/10000000000 : ℝ)] ![(8295315316699/25000000000000 : ℝ), (2953825882353/10000000000000 : ℝ), (3728047989137/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34935309/80000000 : ℝ)|^4113 ≤ (8295315316699/25000000000000 : ℝ)^3089
        have hw : |(34935309/80000000 : ℝ)|=(34935309/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4001671301/10000000000 : ℝ)|^4113 ≤ (2953825882353/10000000000000 : ℝ)^3089
        have hw : |(4001671301/10000000000 : ℝ)|=(4001671301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4766156829/10000000000 : ℝ)|^4113 ≤ (3728047989137/10000000000000 : ℝ)^3089
        have hw : |(4766156829/10000000000 : ℝ)|=(4766156829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s2_4 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2198753857/10000000000 : ℝ)*x 0 + (5142943527/10000000000 : ℝ)*x 1 + (5529713077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2198753857/10000000000 : ℝ)^4113 ≤ (2661576191173/20000000000000 : ℝ)^3089 := by
    have hnat : (2198753857 : ℕ)^4113*20000000000000^3089 ≤ 2661576191173^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2198753857 10000000000 2661576191173 20000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5142943527/10000000000 : ℝ)^4113 ≤ (20627603932711/50000000000000 : ℝ)^3089 := by
    have hnat : (5142943527 : ℕ)^4113*50000000000000^3089 ≤ 20627603932711^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5142943527 10000000000 20627603932711 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5529713077/10000000000 : ℝ)^4113 ≤ (22718455580899/50000000000000 : ℝ)^3089 := by
    have hnat : (5529713077 : ℕ)^4113*50000000000000^3089 ≤ 22718455580899^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5529713077 10000000000 22718455580899 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2198753857/10000000000 : ℝ), (5142943527/10000000000 : ℝ), (5529713077/10000000000 : ℝ)] ![(2661576191173/20000000000000 : ℝ), (20627603932711/50000000000000 : ℝ), (22718455580899/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2198753857/10000000000 : ℝ)|^4113 ≤ (2661576191173/20000000000000 : ℝ)^3089
        have hw : |(-2198753857/10000000000 : ℝ)|=(2198753857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5142943527/10000000000 : ℝ)|^4113 ≤ (20627603932711/50000000000000 : ℝ)^3089
        have hw : |(5142943527/10000000000 : ℝ)|=(5142943527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5529713077/10000000000 : ℝ)|^4113 ≤ (22718455580899/50000000000000 : ℝ)^3089
        have hw : |(5529713077/10000000000 : ℝ)|=(5529713077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s2_5 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279778551/10000000000 : ℝ)*x 0 + (-2013978983/10000000000 : ℝ)*x 1 + (691214141/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279778551/10000000000 : ℝ)^4113 ≤ (1335098015379/3125000000000 : ℝ)^3089 := by
    have hnat : (5279778551 : ℕ)^4113*3125000000000^3089 ≤ 1335098015379^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279778551 10000000000 1335098015379 3125000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2013978983/10000000000 : ℝ)^4113 ≤ (2959987942837/25000000000000 : ℝ)^3089 := by
    have hnat : (2013978983 : ℕ)^4113*25000000000000^3089 ≤ 2959987942837^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2013978983 10000000000 2959987942837 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (691214141/1250000000 : ℝ)^4113 ≤ (1419903491243/3125000000000 : ℝ)^3089 := by
    have hnat : (691214141 : ℕ)^4113*3125000000000^3089 ≤ 1419903491243^3089*1250000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      691214141 1250000000 1419903491243 3125000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279778551/10000000000 : ℝ), (-2013978983/10000000000 : ℝ), (691214141/1250000000 : ℝ)] ![(1335098015379/3125000000000 : ℝ), (2959987942837/25000000000000 : ℝ), (1419903491243/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279778551/10000000000 : ℝ)|^4113 ≤ (1335098015379/3125000000000 : ℝ)^3089
        have hw : |(5279778551/10000000000 : ℝ)|=(5279778551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2013978983/10000000000 : ℝ)|^4113 ≤ (2959987942837/25000000000000 : ℝ)^3089
        have hw : |(-2013978983/10000000000 : ℝ)|=(2013978983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(691214141/1250000000 : ℝ)|^4113 ≤ (1419903491243/3125000000000 : ℝ)^3089
        have hw : |(691214141/1250000000 : ℝ)|=(691214141/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s2_6 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279778747/10000000000 : ℝ)*x 0 + (2764856491/5000000000 : ℝ)*x 1 + (-1006989459/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279778747/10000000000 : ℝ)^4113 ≤ (21361569301943/50000000000000 : ℝ)^3089 := by
    have hnat : (5279778747 : ℕ)^4113*50000000000000^3089 ≤ 21361569301943^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279778747 10000000000 21361569301943 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2764856491/5000000000 : ℝ)^4113 ≤ (22718455061213/50000000000000 : ℝ)^3089 := by
    have hnat : (2764856491 : ℕ)^4113*50000000000000^3089 ≤ 22718455061213^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2764856491 5000000000 22718455061213 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1006989459/5000000000 : ℝ)^4113 ≤ (5919975631273/50000000000000 : ℝ)^3089 := by
    have hnat : (1006989459 : ℕ)^4113*50000000000000^3089 ≤ 5919975631273^3089*5000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006989459 5000000000 5919975631273 50000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279778747/10000000000 : ℝ), (2764856491/5000000000 : ℝ), (-1006989459/5000000000 : ℝ)] ![(21361569301943/50000000000000 : ℝ), (22718455061213/50000000000000 : ℝ), (5919975631273/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279778747/10000000000 : ℝ)|^4113 ≤ (21361569301943/50000000000000 : ℝ)^3089
        have hw : |(5279778747/10000000000 : ℝ)|=(5279778747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2764856491/5000000000 : ℝ)|^4113 ≤ (22718455061213/50000000000000 : ℝ)^3089
        have hw : |(2764856491/5000000000 : ℝ)|=(2764856491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1006989459/5000000000 : ℝ)|^4113 ≤ (5919975631273/50000000000000 : ℝ)^3089
        have hw : |(-1006989459/5000000000 : ℝ)|=(1006989459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1033_s2_7 (p : ℝ) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4367181211/10000000000 : ℝ)*x 0 + (4760470657/10000000000 : ℝ)*x 1 + (801483749/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4367181211/10000000000 : ℝ)^4113 ≤ (8295992126901/25000000000000 : ℝ)^3089 := by
    have hnat : (4367181211 : ℕ)^4113*25000000000000^3089 ≤ 8295992126901^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4367181211 10000000000 8295992126901 25000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4760470657/10000000000 : ℝ)^4113 ≤ (7444254169481/20000000000000 : ℝ)^3089 := by
    have hnat : (4760470657 : ℕ)^4113*20000000000000^3089 ≤ 7444254169481^3089*10000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4760470657 10000000000 7444254169481 20000000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (801483749/2000000000 : ℝ)^4113 ≤ (1849672539683/6250000000000 : ℝ)^3089 := by
    have hnat : (801483749 : ℕ)^4113*6250000000000^3089 ≤ 1849672539683^3089*2000000000^4113 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      801483749 2000000000 1849672539683 6250000000000 4113 3089 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4113/1024 : ℝ)) 4113 3089 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4367181211/10000000000 : ℝ), (4760470657/10000000000 : ℝ), (801483749/2000000000 : ℝ)] ![(8295992126901/25000000000000 : ℝ), (7444254169481/20000000000000 : ℝ), (1849672539683/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4367181211/10000000000 : ℝ)|^4113 ≤ (8295992126901/25000000000000 : ℝ)^3089
        have hw : |(4367181211/10000000000 : ℝ)|=(4367181211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4760470657/10000000000 : ℝ)|^4113 ≤ (7444254169481/20000000000000 : ℝ)^3089
        have hw : |(4760470657/10000000000 : ℝ)|=(4760470657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(801483749/2000000000 : ℝ)|^4113 ≤ (1849672539683/6250000000000 : ℝ)^3089
        have hw : |(801483749/2000000000 : ℝ)|=(801483749/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1033_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18418937/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20943/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2513/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (8551/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1053/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20943/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2513/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20943/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2513/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20943/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2513/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20943/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2513/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20943/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2513/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20943/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2513/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2513/50000 : ℝ) ^ (8225/2048 : ℝ) ≤ (608082310415029/100000000000000000000 : ℝ) := by
    have hpowers : (2513/50000 : ℝ)^8225 ≤ (608082310415029/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2513 : ℕ)^8225*100000000000000000000^2048 ≤ 608082310415029^2048*50000^8225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2513 50000 608082310415029 100000000000000000000 8225 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2513/50000 : ℝ)) (X := (608082310415029/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (20943/100000 : ℝ) ^ (8225/2048 : ℝ) ≤ (9379620862982943/5000000000000000000 : ℝ) := by
    have hpowers : (20943/100000 : ℝ)^8225 ≤ (9379620862982943/5000000000000000000 : ℝ)^2048 := by
      have hnat : (20943 : ℕ)^8225*5000000000000000000^2048 ≤ 9379620862982943^2048*100000^8225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20943 100000 9379620862982943 5000000000000000000 8225 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20943/100000 : ℝ)) (X := (9379620862982943/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000608082310415029/50000000000000000000 : ℝ) ≤ (2000006056398223/2000000000000000 : ℝ) ^ (8225/2048 : ℝ) := by
    have hpowers : (50000608082310415029/50000000000000000000 : ℝ)^2048 ≤ (2000006056398223/2000000000000000 : ℝ)^8225 := by
      have hnat : (50000608082310415029 : ℕ)^2048*2000000000000000^8225 ≤ 2000006056398223^8225*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000608082310415029 50000000000000000000 2000006056398223 2000000000000000 2048 8225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000006056398223/2000000000000000 : ℝ)) (X := (50000608082310415029/50000000000000000000 : ℝ)) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100188200499570073889/100000000000000000000 : ℝ) ≤ (5002341413598381/5000000000000000 : ℝ) ^ (8225/2048 : ℝ) := by
    have hpowers : (100188200499570073889/100000000000000000000 : ℝ)^2048 ≤ (5002341413598381/5000000000000000 : ℝ)^8225 := by
      have hnat : (100188200499570073889 : ℕ)^2048*5000000000000000^8225 ≤ 5002341413598381^8225*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100188200499570073889 100000000000000000000 5002341413598381 5000000000000000 2048 8225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002341413598381/5000000000000000 : ℝ)) (X := (100188200499570073889/100000000000000000000 : ℝ)) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (2509379620862982943/2500000000000000000 : ℝ) ≤ (10009335372402409/10000000000000000 : ℝ) ^ (8225/2048 : ℝ) := by
    have hpowers : (2509379620862982943/2500000000000000000 : ℝ)^2048 ≤ (10009335372402409/10000000000000000 : ℝ)^8225 := by
      have hnat : (2509379620862982943 : ℕ)^2048*10000000000000000^8225 ≤ 10009335372402409^8225*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2509379620862982943 2500000000000000000 10009335372402409 10000000000000000 2048 8225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10009335372402409/10000000000000000 : ℝ)) (X := (2509379620862982943/2500000000000000000 : ℝ)) (by norm_num) 8225 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(608082310415029/100000000000000000000 : ℝ) ≤ ((159123714614045413811/159170000000000000000 : ℝ)+2*(4652545205647/1591700000000000 : ℝ)*(2513/50000 : ℝ))^(8225/2048 : ℝ) := by
    rw [show (159123714614045413811/159170000000000000000 : ℝ)+2*(4652545205647/1591700000000000 : ℝ)*(2513/50000 : ℝ)=(2000006056398223/2000000000000000 : ℝ) by norm_num, show 1+2*(608082310415029/100000000000000000000 : ℝ)=(50000608082310415029/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9379620862982943/5000000000000000000 : ℝ)+(608082310415029/100000000000000000000 : ℝ) ≤ ((159123714614045413811/159170000000000000000 : ℝ)+(4652545205647/1591700000000000 : ℝ)*((20943/100000 : ℝ)+(2513/50000 : ℝ)))^(8225/2048 : ℝ) := by
    rw [show (159123714614045413811/159170000000000000000 : ℝ)+(4652545205647/1591700000000000 : ℝ)*((20943/100000 : ℝ)+(2513/50000 : ℝ))=(5002341413598381/5000000000000000 : ℝ) by norm_num, show 1+(9379620862982943/5000000000000000000 : ℝ)+(608082310415029/100000000000000000000 : ℝ)=(100188200499570073889/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9379620862982943/5000000000000000000 : ℝ) ≤ ((159123714614045413811/159170000000000000000 : ℝ)+2*(4652545205647/1591700000000000 : ℝ)*(20943/100000 : ℝ))^(8225/2048 : ℝ) := by
    rw [show (159123714614045413811/159170000000000000000 : ℝ)+2*(4652545205647/1591700000000000 : ℝ)*(20943/100000 : ℝ)=(10009335372402409/10000000000000000 : ℝ) by norm_num, show 1+2*(9379620862982943/5000000000000000000 : ℝ)=(2509379620862982943/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (159123714614045413811/159170000000000000000 : ℝ)*(X 1 0+X 2 0)+(4652545205647/1591700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8225/2048 : ℝ)) (lo := (2513/50000 : ℝ)) (hi := (20943/100000 : ℝ)) (c := (159123714614045413811/159170000000000000000 : ℝ)) (alpha := (4652545205647/1591700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (159123714614045413811/159170000000000000000 : ℝ)*(X 0 1+X 2 1)+(4652545205647/1591700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8225/2048 : ℝ)) (lo := (2513/50000 : ℝ)) (hi := (20943/100000 : ℝ)) (c := (159123714614045413811/159170000000000000000 : ℝ)) (alpha := (4652545205647/1591700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (159123714614045413811/159170000000000000000 : ℝ)*(X 0 2+X 1 2)+(4652545205647/1591700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8225/2048 : ℝ)) (lo := (2513/50000 : ℝ)) (hi := (20943/100000 : ℝ)) (c := (159123714614045413811/159170000000000000000 : ℝ)) (alpha := (4652545205647/1591700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1099308347/5000000000 : ℝ)*X 0 0+(5532665381/10000000000 : ℝ)*X 0 1+(2570011173/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2689326191/5000000000 : ℝ)*X 1 0+(-2403669021/10000000000 : ℝ)*X 1 1+(41120183/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5378652443/10000000000 : ℝ)*X 2 0+(2570011471/5000000000 : ℝ)*X 2 1+(-300458607/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((34935309/80000000 : ℝ)*X 0 0+(4001671301/10000000000 : ℝ)*X 0 1+(4766156829/10000000000 : ℝ)*X 0 2+(34935309/80000000 : ℝ)*X 1 0+(4001671301/10000000000 : ℝ)*X 1 1+(4766156829/10000000000 : ℝ)*X 1 2+(34935309/80000000 : ℝ)*X 2 0+(4001671301/10000000000 : ℝ)*X 2 1+(4766156829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2198753857/10000000000 : ℝ)*X 0 0+(5142943527/10000000000 : ℝ)*X 0 1+(5529713077/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5279778551/10000000000 : ℝ)*X 1 0+(-2013978983/10000000000 : ℝ)*X 1 1+(691214141/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5279778747/10000000000 : ℝ)*X 2 0+(2764856491/5000000000 : ℝ)*X 2 1+(-1006989459/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4367181211/10000000000 : ℝ)*X 0 0+(4760470657/10000000000 : ℝ)*X 0 1+(801483749/2000000000 : ℝ)*X 0 2+(4367181211/10000000000 : ℝ)*X 1 0+(4760470657/10000000000 : ℝ)*X 1 1+(801483749/2000000000 : ℝ)*X 1 2+(4367181211/10000000000 : ℝ)*X 2 0+(4760470657/10000000000 : ℝ)*X 2 1+(801483749/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1033_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2839732818359194229788420917/994812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (553634879/50000000000000 : ℝ)*(base19) + (1014818011/100000000000000 : ℝ)*(base23) + (67957089/50000000000000 : ℝ)*(upper3) + (16315619/25000000000000 : ℝ)*(upper4) + (142999673/100000000000000 : ℝ)*(upper5) + (240934264415983/12500000000000 : ℝ)*(major0) + (240934264415983/12500000000000 : ℝ)*(major1) + (240934264415983/12500000000000 : ℝ)*(major2) + (1273427630874937/50000000000000 : ℝ)*(sp0) + (79589622913961/3125000000000 : ℝ)*(sp1) + (2546868025698499/100000000000000 : ℝ)*(sp2) + (1308074044204779/100000000000000 : ℝ)*(sp3) + (3444691659/25000000000000 : ℝ)*(sp4) + (1262695769/25000000000000 : ℝ)*(sp7) + (654039547493927/50000000000000 : ℝ)*(f.failure) + (254686904051651/10000000000000 : ℝ)*(f.sum) + (113641907238753/79585000000000000000000000000 : ℝ)*base65 + (831139549561183787/1989625000000000000000000000000000 : ℝ)*base68 + (18921015398757433787/1989625000000000000000000000000000 : ℝ)*base70 + (10761231778356933787/1989625000000000000000000000000000 : ℝ)*base72 + (104267485354893/79585000000000000000000000000 : ℝ)*base73 + (8686918859783433787/1989625000000000000000000000000000 : ℝ)*base76 + (8352233209004558787/1989625000000000000000000000000000 : ℝ)*base78 + (17572415107056683787/1989625000000000000000000000000000 : ℝ)*base80 + (482585909831187/79585000000000000000000000000 : ℝ)*base82 + (704401/625000000000000000000 : ℝ)*base90 + (704401/625000000000000000000 : ℝ)*base92 + (704401/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (32069235860037614476421766093/3979250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (774081811/50000000000000 : ℝ)*(base19) + (1750419017/100000000000000 : ℝ)*(base23) + (195807967/100000000000000 : ℝ)*(upper3) + (41418259/100000000000000 : ℝ)*(lower4) + (11630187/6250000000000 : ℝ)*(upper5) + (1956724462712021/100000000000000 : ℝ)*(major0) + (1956724462712021/100000000000000 : ℝ)*(major1) + (1956724462712021/100000000000000 : ℝ)*(major2) + (13073247959/100000000000000 : ℝ)*(sp1) + (7279599753/50000000000000 : ℝ)*(sp2) + (646379707990089/25000000000000 : ℝ)*(sp4) + (103420168421951/4000000000000 : ℝ)*(sp5) + (2585502522341833/100000000000000 : ℝ)*(sp6) + (10374451756457/781250000000 : ℝ)*(sp7) + (10374451756457/781250000000 : ℝ)*(f.failure) + (646379707990089/25000000000000 : ℝ)*(f.sum) + (55492529391647/79585000000000000000000000000 : ℝ)*base65 + (82741025762300177969/15917000000000000000000000000000000 : ℝ)*base68 + (30896164576116177969/15917000000000000000000000000000000 : ℝ)*base70 + (40650692489895177969/15917000000000000000000000000000000 : ℝ)*base72 + (313613177785593/79585000000000000000000000000 : ℝ)*base74 + (45063964476337177969/15917000000000000000000000000000000 : ℝ)*base76 + (13232116773077177969/15917000000000000000000000000000000 : ℝ)*base78 + (22851921746517822031/15917000000000000000000000000000000 : ℝ)*base79 + (174407216856063/79585000000000000000000000000 : ℝ)*base82 + (101711/39062500000000000000 : ℝ)*base89 + (101711/39062500000000000000 : ℝ)*base91 + (101711/39062500000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1033_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18418937/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20943/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2513/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8551/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1053/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1033_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1033_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18418937/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8551/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1053/6250 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1033_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1033_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1033_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8225/2048 : ℝ) ≤ p) (hpb : p ≤ (4113/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18418937/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8551/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1053/6250 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1033_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
