-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1051_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:55:40.547818+00:00
-- url     : https://prove2.me/submissions/29beba53-ac58-4d9c-86b9-86a9589ae3fa

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
theorem support_rectangle_w1051_s9_0 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672503247/5000000000 : ℝ)*x 0 + (-2277336911/10000000000 : ℝ)*x 1 + (526419871/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672503247/5000000000 : ℝ)^2061 ≤ (10863390490441/25000000000000 : ℝ)^1549 := by
    have hnat : (2672503247 : ℕ)^2061*25000000000000^1549 ≤ 10863390490441^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672503247 5000000000 10863390490441 25000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2277336911/10000000000 : ℝ)^2061 ≤ (17455970243/125000000000 : ℝ)^1549 := by
    have hnat : (2277336911 : ℕ)^2061*125000000000^1549 ≤ 17455970243^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2277336911 10000000000 17455970243 125000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526419871/1000000000 : ℝ)^2061 ≤ (42581661827211/100000000000000 : ℝ)^1549 := by
    have hnat : (526419871 : ℕ)^2061*100000000000000^1549 ≤ 42581661827211^1549*1000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526419871 1000000000 42581661827211 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672503247/5000000000 : ℝ), (-2277336911/10000000000 : ℝ), (526419871/1000000000 : ℝ)] ![(10863390490441/25000000000000 : ℝ), (17455970243/125000000000 : ℝ), (42581661827211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672503247/5000000000 : ℝ)|^2061 ≤ (10863390490441/25000000000000 : ℝ)^1549
        have hw : |(2672503247/5000000000 : ℝ)|=(2672503247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2277336911/10000000000 : ℝ)|^2061 ≤ (17455970243/125000000000 : ℝ)^1549
        have hw : |(-2277336911/10000000000 : ℝ)|=(2277336911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526419871/1000000000 : ℝ)|^2061 ≤ (42581661827211/100000000000000 : ℝ)^1549
        have hw : |(526419871/1000000000 : ℝ)|=(526419871/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s9_1 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2211179901/10000000000 : ℝ)*x 0 + (2632262493/5000000000 : ℝ)*x 1 + (5394266391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2211179901/10000000000 : ℝ)^2061 ≤ (13427614181323/100000000000000 : ℝ)^1549 := by
    have hnat : (2211179901 : ℕ)^2061*100000000000000^1549 ≤ 13427614181323^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2211179901 10000000000 13427614181323 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632262493/5000000000 : ℝ)^2061 ≤ (8517034687777/20000000000000 : ℝ)^1549 := by
    have hnat : (2632262493 : ℕ)^2061*20000000000000^1549 ≤ 8517034687777^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632262493 5000000000 8517034687777 20000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394266391/10000000000 : ℝ)^2061 ≤ (879744247353/2000000000000 : ℝ)^1549 := by
    have hnat : (5394266391 : ℕ)^2061*2000000000000^1549 ≤ 879744247353^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394266391 10000000000 879744247353 2000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2211179901/10000000000 : ℝ), (2632262493/5000000000 : ℝ), (5394266391/10000000000 : ℝ)] ![(13427614181323/100000000000000 : ℝ), (8517034687777/20000000000000 : ℝ), (879744247353/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2211179901/10000000000 : ℝ)|^2061 ≤ (13427614181323/100000000000000 : ℝ)^1549
        have hw : |(-2211179901/10000000000 : ℝ)|=(2211179901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632262493/5000000000 : ℝ)|^2061 ≤ (8517034687777/20000000000000 : ℝ)^1549
        have hw : |(2632262493/5000000000 : ℝ)|=(2632262493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394266391/10000000000 : ℝ)|^2061 ≤ (879744247353/2000000000000 : ℝ)^1549
        have hw : |(5394266391/10000000000 : ℝ)|=(5394266391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s9_2 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312201841/10000000000 : ℝ)*x 0 + (-429453819/2000000000 : ℝ)*x 1 + (5394266489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312201841/10000000000 : ℝ)^2061 ≤ (2693692312101/6250000000000 : ℝ)^1549 := by
    have hnat : (5312201841 : ℕ)^2061*6250000000000^1549 ≤ 2693692312101^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312201841 10000000000 2693692312101 6250000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (429453819/2000000000 : ℝ)^2061 ≤ (3228427391521/25000000000000 : ℝ)^1549 := by
    have hnat : (429453819 : ℕ)^2061*25000000000000^1549 ≤ 3228427391521^1549*2000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429453819 2000000000 3228427391521 25000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394266489/10000000000 : ℝ)^2061 ≤ (2749200839433/6250000000000 : ℝ)^1549 := by
    have hnat : (5394266489 : ℕ)^2061*6250000000000^1549 ≤ 2749200839433^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394266489 10000000000 2749200839433 6250000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312201841/10000000000 : ℝ), (-429453819/2000000000 : ℝ), (5394266489/10000000000 : ℝ)] ![(2693692312101/6250000000000 : ℝ), (3228427391521/25000000000000 : ℝ), (2749200839433/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312201841/10000000000 : ℝ)|^2061 ≤ (2693692312101/6250000000000 : ℝ)^1549
        have hw : |(5312201841/10000000000 : ℝ)|=(5312201841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-429453819/2000000000 : ℝ)|^2061 ≤ (3228427391521/25000000000000 : ℝ)^1549
        have hw : |(-429453819/2000000000 : ℝ)|=(429453819/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394266489/10000000000 : ℝ)|^2061 ≤ (2749200839433/6250000000000 : ℝ)^1549
        have hw : |(5394266489/10000000000 : ℝ)|=(5394266489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s9_3 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312201781/10000000000 : ℝ)*x 0 + (5394266539/10000000000 : ℝ)*x 1 + (-2147269107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312201781/10000000000 : ℝ)^2061 ≤ (134684613581/312500000000 : ℝ)^1549 := by
    have hnat : (5312201781 : ℕ)^2061*312500000000^1549 ≤ 134684613581^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312201781 10000000000 134684613581 312500000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394266539/10000000000 : ℝ)^2061 ≤ (5498401746677/12500000000000 : ℝ)^1549 := by
    have hnat : (5394266539 : ℕ)^2061*12500000000000^1549 ≤ 5498401746677^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394266539 10000000000 5498401746677 12500000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2147269107/10000000000 : ℝ)^2061 ≤ (12913709662107/100000000000000 : ℝ)^1549 := by
    have hnat : (2147269107 : ℕ)^2061*100000000000000^1549 ≤ 12913709662107^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147269107 10000000000 12913709662107 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312201781/10000000000 : ℝ), (5394266539/10000000000 : ℝ), (-2147269107/10000000000 : ℝ)] ![(134684613581/312500000000 : ℝ), (5498401746677/12500000000000 : ℝ), (12913709662107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312201781/10000000000 : ℝ)|^2061 ≤ (134684613581/312500000000 : ℝ)^1549
        have hw : |(5312201781/10000000000 : ℝ)|=(5312201781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394266539/10000000000 : ℝ)|^2061 ≤ (5498401746677/12500000000000 : ℝ)^1549
        have hw : |(5394266539/10000000000 : ℝ)|=(5394266539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2147269107/10000000000 : ℝ)|^2061 ≤ (12913709662107/100000000000000 : ℝ)^1549
        have hw : |(-2147269107/10000000000 : ℝ)|=(2147269107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_s9_4 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4377665233/10000000000 : ℝ)*x 0 + (4506300029/10000000000 : ℝ)*x 1 + (850556389/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4377665233/10000000000 : ℝ)^2061 ≤ (4164571934949/12500000000000 : ℝ)^1549 := by
    have hnat : (4377665233 : ℕ)^2061*12500000000000^1549 ≤ 4164571934949^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4377665233 10000000000 4164571934949 12500000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4506300029/10000000000 : ℝ)^2061 ≤ (34625435498401/100000000000000 : ℝ)^1549 := by
    have hnat : (4506300029 : ℕ)^2061*100000000000000^1549 ≤ 34625435498401^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506300029 10000000000 34625435498401 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (850556389/2000000000 : ℝ)^2061 ≤ (16028994504711/50000000000000 : ℝ)^1549 := by
    have hnat : (850556389 : ℕ)^2061*50000000000000^1549 ≤ 16028994504711^1549*2000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850556389 2000000000 16028994504711 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4377665233/10000000000 : ℝ), (4506300029/10000000000 : ℝ), (850556389/2000000000 : ℝ)] ![(4164571934949/12500000000000 : ℝ), (34625435498401/100000000000000 : ℝ), (16028994504711/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4377665233/10000000000 : ℝ)|^2061 ≤ (4164571934949/12500000000000 : ℝ)^1549
        have hw : |(4377665233/10000000000 : ℝ)|=(4377665233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4506300029/10000000000 : ℝ)|^2061 ≤ (34625435498401/100000000000000 : ℝ)^1549
        have hw : |(4506300029/10000000000 : ℝ)|=(4506300029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(850556389/2000000000 : ℝ)|^2061 ≤ (16028994504711/50000000000000 : ℝ)^1549
        have hw : |(850556389/2000000000 : ℝ)|=(850556389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1051_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147701323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6997/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11231/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11231/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13993/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6997/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11231/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6997/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11231/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6997/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11231/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6997/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11231/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6997/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11231/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6997/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11231/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11231/100000 : ℝ) ^ (8243/2048 : ℝ) ≤ (15067003953852933/100000000000000000000 : ℝ) := by
    have hpowers : (11231/100000 : ℝ)^8243 ≤ (15067003953852933/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11231 : ℕ)^8243*100000000000000000000^2048 ≤ 15067003953852933^2048*100000^8243 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11231 100000 15067003953852933 100000000000000000000 8243 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11231/100000 : ℝ)) (X := (15067003953852933/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (6997/50000 : ℝ) ^ (8243/2048 : ℝ) ≤ (36517364726595539/100000000000000000000 : ℝ) := by
    have hpowers : (6997/50000 : ℝ)^8243 ≤ (36517364726595539/100000000000000000000 : ℝ)^2048 := by
      have hnat : (6997 : ℕ)^8243*100000000000000000000^2048 ≤ 36517364726595539^2048*50000^8243 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6997 50000 36517364726595539 100000000000000000000 8243 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6997/50000 : ℝ)) (X := (36517364726595539/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50015067003953852933/50000000000000000000 : ℝ) ≤ (10000748604405591/10000000000000000 : ℝ) ^ (8243/2048 : ℝ) := by
    have hpowers : (50015067003953852933/50000000000000000000 : ℝ)^2048 ≤ (10000748604405591/10000000000000000 : ℝ)^8243 := by
      have hnat : (50015067003953852933 : ℕ)^2048*10000000000000000^8243 ≤ 10000748604405591^8243*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015067003953852933 50000000000000000000 10000748604405591 10000000000000000 2048 8243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000748604405591/10000000000000000 : ℝ)) (X := (50015067003953852933/50000000000000000000 : ℝ)) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506448046085056059/12500000000000000000 : ℝ) ≤ (2000256276392097/2000000000000000 : ℝ) ^ (8243/2048 : ℝ) := by
    have hpowers : (12506448046085056059/12500000000000000000 : ℝ)^2048 ≤ (2000256276392097/2000000000000000 : ℝ)^8243 := by
      have hnat : (12506448046085056059 : ℕ)^2048*2000000000000000^8243 ≤ 2000256276392097^8243*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506448046085056059 12500000000000000000 2000256276392097 2000000000000000 2048 8243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000256276392097/2000000000000000 : ℝ)) (X := (12506448046085056059/12500000000000000000 : ℝ)) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036517364726595539/50000000000000000000 : ℝ) ≤ (10001814159515379/10000000000000000 : ℝ) ^ (8243/2048 : ℝ) := by
    have hpowers : (50036517364726595539/50000000000000000000 : ℝ)^2048 ≤ (10001814159515379/10000000000000000 : ℝ)^8243 := by
      have hnat : (50036517364726595539 : ℕ)^2048*10000000000000000^8243 ≤ 10001814159515379^8243*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036517364726595539 50000000000000000000 10001814159515379 10000000000000000 2048 8243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001814159515379/10000000000000000 : ℝ)) (X := (50036517364726595539/50000000000000000000 : ℝ)) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15067003953852933/100000000000000000000 : ℝ) ≤ ((1841340076302307927/1842000000000000000 : ℝ)+2*(88796259149/46050000000000 : ℝ)*(11231/100000 : ℝ))^(8243/2048 : ℝ) := by
    rw [show (1841340076302307927/1842000000000000000 : ℝ)+2*(88796259149/46050000000000 : ℝ)*(11231/100000 : ℝ)=(10000748604405591/10000000000000000 : ℝ) by norm_num, show 1+2*(15067003953852933/100000000000000000000 : ℝ)=(50015067003953852933/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36517364726595539/100000000000000000000 : ℝ)+(15067003953852933/100000000000000000000 : ℝ) ≤ ((1841340076302307927/1842000000000000000 : ℝ)+(88796259149/46050000000000 : ℝ)*((6997/50000 : ℝ)+(11231/100000 : ℝ)))^(8243/2048 : ℝ) := by
    rw [show (1841340076302307927/1842000000000000000 : ℝ)+(88796259149/46050000000000 : ℝ)*((6997/50000 : ℝ)+(11231/100000 : ℝ))=(2000256276392097/2000000000000000 : ℝ) by norm_num, show 1+(36517364726595539/100000000000000000000 : ℝ)+(15067003953852933/100000000000000000000 : ℝ)=(12506448046085056059/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36517364726595539/100000000000000000000 : ℝ) ≤ ((1841340076302307927/1842000000000000000 : ℝ)+2*(88796259149/46050000000000 : ℝ)*(6997/50000 : ℝ))^(8243/2048 : ℝ) := by
    rw [show (1841340076302307927/1842000000000000000 : ℝ)+2*(88796259149/46050000000000 : ℝ)*(6997/50000 : ℝ)=(10001814159515379/10000000000000000 : ℝ) by norm_num, show 1+2*(36517364726595539/100000000000000000000 : ℝ)=(50036517364726595539/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1841340076302307927/1842000000000000000 : ℝ)*(X 1 0+X 2 0)+(88796259149/46050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8243/2048 : ℝ)) (lo := (11231/100000 : ℝ)) (hi := (6997/50000 : ℝ)) (c := (1841340076302307927/1842000000000000000 : ℝ)) (alpha := (88796259149/46050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1841340076302307927/1842000000000000000 : ℝ)*(X 0 1+X 2 1)+(88796259149/46050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8243/2048 : ℝ)) (lo := (11231/100000 : ℝ)) (hi := (6997/50000 : ℝ)) (c := (1841340076302307927/1842000000000000000 : ℝ)) (alpha := (88796259149/46050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1841340076302307927/1842000000000000000 : ℝ)*(X 0 2+X 1 2)+(88796259149/46050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8243/2048 : ℝ)) (lo := (11231/100000 : ℝ)) (hi := (6997/50000 : ℝ)) (c := (1841340076302307927/1842000000000000000 : ℝ)) (alpha := (88796259149/46050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((2672503247/5000000000 : ℝ)*X 1 0+(-2277336911/10000000000 : ℝ)*X 1 1+(526419871/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s9_0 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-2211179901/10000000000 : ℝ)*X 0 0+(2632262493/5000000000 : ℝ)*X 0 1+(5394266391/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s9_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5312201841/10000000000 : ℝ)*X 1 0+(-429453819/2000000000 : ℝ)*X 1 1+(5394266489/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s9_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5312201781/10000000000 : ℝ)*X 2 0+(5394266539/10000000000 : ℝ)*X 2 1+(-2147269107/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s9_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((4377665233/10000000000 : ℝ)*X 0 0+(4506300029/10000000000 : ℝ)*X 0 1+(850556389/2000000000 : ℝ)*X 0 2+(4377665233/10000000000 : ℝ)*X 1 0+(4506300029/10000000000 : ℝ)*X 1 1+(850556389/2000000000 : ℝ)*X 1 2+(4377665233/10000000000 : ℝ)*X 2 0+(4506300029/10000000000 : ℝ)*X 2 1+(850556389/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_s9_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10715500276974465414183921/1918750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1250228321/100000000000000 : ℝ)*(base19) + (603584433/50000000000000 : ℝ)*(base23) + (481430803/100000000000000 : ℝ)*(lower1) + (160316671/100000000000000 : ℝ)*(upper3) + (1031801/4000000000000 : ℝ)*(lower4) + (179538039/100000000000000 : ℝ)*(upper5) + (728254608480823/12500000000000 : ℝ)*(major0) + (728254608480823/12500000000000 : ℝ)*(major1) + (728254608480823/12500000000000 : ℝ)*(major2) + (184689733/25000000000000 : ℝ)*(sp0) + (770760186200603/10000000000000 : ℝ)*(sp1) + (963449984127347/12500000000000 : ℝ)*(sp2) + (1926900163709291/25000000000000 : ℝ)*(sp3) + (246529480470809/6250000000000 : ℝ)*(sp4) + (246529480470809/6250000000000 : ℝ)*(f.failure) + (770760186200603/10000000000000 : ℝ)*(f.sum) + (4237602655889/2302500000000000000000000000 : ℝ)*base66 + (91905351935478693/7675000000000000000000000000000 : ℝ)*base68 + (168649310589928693/7675000000000000000000000000000 : ℝ)*base70 + (64041924638978693/7675000000000000000000000000000 : ℝ)*base72 + (780422181847/1151250000000000000000000000 : ℝ)*base74 + (111371950621307/7675000000000000000000000000000 : ℝ)*base75 + (77323650749478693/7675000000000000000000000000000 : ℝ)*base78 + (116781483773278693/7675000000000000000000000000000 : ℝ)*base80 + (6780293867707/1151250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (2180307/625000000000000000000 : ℝ)*base89 + (2180307/625000000000000000000 : ℝ)*base91 + (2180307/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1051_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147701323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6997/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11231/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11231/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13993/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1051_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1051_box_0 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-65037303/312500000 : ℝ)*x 0 + (5377570129/10000000000 : ℝ)*x 1 + (1344392537/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65037303/312500000 : ℝ)^2061 ≤ (6193845432423/50000000000000 : ℝ)^1549 := by
    have hnat : (65037303 : ℕ)^2061*50000000000000^1549 ≤ 6193845432423^1549*312500000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65037303 312500000 6193845432423 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377570129/10000000000 : ℝ)^2061 ≤ (10951538613897/25000000000000 : ℝ)^1549 := by
    have hnat : (5377570129 : ℕ)^2061*25000000000000^1549 ≤ 10951538613897^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377570129 10000000000 10951538613897 25000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1344392537/2500000000 : ℝ)^2061 ≤ (21903077330761/50000000000000 : ℝ)^1549 := by
    have hnat : (1344392537 : ℕ)^2061*50000000000000^1549 ≤ 21903077330761^1549*2500000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344392537 2500000000 21903077330761 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-65037303/312500000 : ℝ), (5377570129/10000000000 : ℝ), (1344392537/2500000000 : ℝ)] ![(6193845432423/50000000000000 : ℝ), (10951538613897/25000000000000 : ℝ), (21903077330761/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-65037303/312500000 : ℝ)|^2061 ≤ (6193845432423/50000000000000 : ℝ)^1549
        have hw : |(-65037303/312500000 : ℝ)|=(65037303/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377570129/10000000000 : ℝ)|^2061 ≤ (10951538613897/25000000000000 : ℝ)^1549
        have hw : |(5377570129/10000000000 : ℝ)|=(5377570129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1344392537/2500000000 : ℝ)|^2061 ≤ (21903077330761/50000000000000 : ℝ)^1549
        have hw : |(1344392537/2500000000 : ℝ)|=(1344392537/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_box_1 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1059006159/2000000000 : ℝ)*x 0 + (-2192889477/10000000000 : ℝ)*x 1 + (1075513959/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059006159/2000000000 : ℝ)^2061 ≤ (42913815784703/100000000000000 : ℝ)^1549 := by
    have hnat : (1059006159 : ℕ)^2061*100000000000000^1549 ≤ 42913815784703^1549*2000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059006159 2000000000 42913815784703 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2192889477/10000000000 : ℝ)^2061 ≤ (13280033364999/100000000000000 : ℝ)^1549 := by
    have hnat : (2192889477 : ℕ)^2061*100000000000000^1549 ≤ 13280033364999^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2192889477 10000000000 13280033364999 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1075513959/2000000000 : ℝ)^2061 ≤ (1752246033419/4000000000000 : ℝ)^1549 := by
    have hnat : (1075513959 : ℕ)^2061*4000000000000^1549 ≤ 1752246033419^1549*2000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075513959 2000000000 1752246033419 4000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059006159/2000000000 : ℝ), (-2192889477/10000000000 : ℝ), (1075513959/2000000000 : ℝ)] ![(42913815784703/100000000000000 : ℝ), (13280033364999/100000000000000 : ℝ), (1752246033419/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059006159/2000000000 : ℝ)|^2061 ≤ (42913815784703/100000000000000 : ℝ)^1549
        have hw : |(1059006159/2000000000 : ℝ)|=(1059006159/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2192889477/10000000000 : ℝ)|^2061 ≤ (13280033364999/100000000000000 : ℝ)^1549
        have hw : |(-2192889477/10000000000 : ℝ)|=(2192889477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1075513959/2000000000 : ℝ)|^2061 ≤ (1752246033419/4000000000000 : ℝ)^1549
        have hw : |(1075513959/2000000000 : ℝ)|=(1075513959/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_box_2 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5295030583/10000000000 : ℝ)*x 0 + (5377570013/10000000000 : ℝ)*x 1 + (-548222367/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295030583/10000000000 : ℝ)^2061 ≤ (167632083979/390625000000 : ℝ)^1549 := by
    have hnat : (5295030583 : ℕ)^2061*390625000000^1549 ≤ 167632083979^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295030583 10000000000 167632083979 390625000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377570013/10000000000 : ℝ)^2061 ≤ (43806153198303/100000000000000 : ℝ)^1549 := by
    have hnat : (5377570013 : ℕ)^2061*100000000000000^1549 ≤ 43806153198303^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377570013 10000000000 43806153198303 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (548222367/2500000000 : ℝ)^2061 ≤ (41500104039/312500000000 : ℝ)^1549 := by
    have hnat : (548222367 : ℕ)^2061*312500000000^1549 ≤ 41500104039^1549*2500000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548222367 2500000000 41500104039 312500000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295030583/10000000000 : ℝ), (5377570013/10000000000 : ℝ), (-548222367/2500000000 : ℝ)] ![(167632083979/390625000000 : ℝ), (43806153198303/100000000000000 : ℝ), (41500104039/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295030583/10000000000 : ℝ)|^2061 ≤ (167632083979/390625000000 : ℝ)^1549
        have hw : |(5295030583/10000000000 : ℝ)|=(5295030583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377570013/10000000000 : ℝ)|^2061 ≤ (43806153198303/100000000000000 : ℝ)^1549
        have hw : |(5377570013/10000000000 : ℝ)|=(5377570013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-548222367/2500000000 : ℝ)|^2061 ≤ (41500104039/312500000000 : ℝ)^1549
        have hw : |(-548222367/2500000000 : ℝ)|=(548222367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_box_3 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2243108167/5000000000 : ℝ)*x 0 + (540693503/1250000000 : ℝ)*x 1 + (865109603/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2243108167/5000000000 : ℝ)^2061 ≤ (4302532528853/12500000000000 : ℝ)^1549 := by
    have hnat : (2243108167 : ℕ)^2061*12500000000000^1549 ≤ 4302532528853^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243108167 5000000000 4302532528853 12500000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540693503/1250000000 : ℝ)^2061 ≤ (8197467479137/25000000000000 : ℝ)^1549 := by
    have hnat : (540693503 : ℕ)^2061*25000000000000^1549 ≤ 8197467479137^1549*1250000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540693503 1250000000 8197467479137 25000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (865109603/2000000000 : ℝ)^2061 ≤ (32789869825773/100000000000000 : ℝ)^1549 := by
    have hnat : (865109603 : ℕ)^2061*100000000000000^1549 ≤ 32789869825773^1549*2000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865109603 2000000000 32789869825773 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2243108167/5000000000 : ℝ), (540693503/1250000000 : ℝ), (865109603/2000000000 : ℝ)] ![(4302532528853/12500000000000 : ℝ), (8197467479137/25000000000000 : ℝ), (32789869825773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2243108167/5000000000 : ℝ)|^2061 ≤ (4302532528853/12500000000000 : ℝ)^1549
        have hw : |(2243108167/5000000000 : ℝ)|=(2243108167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540693503/1250000000 : ℝ)|^2061 ≤ (8197467479137/25000000000000 : ℝ)^1549
        have hw : |(540693503/1250000000 : ℝ)|=(540693503/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(865109603/2000000000 : ℝ)|^2061 ≤ (32789869825773/100000000000000 : ℝ)^1549
        have hw : |(865109603/2000000000 : ℝ)|=(865109603/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_box_4 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2342549021/10000000000 : ℝ)*x 0 + (1055972573/2000000000 : ℝ)*x 1 + (164995707/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2342549021/10000000000 : ℝ)^2061 ≤ (7249669691323/50000000000000 : ℝ)^1549 := by
    have hnat : (2342549021 : ℕ)^2061*50000000000000^1549 ≤ 7249669691323^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2342549021 10000000000 7249669691323 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1055972573/2000000000 : ℝ)^2061 ≤ (42750331599109/100000000000000 : ℝ)^1549 := by
    have hnat : (1055972573 : ℕ)^2061*100000000000000^1549 ≤ 42750331599109^1549*2000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055972573 2000000000 42750331599109 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164995707/312500000 : ℝ)^2061 ≤ (1710013160111/4000000000000 : ℝ)^1549 := by
    have hnat : (164995707 : ℕ)^2061*4000000000000^1549 ≤ 1710013160111^1549*312500000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164995707 312500000 1710013160111 4000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2342549021/10000000000 : ℝ), (1055972573/2000000000 : ℝ), (164995707/312500000 : ℝ)] ![(7249669691323/50000000000000 : ℝ), (42750331599109/100000000000000 : ℝ), (1710013160111/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2342549021/10000000000 : ℝ)|^2061 ≤ (7249669691323/50000000000000 : ℝ)^1549
        have hw : |(-2342549021/10000000000 : ℝ)|=(2342549021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1055972573/2000000000 : ℝ)|^2061 ≤ (42750331599109/100000000000000 : ℝ)^1549
        have hw : |(1055972573/2000000000 : ℝ)|=(1055972573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164995707/312500000 : ℝ)|^2061 ≤ (1710013160111/4000000000000 : ℝ)^1549
        have hw : |(164995707/312500000 : ℝ)|=(164995707/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_box_5 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5364203729/10000000000 : ℝ)*x 0 + (-557760463/2500000000 : ℝ)*x 1 + (5279862443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364203729/10000000000 : ℝ)^2061 ≤ (43661340126487/100000000000000 : ℝ)^1549 := by
    have hnat : (5364203729 : ℕ)^2061*100000000000000^1549 ≤ 43661340126487^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364203729 10000000000 43661340126487 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (557760463/2500000000 : ℝ)^2061 ≤ (13588332807637/100000000000000 : ℝ)^1549 := by
    have hnat : (557760463 : ℕ)^2061*100000000000000^1549 ≤ 13588332807637^1549*2500000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      557760463 2500000000 13588332807637 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5279862443/10000000000 : ℝ)^2061 ≤ (1335947720401/3125000000000 : ℝ)^1549 := by
    have hnat : (5279862443 : ℕ)^2061*3125000000000^1549 ≤ 1335947720401^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279862443 10000000000 1335947720401 3125000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364203729/10000000000 : ℝ), (-557760463/2500000000 : ℝ), (5279862443/10000000000 : ℝ)] ![(43661340126487/100000000000000 : ℝ), (13588332807637/100000000000000 : ℝ), (1335947720401/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364203729/10000000000 : ℝ)|^2061 ≤ (43661340126487/100000000000000 : ℝ)^1549
        have hw : |(5364203729/10000000000 : ℝ)|=(5364203729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-557760463/2500000000 : ℝ)|^2061 ≤ (13588332807637/100000000000000 : ℝ)^1549
        have hw : |(-557760463/2500000000 : ℝ)|=(557760463/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5279862443/10000000000 : ℝ)|^2061 ≤ (1335947720401/3125000000000 : ℝ)^1549
        have hw : |(5279862443/10000000000 : ℝ)|=(5279862443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_box_6 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (268210139/500000000 : ℝ)*x 0 + (527986331/1000000000 : ℝ)*x 1 + (-2231041967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268210139/500000000 : ℝ)^2061 ≤ (1364416557783/3125000000000 : ℝ)^1549 := by
    have hnat : (268210139 : ℕ)^2061*3125000000000^1549 ≤ 1364416557783^1549*500000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268210139 500000000 1364416557783 3125000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (527986331/1000000000 : ℝ)^2061 ≤ (2671896024573/6250000000000 : ℝ)^1549 := by
    have hnat : (527986331 : ℕ)^2061*6250000000000^1549 ≤ 2671896024573^1549*1000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527986331 1000000000 2671896024573 6250000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2231041967/10000000000 : ℝ)^2061 ≤ (6794166869783/50000000000000 : ℝ)^1549 := by
    have hnat : (2231041967 : ℕ)^2061*50000000000000^1549 ≤ 6794166869783^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2231041967 10000000000 6794166869783 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268210139/500000000 : ℝ), (527986331/1000000000 : ℝ), (-2231041967/10000000000 : ℝ)] ![(1364416557783/3125000000000 : ℝ), (2671896024573/6250000000000 : ℝ), (6794166869783/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268210139/500000000 : ℝ)|^2061 ≤ (1364416557783/3125000000000 : ℝ)^1549
        have hw : |(268210139/500000000 : ℝ)|=(268210139/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(527986331/1000000000 : ℝ)|^2061 ≤ (2671896024573/6250000000000 : ℝ)^1549
        have hw : |(527986331/1000000000 : ℝ)|=(527986331/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2231041967/10000000000 : ℝ)|^2061 ≤ (6794166869783/50000000000000 : ℝ)^1549
        have hw : |(-2231041967/10000000000 : ℝ)|=(2231041967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_box_7 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4268770691/10000000000 : ℝ)*x 0 + (2217124769/5000000000 : ℝ)*x 1 + (4434248959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4268770691/10000000000 : ℝ)^2061 ≤ (32218451553187/100000000000000 : ℝ)^1549 := by
    have hnat : (4268770691 : ℕ)^2061*100000000000000^1549 ≤ 32218451553187^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4268770691 10000000000 32218451553187 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2217124769/5000000000 : ℝ)^2061 ≤ (33890777164217/100000000000000 : ℝ)^1549 := by
    have hnat : (2217124769 : ℕ)^2061*100000000000000^1549 ≤ 33890777164217^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217124769 5000000000 33890777164217 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4434248959/10000000000 : ℝ)^2061 ≤ (6778154255247/20000000000000 : ℝ)^1549 := by
    have hnat : (4434248959 : ℕ)^2061*20000000000000^1549 ≤ 6778154255247^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4434248959 10000000000 6778154255247 20000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4268770691/10000000000 : ℝ), (2217124769/5000000000 : ℝ), (4434248959/10000000000 : ℝ)] ![(32218451553187/100000000000000 : ℝ), (33890777164217/100000000000000 : ℝ), (6778154255247/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4268770691/10000000000 : ℝ)|^2061 ≤ (32218451553187/100000000000000 : ℝ)^1549
        have hw : |(4268770691/10000000000 : ℝ)|=(4268770691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2217124769/5000000000 : ℝ)|^2061 ≤ (33890777164217/100000000000000 : ℝ)^1549
        have hw : |(2217124769/5000000000 : ℝ)|=(2217124769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4434248959/10000000000 : ℝ)|^2061 ≤ (6778154255247/20000000000000 : ℝ)^1549
        have hw : |(4434248959/10000000000 : ℝ)|=(4434248959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_box_8 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1144004021/5000000000 : ℝ)*x 0 + (5213591983/10000000000 : ℝ)*x 1 + (673396101/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1144004021/5000000000 : ℝ)^2061 ≤ (878244285711/6250000000000 : ℝ)^1549 := by
    have hnat : (1144004021 : ℕ)^2061*6250000000000^1549 ≤ 878244285711^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1144004021 5000000000 878244285711 6250000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5213591983/10000000000 : ℝ)^2061 ≤ (10509467361247/25000000000000 : ℝ)^1549 := by
    have hnat : (5213591983 : ℕ)^2061*25000000000000^1549 ≤ 10509467361247^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5213591983 10000000000 10509467361247 25000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673396101/1250000000 : ℝ)^2061 ≤ (8782044391717/20000000000000 : ℝ)^1549 := by
    have hnat : (673396101 : ℕ)^2061*20000000000000^1549 ≤ 8782044391717^1549*1250000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673396101 1250000000 8782044391717 20000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1144004021/5000000000 : ℝ), (5213591983/10000000000 : ℝ), (673396101/1250000000 : ℝ)] ![(878244285711/6250000000000 : ℝ), (10509467361247/25000000000000 : ℝ), (8782044391717/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1144004021/5000000000 : ℝ)|^2061 ≤ (878244285711/6250000000000 : ℝ)^1549
        have hw : |(-1144004021/5000000000 : ℝ)|=(1144004021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5213591983/10000000000 : ℝ)|^2061 ≤ (10509467361247/25000000000000 : ℝ)^1549
        have hw : |(5213591983/10000000000 : ℝ)|=(5213591983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673396101/1250000000 : ℝ)|^2061 ≤ (8782044391717/20000000000000 : ℝ)^1549
        have hw : |(673396101/1250000000 : ℝ)|=(673396101/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_box_9 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2644115577/5000000000 : ℝ)*x 0 + (-437814109/2000000000 : ℝ)*x 1 + (5387168741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644115577/5000000000 : ℝ)^2061 ≤ (42840508185981/100000000000000 : ℝ)^1549 := by
    have hnat : (2644115577 : ℕ)^2061*100000000000000^1549 ≤ 42840508185981^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644115577 5000000000 42840508185981 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (437814109/2000000000 : ℝ)^2061 ≤ (13249270565219/100000000000000 : ℝ)^1549 := by
    have hnat : (437814109 : ℕ)^2061*100000000000000^1549 ≤ 13249270565219^1549*2000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437814109 2000000000 13249270565219 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5387168741/10000000000 : ℝ)^2061 ≤ (43910221231967/100000000000000 : ℝ)^1549 := by
    have hnat : (5387168741 : ℕ)^2061*100000000000000^1549 ≤ 43910221231967^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387168741 10000000000 43910221231967 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644115577/5000000000 : ℝ), (-437814109/2000000000 : ℝ), (5387168741/10000000000 : ℝ)] ![(42840508185981/100000000000000 : ℝ), (13249270565219/100000000000000 : ℝ), (43910221231967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644115577/5000000000 : ℝ)|^2061 ≤ (42840508185981/100000000000000 : ℝ)^1549
        have hw : |(2644115577/5000000000 : ℝ)|=(2644115577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-437814109/2000000000 : ℝ)|^2061 ≤ (13249270565219/100000000000000 : ℝ)^1549
        have hw : |(-437814109/2000000000 : ℝ)|=(437814109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5387168741/10000000000 : ℝ)|^2061 ≤ (43910221231967/100000000000000 : ℝ)^1549
        have hw : |(5387168741/10000000000 : ℝ)|=(5387168741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_box_10 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (82628613/156250000 : ℝ)*x 0 + (5387168761/10000000000 : ℝ)*x 1 + (-1094535207/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82628613/156250000 : ℝ)^2061 ≤ (5355063628341/12500000000000 : ℝ)^1549 := by
    have hnat : (82628613 : ℕ)^2061*12500000000000^1549 ≤ 5355063628341^1549*156250000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82628613 156250000 5355063628341 12500000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5387168761/10000000000 : ℝ)^2061 ≤ (10977555362217/25000000000000 : ℝ)^1549 := by
    have hnat : (5387168761 : ℕ)^2061*25000000000000^1549 ≤ 10977555362217^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387168761 10000000000 10977555362217 25000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1094535207/5000000000 : ℝ)^2061 ≤ (13249269510273/100000000000000 : ℝ)^1549 := by
    have hnat : (1094535207 : ℕ)^2061*100000000000000^1549 ≤ 13249269510273^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094535207 5000000000 13249269510273 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82628613/156250000 : ℝ), (5387168761/10000000000 : ℝ), (-1094535207/5000000000 : ℝ)] ![(5355063628341/12500000000000 : ℝ), (10977555362217/25000000000000 : ℝ), (13249269510273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82628613/156250000 : ℝ)|^2061 ≤ (5355063628341/12500000000000 : ℝ)^1549
        have hw : |(82628613/156250000 : ℝ)|=(82628613/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5387168761/10000000000 : ℝ)|^2061 ≤ (10977555362217/25000000000000 : ℝ)^1549
        have hw : |(5387168761/10000000000 : ℝ)|=(5387168761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1094535207/5000000000 : ℝ)|^2061 ≤ (13249269510273/100000000000000 : ℝ)^1549
        have hw : |(-1094535207/5000000000 : ℝ)|=(1094535207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_box_11 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (90146091/200000000 : ℝ)*x 0 + (4314863333/10000000000 : ℝ)*x 1 + (1078715861/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (90146091/200000000 : ℝ)^2061 ≤ (34635705647149/100000000000000 : ℝ)^1549 := by
    have hnat : (90146091 : ℕ)^2061*100000000000000^1549 ≤ 34635705647149^1549*200000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90146091 200000000 34635705647149 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4314863333/10000000000 : ℝ)^2061 ≤ (326821466117/1000000000000 : ℝ)^1549 := by
    have hnat : (4314863333 : ℕ)^2061*1000000000000^1549 ≤ 326821466117^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4314863333 10000000000 326821466117 1000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078715861/2500000000 : ℝ)^2061 ≤ (32682147730347/100000000000000 : ℝ)^1549 := by
    have hnat : (1078715861 : ℕ)^2061*100000000000000^1549 ≤ 32682147730347^1549*2500000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078715861 2500000000 32682147730347 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(90146091/200000000 : ℝ), (4314863333/10000000000 : ℝ), (1078715861/2500000000 : ℝ)] ![(34635705647149/100000000000000 : ℝ), (326821466117/1000000000000 : ℝ), (32682147730347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(90146091/200000000 : ℝ)|^2061 ≤ (34635705647149/100000000000000 : ℝ)^1549
        have hw : |(90146091/200000000 : ℝ)|=(90146091/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4314863333/10000000000 : ℝ)|^2061 ≤ (326821466117/1000000000000 : ℝ)^1549
        have hw : |(4314863333/10000000000 : ℝ)|=(4314863333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078715861/2500000000 : ℝ)|^2061 ≤ (32682147730347/100000000000000 : ℝ)^1549
        have hw : |(1078715861/2500000000 : ℝ)|=(1078715861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_box_12 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2136113623/10000000000 : ℝ)*x 0 + (1360623321/2500000000 : ℝ)*x 1 + (5271869889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2136113623/10000000000 : ℝ)^2061 ≤ (12824521738117/100000000000000 : ℝ)^1549 := by
    have hnat : (2136113623 : ℕ)^2061*100000000000000^1549 ≤ 12824521738117^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136113623 10000000000 12824521738117 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1360623321/2500000000 : ℝ)^2061 ≤ (1390976086687/3125000000000 : ℝ)^1549 := by
    have hnat : (1360623321 : ℕ)^2061*3125000000000^1549 ≤ 1390976086687^1549*2500000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360623321 2500000000 1390976086687 3125000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5271869889/10000000000 : ℝ)^2061 ≤ (21332121739881/50000000000000 : ℝ)^1549 := by
    have hnat : (5271869889 : ℕ)^2061*50000000000000^1549 ≤ 21332121739881^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271869889 10000000000 21332121739881 50000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2136113623/10000000000 : ℝ), (1360623321/2500000000 : ℝ), (5271869889/10000000000 : ℝ)] ![(12824521738117/100000000000000 : ℝ), (1390976086687/3125000000000 : ℝ), (21332121739881/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2136113623/10000000000 : ℝ)|^2061 ≤ (12824521738117/100000000000000 : ℝ)^1549
        have hw : |(-2136113623/10000000000 : ℝ)|=(2136113623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1360623321/2500000000 : ℝ)|^2061 ≤ (1390976086687/3125000000000 : ℝ)^1549
        have hw : |(1360623321/2500000000 : ℝ)|=(1360623321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5271869889/10000000000 : ℝ)|^2061 ≤ (21332121739881/50000000000000 : ℝ)^1549
        have hw : |(5271869889/10000000000 : ℝ)|=(5271869889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_box_13 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (83904063/156250000 : ℝ)*x 0 + (-223410369/1000000000 : ℝ)*x 1 + (5271869761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83904063/156250000 : ℝ)^2061 ≤ (5465325892251/12500000000000 : ℝ)^1549 := by
    have hnat : (83904063 : ℕ)^2061*12500000000000^1549 ≤ 5465325892251^1549*156250000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83904063 156250000 5465325892251 12500000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (223410369/1000000000 : ℝ)^2061 ≤ (13613150746011/100000000000000 : ℝ)^1549 := by
    have hnat : (223410369 : ℕ)^2061*100000000000000^1549 ≤ 13613150746011^1549*1000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223410369 1000000000 13613150746011 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5271869761/10000000000 : ℝ)^2061 ≤ (42664242101487/100000000000000 : ℝ)^1549 := by
    have hnat : (5271869761 : ℕ)^2061*100000000000000^1549 ≤ 42664242101487^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271869761 10000000000 42664242101487 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83904063/156250000 : ℝ), (-223410369/1000000000 : ℝ), (5271869761/10000000000 : ℝ)] ![(5465325892251/12500000000000 : ℝ), (13613150746011/100000000000000 : ℝ), (42664242101487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83904063/156250000 : ℝ)|^2061 ≤ (5465325892251/12500000000000 : ℝ)^1549
        have hw : |(83904063/156250000 : ℝ)|=(83904063/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-223410369/1000000000 : ℝ)|^2061 ≤ (13613150746011/100000000000000 : ℝ)^1549
        have hw : |(-223410369/1000000000 : ℝ)|=(223410369/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5271869761/10000000000 : ℝ)|^2061 ≤ (42664242101487/100000000000000 : ℝ)^1549
        have hw : |(5271869761/10000000000 : ℝ)|=(5271869761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_box_14 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5369860021/10000000000 : ℝ)*x 0 + (2635934851/5000000000 : ℝ)*x 1 + (-2234103783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369860021/10000000000 : ℝ)^2061 ≤ (43722607018839/100000000000000 : ℝ)^1549 := by
    have hnat : (5369860021 : ℕ)^2061*100000000000000^1549 ≤ 43722607018839^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369860021 10000000000 43722607018839 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2635934851/5000000000 : ℝ)^2061 ≤ (10666060366547/25000000000000 : ℝ)^1549 := by
    have hnat : (2635934851 : ℕ)^2061*25000000000000^1549 ≤ 10666060366547^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635934851 5000000000 10666060366547 25000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2234103783/10000000000 : ℝ)^2061 ≤ (13613151499999/100000000000000 : ℝ)^1549 := by
    have hnat : (2234103783 : ℕ)^2061*100000000000000^1549 ≤ 13613151499999^1549*10000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2234103783 10000000000 13613151499999 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369860021/10000000000 : ℝ), (2635934851/5000000000 : ℝ), (-2234103783/10000000000 : ℝ)] ![(43722607018839/100000000000000 : ℝ), (10666060366547/25000000000000 : ℝ), (13613151499999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369860021/10000000000 : ℝ)|^2061 ≤ (43722607018839/100000000000000 : ℝ)^1549
        have hw : |(5369860021/10000000000 : ℝ)|=(5369860021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2635934851/5000000000 : ℝ)|^2061 ≤ (10666060366547/25000000000000 : ℝ)^1549
        have hw : |(2635934851/5000000000 : ℝ)|=(2635934851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2234103783/10000000000 : ℝ)|^2061 ≤ (13613151499999/100000000000000 : ℝ)^1549
        have hw : |(-2234103783/10000000000 : ℝ)|=(2234103783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1051_box_15 (p : ℝ) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2125376803/5000000000 : ℝ)*x 0 + (88862719/200000000 : ℝ)*x 1 + (555392031/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2125376803/5000000000 : ℝ)^2061 ≤ (1601882344879/5000000000000 : ℝ)^1549 := by
    have hnat : (2125376803 : ℕ)^2061*5000000000000^1549 ≤ 1601882344879^1549*5000000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125376803 5000000000 1601882344879 5000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (88862719/200000000 : ℝ)^2061 ≤ (33981175028241/100000000000000 : ℝ)^1549 := by
    have hnat : (88862719 : ℕ)^2061*100000000000000^1549 ≤ 33981175028241^1549*200000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88862719 200000000 33981175028241 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (555392031/1250000000 : ℝ)^2061 ≤ (33981178060677/100000000000000 : ℝ)^1549 := by
    have hnat : (555392031 : ℕ)^2061*100000000000000^1549 ≤ 33981178060677^1549*1250000000^2061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      555392031 1250000000 33981178060677 100000000000000 2061 1549 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2061/512 : ℝ)) 2061 1549 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2125376803/5000000000 : ℝ), (88862719/200000000 : ℝ), (555392031/1250000000 : ℝ)] ![(1601882344879/5000000000000 : ℝ), (33981175028241/100000000000000 : ℝ), (33981178060677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2125376803/5000000000 : ℝ)|^2061 ≤ (1601882344879/5000000000000 : ℝ)^1549
        have hw : |(2125376803/5000000000 : ℝ)|=(2125376803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(88862719/200000000 : ℝ)|^2061 ≤ (33981175028241/100000000000000 : ℝ)^1549
        have hw : |(88862719/200000000 : ℝ)|=(88862719/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(555392031/1250000000 : ℝ)|^2061 ≤ (33981178060677/100000000000000 : ℝ)^1549
        have hw : |(555392031/1250000000 : ℝ)|=(555392031/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1051_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147701323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13993/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11231/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(3889/6250 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(5923/10000 : ℝ) ∧ (3181/4000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (41459/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13993/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11231/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13993/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11231/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13993/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11231/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13993/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11231/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13993/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11231/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13993/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11231/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11231/100000 : ℝ) ^ (8243/2048 : ℝ) ≤ (15067003953852933/100000000000000000000 : ℝ) := by
    have hpowers : (11231/100000 : ℝ)^8243 ≤ (15067003953852933/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11231 : ℕ)^8243*100000000000000000000^2048 ≤ 15067003953852933^2048*100000^8243 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11231 100000 15067003953852933 100000000000000000000 8243 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11231/100000 : ℝ)) (X := (15067003953852933/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (13993/100000 : ℝ) ^ (8243/2048 : ℝ) ≤ (1825343143638681/5000000000000000000 : ℝ) := by
    have hpowers : (13993/100000 : ℝ)^8243 ≤ (1825343143638681/5000000000000000000 : ℝ)^2048 := by
      have hnat : (13993 : ℕ)^8243*5000000000000000000^2048 ≤ 1825343143638681^2048*100000^8243 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13993 100000 1825343143638681 5000000000000000000 8243 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13993/100000 : ℝ)) (X := (1825343143638681/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50015067003953852933/50000000000000000000 : ℝ) ≤ (10000748604405591/10000000000000000 : ℝ) ^ (8243/2048 : ℝ) := by
    have hpowers : (50015067003953852933/50000000000000000000 : ℝ)^2048 ≤ (10000748604405591/10000000000000000 : ℝ)^8243 := by
      have hnat : (50015067003953852933 : ℕ)^2048*10000000000000000^8243 ≤ 10000748604405591^8243*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015067003953852933 50000000000000000000 10000748604405591 10000000000000000 2048 8243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000748604405591/10000000000000000 : ℝ)) (X := (50015067003953852933/50000000000000000000 : ℝ)) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051573866826626553/100000000000000000000 : ℝ) ≤ (1000128112113963/1000000000000000 : ℝ) ^ (8243/2048 : ℝ) := by
    have hpowers : (100051573866826626553/100000000000000000000 : ℝ)^2048 ≤ (1000128112113963/1000000000000000 : ℝ)^8243 := by
      have hnat : (100051573866826626553 : ℕ)^2048*1000000000000000^8243 ≤ 1000128112113963^8243*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051573866826626553 100000000000000000000 1000128112113963 1000000000000000 2048 8243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000128112113963/1000000000000000 : ℝ)) (X := (100051573866826626553/100000000000000000000 : ℝ)) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501825343143638681/2500000000000000000 : ℝ) ≤ (10001813637873669/10000000000000000 : ℝ) ^ (8243/2048 : ℝ) := by
    have hpowers : (2501825343143638681/2500000000000000000 : ℝ)^2048 ≤ (10001813637873669/10000000000000000 : ℝ)^8243 := by
      have hnat : (2501825343143638681 : ℕ)^2048*10000000000000000^8243 ≤ 10001813637873669^8243*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501825343143638681 2500000000000000000 10001813637873669 10000000000000000 2048 8243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001813637873669/10000000000000000 : ℝ)) (X := (2501825343143638681/2500000000000000000 : ℝ)) (by norm_num) 8243 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15067003953852933/100000000000000000000 : ℝ) ≤ ((6902526563622064581/6905000000000000000 : ℝ)+2*(532516734039/276200000000000 : ℝ)*(11231/100000 : ℝ))^(8243/2048 : ℝ) := by
    rw [show (6902526563622064581/6905000000000000000 : ℝ)+2*(532516734039/276200000000000 : ℝ)*(11231/100000 : ℝ)=(10000748604405591/10000000000000000 : ℝ) by norm_num, show 1+2*(15067003953852933/100000000000000000000 : ℝ)=(50015067003953852933/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1825343143638681/5000000000000000000 : ℝ)+(15067003953852933/100000000000000000000 : ℝ) ≤ ((6902526563622064581/6905000000000000000 : ℝ)+(532516734039/276200000000000 : ℝ)*((13993/100000 : ℝ)+(11231/100000 : ℝ)))^(8243/2048 : ℝ) := by
    rw [show (6902526563622064581/6905000000000000000 : ℝ)+(532516734039/276200000000000 : ℝ)*((13993/100000 : ℝ)+(11231/100000 : ℝ))=(1000128112113963/1000000000000000 : ℝ) by norm_num, show 1+(1825343143638681/5000000000000000000 : ℝ)+(15067003953852933/100000000000000000000 : ℝ)=(100051573866826626553/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1825343143638681/5000000000000000000 : ℝ) ≤ ((6902526563622064581/6905000000000000000 : ℝ)+2*(532516734039/276200000000000 : ℝ)*(13993/100000 : ℝ))^(8243/2048 : ℝ) := by
    rw [show (6902526563622064581/6905000000000000000 : ℝ)+2*(532516734039/276200000000000 : ℝ)*(13993/100000 : ℝ)=(10001813637873669/10000000000000000 : ℝ) by norm_num, show 1+2*(1825343143638681/5000000000000000000 : ℝ)=(2501825343143638681/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6902526563622064581/6905000000000000000 : ℝ)*(X 1 0+X 2 0)+(532516734039/276200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8243/2048 : ℝ)) (lo := (11231/100000 : ℝ)) (hi := (13993/100000 : ℝ)) (c := (6902526563622064581/6905000000000000000 : ℝ)) (alpha := (532516734039/276200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6902526563622064581/6905000000000000000 : ℝ)*(X 0 1+X 2 1)+(532516734039/276200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8243/2048 : ℝ)) (lo := (11231/100000 : ℝ)) (hi := (13993/100000 : ℝ)) (c := (6902526563622064581/6905000000000000000 : ℝ)) (alpha := (532516734039/276200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6902526563622064581/6905000000000000000 : ℝ)*(X 0 2+X 1 2)+(532516734039/276200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8243/2048 : ℝ)) (lo := (11231/100000 : ℝ)) (hi := (13993/100000 : ℝ)) (c := (6902526563622064581/6905000000000000000 : ℝ)) (alpha := (532516734039/276200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-65037303/312500000 : ℝ)*X 0 0+(5377570129/10000000000 : ℝ)*X 0 1+(1344392537/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1059006159/2000000000 : ℝ)*X 1 0+(-2192889477/10000000000 : ℝ)*X 1 1+(1075513959/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5295030583/10000000000 : ℝ)*X 2 0+(5377570013/10000000000 : ℝ)*X 2 1+(-548222367/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2243108167/5000000000 : ℝ)*X 0 0+(540693503/1250000000 : ℝ)*X 0 1+(865109603/2000000000 : ℝ)*X 0 2+(2243108167/5000000000 : ℝ)*X 1 0+(540693503/1250000000 : ℝ)*X 1 1+(865109603/2000000000 : ℝ)*X 1 2+(2243108167/5000000000 : ℝ)*X 2 0+(540693503/1250000000 : ℝ)*X 2 1+(865109603/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2342549021/10000000000 : ℝ)*X 0 0+(1055972573/2000000000 : ℝ)*X 0 1+(164995707/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5364203729/10000000000 : ℝ)*X 1 0+(-557760463/2500000000 : ℝ)*X 1 1+(5279862443/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((268210139/500000000 : ℝ)*X 2 0+(527986331/1000000000 : ℝ)*X 2 1+(-2231041967/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4268770691/10000000000 : ℝ)*X 0 0+(2217124769/5000000000 : ℝ)*X 0 1+(4434248959/10000000000 : ℝ)*X 0 2+(4268770691/10000000000 : ℝ)*X 1 0+(2217124769/5000000000 : ℝ)*X 1 1+(4434248959/10000000000 : ℝ)*X 1 2+(4268770691/10000000000 : ℝ)*X 2 0+(2217124769/5000000000 : ℝ)*X 2 1+(4434248959/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1144004021/5000000000 : ℝ)*X 0 0+(5213591983/10000000000 : ℝ)*X 0 1+(673396101/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2644115577/5000000000 : ℝ)*X 1 0+(-437814109/2000000000 : ℝ)*X 1 1+(5387168741/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((82628613/156250000 : ℝ)*X 2 0+(5387168761/10000000000 : ℝ)*X 2 1+(-1094535207/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((90146091/200000000 : ℝ)*X 0 0+(4314863333/10000000000 : ℝ)*X 0 1+(1078715861/2500000000 : ℝ)*X 0 2+(90146091/200000000 : ℝ)*X 1 0+(4314863333/10000000000 : ℝ)*X 1 1+(1078715861/2500000000 : ℝ)*X 1 2+(90146091/200000000 : ℝ)*X 2 0+(4314863333/10000000000 : ℝ)*X 2 1+(1078715861/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2136113623/10000000000 : ℝ)*X 0 0+(1360623321/2500000000 : ℝ)*X 0 1+(5271869889/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((83904063/156250000 : ℝ)*X 1 0+(-223410369/1000000000 : ℝ)*X 1 1+(5271869761/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5369860021/10000000000 : ℝ)*X 2 0+(2635934851/5000000000 : ℝ)*X 2 1+(-2234103783/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2125376803/5000000000 : ℝ)*X 0 0+(88862719/200000000 : ℝ)*X 0 1+(555392031/1250000000 : ℝ)*X 0 2+(2125376803/5000000000 : ℝ)*X 1 0+(88862719/200000000 : ℝ)*X 1 1+(555392031/1250000000 : ℝ)*X 1 2+(2125376803/5000000000 : ℝ)*X 2 0+(88862719/200000000 : ℝ)*X 2 1+(555392031/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1051_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-3889/6250 : ℝ) ≤ (-214819230335444097279439089549549/345250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (120894693/100000000000000 : ℝ)*(upper0) + (132678687/50000000000000 : ℝ)*(upper1) + (208765031/100000000000000 : ℝ)*(upper2) + (42901437/20000000000000 : ℝ)*(upper3) + (3843859123559757/100000000000000 : ℝ)*(major0) + (3843859123559757/100000000000000 : ℝ)*(major1) + (3843859123559757/100000000000000 : ℝ)*(major2) + (4254387627/100000000000000 : ℝ)*(sp1) + (9972070089/50000000000000 : ℝ)*(sp3) + (5106004607534521/100000000000000 : ℝ)*(sp4) + (2553000176573447/50000000000000 : ℝ)*(sp5) + (5105569119708877/100000000000000 : ℝ)*(sp6) + (1301217073661843/50000000000000 : ℝ)*(sp7) + (108871956411/25000000000000 : ℝ)*(sp14) + (325306761432983/12500000000000 : ℝ)*(f.failure) + (5106004607534521/100000000000000 : ℝ)*(f.sum) + (53948773947447/13810000000000000000000000000 : ℝ)*base66 + (905496642727241817/690500000000000000000000000000000 : ℝ)*base67 + (466818786735741817/690500000000000000000000000000000 : ℝ)*base69 + (4260180579264758183/690500000000000000000000000000000 : ℝ)*base72 + (19974185804607/13810000000000000000000000000 : ℝ)*base74 + (3297777134035758183/690500000000000000000000000000000 : ℝ)*base76 + (266822558131258183/690500000000000000000000000000000 : ℝ)*base78 + (8335035568589258183/690500000000000000000000000000000 : ℝ)*base80 + (51379589280793/13810000000000000000000000000 : ℝ)*base81 + (2436509/1250000000000000000000 : ℝ)*base89 + (2436509/1250000000000000000000 : ℝ)*base91 + (2436509/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (5923/10000 : ℝ) ≤ (12781177907135411397779503054641/21578125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9773867/50000000000000 : ℝ)*(lower1) + (21096441/100000000000000 : ℝ)*(lower4) + (33372893/50000000000000 : ℝ)*(lower5) + (122078261174053/3125000000000 : ℝ)*(major0) + (122078261174053/3125000000000 : ℝ)*(major1) + (122078261174053/3125000000000 : ℝ)*(major2) + (514839220951657/10000000000000 : ℝ)*(sp0) + (2574120828662229/50000000000000 : ℝ)*(sp1) + (102967422954533/2000000000000 : ℝ)*(sp2) + (1322433420758991/50000000000000 : ℝ)*(sp3) + (704840893/100000000000000 : ℝ)*(sp7) + (155476069697/100000000000000 : ℝ)*(sp9) + (5197133501/20000000000000 : ℝ)*(sp10) + (984775517/20000000000000 : ℝ)*(sp12) + (1322433773179437/50000000000000 : ℝ)*(f.failure) + (1029679426678831/20000000000000 : ℝ)*(f.sum) + (7907745228177/1726250000000000000000000000 : ℝ)*base66 + (94517198041933207/21578125000000000000000000000000 : ℝ)*base68 + (36922482346151957/21578125000000000000000000000000 : ℝ)*base70 + (2693597001791209/10789062500000000000000000000000 : ℝ)*base71 + (35408146402817/6905000000000000000000000000 : ℝ)*base73 + (150086739857433207/21578125000000000000000000000000 : ℝ)*base76 + (6287696742159083/5394531250000000000000000000000 : ℝ)*base78 + (4378758938543677/1348632812500000000000000000000 : ℝ)*base80 + (62308273037463/6905000000000000000000000000 : ℝ)*base82 + (38704849/5000000000000000000000 : ℝ)*base90 + (38704849/5000000000000000000000 : ℝ)*base92 + (38704849/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (3181/4000 : ℝ) ≤ (137284108955600059258389650139453/172625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17955533/50000000000000 : ℝ)*(upper0) + (60242073/100000000000000 : ℝ)*(lower3) + (33323143/50000000000000 : ℝ)*(upper4) + (2187390012905971/50000000000000 : ℝ)*(major0) + (2187390012905971/50000000000000 : ℝ)*(major1) + (2187390012905971/50000000000000 : ℝ)*(major2) + (31798466989/100000000000000 : ℝ)*(sp1) + (1593210941/2500000000000 : ℝ)*(sp2) + (32722934387/100000000000000 : ℝ)*(sp3) + (827608349/100000000000000 : ℝ)*(sp4) + (1152228051836847/20000000000000 : ℝ)*(sp8) + (1152221857665119/20000000000000 : ℝ)*(sp9) + (1152215471670989/20000000000000 : ℝ)*(sp10) + (296187712117171/10000000000000 : ℝ)*(sp11) + (185119365256631/6250000000000 : ℝ)*(f.failure) + (720142635849073/12500000000000 : ℝ)*(f.sum) + (14369520664013/3452500000000000000000000000 : ℝ)*base66 + (1968098247797761849/345250000000000000000000000000000 : ℝ)*base68 + (481349657093988151/345250000000000000000000000000000 : ℝ)*base69 + (2608161377881511849/345250000000000000000000000000000 : ℝ)*base72 + (14434457797581/6905000000000000000000000000 : ℝ)*base74 + (710603006709511849/345250000000000000000000000000000 : ℝ)*base76 + (4810329345125261849/345250000000000000000000000000000 : ℝ)*base78 + (830734895183488151/345250000000000000000000000000000 : ℝ)*base79 + (11506190934947/3452500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (4277187/625000000000000000000 : ℝ)*base90 + (4277187/625000000000000000000 : ℝ)*base92 + (4277187/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-41459/50000 : ℝ) ≤ (-5725326335587577100731235231/6905000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6493157/50000000000000 : ℝ)*(lower1) + (20753261/50000000000000 : ℝ)*(lower3) + (21485727/25000000000000 : ℝ)*(lower4) + (22979441/100000000000000 : ℝ)*(upper5) + (2204614206364037/50000000000000 : ℝ)*(major0) + (2204614206364037/50000000000000 : ℝ)*(major1) + (2204614206364037/50000000000000 : ℝ)*(major2) + (14544189421/25000000000000 : ℝ)*(sp5) + (39737566639/20000000000000 : ℝ)*(sp6) + (38964242357/100000000000000 : ℝ)*(sp7) + (5860862529765961/100000000000000 : ℝ)*(sp12) + (5860804353008277/100000000000000 : ℝ)*(sp13) + (5860663841932767/100000000000000 : ℝ)*(sp14) + (1492596942420961/50000000000000 : ℝ)*(sp15) + (2985232849084279/100000000000000 : ℝ)*(f.failure) + (5860862529765961/100000000000000 : ℝ)*(f.sum) + (18775801598537/6905000000000000000000000000 : ℝ)*base66 + (715357039323448497/345250000000000000000000000000000 : ℝ)*base67 + (627876221301051503/345250000000000000000000000000000 : ℝ)*base70 + (3359338495561198497/345250000000000000000000000000000 : ℝ)*base71 + (9743910565903/6905000000000000000000000000 : ℝ)*base73 + (679396318271051503/345250000000000000000000000000000 : ℝ)*base76 + (234300293780551503/345250000000000000000000000000000 : ℝ)*base78 + (1297243129383448497/345250000000000000000000000000000 : ℝ)*base79 + (26795579035361/3452500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (53198883/10000000000000000000000 : ℝ)*base90 + (53198883/10000000000000000000000 : ℝ)*base92 + (53198883/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1051_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147701323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13993/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11231/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(5923/10000 : ℝ) else (3181/4000 : ℝ) ≤ X j i ∧ X j i ≤ (41459/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1051_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1051_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147701323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6997/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11231/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(5923/10000 : ℝ) else (3181/4000 : ℝ) ≤ X j i ∧ X j i ≤ (41459/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1051_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1051_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8243/2048 : ℝ) ≤ p) (hpb : p ≤ (2061/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147701323/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6997/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11231/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(5923/10000 : ℝ) else (3181/4000 : ℝ) ≤ X j i ∧ X j i ≤ (41459/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1051_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
