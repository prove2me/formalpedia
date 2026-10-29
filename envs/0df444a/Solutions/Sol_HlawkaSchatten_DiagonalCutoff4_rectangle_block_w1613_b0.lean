-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1613_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:51:49.484245+00:00
-- url     : https://prove2.me/submissions/45908dfd-4a64-4550-b12f-f9d5b3e71eef

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
theorem support_rectangle_w1613_s0_0 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-155986333/1000000000 : ℝ)*x 0 + (1166614647/2000000000 : ℝ)*x 1 + (4895249649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (155986333/1000000000 : ℝ)^4771 ≤ (9387911094057/100000000000000 : ℝ)^3747 := by
    have hnat : (155986333 : ℕ)^4771*100000000000000^3747 ≤ 9387911094057^3747*1000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      155986333 1000000000 9387911094057 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1166614647/2000000000 : ℝ)^4771 ≤ (25170430486689/50000000000000 : ℝ)^3747 := by
    have hnat : (1166614647 : ℕ)^4771*50000000000000^3747 ≤ 25170430486689^3747*2000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1166614647 2000000000 25170430486689 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4895249649/10000000000 : ℝ)^4771 ≤ (8054245583501/20000000000000 : ℝ)^3747 := by
    have hnat : (4895249649 : ℕ)^4771*20000000000000^3747 ≤ 8054245583501^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4895249649 10000000000 8054245583501 20000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-155986333/1000000000 : ℝ), (1166614647/2000000000 : ℝ), (4895249649/10000000000 : ℝ)] ![(9387911094057/100000000000000 : ℝ), (25170430486689/50000000000000 : ℝ), (8054245583501/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-155986333/1000000000 : ℝ)|^4771 ≤ (9387911094057/100000000000000 : ℝ)^3747
        have hw : |(-155986333/1000000000 : ℝ)|=(155986333/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1166614647/2000000000 : ℝ)|^4771 ≤ (25170430486689/50000000000000 : ℝ)^3747
        have hw : |(1166614647/2000000000 : ℝ)|=(1166614647/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4895249649/10000000000 : ℝ)|^4771 ≤ (8054245583501/20000000000000 : ℝ)^3747
        have hw : |(4895249649/10000000000 : ℝ)|=(4895249649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_s0_1 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (340780177/625000000 : ℝ)*x 0 + (-16630057/80000000 : ℝ)*x 1 + (4895249777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (340780177/625000000 : ℝ)^4771 ≤ (9239307042911/20000000000000 : ℝ)^3747 := by
    have hnat : (340780177 : ℕ)^4771*20000000000000^3747 ≤ 9239307042911^3747*625000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340780177 625000000 9239307042911 20000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16630057/80000000 : ℝ)^4771 ≤ (6766117757459/50000000000000 : ℝ)^3747 := by
    have hnat : (16630057 : ℕ)^4771*50000000000000^3747 ≤ 6766117757459^3747*80000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16630057 80000000 6766117757459 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4895249777/10000000000 : ℝ)^4771 ≤ (1006780731457/2500000000000 : ℝ)^3747 := by
    have hnat : (4895249777 : ℕ)^4771*2500000000000^3747 ≤ 1006780731457^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4895249777 10000000000 1006780731457 2500000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(340780177/625000000 : ℝ), (-16630057/80000000 : ℝ), (4895249777/10000000000 : ℝ)] ![(9239307042911/20000000000000 : ℝ), (6766117757459/50000000000000 : ℝ), (1006780731457/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(340780177/625000000 : ℝ)|^4771 ≤ (9239307042911/20000000000000 : ℝ)^3747
        have hw : |(340780177/625000000 : ℝ)|=(340780177/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-16630057/80000000 : ℝ)|^4771 ≤ (6766117757459/50000000000000 : ℝ)^3747
        have hw : |(-16630057/80000000 : ℝ)|=(16630057/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4895249777/10000000000 : ℝ)|^4771 ≤ (1006780731457/2500000000000 : ℝ)^3747
        have hw : |(4895249777/10000000000 : ℝ)|=(4895249777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_s0_2 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (545248303/1000000000 : ℝ)*x 0 + (4895249599/10000000000 : ℝ)*x 1 + (-519689273/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545248303/1000000000 : ℝ)^4771 ≤ (23098268675289/50000000000000 : ℝ)^3747 := by
    have hnat : (545248303 : ℕ)^4771*50000000000000^3747 ≤ 23098268675289^3747*1000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545248303 1000000000 23098268675289 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4895249599/10000000000 : ℝ)^4771 ≤ (8054245478753/20000000000000 : ℝ)^3747 := by
    have hnat : (4895249599 : ℕ)^4771*20000000000000^3747 ≤ 8054245478753^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4895249599 10000000000 8054245478753 20000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (519689273/2500000000 : ℝ)^4771 ≤ (3383058810347/25000000000000 : ℝ)^3747 := by
    have hnat : (519689273 : ℕ)^4771*25000000000000^3747 ≤ 3383058810347^3747*2500000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519689273 2500000000 3383058810347 25000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(545248303/1000000000 : ℝ), (4895249599/10000000000 : ℝ), (-519689273/2500000000 : ℝ)] ![(23098268675289/50000000000000 : ℝ), (8054245478753/20000000000000 : ℝ), (3383058810347/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(545248303/1000000000 : ℝ)|^4771 ≤ (23098268675289/50000000000000 : ℝ)^3747
        have hw : |(545248303/1000000000 : ℝ)|=(545248303/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4895249599/10000000000 : ℝ)|^4771 ≤ (8054245478753/20000000000000 : ℝ)^3747
        have hw : |(4895249599/10000000000 : ℝ)|=(4895249599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-519689273/2500000000 : ℝ)|^4771 ≤ (3383058810347/25000000000000 : ℝ)^3747
        have hw : |(-519689273/2500000000 : ℝ)|=(519689273/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_s0_3 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (513538919/1250000000 : ℝ)*x 0 + (614958087/2000000000 : ℝ)*x 1 + (5388448067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (513538919/1250000000 : ℝ)^4771 ≤ (1288674442323/4000000000000 : ℝ)^3747 := by
    have hnat : (513538919 : ℕ)^4771*4000000000000^3747 ≤ 1288674442323^3747*1250000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513538919 1250000000 1288674442323 4000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (614958087/2000000000 : ℝ)^4771 ≤ (11138149413387/50000000000000 : ℝ)^3747 := by
    have hnat : (614958087 : ℕ)^4771*50000000000000^3747 ≤ 11138149413387^3747*2000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      614958087 2000000000 11138149413387 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5388448067/10000000000 : ℝ)^4771 ≤ (45506840098787/100000000000000 : ℝ)^3747 := by
    have hnat : (5388448067 : ℕ)^4771*100000000000000^3747 ≤ 45506840098787^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388448067 10000000000 45506840098787 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(513538919/1250000000 : ℝ), (614958087/2000000000 : ℝ), (5388448067/10000000000 : ℝ)] ![(1288674442323/4000000000000 : ℝ), (11138149413387/50000000000000 : ℝ), (45506840098787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(513538919/1250000000 : ℝ)|^4771 ≤ (1288674442323/4000000000000 : ℝ)^3747
        have hw : |(513538919/1250000000 : ℝ)|=(513538919/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(614958087/2000000000 : ℝ)|^4771 ≤ (11138149413387/50000000000000 : ℝ)^3747
        have hw : |(614958087/2000000000 : ℝ)|=(614958087/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5388448067/10000000000 : ℝ)|^4771 ≤ (45506840098787/100000000000000 : ℝ)^3747
        have hw : |(5388448067/10000000000 : ℝ)|=(5388448067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_s0_4 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-62504671/400000000 : ℝ)*x 0 + (4918954117/10000000000 : ℝ)*x 1 + (1161705559/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (62504671/400000000 : ℝ)^4771 ≤ (4704508141463/50000000000000 : ℝ)^3747 := by
    have hnat : (62504671 : ℕ)^4771*50000000000000^3747 ≤ 4704508141463^3747*400000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62504671 400000000 4704508141463 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4918954117/10000000000 : ℝ)^4771 ≤ (405196915853/1000000000000 : ℝ)^3747 := by
    have hnat : (4918954117 : ℕ)^4771*1000000000000^3747 ≤ 405196915853^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4918954117 10000000000 405196915853 1000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1161705559/2000000000 : ℝ)^4771 ≤ (25035646059369/50000000000000 : ℝ)^3747 := by
    have hnat : (1161705559 : ℕ)^4771*50000000000000^3747 ≤ 25035646059369^3747*2000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1161705559 2000000000 25035646059369 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-62504671/400000000 : ℝ), (4918954117/10000000000 : ℝ), (1161705559/2000000000 : ℝ)] ![(4704508141463/50000000000000 : ℝ), (405196915853/1000000000000 : ℝ), (25035646059369/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-62504671/400000000 : ℝ)|^4771 ≤ (4704508141463/50000000000000 : ℝ)^3747
        have hw : |(-62504671/400000000 : ℝ)|=(62504671/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4918954117/10000000000 : ℝ)|^4771 ≤ (405196915853/1000000000000 : ℝ)^3747
        have hw : |(4918954117/10000000000 : ℝ)|=(4918954117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1161705559/2000000000 : ℝ)|^4771 ≤ (25035646059369/50000000000000 : ℝ)^3747
        have hw : |(1161705559/2000000000 : ℝ)|=(1161705559/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_s0_5 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5196358441/10000000000 : ℝ)*x 0 + (-1165479267/10000000000 : ℝ)*x 1 + (580852791/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5196358441/10000000000 : ℝ)^4771 ≤ (21725703587793/50000000000000 : ℝ)^3747 := by
    have hnat : (5196358441 : ℕ)^4771*50000000000000^3747 ≤ 21725703587793^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196358441 10000000000 21725703587793 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1165479267/10000000000 : ℝ)^4771 ≤ (809662427797/12500000000000 : ℝ)^3747 := by
    have hnat : (1165479267 : ℕ)^4771*12500000000000^3747 ≤ 809662427797^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1165479267 10000000000 809662427797 12500000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (580852791/1000000000 : ℝ)^4771 ≤ (50071293380991/100000000000000 : ℝ)^3747 := by
    have hnat : (580852791 : ℕ)^4771*100000000000000^3747 ≤ 50071293380991^3747*1000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      580852791 1000000000 50071293380991 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5196358441/10000000000 : ℝ), (-1165479267/10000000000 : ℝ), (580852791/1000000000 : ℝ)] ![(21725703587793/50000000000000 : ℝ), (809662427797/12500000000000 : ℝ), (50071293380991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5196358441/10000000000 : ℝ)|^4771 ≤ (21725703587793/50000000000000 : ℝ)^3747
        have hw : |(5196358441/10000000000 : ℝ)|=(5196358441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1165479267/10000000000 : ℝ)|^4771 ≤ (809662427797/12500000000000 : ℝ)^3747
        have hw : |(-1165479267/10000000000 : ℝ)|=(1165479267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(580852791/1000000000 : ℝ)|^4771 ≤ (50071293380991/100000000000000 : ℝ)^3747
        have hw : |(580852791/1000000000 : ℝ)|=(580852791/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_s0_6 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5196358501/10000000000 : ℝ)*x 0 + (363033017/625000000 : ℝ)*x 1 + (-145684827/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5196358501/10000000000 : ℝ)^4771 ≤ (43451407814411/100000000000000 : ℝ)^3747 := by
    have hnat : (5196358501 : ℕ)^4771*100000000000000^3747 ≤ 43451407814411^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196358501 10000000000 43451407814411 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (363033017/625000000 : ℝ)^4771 ≤ (50071297354343/100000000000000 : ℝ)^3747 := by
    have hnat : (363033017 : ℕ)^4771*100000000000000^3747 ≤ 50071297354343^3747*625000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      363033017 625000000 50071297354343 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (145684827/1250000000 : ℝ)^4771 ≤ (6477294815611/100000000000000 : ℝ)^3747 := by
    have hnat : (145684827 : ℕ)^4771*100000000000000^3747 ≤ 6477294815611^3747*1250000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      145684827 1250000000 6477294815611 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5196358501/10000000000 : ℝ), (363033017/625000000 : ℝ), (-145684827/1250000000 : ℝ)] ![(43451407814411/100000000000000 : ℝ), (50071297354343/100000000000000 : ℝ), (6477294815611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5196358501/10000000000 : ℝ)|^4771 ≤ (43451407814411/100000000000000 : ℝ)^3747
        have hw : |(5196358501/10000000000 : ℝ)|=(5196358501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(363033017/625000000 : ℝ)|^4771 ≤ (50071297354343/100000000000000 : ℝ)^3747
        have hw : |(363033017/625000000 : ℝ)|=(363033017/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-145684827/1250000000 : ℝ)|^4771 ≤ (6477294815611/100000000000000 : ℝ)^3747
        have hw : |(-145684827/1250000000 : ℝ)|=(145684827/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_s0_7 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2057550931/5000000000 : ℝ)*x 0 + (1065993711/2000000000 : ℝ)*x 1 + (313534447/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2057550931/5000000000 : ℝ)^4771 ≤ (645693584439/2000000000000 : ℝ)^3747 := by
    have hnat : (2057550931 : ℕ)^4771*2000000000000^3747 ≤ 645693584439^3747*5000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2057550931 5000000000 645693584439 2000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1065993711/2000000000 : ℝ)^4771 ≤ (44878931799309/100000000000000 : ℝ)^3747 := by
    have hnat : (1065993711 : ℕ)^4771*100000000000000^3747 ≤ 44878931799309^3747*2000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065993711 2000000000 44878931799309 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (313534447/1000000000 : ℝ)^4771 ≤ (5709097242013/25000000000000 : ℝ)^3747 := by
    have hnat : (313534447 : ℕ)^4771*25000000000000^3747 ≤ 5709097242013^3747*1000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      313534447 1000000000 5709097242013 25000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2057550931/5000000000 : ℝ), (1065993711/2000000000 : ℝ), (313534447/1000000000 : ℝ)] ![(645693584439/2000000000000 : ℝ), (44878931799309/100000000000000 : ℝ), (5709097242013/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2057550931/5000000000 : ℝ)|^4771 ≤ (645693584439/2000000000000 : ℝ)^3747
        have hw : |(2057550931/5000000000 : ℝ)|=(2057550931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1065993711/2000000000 : ℝ)|^4771 ≤ (44878931799309/100000000000000 : ℝ)^3747
        have hw : |(1065993711/2000000000 : ℝ)|=(1065993711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(313534447/1000000000 : ℝ)|^4771 ≤ (5709097242013/25000000000000 : ℝ)^3747
        have hw : |(313534447/1000000000 : ℝ)|=(313534447/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1613_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3467051/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (4087/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (24173/100000 : ℝ)*pair X 0 0 := by
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
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4767/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4767 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4767*1^1024 ≤ 0^1024*1^4767 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4767 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4767 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4767/1024 : ℝ) ≤ (280873291417137421/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4767 ≤ (280873291417137421/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4767*20000000000000000000^1024 ≤ 280873291417137421^1024*5^4767 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 280873291417137421 20000000000000000000 4767 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (280873291417137421/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4767 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4767/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4767 := by
      have hnat : (1 : ℕ)^1024*1^4767 ≤ 1^4767*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4767 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4767 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20280873291417137421/20000000000000000000 : ℝ) ≤ (10030002267796291/10000000000000000 : ℝ) ^ (4767/1024 : ℝ) := by
    have hpowers : (20280873291417137421/20000000000000000000 : ℝ)^1024 ≤ (10030002267796291/10000000000000000 : ℝ)^4767 := by
      have hnat : (20280873291417137421 : ℕ)^1024*10000000000000000^4767 ≤ 10030002267796291^4767*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20280873291417137421 20000000000000000000 10030002267796291 10000000000000000 1024 4767 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10030002267796291/10000000000000000 : ℝ)) (X := (20280873291417137421/20000000000000000000 : ℝ)) (by norm_num) 4767 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10280873291417137421/10000000000000000000 : ℝ) ≤ (5030002267796291/5000000000000000 : ℝ) ^ (4767/1024 : ℝ) := by
    have hpowers : (10280873291417137421/10000000000000000000 : ℝ)^1024 ≤ (5030002267796291/5000000000000000 : ℝ)^4767 := by
      have hnat : (10280873291417137421 : ℕ)^1024*5000000000000000^4767 ≤ 5030002267796291^4767*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10280873291417137421 10000000000000000000 5030002267796291 5000000000000000 1024 4767 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5030002267796291/5000000000000000 : ℝ)) (X := (10280873291417137421/10000000000000000000 : ℝ)) (by norm_num) 4767 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(30002267796291/4000000000000000 : ℝ)*(0 : ℝ))^(4767/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(30002267796291/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(280873291417137421/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(30002267796291/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4767/1024 : ℝ) := by
    rw [show (1 : ℝ)+(30002267796291/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10030002267796291/10000000000000000 : ℝ) by norm_num, show 1+(280873291417137421/20000000000000000000 : ℝ)+(0 : ℝ)=(20280873291417137421/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(280873291417137421/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(30002267796291/4000000000000000 : ℝ)*(2/5 : ℝ))^(4767/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(30002267796291/4000000000000000 : ℝ)*(2/5 : ℝ)=(5030002267796291/5000000000000000 : ℝ) by norm_num, show 1+2*(280873291417137421/20000000000000000000 : ℝ)=(10280873291417137421/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(30002267796291/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4767/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30002267796291/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(30002267796291/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4767/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30002267796291/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(30002267796291/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4767/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30002267796291/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-155986333/1000000000 : ℝ)*X 0 0+(1166614647/2000000000 : ℝ)*X 0 1+(4895249649/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((340780177/625000000 : ℝ)*X 1 0+(-16630057/80000000 : ℝ)*X 1 1+(4895249777/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((545248303/1000000000 : ℝ)*X 2 0+(4895249599/10000000000 : ℝ)*X 2 1+(-519689273/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((513538919/1250000000 : ℝ)*X 0 0+(614958087/2000000000 : ℝ)*X 0 1+(5388448067/10000000000 : ℝ)*X 0 2+(513538919/1250000000 : ℝ)*X 1 0+(614958087/2000000000 : ℝ)*X 1 1+(5388448067/10000000000 : ℝ)*X 1 2+(513538919/1250000000 : ℝ)*X 2 0+(614958087/2000000000 : ℝ)*X 2 1+(5388448067/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-62504671/400000000 : ℝ)*X 0 0+(4918954117/10000000000 : ℝ)*X 0 1+(1161705559/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5196358441/10000000000 : ℝ)*X 1 0+(-1165479267/10000000000 : ℝ)*X 1 1+(580852791/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5196358501/10000000000 : ℝ)*X 2 0+(363033017/625000000 : ℝ)*X 2 1+(-145684827/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2057550931/5000000000 : ℝ)*X 0 0+(1065993711/2000000000 : ℝ)*X 0 1+(313534447/1000000000 : ℝ)*X 0 2+(2057550931/5000000000 : ℝ)*X 1 0+(1065993711/2000000000 : ℝ)*X 1 1+(313534447/1000000000 : ℝ)*X 1 2+(2057550931/5000000000 : ℝ)*X 2 0+(1065993711/2000000000 : ℝ)*X 2 1+(313534447/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1701408508219647049264917/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (114606411/100000000000000 : ℝ)*(base1) + (899628181/50000000000000 : ℝ)*(base19) + (367595613/20000000000000 : ℝ)*(base23) + (115855221/50000000000000 : ℝ)*(upper3) + (50460177/20000000000000 : ℝ)*(upper5) + (749266883418771/100000000000000 : ℝ)*(major0) + (749266883418771/100000000000000 : ℝ)*(major1) + (749266883418771/100000000000000 : ℝ)*(major2) + (42652204221041/4000000000000 : ℝ)*(sp0) + (1066310246590467/100000000000000 : ℝ)*(sp1) + (266577551967191/25000000000000 : ℝ)*(sp2) + (216109322536177/50000000000000 : ℝ)*(sp3) + (1410985443/20000000000000 : ℝ)*(sp4) + (2677743859/100000000000000 : ℝ)*(sp7) + (432221437422623/100000000000000 : ℝ)*(f.failure) + (1066312045846829/100000000000000 : ℝ)*(f.sum) + (5448364621639/200000000000000000000000000000 : ℝ)*base66 + (2652409167578361/400000000000000000000000000000 : ℝ)*base67 + (583623965621639/400000000000000000000000000000 : ℝ)*base70 + (2803462029578361/400000000000000000000000000000 : ℝ)*base71 + (207586201578361/200000000000000000000000000000 : ℝ)*base73 + (727968150778361/400000000000000000000000000000 : ℝ)*base75 + (2673577079178361/400000000000000000000000000000 : ℝ)*base77 + (3759372925178361/400000000000000000000000000000 : ℝ)*base79 + (1285436758421639/200000000000000000000000000000 : ℝ)*base82 + (494773/200000000000000000000 : ℝ)*base89 + (494773/200000000000000000000 : ℝ)*base91 + (494773/200000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (768239362966101883791861/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (571258469/100000000000000 : ℝ)*(base19) + (487466123/50000000000000 : ℝ)*(base23) + (405595609/100000000000000 : ℝ)*(base39) + (1761099/5000000000000 : ℝ)*(upper3) + (274104823/100000000000000 : ℝ)*(upper5) + (394947561484963/50000000000000 : ℝ)*(major0) + (394947561484963/50000000000000 : ℝ)*(major1) + (789894717374317/100000000000000 : ℝ)*(major2) + (2377664781/100000000000000 : ℝ)*(sp1) + (137131909/6250000000000 : ℝ)*(sp2) + (562065752118247/50000000000000 : ℝ)*(sp4) + (281032138828311/25000000000000 : ℝ)*(sp5) + (1124128740789313/100000000000000 : ℝ)*(sp6) + (455658208067851/100000000000000 : ℝ)*(sp7) + (455658208067851/100000000000000 : ℝ)*(f.failure) + (1124131909832103/100000000000000 : ℝ)*(f.sum) + (589815753802713/400000000000000000000000000000 : ℝ)*base65 + (556220910058247/400000000000000000000000000000 : ℝ)*base67 + (31096603672233/200000000000000000000000000000 : ℝ)*base69 + (1218180968058247/400000000000000000000000000000 : ℝ)*base71 + (297282974197287/400000000000000000000000000000 : ℝ)*base74 + (54037974272233/200000000000000000000000000000 : ℝ)*base75 + (718292204672233/200000000000000000000000000000 : ℝ)*base77 + (371082684272233/200000000000000000000000000000 : ℝ)*base79 + (113188967727767/100000000000000000000000000000 : ℝ)*base82 + (1122599/200000000000000000000 : ℝ)*base90 + (1122599/200000000000000000000 : ℝ)*base92 + (1122599/200000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1613_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3467051/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4087/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (24173/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1613_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1613_s1_0 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1681887267/10000000000 : ℝ)*x 0 + (172722149/312500000 : ℝ)*x 1 + (5122266533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1681887267/10000000000 : ℝ)^4771 ≤ (10332812660279/100000000000000 : ℝ)^3747 := by
    have hnat : (1681887267 : ℕ)^4771*100000000000000^3747 ≤ 10332812660279^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1681887267 10000000000 10332812660279 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (172722149/312500000 : ℝ)^4771 ≤ (11750775060653/25000000000000 : ℝ)^3747 := by
    have hnat : (172722149 : ℕ)^4771*25000000000000^3747 ≤ 11750775060653^3747*312500000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172722149 312500000 11750775060653 25000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5122266533/10000000000 : ℝ)^4771 ≤ (21332043541057/50000000000000 : ℝ)^3747 := by
    have hnat : (5122266533 : ℕ)^4771*50000000000000^3747 ≤ 21332043541057^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5122266533 10000000000 21332043541057 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1681887267/10000000000 : ℝ), (172722149/312500000 : ℝ), (5122266533/10000000000 : ℝ)] ![(10332812660279/100000000000000 : ℝ), (11750775060653/25000000000000 : ℝ), (21332043541057/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1681887267/10000000000 : ℝ)|^4771 ≤ (10332812660279/100000000000000 : ℝ)^3747
        have hw : |(-1681887267/10000000000 : ℝ)|=(1681887267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(172722149/312500000 : ℝ)|^4771 ≤ (11750775060653/25000000000000 : ℝ)^3747
        have hw : |(172722149/312500000 : ℝ)|=(172722149/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5122266533/10000000000 : ℝ)|^4771 ≤ (21332043541057/50000000000000 : ℝ)^3747
        have hw : |(5122266533/10000000000 : ℝ)|=(5122266533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_s1_1 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5371070353/10000000000 : ℝ)*x 0 + (-946753869/5000000000 : ℝ)*x 1 + (40978131/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5371070353/10000000000 : ℝ)^4771 ≤ (45320056054731/100000000000000 : ℝ)^3747 := by
    have hnat : (5371070353 : ℕ)^4771*100000000000000^3747 ≤ 45320056054731^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5371070353 10000000000 45320056054731 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (946753869/5000000000 : ℝ)^4771 ≤ (6007929261559/50000000000000 : ℝ)^3747 := by
    have hnat : (946753869 : ℕ)^4771*50000000000000^3747 ≤ 6007929261559^3747*5000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      946753869 5000000000 6007929261559 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40978131/80000000 : ℝ)^4771 ≤ (8532817081293/20000000000000 : ℝ)^3747 := by
    have hnat : (40978131 : ℕ)^4771*20000000000000^3747 ≤ 8532817081293^3747*80000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40978131 80000000 8532817081293 20000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5371070353/10000000000 : ℝ), (-946753869/5000000000 : ℝ), (40978131/80000000 : ℝ)] ![(45320056054731/100000000000000 : ℝ), (6007929261559/50000000000000 : ℝ), (8532817081293/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5371070353/10000000000 : ℝ)|^4771 ≤ (45320056054731/100000000000000 : ℝ)^3747
        have hw : |(5371070353/10000000000 : ℝ)|=(5371070353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-946753869/5000000000 : ℝ)|^4771 ≤ (6007929261559/50000000000000 : ℝ)^3747
        have hw : |(-946753869/5000000000 : ℝ)|=(946753869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(40978131/80000000 : ℝ)|^4771 ≤ (8532817081293/20000000000000 : ℝ)^3747
        have hw : |(40978131/80000000 : ℝ)|=(40978131/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_s1_2 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (20980743/39062500 : ℝ)*x 0 + (1024453289/2000000000 : ℝ)*x 1 + (-1893507839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20980743/39062500 : ℝ)^4771 ≤ (4532005449689/10000000000000 : ℝ)^3747 := by
    have hnat : (20980743 : ℕ)^4771*10000000000000^3747 ≤ 4532005449689^3747*39062500^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20980743 39062500 4532005449689 10000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1024453289/2000000000 : ℝ)^4771 ≤ (42664086148841/100000000000000 : ℝ)^3747 := by
    have hnat : (1024453289 : ℕ)^4771*100000000000000^3747 ≤ 42664086148841^3747*2000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024453289 2000000000 42664086148841 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1893507839/10000000000 : ℝ)^4771 ≤ (6007929669601/50000000000000 : ℝ)^3747 := by
    have hnat : (1893507839 : ℕ)^4771*50000000000000^3747 ≤ 6007929669601^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1893507839 10000000000 6007929669601 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20980743/39062500 : ℝ), (1024453289/2000000000 : ℝ), (-1893507839/10000000000 : ℝ)] ![(4532005449689/10000000000000 : ℝ), (42664086148841/100000000000000 : ℝ), (6007929669601/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20980743/39062500 : ℝ)|^4771 ≤ (4532005449689/10000000000000 : ℝ)^3747
        have hw : |(20980743/39062500 : ℝ)|=(20980743/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1024453289/2000000000 : ℝ)|^4771 ≤ (42664086148841/100000000000000 : ℝ)^3747
        have hw : |(1024453289/2000000000 : ℝ)|=(1024453289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1893507839/10000000000 : ℝ)|^4771 ≤ (6007929669601/50000000000000 : ℝ)^3747
        have hw : |(-1893507839/10000000000 : ℝ)|=(1893507839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_s1_3 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (262449541/625000000 : ℝ)*x 0 + (3722503993/10000000000 : ℝ)*x 1 + (4721271081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262449541/625000000 : ℝ)^4771 ≤ (16563517051767/50000000000000 : ℝ)^3747 := by
    have hnat : (262449541 : ℕ)^4771*50000000000000^3747 ≤ 16563517051767^3747*625000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262449541 625000000 16563517051767 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3722503993/10000000000 : ℝ)^4771 ≤ (28415201217201/100000000000000 : ℝ)^3747 := by
    have hnat : (3722503993 : ℕ)^4771*100000000000000^3747 ≤ 28415201217201^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3722503993 10000000000 28415201217201 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4721271081/10000000000 : ℝ)^4771 ≤ (9614441165577/25000000000000 : ℝ)^3747 := by
    have hnat : (4721271081 : ℕ)^4771*25000000000000^3747 ≤ 9614441165577^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4721271081 10000000000 9614441165577 25000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262449541/625000000 : ℝ), (3722503993/10000000000 : ℝ), (4721271081/10000000000 : ℝ)] ![(16563517051767/50000000000000 : ℝ), (28415201217201/100000000000000 : ℝ), (9614441165577/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262449541/625000000 : ℝ)|^4771 ≤ (16563517051767/50000000000000 : ℝ)^3747
        have hw : |(262449541/625000000 : ℝ)|=(262449541/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3722503993/10000000000 : ℝ)|^4771 ≤ (28415201217201/100000000000000 : ℝ)^3747
        have hw : |(3722503993/10000000000 : ℝ)|=(3722503993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4721271081/10000000000 : ℝ)|^4771 ≤ (9614441165577/25000000000000 : ℝ)^3747
        have hw : |(4721271081/10000000000 : ℝ)|=(4721271081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_s1_4 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-336420777/2000000000 : ℝ)*x 0 + (1025329413/2000000000 : ℝ)*x 1 + (1380665219/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (336420777/2000000000 : ℝ)^4771 ≤ (5167253595761/50000000000000 : ℝ)^3747 := by
    have hnat : (336420777 : ℕ)^4771*50000000000000^3747 ≤ 5167253595761^3747*2000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336420777 2000000000 5167253595761 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1025329413/2000000000 : ℝ)^4771 ≤ (21355274846007/50000000000000 : ℝ)^3747 := by
    have hnat : (1025329413 : ℕ)^4771*50000000000000^3747 ≤ 21355274846007^3747*2000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025329413 2000000000 21355274846007 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1380665219/2500000000 : ℝ)^4771 ≤ (23477471551557/50000000000000 : ℝ)^3747 := by
    have hnat : (1380665219 : ℕ)^4771*50000000000000^3747 ≤ 23477471551557^3747*2500000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1380665219 2500000000 23477471551557 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-336420777/2000000000 : ℝ), (1025329413/2000000000 : ℝ), (1380665219/2500000000 : ℝ)] ![(5167253595761/50000000000000 : ℝ), (21355274846007/50000000000000 : ℝ), (23477471551557/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-336420777/2000000000 : ℝ)|^4771 ≤ (5167253595761/50000000000000 : ℝ)^3747
        have hw : |(-336420777/2000000000 : ℝ)|=(336420777/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1025329413/2000000000 : ℝ)|^4771 ≤ (21355274846007/50000000000000 : ℝ)^3747
        have hw : |(1025329413/2000000000 : ℝ)|=(1025329413/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1380665219/2500000000 : ℝ)|^4771 ≤ (23477471551557/50000000000000 : ℝ)^3747
        have hw : |(1380665219/2500000000 : ℝ)|=(1380665219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_s1_5 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5263323373/10000000000 : ℝ)*x 0 + (-59724513/400000000 : ℝ)*x 1 + (552266121/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5263323373/10000000000 : ℝ)^4771 ≤ (44165639673697/100000000000000 : ℝ)^3747 := by
    have hnat : (5263323373 : ℕ)^4771*100000000000000^3747 ≤ 44165639673697^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263323373 10000000000 44165639673697 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (59724513/400000000 : ℝ)^4771 ≤ (4439706797609/50000000000000 : ℝ)^3747 := by
    have hnat : (59724513 : ℕ)^4771*50000000000000^3747 ≤ 4439706797609^3747*400000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59724513 400000000 4439706797609 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (552266121/1000000000 : ℝ)^4771 ≤ (1173873667973/2500000000000 : ℝ)^3747 := by
    have hnat : (552266121 : ℕ)^4771*2500000000000^3747 ≤ 1173873667973^3747*1000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552266121 1000000000 1173873667973 2500000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5263323373/10000000000 : ℝ), (-59724513/400000000 : ℝ), (552266121/1000000000 : ℝ)] ![(44165639673697/100000000000000 : ℝ), (4439706797609/50000000000000 : ℝ), (1173873667973/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5263323373/10000000000 : ℝ)|^4771 ≤ (44165639673697/100000000000000 : ℝ)^3747
        have hw : |(5263323373/10000000000 : ℝ)|=(5263323373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-59724513/400000000 : ℝ)|^4771 ≤ (4439706797609/50000000000000 : ℝ)^3747
        have hw : |(-59724513/400000000 : ℝ)|=(59724513/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(552266121/1000000000 : ℝ)|^4771 ≤ (1173873667973/2500000000000 : ℝ)^3747
        have hw : |(552266121/1000000000 : ℝ)|=(552266121/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_s1_6 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5263322727/10000000000 : ℝ)*x 0 + (1104532291/2000000000 : ℝ)*x 1 + (-298622677/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5263322727/10000000000 : ℝ)^4771 ≤ (22082816385787/50000000000000 : ℝ)^3747 := by
    have hnat : (5263322727 : ℕ)^4771*50000000000000^3747 ≤ 22082816385787^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263322727 10000000000 22082816385787 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1104532291/2000000000 : ℝ)^4771 ≤ (46954949371233/100000000000000 : ℝ)^3747 := by
    have hnat : (1104532291 : ℕ)^4771*100000000000000^3747 ≤ 46954949371233^3747*2000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104532291 2000000000 46954949371233 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (298622677/2000000000 : ℝ)^4771 ≤ (2219854458901/25000000000000 : ℝ)^3747 := by
    have hnat : (298622677 : ℕ)^4771*25000000000000^3747 ≤ 2219854458901^3747*2000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      298622677 2000000000 2219854458901 25000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5263322727/10000000000 : ℝ), (1104532291/2000000000 : ℝ), (-298622677/2000000000 : ℝ)] ![(22082816385787/50000000000000 : ℝ), (46954949371233/100000000000000 : ℝ), (2219854458901/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5263322727/10000000000 : ℝ)|^4771 ≤ (22082816385787/50000000000000 : ℝ)^3747
        have hw : |(5263322727/10000000000 : ℝ)|=(5263322727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1104532291/2000000000 : ℝ)|^4771 ≤ (46954949371233/100000000000000 : ℝ)^3747
        have hw : |(1104532291/2000000000 : ℝ)|=(1104532291/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-298622677/2000000000 : ℝ)|^4771 ≤ (2219854458901/25000000000000 : ℝ)^3747
        have hw : |(-298622677/2000000000 : ℝ)|=(298622677/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_s1_7 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167989023/400000000 : ℝ)*x 0 + (1177616319/2500000000 : ℝ)*x 1 + (3733476191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167989023/400000000 : ℝ)^4771 ≤ (16566193637863/50000000000000 : ℝ)^3747 := by
    have hnat : (167989023 : ℕ)^4771*50000000000000^3747 ≤ 16566193637863^3747*400000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167989023 400000000 16566193637863 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1177616319/2500000000 : ℝ)^4771 ≤ (38345724937927/100000000000000 : ℝ)^3747 := by
    have hnat : (1177616319 : ℕ)^4771*100000000000000^3747 ≤ 38345724937927^3747*2500000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1177616319 2500000000 38345724937927 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3733476191/10000000000 : ℝ)^4771 ≤ (3565235971137/12500000000000 : ℝ)^3747 := by
    have hnat : (3733476191 : ℕ)^4771*12500000000000^3747 ≤ 3565235971137^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3733476191 10000000000 3565235971137 12500000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167989023/400000000 : ℝ), (1177616319/2500000000 : ℝ), (3733476191/10000000000 : ℝ)] ![(16566193637863/50000000000000 : ℝ), (38345724937927/100000000000000 : ℝ), (3565235971137/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167989023/400000000 : ℝ)|^4771 ≤ (16566193637863/50000000000000 : ℝ)^3747
        have hw : |(167989023/400000000 : ℝ)|=(167989023/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1177616319/2500000000 : ℝ)|^4771 ≤ (38345724937927/100000000000000 : ℝ)^3747
        have hw : |(1177616319/2500000000 : ℝ)|=(1177616319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3733476191/10000000000 : ℝ)|^4771 ≤ (3565235971137/12500000000000 : ℝ)^3747
        have hw : |(3733476191/10000000000 : ℝ)|=(3733476191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1613_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3467051/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24173/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4087/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (287/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3553/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (24173/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4087/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (24173/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4087/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (24173/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4087/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (24173/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4087/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (24173/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4087/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (24173/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4087/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4087/100000 : ℝ) ^ (4767/1024 : ℝ) ≤ (6866554796529/20000000000000000000 : ℝ) := by
    have hpowers : (4087/100000 : ℝ)^4767 ≤ (6866554796529/20000000000000000000 : ℝ)^1024 := by
      have hnat : (4087 : ℕ)^4767*20000000000000000000^1024 ≤ 6866554796529^1024*100000^4767 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4087 100000 6866554796529 20000000000000000000 4767 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4087/100000 : ℝ)) (X := (6866554796529/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4767 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (24173/100000 : ℝ) ^ (4767/1024 : ℝ) ≤ (67329455694984819/50000000000000000000 : ℝ) := by
    have hpowers : (24173/100000 : ℝ)^4767 ≤ (67329455694984819/50000000000000000000 : ℝ)^1024 := by
      have hnat : (24173 : ℕ)^4767*50000000000000000000^1024 ≤ 67329455694984819^1024*100000^4767 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24173 100000 67329455694984819 50000000000000000000 4767 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (24173/100000 : ℝ)) (X := (67329455694984819/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4767 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000006866554796529/10000000000000000000 : ℝ) ≤ (1000000147500529/1000000000000000 : ℝ) ^ (4767/1024 : ℝ) := by
    have hpowers : (10000006866554796529/10000000000000000000 : ℝ)^1024 ≤ (1000000147500529/1000000000000000 : ℝ)^4767 := by
      have hnat : (10000006866554796529 : ℕ)^1024*1000000000000000^4767 ≤ 1000000147500529^4767*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000006866554796529 10000000000000000000 1000000147500529 1000000000000000 1024 4767 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000000147500529/1000000000000000 : ℝ)) (X := (10000006866554796529/10000000000000000000 : ℝ)) (by norm_num) 4767 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100134693244163952283/100000000000000000000 : ℝ) ≤ (2000578363773363/2000000000000000 : ℝ) ^ (4767/1024 : ℝ) := by
    have hpowers : (100134693244163952283/100000000000000000000 : ℝ)^1024 ≤ (2000578363773363/2000000000000000 : ℝ)^4767 := by
      have hnat : (100134693244163952283 : ℕ)^1024*2000000000000000^4767 ≤ 2000578363773363^4767*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100134693244163952283 100000000000000000000 2000578363773363 2000000000000000 1024 4767 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000578363773363/2000000000000000 : ℝ)) (X := (100134693244163952283/100000000000000000000 : ℝ)) (by norm_num) 4767 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25067329455694984819/25000000000000000000 : ℝ) ≤ (500289108136417/500000000000000 : ℝ) ^ (4767/1024 : ℝ) := by
    have hpowers : (25067329455694984819/25000000000000000000 : ℝ)^1024 ≤ (500289108136417/500000000000000 : ℝ)^4767 := by
      have hnat : (25067329455694984819 : ℕ)^1024*500000000000000^4767 ≤ 500289108136417^4767*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25067329455694984819 25000000000000000000 500289108136417 500000000000000 1024 4767 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500289108136417/500000000000000 : ℝ)) (X := (25067329455694984819/25000000000000000000 : ℝ)) (by norm_num) 4767 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6866554796529/20000000000000000000 : ℝ) ≤ ((20083640395623214959/20086000000000000000 : ℝ)+2*(115613754461/80344000000000 : ℝ)*(4087/100000 : ℝ))^(4767/1024 : ℝ) := by
    rw [show (20083640395623214959/20086000000000000000 : ℝ)+2*(115613754461/80344000000000 : ℝ)*(4087/100000 : ℝ)=(1000000147500529/1000000000000000 : ℝ) by norm_num, show 1+2*(6866554796529/20000000000000000000 : ℝ)=(10000006866554796529/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(67329455694984819/50000000000000000000 : ℝ)+(6866554796529/20000000000000000000 : ℝ) ≤ ((20083640395623214959/20086000000000000000 : ℝ)+(115613754461/80344000000000 : ℝ)*((24173/100000 : ℝ)+(4087/100000 : ℝ)))^(4767/1024 : ℝ) := by
    rw [show (20083640395623214959/20086000000000000000 : ℝ)+(115613754461/80344000000000 : ℝ)*((24173/100000 : ℝ)+(4087/100000 : ℝ))=(2000578363773363/2000000000000000 : ℝ) by norm_num, show 1+(67329455694984819/50000000000000000000 : ℝ)+(6866554796529/20000000000000000000 : ℝ)=(100134693244163952283/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(67329455694984819/50000000000000000000 : ℝ) ≤ ((20083640395623214959/20086000000000000000 : ℝ)+2*(115613754461/80344000000000 : ℝ)*(24173/100000 : ℝ))^(4767/1024 : ℝ) := by
    rw [show (20083640395623214959/20086000000000000000 : ℝ)+2*(115613754461/80344000000000 : ℝ)*(24173/100000 : ℝ)=(500289108136417/500000000000000 : ℝ) by norm_num, show 1+2*(67329455694984819/50000000000000000000 : ℝ)=(25067329455694984819/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (20083640395623214959/20086000000000000000 : ℝ)*(X 1 0+X 2 0)+(115613754461/80344000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4767/1024 : ℝ)) (lo := (4087/100000 : ℝ)) (hi := (24173/100000 : ℝ)) (c := (20083640395623214959/20086000000000000000 : ℝ)) (alpha := (115613754461/80344000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (20083640395623214959/20086000000000000000 : ℝ)*(X 0 1+X 2 1)+(115613754461/80344000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4767/1024 : ℝ)) (lo := (4087/100000 : ℝ)) (hi := (24173/100000 : ℝ)) (c := (20083640395623214959/20086000000000000000 : ℝ)) (alpha := (115613754461/80344000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (20083640395623214959/20086000000000000000 : ℝ)*(X 0 2+X 1 2)+(115613754461/80344000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4767/1024 : ℝ)) (lo := (4087/100000 : ℝ)) (hi := (24173/100000 : ℝ)) (c := (20083640395623214959/20086000000000000000 : ℝ)) (alpha := (115613754461/80344000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1681887267/10000000000 : ℝ)*X 0 0+(172722149/312500000 : ℝ)*X 0 1+(5122266533/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5371070353/10000000000 : ℝ)*X 1 0+(-946753869/5000000000 : ℝ)*X 1 1+(40978131/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((20980743/39062500 : ℝ)*X 2 0+(1024453289/2000000000 : ℝ)*X 2 1+(-1893507839/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((262449541/625000000 : ℝ)*X 0 0+(3722503993/10000000000 : ℝ)*X 0 1+(4721271081/10000000000 : ℝ)*X 0 2+(262449541/625000000 : ℝ)*X 1 0+(3722503993/10000000000 : ℝ)*X 1 1+(4721271081/10000000000 : ℝ)*X 1 2+(262449541/625000000 : ℝ)*X 2 0+(3722503993/10000000000 : ℝ)*X 2 1+(4721271081/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-336420777/2000000000 : ℝ)*X 0 0+(1025329413/2000000000 : ℝ)*X 0 1+(1380665219/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5263323373/10000000000 : ℝ)*X 1 0+(-59724513/400000000 : ℝ)*X 1 1+(552266121/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5263322727/10000000000 : ℝ)*X 2 0+(1104532291/2000000000 : ℝ)*X 2 1+(-298622677/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((167989023/400000000 : ℝ)*X 0 0+(1177616319/2500000000 : ℝ)*X 0 1+(3733476191/10000000000 : ℝ)*X 0 2+(167989023/400000000 : ℝ)*X 1 0+(1177616319/2500000000 : ℝ)*X 1 1+(3733476191/10000000000 : ℝ)*X 1 2+(167989023/400000000 : ℝ)*X 2 0+(1177616319/2500000000 : ℝ)*X 2 1+(3733476191/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18966207487738982986767/4017200000000000000000000000 : ℝ) := by norm_num
    linear_combination (19946157/12500000000000 : ℝ)*(base1) + (133784787/12500000000000 : ℝ)*(base19) + (1003593993/100000000000000 : ℝ)*(base23) + (144500849/100000000000000 : ℝ)*(upper3) + (18713573/25000000000000 : ℝ)*(upper5) + (1735676405207799/100000000000000 : ℝ)*(major0) + (1735676405207799/100000000000000 : ℝ)*(major1) + (1735676405207799/100000000000000 : ℝ)*(major2) + (2470105629915217/100000000000000 : ℝ)*(sp0) + (617527703367497/25000000000000 : ℝ)*(sp1) + (617527720038573/25000000000000 : ℝ)*(sp2) + (200247465094573/20000000000000 : ℝ)*(sp3) + (1603350581/25000000000000 : ℝ)*(sp4) + (410531271/12500000000000 : ℝ)*(sp7) + (488887094381/48828125000 : ℝ)*(f.failure) + (494022376749657/20000000000000 : ℝ)*(f.sum) + (5940894374351/20086000000000000000000000000 : ℝ)*base66 + (559466421874384759/2008600000000000000000000000000000 : ℝ)*base68 + (8156910775311784759/2008600000000000000000000000000000 : ℝ)*base70 + (9564331973660615241/2008600000000000000000000000000000 : ℝ)*base71 + (12630745598161/20086000000000000000000000000 : ℝ)*base73 + (11657436087559215241/2008600000000000000000000000000000 : ℝ)*base75 + (11731783186298584759/2008600000000000000000000000000000 : ℝ)*base78 + (6755392350199215241/2008600000000000000000000000000000 : ℝ)*base79 + (393325260101/4017200000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (12479/1562500000000000000 : ℝ)*base90 + (12479/1562500000000000000 : ℝ)*base92 + (12479/1562500000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5420387634718149888361704483/502150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2112961367/100000000000000 : ℝ)*(base19) + (228479291/12500000000000 : ℝ)*(base23) + (4601551/20000000000000 : ℝ)*(upper2) + (96113687/25000000000000 : ℝ)*(upper3) + (145290577/100000000000000 : ℝ)*(upper5) + (887178334190107/50000000000000 : ℝ)*(major0) + (887178334190107/50000000000000 : ℝ)*(major1) + (887178334190107/50000000000000 : ℝ)*(major2) + (16132324911/100000000000000 : ℝ)*(sp1) + (1520840709/10000000000000 : ℝ)*(sp2) + (631289786239201/25000000000000 : ℝ)*(sp4) + (1262570449835263/50000000000000 : ℝ)*(sp5) + (1262571054357693/50000000000000 : ℝ)*(sp6) + (511776915995817/50000000000000 : ℝ)*(sp7) + (511776915995817/50000000000000 : ℝ)*(f.failure) + (631289786239201/25000000000000 : ℝ)*(f.sum) + (6401358904359/2008600000000000000000000000 : ℝ)*base66 + (2705086606814760613/1004300000000000000000000000000000 : ℝ)*base67 + (824127960652560613/1004300000000000000000000000000000 : ℝ)*base69 + (2433598117640660613/1004300000000000000000000000000000 : ℝ)*base71 + (11875477553153/10043000000000000000000000000 : ℝ)*base74 + (7101139765394260613/1004300000000000000000000000000000 : ℝ)*base75 + (6236998153028360613/1004300000000000000000000000000000 : ℝ)*base77 + (639882832708760613/1004300000000000000000000000000000 : ℝ)*base79 + (9005411690247/10043000000000000000000000000 : ℝ)*base82 + (674333/100000000000000000000 : ℝ)*base90 + (674333/100000000000000000000 : ℝ)*base92 + (674333/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1613_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3467051/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24173/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4087/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (287/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3553/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1613_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1613_s2_0 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1695382227/10000000000 : ℝ)*x 0 + (54654451/100000000 : ℝ)*x 1 + (258754511/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1695382227/10000000000 : ℝ)^4771 ≤ (10438492943231/100000000000000 : ℝ)^3747 := by
    have hnat : (1695382227 : ℕ)^4771*100000000000000^3747 ≤ 10438492943231^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1695382227 10000000000 10438492943231 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54654451/100000000 : ℝ)^4771 ≤ (46336417522963/100000000000000 : ℝ)^3747 := by
    have hnat : (54654451 : ℕ)^4771*100000000000000^3747 ≤ 46336417522963^3747*100000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54654451 100000000 46336417522963 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258754511/500000000 : ℝ)^4771 ≤ (43225089519069/100000000000000 : ℝ)^3747 := by
    have hnat : (258754511 : ℕ)^4771*100000000000000^3747 ≤ 43225089519069^3747*500000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258754511 500000000 43225089519069 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1695382227/10000000000 : ℝ), (54654451/100000000 : ℝ), (258754511/500000000 : ℝ)] ![(10438492943231/100000000000000 : ℝ), (46336417522963/100000000000000 : ℝ), (43225089519069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1695382227/10000000000 : ℝ)|^4771 ≤ (10438492943231/100000000000000 : ℝ)^3747
        have hw : |(-1695382227/10000000000 : ℝ)|=(1695382227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(54654451/100000000 : ℝ)|^4771 ≤ (46336417522963/100000000000000 : ℝ)^3747
        have hw : |(54654451/100000000 : ℝ)|=(54654451/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(258754511/500000000 : ℝ)|^4771 ≤ (43225089519069/100000000000000 : ℝ)^3747
        have hw : |(258754511/500000000 : ℝ)|=(258754511/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_s2_1 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669372621/1250000000 : ℝ)*x 0 + (-922646441/5000000000 : ℝ)*x 1 + (258754507/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669372621/1250000000 : ℝ)^4771 ≤ (705426043119/1562500000000 : ℝ)^3747 := by
    have hnat : (669372621 : ℕ)^4771*1562500000000^3747 ≤ 705426043119^3747*1250000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669372621 1250000000 705426043119 1562500000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (922646441/5000000000 : ℝ)^4771 ≤ (2325528910923/20000000000000 : ℝ)^3747 := by
    have hnat : (922646441 : ℕ)^4771*20000000000000^3747 ≤ 2325528910923^3747*5000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      922646441 5000000000 2325528910923 20000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258754507/500000000 : ℝ)^4771 ≤ (1350784020883/3125000000000 : ℝ)^3747 := by
    have hnat : (258754507 : ℕ)^4771*3125000000000^3747 ≤ 1350784020883^3747*500000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258754507 500000000 1350784020883 3125000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669372621/1250000000 : ℝ), (-922646441/5000000000 : ℝ), (258754507/500000000 : ℝ)] ![(705426043119/1562500000000 : ℝ), (2325528910923/20000000000000 : ℝ), (1350784020883/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669372621/1250000000 : ℝ)|^4771 ≤ (705426043119/1562500000000 : ℝ)^3747
        have hw : |(669372621/1250000000 : ℝ)|=(669372621/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-922646441/5000000000 : ℝ)|^4771 ≤ (2325528910923/20000000000000 : ℝ)^3747
        have hw : |(-922646441/5000000000 : ℝ)|=(922646441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(258754507/500000000 : ℝ)|^4771 ≤ (1350784020883/3125000000000 : ℝ)^3747
        have hw : |(258754507/500000000 : ℝ)|=(258754507/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_s2_2 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677490457/5000000000 : ℝ)*x 0 + (258754507/500000000 : ℝ)*x 1 + (-922646477/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677490457/5000000000 : ℝ)^4771 ≤ (45147266179929/100000000000000 : ℝ)^3747 := by
    have hnat : (2677490457 : ℕ)^4771*100000000000000^3747 ≤ 45147266179929^3747*5000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677490457 5000000000 45147266179929 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (258754507/500000000 : ℝ)^4771 ≤ (1350784020883/3125000000000 : ℝ)^3747 := by
    have hnat : (258754507 : ℕ)^4771*3125000000000^3747 ≤ 1350784020883^3747*500000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258754507 500000000 1350784020883 3125000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (922646477/5000000000 : ℝ)^4771 ≤ (11627645132291/100000000000000 : ℝ)^3747 := by
    have hnat : (922646477 : ℕ)^4771*100000000000000^3747 ≤ 11627645132291^3747*5000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      922646477 5000000000 11627645132291 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677490457/5000000000 : ℝ), (258754507/500000000 : ℝ), (-922646477/5000000000 : ℝ)] ![(45147266179929/100000000000000 : ℝ), (1350784020883/3125000000000 : ℝ), (11627645132291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677490457/5000000000 : ℝ)|^4771 ≤ (45147266179929/100000000000000 : ℝ)^3747
        have hw : |(2677490457/5000000000 : ℝ)|=(2677490457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(258754507/500000000 : ℝ)|^4771 ≤ (1350784020883/3125000000000 : ℝ)^3747
        have hw : |(258754507/500000000 : ℝ)|=(258754507/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-922646477/5000000000 : ℝ)|^4771 ≤ (11627645132291/100000000000000 : ℝ)^3747
        have hw : |(-922646477/5000000000 : ℝ)|=(922646477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_s2_3 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (841831987/2000000000 : ℝ)*x 0 + (1931338479/5000000000 : ℝ)*x 1 + (2289498691/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (841831987/2000000000 : ℝ)^4771 ≤ (33227186154473/100000000000000 : ℝ)^3747 := by
    have hnat : (841831987 : ℕ)^4771*100000000000000^3747 ≤ 33227186154473^3747*2000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      841831987 2000000000 33227186154473 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1931338479/5000000000 : ℝ)^4771 ≤ (14892275599899/50000000000000 : ℝ)^3747 := by
    have hnat : (1931338479 : ℕ)^4771*50000000000000^3747 ≤ 14892275599899^3747*5000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1931338479 5000000000 14892275599899 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2289498691/5000000000 : ℝ)^4771 ≤ (36988262632371/100000000000000 : ℝ)^3747 := by
    have hnat : (2289498691 : ℕ)^4771*100000000000000^3747 ≤ 36988262632371^3747*5000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2289498691 5000000000 36988262632371 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(841831987/2000000000 : ℝ), (1931338479/5000000000 : ℝ), (2289498691/5000000000 : ℝ)] ![(33227186154473/100000000000000 : ℝ), (14892275599899/50000000000000 : ℝ), (36988262632371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(841831987/2000000000 : ℝ)|^4771 ≤ (33227186154473/100000000000000 : ℝ)^3747
        have hw : |(841831987/2000000000 : ℝ)|=(841831987/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1931338479/5000000000 : ℝ)|^4771 ≤ (14892275599899/50000000000000 : ℝ)^3747
        have hw : |(1931338479/5000000000 : ℝ)|=(1931338479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2289498691/5000000000 : ℝ)|^4771 ≤ (36988262632371/100000000000000 : ℝ)^3747
        have hw : |(2289498691/5000000000 : ℝ)|=(2289498691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_s2_4 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1695462611/10000000000 : ℝ)*x 0 + (258867523/500000000 : ℝ)*x 1 + (5463159687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1695462611/10000000000 : ℝ)^4771 ≤ (2087824625723/20000000000000 : ℝ)^3747 := by
    have hnat : (1695462611 : ℕ)^4771*20000000000000^3747 ≤ 2087824625723^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1695462611 10000000000 2087824625723 20000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (258867523/500000000 : ℝ)^4771 ≤ (43249128949333/100000000000000 : ℝ)^3747 := by
    have hnat : (258867523 : ℕ)^4771*100000000000000^3747 ≤ 43249128949333^3747*500000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258867523 500000000 43249128949333 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5463159687/10000000000 : ℝ)^4771 ≤ (23155873949881/50000000000000 : ℝ)^3747 := by
    have hnat : (5463159687 : ℕ)^4771*50000000000000^3747 ≤ 23155873949881^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463159687 10000000000 23155873949881 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1695462611/10000000000 : ℝ), (258867523/500000000 : ℝ), (5463159687/10000000000 : ℝ)] ![(2087824625723/20000000000000 : ℝ), (43249128949333/100000000000000 : ℝ), (23155873949881/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1695462611/10000000000 : ℝ)|^4771 ≤ (2087824625723/20000000000000 : ℝ)^3747
        have hw : |(-1695462611/10000000000 : ℝ)|=(1695462611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(258867523/500000000 : ℝ)|^4771 ≤ (43249128949333/100000000000000 : ℝ)^3747
        have hw : |(258867523/500000000 : ℝ)|=(258867523/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5463159687/10000000000 : ℝ)|^4771 ≤ (23155873949881/50000000000000 : ℝ)^3747
        have hw : |(5463159687/10000000000 : ℝ)|=(5463159687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_s2_5 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638909143/5000000000 : ℝ)*x 0 + (-1557223629/10000000000 : ℝ)*x 1 + (2731579723/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638909143/5000000000 : ℝ)^4771 ≤ (44320567381801/100000000000000 : ℝ)^3747 := by
    have hnat : (2638909143 : ℕ)^4771*100000000000000^3747 ≤ 44320567381801^3747*5000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638909143 5000000000 44320567381801 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1557223629/10000000000 : ℝ)^4771 ≤ (9367687310773/100000000000000 : ℝ)^3747 := by
    have hnat : (1557223629 : ℕ)^4771*100000000000000^3747 ≤ 9367687310773^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1557223629 10000000000 9367687310773 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2731579723/5000000000 : ℝ)^4771 ≤ (1447242040577/3125000000000 : ℝ)^3747 := by
    have hnat : (2731579723 : ℕ)^4771*3125000000000^3747 ≤ 1447242040577^3747*5000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731579723 5000000000 1447242040577 3125000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638909143/5000000000 : ℝ), (-1557223629/10000000000 : ℝ), (2731579723/5000000000 : ℝ)] ![(44320567381801/100000000000000 : ℝ), (9367687310773/100000000000000 : ℝ), (1447242040577/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638909143/5000000000 : ℝ)|^4771 ≤ (44320567381801/100000000000000 : ℝ)^3747
        have hw : |(2638909143/5000000000 : ℝ)|=(2638909143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1557223629/10000000000 : ℝ)|^4771 ≤ (9367687310773/100000000000000 : ℝ)^3747
        have hw : |(-1557223629/10000000000 : ℝ)|=(1557223629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2731579723/5000000000 : ℝ)|^4771 ≤ (1447242040577/3125000000000 : ℝ)^3747
        have hw : |(2731579723/5000000000 : ℝ)|=(2731579723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_s2_6 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638908757/5000000000 : ℝ)*x 0 + (5463160929/10000000000 : ℝ)*x 1 + (-194652827/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638908757/5000000000 : ℝ)^4771 ≤ (22160279563621/50000000000000 : ℝ)^3747 := by
    have hnat : (2638908757 : ℕ)^4771*50000000000000^3747 ≤ 22160279563621^3747*5000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638908757 5000000000 22160279563621 50000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5463160929/10000000000 : ℝ)^4771 ≤ (2315588065281/5000000000000 : ℝ)^3747 := by
    have hnat : (5463160929 : ℕ)^4771*5000000000000^3747 ≤ 2315588065281^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463160929 10000000000 2315588065281 5000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (194652827/1250000000 : ℝ)^4771 ≤ (468383977579/5000000000000 : ℝ)^3747 := by
    have hnat : (194652827 : ℕ)^4771*5000000000000^3747 ≤ 468383977579^3747*1250000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194652827 1250000000 468383977579 5000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638908757/5000000000 : ℝ), (5463160929/10000000000 : ℝ), (-194652827/1250000000 : ℝ)] ![(22160279563621/50000000000000 : ℝ), (2315588065281/5000000000000 : ℝ), (468383977579/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638908757/5000000000 : ℝ)|^4771 ≤ (22160279563621/50000000000000 : ℝ)^3747
        have hw : |(2638908757/5000000000 : ℝ)|=(2638908757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5463160929/10000000000 : ℝ)|^4771 ≤ (2315588065281/5000000000000 : ℝ)^3747
        have hw : |(5463160929/10000000000 : ℝ)|=(5463160929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-194652827/1250000000 : ℝ)|^4771 ≤ (468383977579/5000000000000 : ℝ)^3747
        have hw : |(-194652827/1250000000 : ℝ)|=(194652827/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1613_s2_7 (p : ℝ) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4209357547/10000000000 : ℝ)*x 0 + (2286710253/5000000000 : ℝ)*x 1 + (3868314827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4209357547/10000000000 : ℝ)^4771 ≤ (33229172432141/100000000000000 : ℝ)^3747 := by
    have hnat : (4209357547 : ℕ)^4771*100000000000000^3747 ≤ 33229172432141^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4209357547 10000000000 33229172432141 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2286710253/5000000000 : ℝ)^4771 ≤ (461636400437/1250000000000 : ℝ)^3747 := by
    have hnat : (2286710253 : ℕ)^4771*1250000000000^3747 ≤ 461636400437^3747*5000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2286710253 5000000000 461636400437 1250000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3868314827/10000000000 : ℝ)^4771 ≤ (29839915517493/100000000000000 : ℝ)^3747 := by
    have hnat : (3868314827 : ℕ)^4771*100000000000000^3747 ≤ 29839915517493^3747*10000000000^4771 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3868314827 10000000000 29839915517493 100000000000000 4771 3747 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4771/1024 : ℝ)) 4771 3747 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4209357547/10000000000 : ℝ), (2286710253/5000000000 : ℝ), (3868314827/10000000000 : ℝ)] ![(33229172432141/100000000000000 : ℝ), (461636400437/1250000000000 : ℝ), (29839915517493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4209357547/10000000000 : ℝ)|^4771 ≤ (33229172432141/100000000000000 : ℝ)^3747
        have hw : |(4209357547/10000000000 : ℝ)|=(4209357547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2286710253/5000000000 : ℝ)|^4771 ≤ (461636400437/1250000000000 : ℝ)^3747
        have hw : |(2286710253/5000000000 : ℝ)|=(2286710253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3868314827/10000000000 : ℝ)|^4771 ≤ (29839915517493/100000000000000 : ℝ)^3747
        have hw : |(3868314827/10000000000 : ℝ)|=(3868314827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1613_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3467051/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3553/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (287/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (413/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16481/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3553/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (287/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3553/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (287/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3553/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (287/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3553/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (287/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3553/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (287/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3553/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (287/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (287/3125 : ℝ) ^ (4767/1024 : ℝ) ≤ (37202304324523/2500000000000000000 : ℝ) := by
    have hpowers : (287/3125 : ℝ)^4767 ≤ (37202304324523/2500000000000000000 : ℝ)^1024 := by
      have hnat : (287 : ℕ)^4767*2500000000000000000^1024 ≤ 37202304324523^1024*3125^4767 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        287 3125 37202304324523 2500000000000000000 4767 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (287/3125 : ℝ)) (X := (37202304324523/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4767 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3553/20000 : ℝ) ^ (4767/1024 : ℝ) ≤ (32101170184283407/100000000000000000000 : ℝ) := by
    have hpowers : (3553/20000 : ℝ)^4767 ≤ (32101170184283407/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3553 : ℕ)^4767*100000000000000000000^1024 ≤ 32101170184283407^1024*20000^4767 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3553 20000 32101170184283407 100000000000000000000 4767 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3553/20000 : ℝ)) (X := (32101170184283407/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4767 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250037202304324523/1250000000000000000 : ℝ) ≤ (312501997834829/312500000000000 : ℝ) ^ (4767/1024 : ℝ) := by
    have hpowers : (1250037202304324523/1250000000000000000 : ℝ)^1024 ≤ (312501997834829/312500000000000 : ℝ)^4767 := by
      have hnat : (1250037202304324523 : ℕ)^1024*312500000000000^4767 ≤ 312501997834829^4767*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250037202304324523 1250000000000000000 312501997834829 312500000000000 1024 4767 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312501997834829/312500000000000 : ℝ)) (X := (1250037202304324523/1250000000000000000 : ℝ)) (by norm_num) 4767 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100033589262357264327/100000000000000000000 : ℝ) ≤ (5000360718164959/5000000000000000 : ℝ) ^ (4767/1024 : ℝ) := by
    have hpowers : (100033589262357264327/100000000000000000000 : ℝ)^1024 ≤ (5000360718164959/5000000000000000 : ℝ)^4767 := by
      have hnat : (100033589262357264327 : ℕ)^1024*5000000000000000^4767 ≤ 5000360718164959^4767*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100033589262357264327 100000000000000000000 5000360718164959 5000000000000000 1024 4767 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000360718164959/5000000000000000 : ℝ)) (X := (100033589262357264327/100000000000000000000 : ℝ)) (by norm_num) 4767 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032101170184283407/50000000000000000000 : ℝ) ≤ (2500344735486327/2500000000000000 : ℝ) ^ (4767/1024 : ℝ) := by
    have hpowers : (50032101170184283407/50000000000000000000 : ℝ)^1024 ≤ (2500344735486327/2500000000000000 : ℝ)^4767 := by
      have hnat : (50032101170184283407 : ℕ)^1024*2500000000000000^4767 ≤ 2500344735486327^4767*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032101170184283407 50000000000000000000 2500344735486327 2500000000000000 1024 4767 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500344735486327/2500000000000000 : ℝ)) (X := (50032101170184283407/50000000000000000000 : ℝ)) (by norm_num) 4767 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(37202304324523/2500000000000000000 : ℝ) ≤ ((2681202235197433789/2681562500000000000 : ℝ)+2*(65750561539/85810000000000 : ℝ)*(287/3125 : ℝ))^(4767/1024 : ℝ) := by
    rw [show (2681202235197433789/2681562500000000000 : ℝ)+2*(65750561539/85810000000000 : ℝ)*(287/3125 : ℝ)=(312501997834829/312500000000000 : ℝ) by norm_num, show 1+2*(37202304324523/2500000000000000000 : ℝ)=(1250037202304324523/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32101170184283407/100000000000000000000 : ℝ)+(37202304324523/2500000000000000000 : ℝ) ≤ ((2681202235197433789/2681562500000000000 : ℝ)+(65750561539/85810000000000 : ℝ)*((3553/20000 : ℝ)+(287/3125 : ℝ)))^(4767/1024 : ℝ) := by
    rw [show (2681202235197433789/2681562500000000000 : ℝ)+(65750561539/85810000000000 : ℝ)*((3553/20000 : ℝ)+(287/3125 : ℝ))=(5000360718164959/5000000000000000 : ℝ) by norm_num, show 1+(32101170184283407/100000000000000000000 : ℝ)+(37202304324523/2500000000000000000 : ℝ)=(100033589262357264327/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32101170184283407/100000000000000000000 : ℝ) ≤ ((2681202235197433789/2681562500000000000 : ℝ)+2*(65750561539/85810000000000 : ℝ)*(3553/20000 : ℝ))^(4767/1024 : ℝ) := by
    rw [show (2681202235197433789/2681562500000000000 : ℝ)+2*(65750561539/85810000000000 : ℝ)*(3553/20000 : ℝ)=(2500344735486327/2500000000000000 : ℝ) by norm_num, show 1+2*(32101170184283407/100000000000000000000 : ℝ)=(50032101170184283407/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2681202235197433789/2681562500000000000 : ℝ)*(X 1 0+X 2 0)+(65750561539/85810000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4767/1024 : ℝ)) (lo := (287/3125 : ℝ)) (hi := (3553/20000 : ℝ)) (c := (2681202235197433789/2681562500000000000 : ℝ)) (alpha := (65750561539/85810000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2681202235197433789/2681562500000000000 : ℝ)*(X 0 1+X 2 1)+(65750561539/85810000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4767/1024 : ℝ)) (lo := (287/3125 : ℝ)) (hi := (3553/20000 : ℝ)) (c := (2681202235197433789/2681562500000000000 : ℝ)) (alpha := (65750561539/85810000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2681202235197433789/2681562500000000000 : ℝ)*(X 0 2+X 1 2)+(65750561539/85810000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4767/1024 : ℝ)) (lo := (287/3125 : ℝ)) (hi := (3553/20000 : ℝ)) (c := (2681202235197433789/2681562500000000000 : ℝ)) (alpha := (65750561539/85810000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1695382227/10000000000 : ℝ)*X 0 0+(54654451/100000000 : ℝ)*X 0 1+(258754511/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((669372621/1250000000 : ℝ)*X 1 0+(-922646441/5000000000 : ℝ)*X 1 1+(258754507/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677490457/5000000000 : ℝ)*X 2 0+(258754507/500000000 : ℝ)*X 2 1+(-922646477/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((841831987/2000000000 : ℝ)*X 0 0+(1931338479/5000000000 : ℝ)*X 0 1+(2289498691/5000000000 : ℝ)*X 0 2+(841831987/2000000000 : ℝ)*X 1 0+(1931338479/5000000000 : ℝ)*X 1 1+(2289498691/5000000000 : ℝ)*X 1 2+(841831987/2000000000 : ℝ)*X 2 0+(1931338479/5000000000 : ℝ)*X 2 1+(2289498691/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1695462611/10000000000 : ℝ)*X 0 0+(258867523/500000000 : ℝ)*X 0 1+(5463159687/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2638909143/5000000000 : ℝ)*X 1 0+(-1557223629/10000000000 : ℝ)*X 1 1+(2731579723/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2638908757/5000000000 : ℝ)*X 2 0+(5463160929/10000000000 : ℝ)*X 2 1+(-194652827/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4209357547/10000000000 : ℝ)*X 0 0+(2286710253/5000000000 : ℝ)*X 0 1+(3868314827/10000000000 : ℝ)*X 0 2+(4209357547/10000000000 : ℝ)*X 1 0+(2286710253/5000000000 : ℝ)*X 1 1+(3868314827/10000000000 : ℝ)*X 1 2+(4209357547/10000000000 : ℝ)*X 2 0+(2286710253/5000000000 : ℝ)*X 2 1+(3868314827/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1613_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4315319397045223222521/1716200000000000000000000000 : ℝ) := by norm_num
    linear_combination (560884467/100000000000000 : ℝ)*(base19) + (242393/48828125000 : ℝ)*(base23) + (108007019/100000000000000 : ℝ)*(upper3) + (318443/2000000000000 : ℝ)*(upper4) + (14502521/50000000000000 : ℝ)*(upper5) + (1210025084114459/50000000000000 : ℝ)*(major0) + (1210025084114459/50000000000000 : ℝ)*(major1) + (1210025084114459/50000000000000 : ℝ)*(major2) + (3444067545937353/100000000000000 : ℝ)*(sp0) + (1722035836789151/50000000000000 : ℝ)*(sp1) + (1722035869020953/50000000000000 : ℝ)*(sp2) + (698012670648563/50000000000000 : ℝ)*(sp3) + (4688525417/100000000000000 : ℝ)*(sp4) + (1338441271/50000000000000 : ℝ)*(sp7) + (349007004544917/25000000000000 : ℝ)*(f.failure) + (344407223446277/10000000000000 : ℝ)*(f.sum) + (12784696143479/4290500000000000000000000000 : ℝ)*base65 + (387924984160538599/134078125000000000000000000000000 : ℝ)*base68 + (141797299342970819/33519531250000000000000000000000 : ℝ)*base69 + (355190686812726099/134078125000000000000000000000000 : ℝ)*base72 + (897662769583/536312500000000000000000000 : ℝ)*base73 + (121260083310617651/134078125000000000000000000000000 : ℝ)*base75 + (180141739056288599/134078125000000000000000000000000 : ℝ)*base78 + (234204927678211401/134078125000000000000000000000000 : ℝ)*base79 + (29157837622601/4290500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (29767/50000000000000000000 : ℝ)*base89 + (29767/50000000000000000000 : ℝ)*base91 + (29767/50000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (594144809757552685727814777/134078125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (526739877/50000000000000 : ℝ)*(base19) + (928726981/100000000000000 : ℝ)*(base23) + (26194353/25000000000000 : ℝ)*(upper2) + (96791321/50000000000000 : ℝ)*(upper3) + (237148653/100000000000000 : ℝ)*(upper5) + (153658182482009/6250000000000 : ℝ)*(major0) + (153658182482009/6250000000000 : ℝ)*(major1) + (153658182482009/6250000000000 : ℝ)*(major2) + (868030631/12500000000000 : ℝ)*(sp1) + (9918824419/50000000000000 : ℝ)*(sp2) + (437354462621533/12500000000000 : ℝ)*(sp4) + (3498827703247463/100000000000000 : ℝ)*(sp5) + (874703733649111/25000000000000 : ℝ)*(sp6) + (1418225990740917/100000000000000 : ℝ)*(sp7) + (1418225990740917/100000000000000 : ℝ)*(f.failure) + (437354462621533/12500000000000 : ℝ)*(f.sum) + (14939640278837/8581000000000000000000000000 : ℝ)*base65 + (224903400624605279/67039062500000000000000000000000 : ℝ)*base67 + (596594164650555067/134078125000000000000000000000000 : ℝ)*base70 + (638760416020163683/134078125000000000000000000000000 : ℝ)*base71 + (36826655140173/8581000000000000000000000000 : ℝ)*base73 + (680083386273211317/134078125000000000000000000000000 : ℝ)*base76 + (1735942727496007433/134078125000000000000000000000000 : ℝ)*base77 + (755064908696199029/67039062500000000000000000000000 : ℝ)*base79 + (25334271589911/8581000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (974233/200000000000000000000 : ℝ)*base90 + (974233/200000000000000000000 : ℝ)*base92 + (974233/200000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1613_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3467051/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3553/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (287/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (413/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16481/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1613_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1613_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3467051/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (413/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16481/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1613_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1613_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1613_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4767/1024 : ℝ) ≤ p) (hpb : p ≤ (4771/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3467051/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (413/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16481/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1613_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
