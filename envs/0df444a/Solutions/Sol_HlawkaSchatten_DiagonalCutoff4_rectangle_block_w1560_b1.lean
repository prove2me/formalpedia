-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1560_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:24:34.709736+00:00
-- url     : https://prove2.me/submissions/d4462407-cead-4ab3-a6bb-3138f3b10ace

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
theorem support_rectangle_w1560_s3_0 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1799086187/10000000000 : ℝ)*x 0 + (1357234943/2500000000 : ℝ)*x 1 + (5218017889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1799086187/10000000000 : ℝ)^4617 ≤ (5517124969489/50000000000000 : ℝ)^3593 := by
    have hnat : (1799086187 : ℕ)^4617*50000000000000^3593 ≤ 5517124969489^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1799086187 10000000000 5517124969489 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357234943/2500000000 : ℝ)^4617 ≤ (9123031412897/20000000000000 : ℝ)^3593 := by
    have hnat : (1357234943 : ℕ)^4617*20000000000000^3593 ≤ 9123031412897^3593*2500000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357234943 2500000000 9123031412897 20000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218017889/10000000000 : ℝ)^4617 ≤ (43350592978719/100000000000000 : ℝ)^3593 := by
    have hnat : (5218017889 : ℕ)^4617*100000000000000^3593 ≤ 43350592978719^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218017889 10000000000 43350592978719 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1799086187/10000000000 : ℝ), (1357234943/2500000000 : ℝ), (5218017889/10000000000 : ℝ)] ![(5517124969489/50000000000000 : ℝ), (9123031412897/20000000000000 : ℝ), (43350592978719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1799086187/10000000000 : ℝ)|^4617 ≤ (5517124969489/50000000000000 : ℝ)^3593
        have hw : |(-1799086187/10000000000 : ℝ)|=(1799086187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1357234943/2500000000 : ℝ)|^4617 ≤ (9123031412897/20000000000000 : ℝ)^3593
        have hw : |(1357234943/2500000000 : ℝ)|=(1357234943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218017889/10000000000 : ℝ)|^4617 ≤ (43350592978719/100000000000000 : ℝ)^3593
        have hw : |(5218017889/10000000000 : ℝ)|=(5218017889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s3_1 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349297313/10000000000 : ℝ)*x 0 + (-1907052797/10000000000 : ℝ)*x 1 + (5218017831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349297313/10000000000 : ℝ)^4617 ≤ (44757073781519/100000000000000 : ℝ)^3593 := by
    have hnat : (5349297313 : ℕ)^4617*100000000000000^3593 ≤ 44757073781519^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349297313 10000000000 44757073781519 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1907052797/10000000000 : ℝ)^4617 ≤ (5946166923507/50000000000000 : ℝ)^3593 := by
    have hnat : (1907052797 : ℕ)^4617*50000000000000^3593 ≤ 5946166923507^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1907052797 10000000000 5946166923507 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218017831/10000000000 : ℝ)^4617 ≤ (8670118471907/20000000000000 : ℝ)^3593 := by
    have hnat : (5218017831 : ℕ)^4617*20000000000000^3593 ≤ 8670118471907^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218017831 10000000000 8670118471907 20000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349297313/10000000000 : ℝ), (-1907052797/10000000000 : ℝ), (5218017831/10000000000 : ℝ)] ![(44757073781519/100000000000000 : ℝ), (5946166923507/50000000000000 : ℝ), (8670118471907/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349297313/10000000000 : ℝ)|^4617 ≤ (44757073781519/100000000000000 : ℝ)^3593
        have hw : |(5349297313/10000000000 : ℝ)|=(5349297313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1907052797/10000000000 : ℝ)|^4617 ≤ (5946166923507/50000000000000 : ℝ)^3593
        have hw : |(-1907052797/10000000000 : ℝ)|=(1907052797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218017831/10000000000 : ℝ)|^4617 ≤ (8670118471907/20000000000000 : ℝ)^3593
        have hw : |(5218017831/10000000000 : ℝ)|=(5218017831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s3_2 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674648719/5000000000 : ℝ)*x 0 + (2609008881/5000000000 : ℝ)*x 1 + (-1907052721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674648719/5000000000 : ℝ)^4617 ≤ (11189268781363/25000000000000 : ℝ)^3593 := by
    have hnat : (2674648719 : ℕ)^4617*25000000000000^3593 ≤ 11189268781363^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674648719 5000000000 11189268781363 25000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609008881/5000000000 : ℝ)^4617 ≤ (21675295811459/50000000000000 : ℝ)^3593 := by
    have hnat : (2609008881 : ℕ)^4617*50000000000000^3593 ≤ 21675295811459^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609008881 5000000000 21675295811459 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1907052721/10000000000 : ℝ)^4617 ≤ (1189233323801/10000000000000 : ℝ)^3593 := by
    have hnat : (1907052721 : ℕ)^4617*10000000000000^3593 ≤ 1189233323801^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1907052721 10000000000 1189233323801 10000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674648719/5000000000 : ℝ), (2609008881/5000000000 : ℝ), (-1907052721/10000000000 : ℝ)] ![(11189268781363/25000000000000 : ℝ), (21675295811459/50000000000000 : ℝ), (1189233323801/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674648719/5000000000 : ℝ)|^4617 ≤ (11189268781363/25000000000000 : ℝ)^3593
        have hw : |(2674648719/5000000000 : ℝ)|=(2674648719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609008881/5000000000 : ℝ)|^4617 ≤ (21675295811459/50000000000000 : ℝ)^3593
        have hw : |(2609008881/5000000000 : ℝ)|=(2609008881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1907052721/10000000000 : ℝ)|^4617 ≤ (1189233323801/10000000000000 : ℝ)^3593
        have hw : |(-1907052721/10000000000 : ℝ)|=(1907052721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s3_3 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2123876533/5000000000 : ℝ)*x 0 + (801275067/2000000000 : ℝ)*x 1 + (450087961/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2123876533/5000000000 : ℝ)^4617 ≤ (33280141884027/100000000000000 : ℝ)^3593 := by
    have hnat : (2123876533 : ℕ)^4617*100000000000000^3593 ≤ 33280141884027^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123876533 5000000000 33280141884027 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (801275067/2000000000 : ℝ)^4617 ≤ (30869983819779/100000000000000 : ℝ)^3593 := by
    have hnat : (801275067 : ℕ)^4617*100000000000000^3593 ≤ 30869983819779^3593*2000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      801275067 2000000000 30869983819779 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (450087961/1000000000 : ℝ)^4617 ≤ (17924937140837/50000000000000 : ℝ)^3593 := by
    have hnat : (450087961 : ℕ)^4617*50000000000000^3593 ≤ 17924937140837^3593*1000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450087961 1000000000 17924937140837 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2123876533/5000000000 : ℝ), (801275067/2000000000 : ℝ), (450087961/1000000000 : ℝ)] ![(33280141884027/100000000000000 : ℝ), (30869983819779/100000000000000 : ℝ), (17924937140837/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2123876533/5000000000 : ℝ)|^4617 ≤ (33280141884027/100000000000000 : ℝ)^3593
        have hw : |(2123876533/5000000000 : ℝ)|=(2123876533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(801275067/2000000000 : ℝ)|^4617 ≤ (30869983819779/100000000000000 : ℝ)^3593
        have hw : |(801275067/2000000000 : ℝ)|=(801275067/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(450087961/1000000000 : ℝ)|^4617 ≤ (17924937140837/50000000000000 : ℝ)^3593
        have hw : |(450087961/1000000000 : ℝ)|=(450087961/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s3_4 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-112444669/625000000 : ℝ)*x 0 + (2609566461/5000000000 : ℝ)*x 1 + (2713908189/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (112444669/625000000 : ℝ)^4617 ≤ (2206894937653/20000000000000 : ℝ)^3593 := by
    have hnat : (112444669 : ℕ)^4617*20000000000000^3593 ≤ 2206894937653^3593*625000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112444669 625000000 2206894937653 20000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609566461/5000000000 : ℝ)^4617 ≤ (43362496983167/100000000000000 : ℝ)^3593 := by
    have hnat : (2609566461 : ℕ)^4617*100000000000000^3593 ≤ 43362496983167^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609566461 5000000000 43362496983167 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2713908189/5000000000 : ℝ)^4617 ≤ (11400757078223/25000000000000 : ℝ)^3593 := by
    have hnat : (2713908189 : ℕ)^4617*25000000000000^3593 ≤ 11400757078223^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713908189 5000000000 11400757078223 25000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-112444669/625000000 : ℝ), (2609566461/5000000000 : ℝ), (2713908189/5000000000 : ℝ)] ![(2206894937653/20000000000000 : ℝ), (43362496983167/100000000000000 : ℝ), (11400757078223/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-112444669/625000000 : ℝ)|^4617 ≤ (2206894937653/20000000000000 : ℝ)^3593
        have hw : |(-112444669/625000000 : ℝ)|=(112444669/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609566461/5000000000 : ℝ)|^4617 ≤ (43362496983167/100000000000000 : ℝ)^3593
        have hw : |(2609566461/5000000000 : ℝ)|=(2609566461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2713908189/5000000000 : ℝ)|^4617 ≤ (11400757078223/25000000000000 : ℝ)^3593
        have hw : |(2713908189/5000000000 : ℝ)|=(2713908189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s3_5 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661695147/1250000000 : ℝ)*x 0 + (-848627093/5000000000 : ℝ)*x 1 + (1356954067/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661695147/1250000000 : ℝ)^4617 ≤ (44158720658197/100000000000000 : ℝ)^3593 := by
    have hnat : (661695147 : ℕ)^4617*100000000000000^3593 ≤ 44158720658197^3593*1250000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661695147 1250000000 44158720658197 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (848627093/5000000000 : ℝ)^4617 ≤ (10238252204397/100000000000000 : ℝ)^3593 := by
    have hnat : (848627093 : ℕ)^4617*100000000000000^3593 ≤ 10238252204397^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848627093 5000000000 10238252204397 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356954067/2500000000 : ℝ)^4617 ≤ (45603027125309/100000000000000 : ℝ)^3593 := by
    have hnat : (1356954067 : ℕ)^4617*100000000000000^3593 ≤ 45603027125309^3593*2500000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356954067 2500000000 45603027125309 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661695147/1250000000 : ℝ), (-848627093/5000000000 : ℝ), (1356954067/2500000000 : ℝ)] ![(44158720658197/100000000000000 : ℝ), (10238252204397/100000000000000 : ℝ), (45603027125309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661695147/1250000000 : ℝ)|^4617 ≤ (44158720658197/100000000000000 : ℝ)^3593
        have hw : |(661695147/1250000000 : ℝ)|=(661695147/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-848627093/5000000000 : ℝ)|^4617 ≤ (10238252204397/100000000000000 : ℝ)^3593
        have hw : |(-848627093/5000000000 : ℝ)|=(848627093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356954067/2500000000 : ℝ)|^4617 ≤ (45603027125309/100000000000000 : ℝ)^3593
        have hw : |(1356954067/2500000000 : ℝ)|=(1356954067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s3_6 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (13233903/25000000 : ℝ)*x 0 + (678477033/1250000000 : ℝ)*x 1 + (-1697254159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13233903/25000000 : ℝ)^4617 ≤ (44158720915463/100000000000000 : ℝ)^3593 := by
    have hnat : (13233903 : ℕ)^4617*100000000000000^3593 ≤ 44158720915463^3593*25000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13233903 25000000 44158720915463 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (678477033/1250000000 : ℝ)^4617 ≤ (11400756770531/25000000000000 : ℝ)^3593 := by
    have hnat : (678477033 : ℕ)^4617*25000000000000^3593 ≤ 11400756770531^3593*1250000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678477033 1250000000 11400756770531 25000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1697254159/10000000000 : ℝ)^4617 ≤ (10238251995109/100000000000000 : ℝ)^3593 := by
    have hnat : (1697254159 : ℕ)^4617*100000000000000^3593 ≤ 10238251995109^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1697254159 10000000000 10238251995109 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(13233903/25000000 : ℝ), (678477033/1250000000 : ℝ), (-1697254159/10000000000 : ℝ)] ![(44158720915463/100000000000000 : ℝ), (11400756770531/25000000000000 : ℝ), (10238251995109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(13233903/25000000 : ℝ)|^4617 ≤ (44158720915463/100000000000000 : ℝ)^3593
        have hw : |(13233903/25000000 : ℝ)|=(13233903/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(678477033/1250000000 : ℝ)|^4617 ≤ (11400756770531/25000000000000 : ℝ)^3593
        have hw : |(678477033/1250000000 : ℝ)|=(678477033/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1697254159/10000000000 : ℝ)|^4617 ≤ (10238251995109/100000000000000 : ℝ)^3593
        have hw : |(-1697254159/10000000000 : ℝ)|=(1697254159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s3_7 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061955039/2500000000 : ℝ)*x 0 + (562283161/1250000000 : ℝ)*x 1 + (4009009139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061955039/2500000000 : ℝ)^4617 ≤ (16640408662447/50000000000000 : ℝ)^3593 := by
    have hnat : (1061955039 : ℕ)^4617*50000000000000^3593 ≤ 16640408662447^3593*2500000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061955039 2500000000 16640408662447 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (562283161/1250000000 : ℝ)^4617 ≤ (35823118599877/100000000000000 : ℝ)^3593 := by
    have hnat : (562283161 : ℕ)^4617*100000000000000^3593 ≤ 35823118599877^3593*1250000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562283161 1250000000 35823118599877 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4009009139/10000000000 : ℝ)^4617 ≤ (30896064058049/100000000000000 : ℝ)^3593 := by
    have hnat : (4009009139 : ℕ)^4617*100000000000000^3593 ≤ 30896064058049^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4009009139 10000000000 30896064058049 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061955039/2500000000 : ℝ), (562283161/1250000000 : ℝ), (4009009139/10000000000 : ℝ)] ![(16640408662447/50000000000000 : ℝ), (35823118599877/100000000000000 : ℝ), (30896064058049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061955039/2500000000 : ℝ)|^4617 ≤ (16640408662447/50000000000000 : ℝ)^3593
        have hw : |(1061955039/2500000000 : ℝ)|=(1061955039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(562283161/1250000000 : ℝ)|^4617 ≤ (35823118599877/100000000000000 : ℝ)^3593
        have hw : |(562283161/1250000000 : ℝ)|=(562283161/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4009009139/10000000000 : ℝ)|^4617 ≤ (30896064058049/100000000000000 : ℝ)^3593
        have hw : |(4009009139/10000000000 : ℝ)|=(4009009139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1560_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83612239/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15839/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5381/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2763/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3881/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15839/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5381/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15839/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5381/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15839/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5381/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15839/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5381/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15839/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5381/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15839/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5381/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5381/50000 : ℝ) ^ (4615/1024 : ℝ) ≤ (1083528987272581/25000000000000000000 : ℝ) := by
    have hpowers : (5381/50000 : ℝ)^4615 ≤ (1083528987272581/25000000000000000000 : ℝ)^1024 := by
      have hnat : (5381 : ℕ)^4615*25000000000000000000^1024 ≤ 1083528987272581^1024*50000^4615 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5381 50000 1083528987272581 25000000000000000000 4615 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5381/50000 : ℝ)) (X := (1083528987272581/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4615 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15839/100000 : ℝ) ^ (4615/1024 : ℝ) ≤ (24734566518285513/100000000000000000000 : ℝ) := by
    have hpowers : (15839/100000 : ℝ)^4615 ≤ (24734566518285513/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15839 : ℕ)^4615*100000000000000000000^1024 ≤ 24734566518285513^1024*100000^4615 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15839 100000 24734566518285513 100000000000000000000 4615 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15839/100000 : ℝ)) (X := (24734566518285513/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4615 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501083528987272581/12500000000000000000 : ℝ) ≤ (1250024041089199/1250000000000000 : ℝ) ^ (4615/1024 : ℝ) := by
    have hpowers : (12501083528987272581/12500000000000000000 : ℝ)^1024 ≤ (1250024041089199/1250000000000000 : ℝ)^4615 := by
      have hnat : (12501083528987272581 : ℕ)^1024*1250000000000000^4615 ≤ 1250024041089199^4615*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501083528987272581 12500000000000000000 1250024041089199 1250000000000000 1024 4615 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250024041089199/1250000000000000 : ℝ)) (X := (12501083528987272581/12500000000000000000 : ℝ)) (by norm_num) 4615 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100029068682467375837/100000000000000000000 : ℝ) ≤ (2000128983597127/2000000000000000 : ℝ) ^ (4615/1024 : ℝ) := by
    have hpowers : (100029068682467375837/100000000000000000000 : ℝ)^1024 ≤ (2000128983597127/2000000000000000 : ℝ)^4615 := by
      have hnat : (100029068682467375837 : ℕ)^1024*2000000000000000^4615 ≤ 2000128983597127^4615*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100029068682467375837 100000000000000000000 2000128983597127 2000000000000000 1024 4615 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000128983597127/2000000000000000 : ℝ)) (X := (100029068682467375837/100000000000000000000 : ℝ)) (by norm_num) 4615 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50024734566518285513/50000000000000000000 : ℝ) ≤ (5000548753628839/5000000000000000 : ℝ) ^ (4615/1024 : ℝ) := by
    have hpowers : (50024734566518285513/50000000000000000000 : ℝ)^1024 ≤ (5000548753628839/5000000000000000 : ℝ)^4615 := by
      have hnat : (50024734566518285513 : ℕ)^1024*5000000000000000^4615 ≤ 5000548753628839^4615*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024734566518285513 50000000000000000000 5000548753628839 5000000000000000 1024 4615 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000548753628839/5000000000000000 : ℝ)) (X := (50024734566518285513/50000000000000000000 : ℝ)) (by norm_num) 4615 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1083528987272581/25000000000000000000 : ℝ) ≤ ((12690308730346863263/12692500000000000000 : ℝ)+2*(452589272043/507700000000000 : ℝ)*(5381/50000 : ℝ))^(4615/1024 : ℝ) := by
    rw [show (12690308730346863263/12692500000000000000 : ℝ)+2*(452589272043/507700000000000 : ℝ)*(5381/50000 : ℝ)=(1250024041089199/1250000000000000 : ℝ) by norm_num, show 1+2*(1083528987272581/25000000000000000000 : ℝ)=(12501083528987272581/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(24734566518285513/100000000000000000000 : ℝ)+(1083528987272581/25000000000000000000 : ℝ) ≤ ((12690308730346863263/12692500000000000000 : ℝ)+(452589272043/507700000000000 : ℝ)*((15839/100000 : ℝ)+(5381/50000 : ℝ)))^(4615/1024 : ℝ) := by
    rw [show (12690308730346863263/12692500000000000000 : ℝ)+(452589272043/507700000000000 : ℝ)*((15839/100000 : ℝ)+(5381/50000 : ℝ))=(2000128983597127/2000000000000000 : ℝ) by norm_num, show 1+(24734566518285513/100000000000000000000 : ℝ)+(1083528987272581/25000000000000000000 : ℝ)=(100029068682467375837/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(24734566518285513/100000000000000000000 : ℝ) ≤ ((12690308730346863263/12692500000000000000 : ℝ)+2*(452589272043/507700000000000 : ℝ)*(15839/100000 : ℝ))^(4615/1024 : ℝ) := by
    rw [show (12690308730346863263/12692500000000000000 : ℝ)+2*(452589272043/507700000000000 : ℝ)*(15839/100000 : ℝ)=(5000548753628839/5000000000000000 : ℝ) by norm_num, show 1+2*(24734566518285513/100000000000000000000 : ℝ)=(50024734566518285513/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12690308730346863263/12692500000000000000 : ℝ)*(X 1 0+X 2 0)+(452589272043/507700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4615/1024 : ℝ)) (lo := (5381/50000 : ℝ)) (hi := (15839/100000 : ℝ)) (c := (12690308730346863263/12692500000000000000 : ℝ)) (alpha := (452589272043/507700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12690308730346863263/12692500000000000000 : ℝ)*(X 0 1+X 2 1)+(452589272043/507700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4615/1024 : ℝ)) (lo := (5381/50000 : ℝ)) (hi := (15839/100000 : ℝ)) (c := (12690308730346863263/12692500000000000000 : ℝ)) (alpha := (452589272043/507700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12690308730346863263/12692500000000000000 : ℝ)*(X 0 2+X 1 2)+(452589272043/507700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4615/1024 : ℝ)) (lo := (5381/50000 : ℝ)) (hi := (15839/100000 : ℝ)) (c := (12690308730346863263/12692500000000000000 : ℝ)) (alpha := (452589272043/507700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1799086187/10000000000 : ℝ)*X 0 0+(1357234943/2500000000 : ℝ)*X 0 1+(5218017889/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349297313/10000000000 : ℝ)*X 1 0+(-1907052797/10000000000 : ℝ)*X 1 1+(5218017831/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674648719/5000000000 : ℝ)*X 2 0+(2609008881/5000000000 : ℝ)*X 2 1+(-1907052721/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2123876533/5000000000 : ℝ)*X 0 0+(801275067/2000000000 : ℝ)*X 0 1+(450087961/1000000000 : ℝ)*X 0 2+(2123876533/5000000000 : ℝ)*X 1 0+(801275067/2000000000 : ℝ)*X 1 1+(450087961/1000000000 : ℝ)*X 1 2+(2123876533/5000000000 : ℝ)*X 2 0+(801275067/2000000000 : ℝ)*X 2 1+(450087961/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-112444669/625000000 : ℝ)*X 0 0+(2609566461/5000000000 : ℝ)*X 0 1+(2713908189/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((661695147/1250000000 : ℝ)*X 1 0+(-848627093/5000000000 : ℝ)*X 1 1+(1356954067/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((13233903/25000000 : ℝ)*X 2 0+(678477033/1250000000 : ℝ)*X 2 1+(-1697254159/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1061955039/2500000000 : ℝ)*X 0 0+(562283161/1250000000 : ℝ)*X 0 1+(4009009139/10000000000 : ℝ)*X 0 2+(1061955039/2500000000 : ℝ)*X 1 0+(562283161/1250000000 : ℝ)*X 1 1+(4009009139/10000000000 : ℝ)*X 1 2+(1061955039/2500000000 : ℝ)*X 2 0+(562283161/1250000000 : ℝ)*X 2 1+(4009009139/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2838748406798679042314159577/317312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18453953/1250000000000 : ℝ)*(base19) + (310685231/20000000000000 : ℝ)*(base23) + (720633/4000000000000 : ℝ)*(lower2) + (3871033/2500000000000 : ℝ)*(upper3) + (5559367/2500000000000 : ℝ)*(upper5) + (3381693216447107/100000000000000 : ℝ)*(major0) + (3381693216447107/100000000000000 : ℝ)*(major1) + (3381693216447107/100000000000000 : ℝ)*(major2) + (4741113442245441/100000000000000 : ℝ)*(sp0) + (4741136924730063/100000000000000 : ℝ)*(sp1) + (1185284211905037/25000000000000 : ℝ)*(sp2) + (505559396857641/25000000000000 : ℝ)*(sp3) + (12479400431/50000000000000 : ℝ)*(sp4) + (5073104953/50000000000000 : ℝ)*(sp7) + (202224773364047/10000000000000 : ℝ)*(f.failure) + (4741138401046303/100000000000000 : ℝ)*(f.sum) + (1731001212569/6346250000000000000000000000 : ℝ)*base65 + (1330978874576044859/1269250000000000000000000000000000 : ℝ)*base68 + (3525802728255205141/1269250000000000000000000000000000 : ℝ)*base69 + (1901857744170205141/1269250000000000000000000000000000 : ℝ)*base71 + (286778880417/793281250000000000000000000 : ℝ)*base74 + (3367220769996205141/1269250000000000000000000000000000 : ℝ)*base75 + (8454538430898955141/1269250000000000000000000000000000 : ℝ)*base77 + (1770673947143955141/1269250000000000000000000000000000 : ℝ)*base79 + (140473676997191/25385000000000000000000000000 : ℝ)*base81 + (3228767/500000000000000000000 : ℝ)*base90 + (3228767/500000000000000000000 : ℝ)*base92 + (3228767/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1766883296448199727478105189/317312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (563913817/50000000000000 : ℝ)*(base19) + (1254220607/100000000000000 : ℝ)*(base23) + (12679407/10000000000000 : ℝ)*(upper3) + (1793529/4000000000000 : ℝ)*(lower4) + (66890209/50000000000000 : ℝ)*(upper5) + (1708966332342867/50000000000000 : ℝ)*(major0) + (1708966332342867/50000000000000 : ℝ)*(major1) + (1708966332342867/50000000000000 : ℝ)*(major2) + (4005726183/25000000000000 : ℝ)*(sp1) + (3583789833/20000000000000 : ℝ)*(sp2) + (38335570172949/800000000000 : ℝ)*(sp4) + (4791929120886259/100000000000000 : ℝ)*(sp5) + (1197981774612213/25000000000000 : ℝ)*(sp6) + (2043918872143667/100000000000000 : ℝ)*(sp7) + (2043918872143667/100000000000000 : ℝ)*(f.failure) + (38335570172949/800000000000 : ℝ)*(f.sum) + (26577485667729/12692500000000000000000000000 : ℝ)*base66 + (3812838784990829979/634625000000000000000000000000000 : ℝ)*base68 + (1677712538179454979/634625000000000000000000000000000 : ℝ)*base70 + (7873940227398579979/634625000000000000000000000000000 : ℝ)*base72 + (10621892884967/6346250000000000000000000000 : ℝ)*base74 + (2834822684924204979/634625000000000000000000000000000 : ℝ)*base76 + (3064508262359829979/634625000000000000000000000000000 : ℝ)*base78 + (2186247572042829979/634625000000000000000000000000000 : ℝ)*base80 + (37498325730881/12692500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (27540413/5000000000000000000000 : ℝ)*base89 + (27540413/5000000000000000000000 : ℝ)*base91 + (27540413/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1560_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83612239/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15839/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5381/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2763/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3881/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1560_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1560_s4_0 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1799339313/10000000000 : ℝ)*x 0 + (2713625103/5000000000 : ℝ)*x 1 + (5219539633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1799339313/10000000000 : ℝ)^4617 ≤ (5518122460459/50000000000000 : ℝ)^3593 := by
    have hnat : (1799339313 : ℕ)^4617*50000000000000^3593 ≤ 5518122460459^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1799339313 10000000000 5518122460459 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713625103/5000000000 : ℝ)^4617 ≤ (11399228973443/25000000000000 : ℝ)^3593 := by
    have hnat : (2713625103 : ℕ)^4617*25000000000000^3593 ≤ 11399228973443^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713625103 5000000000 11399228973443 25000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219539633/10000000000 : ℝ)^4617 ≤ (10841709794543/25000000000000 : ℝ)^3593 := by
    have hnat : (5219539633 : ℕ)^4617*25000000000000^3593 ≤ 10841709794543^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219539633 10000000000 10841709794543 25000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1799339313/10000000000 : ℝ), (2713625103/5000000000 : ℝ), (5219539633/10000000000 : ℝ)] ![(5518122460459/50000000000000 : ℝ), (11399228973443/25000000000000 : ℝ), (10841709794543/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1799339313/10000000000 : ℝ)|^4617 ≤ (5518122460459/50000000000000 : ℝ)^3593
        have hw : |(-1799339313/10000000000 : ℝ)|=(1799339313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713625103/5000000000 : ℝ)|^4617 ≤ (11399228973443/25000000000000 : ℝ)^3593
        have hw : |(2713625103/5000000000 : ℝ)|=(2713625103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219539633/10000000000 : ℝ)|^4617 ≤ (10841709794543/25000000000000 : ℝ)^3593
        have hw : |(5219539633/10000000000 : ℝ)|=(5219539633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s4_1 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069770127/2000000000 : ℝ)*x 0 + (-1905624511/10000000000 : ℝ)*x 1 + (5219539587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069770127/2000000000 : ℝ)^4617 ≤ (1790090855849/4000000000000 : ℝ)^3593 := by
    have hnat : (1069770127 : ℕ)^4617*4000000000000^3593 ≤ 1790090855849^3593*2000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069770127 2000000000 1790090855849 4000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1905624511/10000000000 : ℝ)^4617 ≤ (11880889899651/100000000000000 : ℝ)^3593 := by
    have hnat : (1905624511 : ℕ)^4617*100000000000000^3593 ≤ 11880889899651^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1905624511 10000000000 11880889899651 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219539587/10000000000 : ℝ)^4617 ≤ (21683419343527/50000000000000 : ℝ)^3593 := by
    have hnat : (5219539587 : ℕ)^4617*50000000000000^3593 ≤ 21683419343527^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219539587 10000000000 21683419343527 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069770127/2000000000 : ℝ), (-1905624511/10000000000 : ℝ), (5219539587/10000000000 : ℝ)] ![(1790090855849/4000000000000 : ℝ), (11880889899651/100000000000000 : ℝ), (21683419343527/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069770127/2000000000 : ℝ)|^4617 ≤ (1790090855849/4000000000000 : ℝ)^3593
        have hw : |(1069770127/2000000000 : ℝ)|=(1069770127/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1905624511/10000000000 : ℝ)|^4617 ≤ (11880889899651/100000000000000 : ℝ)^3593
        have hw : |(-1905624511/10000000000 : ℝ)|=(1905624511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219539587/10000000000 : ℝ)|^4617 ≤ (21683419343527/50000000000000 : ℝ)^3593
        have hw : |(5219539587/10000000000 : ℝ)|=(5219539587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s4_2 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069770101/2000000000 : ℝ)*x 0 + (326221229/625000000 : ℝ)*x 1 + (-1905624583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069770101/2000000000 : ℝ)^4617 ≤ (5594033749821/12500000000000 : ℝ)^3593 := by
    have hnat : (1069770101 : ℕ)^4617*12500000000000^3593 ≤ 5594033749821^3593*2000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069770101 2000000000 5594033749821 12500000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (326221229/625000000 : ℝ)^4617 ≤ (43366839509143/100000000000000 : ℝ)^3593 := by
    have hnat : (326221229 : ℕ)^4617*100000000000000^3593 ≤ 43366839509143^3593*625000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326221229 625000000 43366839509143 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1905624583/10000000000 : ℝ)^4617 ≤ (11880890476479/100000000000000 : ℝ)^3593 := by
    have hnat : (1905624583 : ℕ)^4617*100000000000000^3593 ≤ 11880890476479^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1905624583 10000000000 11880890476479 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069770101/2000000000 : ℝ), (326221229/625000000 : ℝ), (-1905624583/10000000000 : ℝ)] ![(5594033749821/12500000000000 : ℝ), (43366839509143/100000000000000 : ℝ), (11880890476479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069770101/2000000000 : ℝ)|^4617 ≤ (5594033749821/12500000000000 : ℝ)^3593
        have hw : |(1069770101/2000000000 : ℝ)|=(1069770101/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(326221229/625000000 : ℝ)|^4617 ≤ (43366839509143/100000000000000 : ℝ)^3593
        have hw : |(326221229/625000000 : ℝ)|=(326221229/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1905624583/10000000000 : ℝ)|^4617 ≤ (11880890476479/100000000000000 : ℝ)^3593
        have hw : |(-1905624583/10000000000 : ℝ)|=(1905624583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s4_3 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530989057/1250000000 : ℝ)*x 0 + (4010121963/10000000000 : ℝ)*x 1 + (4497097499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530989057/1250000000 : ℝ)^4617 ≤ (33281746577023/100000000000000 : ℝ)^3593 := by
    have hnat : (530989057 : ℕ)^4617*100000000000000^3593 ≤ 33281746577023^3593*1250000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530989057 1250000000 33281746577023 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4010121963/10000000000 : ℝ)^4617 ≤ (3863385605059/12500000000000 : ℝ)^3593 := by
    have hnat : (4010121963 : ℕ)^4617*12500000000000^3593 ≤ 3863385605059^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4010121963 10000000000 3863385605059 12500000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4497097499/10000000000 : ℝ)^4617 ≤ (35811168561609/100000000000000 : ℝ)^3593 := by
    have hnat : (4497097499 : ℕ)^4617*100000000000000^3593 ≤ 35811168561609^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497097499 10000000000 35811168561609 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530989057/1250000000 : ℝ), (4010121963/10000000000 : ℝ), (4497097499/10000000000 : ℝ)] ![(33281746577023/100000000000000 : ℝ), (3863385605059/12500000000000 : ℝ), (35811168561609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530989057/1250000000 : ℝ)|^4617 ≤ (33281746577023/100000000000000 : ℝ)^3593
        have hw : |(530989057/1250000000 : ℝ)|=(530989057/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4010121963/10000000000 : ℝ)|^4617 ≤ (3863385605059/12500000000000 : ℝ)^3593
        have hw : |(4010121963/10000000000 : ℝ)|=(4010121963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4497097499/10000000000 : ℝ)|^4617 ≤ (35811168561609/100000000000000 : ℝ)^3593
        have hw : |(4497097499/10000000000 : ℝ)|=(4497097499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s4_4 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-359873323/2000000000 : ℝ)*x 0 + (5220621141/10000000000 : ℝ)*x 1 + (678270083/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (359873323/2000000000 : ℝ)^4617 ≤ (5518230051553/50000000000000 : ℝ)^3593 := by
    have hnat : (359873323 : ℕ)^4617*50000000000000^3593 ≤ 5518230051553^3593*2000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      359873323 2000000000 5518230051553 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5220621141/10000000000 : ℝ)^4617 ≤ (10844596555311/25000000000000 : ℝ)^3593 := by
    have hnat : (5220621141 : ℕ)^4617*25000000000000^3593 ≤ 10844596555311^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220621141 10000000000 10844596555311 25000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (678270083/1250000000 : ℝ)^4617 ≤ (45585153659269/100000000000000 : ℝ)^3593 := by
    have hnat : (678270083 : ℕ)^4617*100000000000000^3593 ≤ 45585153659269^3593*1250000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678270083 1250000000 45585153659269 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-359873323/2000000000 : ℝ), (5220621141/10000000000 : ℝ), (678270083/1250000000 : ℝ)] ![(5518230051553/50000000000000 : ℝ), (10844596555311/25000000000000 : ℝ), (45585153659269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-359873323/2000000000 : ℝ)|^4617 ≤ (5518230051553/50000000000000 : ℝ)^3593
        have hw : |(-359873323/2000000000 : ℝ)|=(359873323/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5220621141/10000000000 : ℝ)|^4617 ≤ (10844596555311/25000000000000 : ℝ)^3593
        have hw : |(5220621141/10000000000 : ℝ)|=(5220621141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(678270083/1250000000 : ℝ)|^4617 ≤ (45585153659269/100000000000000 : ℝ)^3593
        have hw : |(678270083/1250000000 : ℝ)|=(678270083/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s4_5 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646981619/5000000000 : ℝ)*x 0 + (-1699003659/10000000000 : ℝ)*x 1 + (1356540181/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646981619/5000000000 : ℝ)^4617 ≤ (8832606115091/20000000000000 : ℝ)^3593 := by
    have hnat : (2646981619 : ℕ)^4617*20000000000000^3593 ≤ 8832606115091^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646981619 5000000000 8832606115091 20000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1699003659/10000000000 : ℝ)^4617 ≤ (5125907552939/50000000000000 : ℝ)^3593 := by
    have hnat : (1699003659 : ℕ)^4617*50000000000000^3593 ≤ 5125907552939^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1699003659 10000000000 5125907552939 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356540181/2500000000 : ℝ)^4617 ≤ (9117030861397/20000000000000 : ℝ)^3593 := by
    have hnat : (1356540181 : ℕ)^4617*20000000000000^3593 ≤ 9117030861397^3593*2500000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356540181 2500000000 9117030861397 20000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646981619/5000000000 : ℝ), (-1699003659/10000000000 : ℝ), (1356540181/2500000000 : ℝ)] ![(8832606115091/20000000000000 : ℝ), (5125907552939/50000000000000 : ℝ), (9117030861397/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646981619/5000000000 : ℝ)|^4617 ≤ (8832606115091/20000000000000 : ℝ)^3593
        have hw : |(2646981619/5000000000 : ℝ)|=(2646981619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1699003659/10000000000 : ℝ)|^4617 ≤ (5125907552939/50000000000000 : ℝ)^3593
        have hw : |(-1699003659/10000000000 : ℝ)|=(1699003659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356540181/2500000000 : ℝ)|^4617 ≤ (9117030861397/20000000000000 : ℝ)^3593
        have hw : |(1356540181/2500000000 : ℝ)|=(1356540181/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s4_6 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661745407/1250000000 : ℝ)*x 0 + (2713080373/5000000000 : ℝ)*x 1 + (-1699003603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661745407/1250000000 : ℝ)^4617 ≤ (44163030768409/100000000000000 : ℝ)^3593 := by
    have hnat : (661745407 : ℕ)^4617*100000000000000^3593 ≤ 44163030768409^3593*1250000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661745407 1250000000 44163030768409 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713080373/5000000000 : ℝ)^4617 ≤ (45585154544481/100000000000000 : ℝ)^3593 := by
    have hnat : (2713080373 : ℕ)^4617*100000000000000^3593 ≤ 45585154544481^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713080373 5000000000 45585154544481 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1699003603/10000000000 : ℝ)^4617 ≤ (10251814671671/100000000000000 : ℝ)^3593 := by
    have hnat : (1699003603 : ℕ)^4617*100000000000000^3593 ≤ 10251814671671^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1699003603 10000000000 10251814671671 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661745407/1250000000 : ℝ), (2713080373/5000000000 : ℝ), (-1699003603/10000000000 : ℝ)] ![(44163030768409/100000000000000 : ℝ), (45585154544481/100000000000000 : ℝ), (10251814671671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661745407/1250000000 : ℝ)|^4617 ≤ (44163030768409/100000000000000 : ℝ)^3593
        have hw : |(661745407/1250000000 : ℝ)|=(661745407/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713080373/5000000000 : ℝ)|^4617 ≤ (45585154544481/100000000000000 : ℝ)^3593
        have hw : |(2713080373/5000000000 : ℝ)|=(2713080373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1699003603/10000000000 : ℝ)|^4617 ≤ (10251814671671/100000000000000 : ℝ)^3593
        have hw : |(-1699003603/10000000000 : ℝ)|=(1699003603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s4_7 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4247976577/10000000000 : ℝ)*x 0 + (179782469/400000000 : ℝ)*x 1 + (1003169077/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4247976577/10000000000 : ℝ)^4617 ≤ (16641196066889/50000000000000 : ℝ)^3593 := by
    have hnat : (4247976577 : ℕ)^4617*50000000000000^3593 ≤ 16641196066889^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4247976577 10000000000 16641196066889 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (179782469/400000000 : ℝ)^4617 ≤ (715704458311/2000000000000 : ℝ)^3593 := by
    have hnat : (179782469 : ℕ)^4617*2000000000000^3593 ≤ 715704458311^3593*400000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179782469 400000000 715704458311 2000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1003169077/2500000000 : ℝ)^4617 ≤ (30932384931699/100000000000000 : ℝ)^3593 := by
    have hnat : (1003169077 : ℕ)^4617*100000000000000^3593 ≤ 30932384931699^3593*2500000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003169077 2500000000 30932384931699 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4247976577/10000000000 : ℝ), (179782469/400000000 : ℝ), (1003169077/2500000000 : ℝ)] ![(16641196066889/50000000000000 : ℝ), (715704458311/2000000000000 : ℝ), (30932384931699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4247976577/10000000000 : ℝ)|^4617 ≤ (16641196066889/50000000000000 : ℝ)^3593
        have hw : |(4247976577/10000000000 : ℝ)|=(4247976577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(179782469/400000000 : ℝ)|^4617 ≤ (715704458311/2000000000000 : ℝ)^3593
        have hw : |(179782469/400000000 : ℝ)|=(179782469/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1003169077/2500000000 : ℝ)|^4617 ≤ (30932384931699/100000000000000 : ℝ)^3593
        have hw : |(1003169077/2500000000 : ℝ)|=(1003169077/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1560_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83612239/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3881/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2763/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2217/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15489/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3881/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2763/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3881/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2763/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3881/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2763/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3881/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2763/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3881/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2763/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3881/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2763/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2763/25000 : ℝ) ^ (4615/1024 : ℝ) ≤ (4885904395648503/100000000000000000000 : ℝ) := by
    have hpowers : (2763/25000 : ℝ)^4615 ≤ (4885904395648503/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2763 : ℕ)^4615*100000000000000000000^1024 ≤ 4885904395648503^1024*25000^4615 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2763 25000 4885904395648503 100000000000000000000 4615 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2763/25000 : ℝ)) (X := (4885904395648503/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4615 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3881/25000 : ℝ) ^ (4615/1024 : ℝ) ≤ (22593634805354391/100000000000000000000 : ℝ) := by
    have hpowers : (3881/25000 : ℝ)^4615 ≤ (22593634805354391/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3881 : ℕ)^4615*100000000000000000000^1024 ≤ 22593634805354391^1024*25000^4615 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3881 25000 22593634805354391 100000000000000000000 4615 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3881/25000 : ℝ)) (X := (22593634805354391/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4615 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004885904395648503/50000000000000000000 : ℝ) ≤ (1000021681369023/1000000000000000 : ℝ) ^ (4615/1024 : ℝ) := by
    have hpowers : (50004885904395648503/50000000000000000000 : ℝ)^1024 ≤ (1000021681369023/1000000000000000 : ℝ)^4615 := by
      have hnat : (50004885904395648503 : ℕ)^1024*1000000000000000^4615 ≤ 1000021681369023^4615*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004885904395648503 50000000000000000000 1000021681369023 1000000000000000 1024 4615 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000021681369023/1000000000000000 : ℝ)) (X := (50004885904395648503/50000000000000000000 : ℝ)) (by norm_num) 4615 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50013739769600501447/50000000000000000000 : ℝ) ≤ (10000609665010893/10000000000000000 : ℝ) ^ (4615/1024 : ℝ) := by
    have hpowers : (50013739769600501447/50000000000000000000 : ℝ)^1024 ≤ (10000609665010893/10000000000000000 : ℝ)^4615 := by
      have hnat : (50013739769600501447 : ℕ)^1024*10000000000000000^4615 ≤ 10000609665010893^4615*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013739769600501447 50000000000000000000 10000609665010893 10000000000000000 1024 4615 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000609665010893/10000000000000000 : ℝ)) (X := (50013739769600501447/50000000000000000000 : ℝ)) (by norm_num) 4615 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50022593634805354391/50000000000000000000 : ℝ) ≤ (2500250629082889/2500000000000000 : ℝ) ^ (4615/1024 : ℝ) := by
    have hpowers : (50022593634805354391/50000000000000000000 : ℝ)^1024 ≤ (2500250629082889/2500000000000000 : ℝ)^4615 := by
      have hnat : (50022593634805354391 : ℕ)^1024*2500000000000000^4615 ≤ 2500250629082889^4615*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022593634805354391 50000000000000000000 2500250629082889 2500000000000000 1024 4615 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500250629082889/2500000000000000 : ℝ)) (X := (50022593634805354391/50000000000000000000 : ℝ)) (by norm_num) 4615 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4885904395648503/100000000000000000000 : ℝ) ≤ ((5589035750653846701/5590000000000000000 : ℝ)+2*(392851320663/447200000000000 : ℝ)*(2763/25000 : ℝ))^(4615/1024 : ℝ) := by
    rw [show (5589035750653846701/5590000000000000000 : ℝ)+2*(392851320663/447200000000000 : ℝ)*(2763/25000 : ℝ)=(1000021681369023/1000000000000000 : ℝ) by norm_num, show 1+2*(4885904395648503/100000000000000000000 : ℝ)=(50004885904395648503/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(22593634805354391/100000000000000000000 : ℝ)+(4885904395648503/100000000000000000000 : ℝ) ≤ ((5589035750653846701/5590000000000000000 : ℝ)+(392851320663/447200000000000 : ℝ)*((3881/25000 : ℝ)+(2763/25000 : ℝ)))^(4615/1024 : ℝ) := by
    rw [show (5589035750653846701/5590000000000000000 : ℝ)+(392851320663/447200000000000 : ℝ)*((3881/25000 : ℝ)+(2763/25000 : ℝ))=(10000609665010893/10000000000000000 : ℝ) by norm_num, show 1+(22593634805354391/100000000000000000000 : ℝ)+(4885904395648503/100000000000000000000 : ℝ)=(50013739769600501447/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(22593634805354391/100000000000000000000 : ℝ) ≤ ((5589035750653846701/5590000000000000000 : ℝ)+2*(392851320663/447200000000000 : ℝ)*(3881/25000 : ℝ))^(4615/1024 : ℝ) := by
    rw [show (5589035750653846701/5590000000000000000 : ℝ)+2*(392851320663/447200000000000 : ℝ)*(3881/25000 : ℝ)=(2500250629082889/2500000000000000 : ℝ) by norm_num, show 1+2*(22593634805354391/100000000000000000000 : ℝ)=(50022593634805354391/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5589035750653846701/5590000000000000000 : ℝ)*(X 1 0+X 2 0)+(392851320663/447200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4615/1024 : ℝ)) (lo := (2763/25000 : ℝ)) (hi := (3881/25000 : ℝ)) (c := (5589035750653846701/5590000000000000000 : ℝ)) (alpha := (392851320663/447200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5589035750653846701/5590000000000000000 : ℝ)*(X 0 1+X 2 1)+(392851320663/447200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4615/1024 : ℝ)) (lo := (2763/25000 : ℝ)) (hi := (3881/25000 : ℝ)) (c := (5589035750653846701/5590000000000000000 : ℝ)) (alpha := (392851320663/447200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5589035750653846701/5590000000000000000 : ℝ)*(X 0 2+X 1 2)+(392851320663/447200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4615/1024 : ℝ)) (lo := (2763/25000 : ℝ)) (hi := (3881/25000 : ℝ)) (c := (5589035750653846701/5590000000000000000 : ℝ)) (alpha := (392851320663/447200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1799339313/10000000000 : ℝ)*X 0 0+(2713625103/5000000000 : ℝ)*X 0 1+(5219539633/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069770127/2000000000 : ℝ)*X 1 0+(-1905624511/10000000000 : ℝ)*X 1 1+(5219539587/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069770101/2000000000 : ℝ)*X 2 0+(326221229/625000000 : ℝ)*X 2 1+(-1905624583/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((530989057/1250000000 : ℝ)*X 0 0+(4010121963/10000000000 : ℝ)*X 0 1+(4497097499/10000000000 : ℝ)*X 0 2+(530989057/1250000000 : ℝ)*X 1 0+(4010121963/10000000000 : ℝ)*X 1 1+(4497097499/10000000000 : ℝ)*X 1 2+(530989057/1250000000 : ℝ)*X 2 0+(4010121963/10000000000 : ℝ)*X 2 1+(4497097499/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-359873323/2000000000 : ℝ)*X 0 0+(5220621141/10000000000 : ℝ)*X 0 1+(678270083/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2646981619/5000000000 : ℝ)*X 1 0+(-1699003659/10000000000 : ℝ)*X 1 1+(1356540181/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((661745407/1250000000 : ℝ)*X 2 0+(2713080373/5000000000 : ℝ)*X 2 1+(-1699003603/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4247976577/10000000000 : ℝ)*X 0 0+(179782469/400000000 : ℝ)*X 0 1+(1003169077/2500000000 : ℝ)*X 0 2+(4247976577/10000000000 : ℝ)*X 1 0+(179782469/400000000 : ℝ)*X 1 1+(1003169077/2500000000 : ℝ)*X 1 2+(4247976577/10000000000 : ℝ)*X 2 0+(179782469/400000000 : ℝ)*X 2 1+(1003169077/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (177300451812672651891824229/34937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (840720597/100000000000000 : ℝ)*(base19) + (697883863/100000000000000 : ℝ)*(base23) + (13813791/100000000000000 : ℝ)*(lower2) + (63216837/50000000000000 : ℝ)*(upper3) + (3607691/20000000000000 : ℝ)*(upper5) + (858490515509607/25000000000000 : ℝ)*(major0) + (858490515509607/25000000000000 : ℝ)*(major1) + (858490515509607/25000000000000 : ℝ)*(major2) + (4814407265676267/100000000000000 : ℝ)*(sp0) + (962883737046941/20000000000000 : ℝ)*(sp1) + (2407209414035719/50000000000000 : ℝ)*(sp2) + (205349732258309/10000000000000 : ℝ)*(sp3) + (2452055807/20000000000000 : ℝ)*(sp4) + (111037169/1562500000000 : ℝ)*(sp7) + (1026752214480953/50000000000000 : ℝ)*(f.failure) + (2407209762977651/50000000000000 : ℝ)*(f.sum) + (11172947371601/5590000000000000000000000000 : ℝ)*base65 + (10247997235424539/10750000000000000000000000000000 : ℝ)*base67 + (50439137453924539/10750000000000000000000000000000 : ℝ)*base69 + (9176369080424539/10750000000000000000000000000000 : ℝ)*base71 + (9190687315591/5590000000000000000000000000 : ℝ)*base73 + (54750988425924539/10750000000000000000000000000000 : ℝ)*base75 + (91316167544174539/10750000000000000000000000000000 : ℝ)*base77 + (51901804385825461/10750000000000000000000000000000 : ℝ)*base80 + (3868706187881/5590000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (3183767/2500000000000000000000 : ℝ)*base89 + (3183767/2500000000000000000000 : ℝ)*base91 + (3183767/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (702024079236003420380103069/69875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (642845477/50000000000000 : ℝ)*(base19) + (183817381/12500000000000 : ℝ)*(base23) + (8749677/4000000000000 : ℝ)*(upper3) + (33318893/50000000000000 : ℝ)*(lower4) + (192005591/100000000000000 : ℝ)*(upper5) + (867553123015641/25000000000000 : ℝ)*(major0) + (867553123015641/25000000000000 : ℝ)*(major1) + (867553123015641/25000000000000 : ℝ)*(major2) + (19286696071/100000000000000 : ℝ)*(sp1) + (2922407703/12500000000000 : ℝ)*(sp2) + (4865242514672693/100000000000000 : ℝ)*(sp4) + (4865221942285667/100000000000000 : ℝ)*(sp5) + (4865217664872021/100000000000000 : ℝ)*(sp6) + (1037591067278609/50000000000000 : ℝ)*(sp7) + (1037591067278609/50000000000000 : ℝ)*(f.failure) + (4865242514672693/100000000000000 : ℝ)*(f.sum) + (10190938766293/5590000000000000000000000000 : ℝ)*base65 + (133865664478093243/10750000000000000000000000000000 : ℝ)*base68 + (98421361457843243/10750000000000000000000000000000 : ℝ)*base70 + (8052650908593243/10750000000000000000000000000000 : ℝ)*base72 + (16585667827457/5590000000000000000000000000 : ℝ)*base74 + (168230328862593243/10750000000000000000000000000000 : ℝ)*base76 + (7658294307343243/10750000000000000000000000000000 : ℝ)*base78 + (254198361834843243/10750000000000000000000000000000 : ℝ)*base80 + (7120585998473/5590000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (35295551/2500000000000000000000 : ℝ)*base89 + (35295551/2500000000000000000000 : ℝ)*base91 + (35295551/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1560_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83612239/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3881/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2763/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2217/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1560_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1560_s5_0 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1799364747/10000000000 : ℝ)*x 0 + (2713536789/5000000000 : ℝ)*x 1 + (2609849729/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1799364747/10000000000 : ℝ)^4617 ≤ (11036445380333/100000000000000 : ℝ)^3593 := by
    have hnat : (1799364747 : ℕ)^4617*100000000000000^3593 ≤ 11036445380333^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1799364747 10000000000 11036445380333 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713536789/5000000000 : ℝ)^4617 ≤ (45595009046897/100000000000000 : ℝ)^3593 := by
    have hnat : (2713536789 : ℕ)^4617*100000000000000^3593 ≤ 45595009046897^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713536789 5000000000 45595009046897 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609849729/5000000000 : ℝ)^4617 ≤ (43368545554569/100000000000000 : ℝ)^3593 := by
    have hnat : (2609849729 : ℕ)^4617*100000000000000^3593 ≤ 43368545554569^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609849729 5000000000 43368545554569 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1799364747/10000000000 : ℝ), (2713536789/5000000000 : ℝ), (2609849729/5000000000 : ℝ)] ![(11036445380333/100000000000000 : ℝ), (45595009046897/100000000000000 : ℝ), (43368545554569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1799364747/10000000000 : ℝ)|^4617 ≤ (11036445380333/100000000000000 : ℝ)^3593
        have hw : |(-1799364747/10000000000 : ℝ)|=(1799364747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713536789/5000000000 : ℝ)|^4617 ≤ (45595009046897/100000000000000 : ℝ)^3593
        have hw : |(2713536789/5000000000 : ℝ)|=(2713536789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609849729/5000000000 : ℝ)|^4617 ≤ (43368545554569/100000000000000 : ℝ)^3593
        have hw : |(2609849729/5000000000 : ℝ)|=(2609849729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s5_1 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348804097/10000000000 : ℝ)*x 0 + (-476368479/2500000000 : ℝ)*x 1 + (2609849727/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348804097/10000000000 : ℝ)^4617 ≤ (44751771057121/100000000000000 : ℝ)^3593 := by
    have hnat : (5348804097 : ℕ)^4617*100000000000000^3593 ≤ 44751771057121^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348804097 10000000000 44751771057121 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (476368479/2500000000 : ℝ)^4617 ≤ (11879683420113/100000000000000 : ℝ)^3593 := by
    have hnat : (476368479 : ℕ)^4617*100000000000000^3593 ≤ 11879683420113^3593*2500000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      476368479 2500000000 11879683420113 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609849727/5000000000 : ℝ)^4617 ≤ (43368545511863/100000000000000 : ℝ)^3593 := by
    have hnat : (2609849727 : ℕ)^4617*100000000000000^3593 ≤ 43368545511863^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609849727 5000000000 43368545511863 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348804097/10000000000 : ℝ), (-476368479/2500000000 : ℝ), (2609849727/5000000000 : ℝ)] ![(44751771057121/100000000000000 : ℝ), (11879683420113/100000000000000 : ℝ), (43368545511863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348804097/10000000000 : ℝ)|^4617 ≤ (44751771057121/100000000000000 : ℝ)^3593
        have hw : |(5348804097/10000000000 : ℝ)|=(5348804097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-476368479/2500000000 : ℝ)|^4617 ≤ (11879683420113/100000000000000 : ℝ)^3593
        have hw : |(-476368479/2500000000 : ℝ)|=(476368479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609849727/5000000000 : ℝ)|^4617 ≤ (43368545511863/100000000000000 : ℝ)^3593
        have hw : |(2609849727/5000000000 : ℝ)|=(2609849727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s5_2 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348804069/10000000000 : ℝ)*x 0 + (5219699491/10000000000 : ℝ)*x 1 + (-1905473903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348804069/10000000000 : ℝ)^4617 ≤ (5593971344511/12500000000000 : ℝ)^3593 := by
    have hnat : (5348804069 : ℕ)^4617*12500000000000^3593 ≤ 5593971344511^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348804069 10000000000 5593971344511 12500000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219699491/10000000000 : ℝ)^4617 ≤ (2710534119181/6250000000000 : ℝ)^3593 := by
    have hnat : (5219699491 : ℕ)^4617*6250000000000^3593 ≤ 2710534119181^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219699491 10000000000 2710534119181 6250000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1905473903/10000000000 : ℝ)^4617 ≤ (5939841657983/50000000000000 : ℝ)^3593 := by
    have hnat : (1905473903 : ℕ)^4617*50000000000000^3593 ≤ 5939841657983^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1905473903 10000000000 5939841657983 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348804069/10000000000 : ℝ), (5219699491/10000000000 : ℝ), (-1905473903/10000000000 : ℝ)] ![(5593971344511/12500000000000 : ℝ), (2710534119181/6250000000000 : ℝ), (5939841657983/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348804069/10000000000 : ℝ)|^4617 ≤ (5593971344511/12500000000000 : ℝ)^3593
        have hw : |(5348804069/10000000000 : ℝ)|=(5348804069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219699491/10000000000 : ℝ)|^4617 ≤ (2710534119181/6250000000000 : ℝ)^3593
        have hw : |(5219699491/10000000000 : ℝ)|=(5219699491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1905473903/10000000000 : ℝ)|^4617 ≤ (5939841657983/50000000000000 : ℝ)^3593
        have hw : |(-1905473903/10000000000 : ℝ)|=(1905473903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s5_3 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4247929221/10000000000 : ℝ)*x 0 + (4010514537/10000000000 : ℝ)*x 1 + (1124175259/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4247929221/10000000000 : ℝ)^4617 ≤ (33281915363253/100000000000000 : ℝ)^3593 := by
    have hnat : (4247929221 : ℕ)^4617*100000000000000^3593 ≤ 33281915363253^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4247929221 10000000000 33281915363253 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4010514537/10000000000 : ℝ)^4617 ≤ (30910972880359/100000000000000 : ℝ)^3593 := by
    have hnat : (4010514537 : ℕ)^4617*100000000000000^3593 ≤ 30910972880359^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4010514537 10000000000 30910972880359 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1124175259/2500000000 : ℝ)^4617 ≤ (17903555869333/50000000000000 : ℝ)^3593 := by
    have hnat : (1124175259 : ℕ)^4617*50000000000000^3593 ≤ 17903555869333^3593*2500000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124175259 2500000000 17903555869333 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4247929221/10000000000 : ℝ), (4010514537/10000000000 : ℝ), (1124175259/2500000000 : ℝ)] ![(33281915363253/100000000000000 : ℝ), (30910972880359/100000000000000 : ℝ), (17903555869333/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4247929221/10000000000 : ℝ)|^4617 ≤ (33281915363253/100000000000000 : ℝ)^3593
        have hw : |(4247929221/10000000000 : ℝ)|=(4247929221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4010514537/10000000000 : ℝ)|^4617 ≤ (30910972880359/100000000000000 : ℝ)^3593
        have hw : |(4010514537/10000000000 : ℝ)|=(4010514537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1124175259/2500000000 : ℝ)|^4617 ≤ (17903555869333/50000000000000 : ℝ)^3593
        have hw : |(1124175259/2500000000 : ℝ)|=(1124175259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s5_4 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-899695839/5000000000 : ℝ)*x 0 + (5220777581/10000000000 : ℝ)*x 1 + (5425987637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (899695839/5000000000 : ℝ)^4617 ≤ (5518328819657/50000000000000 : ℝ)^3593 := by
    have hnat : (899695839 : ℕ)^4617*50000000000000^3593 ≤ 5518328819657^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899695839 5000000000 5518328819657 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5220777581/10000000000 : ℝ)^4617 ≤ (43380056556057/100000000000000 : ℝ)^3593 := by
    have hnat : (5220777581 : ℕ)^4617*100000000000000^3593 ≤ 43380056556057^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220777581 10000000000 43380056556057 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5425987637/10000000000 : ℝ)^4617 ≤ (45583285794907/100000000000000 : ℝ)^3593 := by
    have hnat : (5425987637 : ℕ)^4617*100000000000000^3593 ≤ 45583285794907^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425987637 10000000000 45583285794907 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-899695839/5000000000 : ℝ), (5220777581/10000000000 : ℝ), (5425987637/10000000000 : ℝ)] ![(5518328819657/50000000000000 : ℝ), (43380056556057/100000000000000 : ℝ), (45583285794907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-899695839/5000000000 : ℝ)|^4617 ≤ (5518328819657/50000000000000 : ℝ)^3593
        have hw : |(-899695839/5000000000 : ℝ)|=(899695839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5220777581/10000000000 : ℝ)|^4617 ≤ (43380056556057/100000000000000 : ℝ)^3593
        have hw : |(5220777581/10000000000 : ℝ)|=(5220777581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5425987637/10000000000 : ℝ)|^4617 ≤ (45583285794907/100000000000000 : ℝ)^3593
        have hw : |(5425987637/10000000000 : ℝ)|=(5425987637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s5_5 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647003039/5000000000 : ℝ)*x 0 + (-1699185477/10000000000 : ℝ)*x 1 + (5425987591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647003039/5000000000 : ℝ)^4617 ≤ (44163489805789/100000000000000 : ℝ)^3593 := by
    have hnat : (2647003039 : ℕ)^4617*100000000000000^3593 ≤ 44163489805789^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647003039 5000000000 44163489805789 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1699185477/10000000000 : ℝ)^4617 ≤ (5126612444987/50000000000000 : ℝ)^3593 := by
    have hnat : (1699185477 : ℕ)^4617*50000000000000^3593 ≤ 5126612444987^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1699185477 10000000000 5126612444987 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5425987591/10000000000 : ℝ)^4617 ≤ (45583285298329/100000000000000 : ℝ)^3593 := by
    have hnat : (5425987591 : ℕ)^4617*100000000000000^3593 ≤ 45583285298329^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425987591 10000000000 45583285298329 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647003039/5000000000 : ℝ), (-1699185477/10000000000 : ℝ), (5425987591/10000000000 : ℝ)] ![(44163489805789/100000000000000 : ℝ), (5126612444987/50000000000000 : ℝ), (45583285298329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647003039/5000000000 : ℝ)|^4617 ≤ (44163489805789/100000000000000 : ℝ)^3593
        have hw : |(2647003039/5000000000 : ℝ)|=(2647003039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1699185477/10000000000 : ℝ)|^4617 ≤ (5126612444987/50000000000000 : ℝ)^3593
        have hw : |(-1699185477/10000000000 : ℝ)|=(1699185477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5425987591/10000000000 : ℝ)|^4617 ≤ (45583285298329/100000000000000 : ℝ)^3593
        have hw : |(5425987591/10000000000 : ℝ)|=(5425987591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s5_6 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647003029/5000000000 : ℝ)*x 0 + (2712993743/5000000000 : ℝ)*x 1 + (-33983713/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647003029/5000000000 : ℝ)^4617 ≤ (11040872397849/25000000000000 : ℝ)^3593 := by
    have hnat : (2647003029 : ℕ)^4617*25000000000000^3593 ≤ 11040872397849^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647003029 5000000000 11040872397849 25000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2712993743/5000000000 : ℝ)^4617 ≤ (11395821041209/25000000000000 : ℝ)^3593 := by
    have hnat : (2712993743 : ℕ)^4617*25000000000000^3593 ≤ 11395821041209^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712993743 5000000000 11395821041209 25000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33983713/200000000 : ℝ)^4617 ≤ (5126613115703/50000000000000 : ℝ)^3593 := by
    have hnat : (33983713 : ℕ)^4617*50000000000000^3593 ≤ 5126613115703^3593*200000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33983713 200000000 5126613115703 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647003029/5000000000 : ℝ), (2712993743/5000000000 : ℝ), (-33983713/200000000 : ℝ)] ![(11040872397849/25000000000000 : ℝ), (11395821041209/25000000000000 : ℝ), (5126613115703/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647003029/5000000000 : ℝ)|^4617 ≤ (11040872397849/25000000000000 : ℝ)^3593
        have hw : |(2647003029/5000000000 : ℝ)|=(2647003029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2712993743/5000000000 : ℝ)|^4617 ≤ (11395821041209/25000000000000 : ℝ)^3593
        have hw : |(2712993743/5000000000 : ℝ)|=(2712993743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-33983713/200000000 : ℝ)|^4617 ≤ (5126613115703/50000000000000 : ℝ)^3593
        have hw : |(-33983713/200000000 : ℝ)|=(33983713/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s5_7 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530999093/1250000000 : ℝ)*x 0 + (1123543337/2500000000 : ℝ)*x 1 + (2006530501/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530999093/1250000000 : ℝ)^4617 ≤ (2080159681261/6250000000000 : ℝ)^3593 := by
    have hnat : (530999093 : ℕ)^4617*6250000000000^3593 ≤ 2080159681261^3593*1250000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530999093 1250000000 2080159681261 6250000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1123543337/2500000000 : ℝ)^4617 ≤ (7156249894139/20000000000000 : ℝ)^3593 := by
    have hnat : (1123543337 : ℕ)^4617*20000000000000^3593 ≤ 7156249894139^3593*2500000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123543337 2500000000 7156249894139 20000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2006530501/5000000000 : ℝ)^4617 ≤ (7734048904681/25000000000000 : ℝ)^3593 := by
    have hnat : (2006530501 : ℕ)^4617*25000000000000^3593 ≤ 7734048904681^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2006530501 5000000000 7734048904681 25000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530999093/1250000000 : ℝ), (1123543337/2500000000 : ℝ), (2006530501/5000000000 : ℝ)] ![(2080159681261/6250000000000 : ℝ), (7156249894139/20000000000000 : ℝ), (7734048904681/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530999093/1250000000 : ℝ)|^4617 ≤ (2080159681261/6250000000000 : ℝ)^3593
        have hw : |(530999093/1250000000 : ℝ)|=(530999093/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1123543337/2500000000 : ℝ)|^4617 ≤ (7156249894139/20000000000000 : ℝ)^3593
        have hw : |(1123543337/2500000000 : ℝ)|=(1123543337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2006530501/5000000000 : ℝ)|^4617 ≤ (7734048904681/25000000000000 : ℝ)^3593
        have hw : |(2006530501/5000000000 : ℝ)|=(2006530501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1560_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83612239/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2217/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (693/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2217/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2217/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2217/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2217/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2217/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2217/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2217/20000 : ℝ) ^ (4615/1024 : ℝ) ≤ (154749955618657/3125000000000000000 : ℝ) := by
    have hpowers : (2217/20000 : ℝ)^4615 ≤ (154749955618657/3125000000000000000 : ℝ)^1024 := by
      have hnat : (2217 : ℕ)^4615*3125000000000000000^1024 ≤ 154749955618657^1024*20000^4615 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2217 20000 154749955618657 3125000000000000000 4615 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2217/20000 : ℝ)) (X := (154749955618657/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4615 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15489/100000 : ℝ) ^ (4615/1024 : ℝ) ≤ (22364966881582407/100000000000000000000 : ℝ) := by
    have hpowers : (15489/100000 : ℝ)^4615 ≤ (22364966881582407/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15489 : ℕ)^4615*100000000000000000000^1024 ≤ 22364966881582407^1024*100000^4615 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15489 100000 22364966881582407 100000000000000000000 4615 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15489/100000 : ℝ)) (X := (22364966881582407/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4615 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562654749955618657/1562500000000000000 : ℝ) ≤ (1000021974652941/1000000000000000 : ℝ) ^ (4615/1024 : ℝ) := by
    have hpowers : (1562654749955618657/1562500000000000000 : ℝ)^1024 ≤ (1000021974652941/1000000000000000 : ℝ)^4615 := by
      have hnat : (1562654749955618657 : ℕ)^1024*1000000000000000^4615 ≤ 1000021974652941^4615*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562654749955618657 1562500000000000000 1000021974652941 1000000000000000 1024 4615 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000021974652941/1000000000000000 : ℝ)) (X := (1562654749955618657/1562500000000000000 : ℝ)) (by norm_num) 4615 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100027316965461379431/100000000000000000000 : ℝ) ≤ (2500151514627441/2500000000000000 : ℝ) ^ (4615/1024 : ℝ) := by
    have hpowers : (100027316965461379431/100000000000000000000 : ℝ)^1024 ≤ (2500151514627441/2500000000000000 : ℝ)^4615 := by
      have hnat : (100027316965461379431 : ℕ)^1024*2500000000000000^4615 ≤ 2500151514627441^4615*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100027316965461379431 100000000000000000000 2500151514627441 2500000000000000 1024 4615 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500151514627441/2500000000000000 : ℝ)) (X := (100027316965461379431/100000000000000000000 : ℝ)) (by norm_num) 4615 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50022364966881582407/50000000000000000000 : ℝ) ≤ (5000496185245059/5000000000000000 : ℝ) ^ (4615/1024 : ℝ) := by
    have hpowers : (50022364966881582407/50000000000000000000 : ℝ)^1024 ≤ (5000496185245059/5000000000000000 : ℝ)^4615 := by
      have hnat : (50022364966881582407 : ℕ)^1024*5000000000000000^4615 ≤ 5000496185245059^4615*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022364966881582407 50000000000000000000 5000496185245059 5000000000000000 1024 4615 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000496185245059/5000000000000000 : ℝ)) (X := (50022364966881582407/50000000000000000000 : ℝ)) (by norm_num) 4615 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(154749955618657/3125000000000000000 : ℝ) ≤ ((733873387118517891/734000000000000000 : ℝ)+2*(64385330059/73400000000000 : ℝ)*(2217/20000 : ℝ))^(4615/1024 : ℝ) := by
    rw [show (733873387118517891/734000000000000000 : ℝ)+2*(64385330059/73400000000000 : ℝ)*(2217/20000 : ℝ)=(1000021974652941/1000000000000000 : ℝ) by norm_num, show 1+2*(154749955618657/3125000000000000000 : ℝ)=(1562654749955618657/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(22364966881582407/100000000000000000000 : ℝ)+(154749955618657/3125000000000000000 : ℝ) ≤ ((733873387118517891/734000000000000000 : ℝ)+(64385330059/73400000000000 : ℝ)*((15489/100000 : ℝ)+(2217/20000 : ℝ)))^(4615/1024 : ℝ) := by
    rw [show (733873387118517891/734000000000000000 : ℝ)+(64385330059/73400000000000 : ℝ)*((15489/100000 : ℝ)+(2217/20000 : ℝ))=(2500151514627441/2500000000000000 : ℝ) by norm_num, show 1+(22364966881582407/100000000000000000000 : ℝ)+(154749955618657/3125000000000000000 : ℝ)=(100027316965461379431/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(22364966881582407/100000000000000000000 : ℝ) ≤ ((733873387118517891/734000000000000000 : ℝ)+2*(64385330059/73400000000000 : ℝ)*(15489/100000 : ℝ))^(4615/1024 : ℝ) := by
    rw [show (733873387118517891/734000000000000000 : ℝ)+2*(64385330059/73400000000000 : ℝ)*(15489/100000 : ℝ)=(5000496185245059/5000000000000000 : ℝ) by norm_num, show 1+2*(22364966881582407/100000000000000000000 : ℝ)=(50022364966881582407/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (733873387118517891/734000000000000000 : ℝ)*(X 1 0+X 2 0)+(64385330059/73400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4615/1024 : ℝ)) (lo := (2217/20000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (733873387118517891/734000000000000000 : ℝ)) (alpha := (64385330059/73400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (733873387118517891/734000000000000000 : ℝ)*(X 0 1+X 2 1)+(64385330059/73400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4615/1024 : ℝ)) (lo := (2217/20000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (733873387118517891/734000000000000000 : ℝ)) (alpha := (64385330059/73400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (733873387118517891/734000000000000000 : ℝ)*(X 0 2+X 1 2)+(64385330059/73400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4615/1024 : ℝ)) (lo := (2217/20000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (733873387118517891/734000000000000000 : ℝ)) (alpha := (64385330059/73400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1799364747/10000000000 : ℝ)*X 0 0+(2713536789/5000000000 : ℝ)*X 0 1+(2609849729/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348804097/10000000000 : ℝ)*X 1 0+(-476368479/2500000000 : ℝ)*X 1 1+(2609849727/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348804069/10000000000 : ℝ)*X 2 0+(5219699491/10000000000 : ℝ)*X 2 1+(-1905473903/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4247929221/10000000000 : ℝ)*X 0 0+(4010514537/10000000000 : ℝ)*X 0 1+(1124175259/2500000000 : ℝ)*X 0 2+(4247929221/10000000000 : ℝ)*X 1 0+(4010514537/10000000000 : ℝ)*X 1 1+(1124175259/2500000000 : ℝ)*X 1 2+(4247929221/10000000000 : ℝ)*X 2 0+(4010514537/10000000000 : ℝ)*X 2 1+(1124175259/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-899695839/5000000000 : ℝ)*X 0 0+(5220777581/10000000000 : ℝ)*X 0 1+(5425987637/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647003039/5000000000 : ℝ)*X 1 0+(-1699185477/10000000000 : ℝ)*X 1 1+(5425987591/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647003029/5000000000 : ℝ)*X 2 0+(2712993743/5000000000 : ℝ)*X 2 1+(-33983713/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((530999093/1250000000 : ℝ)*X 0 0+(1123543337/2500000000 : ℝ)*X 0 1+(2006530501/5000000000 : ℝ)*X 0 2+(530999093/1250000000 : ℝ)*X 1 0+(1123543337/2500000000 : ℝ)*X 1 1+(2006530501/5000000000 : ℝ)*X 1 2+(530999093/1250000000 : ℝ)*X 2 0+(1123543337/2500000000 : ℝ)*X 2 1+(2006530501/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (86621625524524315667862597/9175000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (63013597/4000000000000 : ℝ)*(base19) + (718536161/50000000000000 : ℝ)*(base23) + (15113581/25000000000000 : ℝ)*(lower2) + (114566909/50000000000000 : ℝ)*(upper3) + (15620843/10000000000000 : ℝ)*(upper5) + (1719775127420989/50000000000000 : ℝ)*(major0) + (1719775127420989/50000000000000 : ℝ)*(major1) + (1719775127420989/50000000000000 : ℝ)*(major2) + (482222873040533/10000000000000 : ℝ)*(sp0) + (150695389354127/3125000000000 : ℝ)*(sp1) + (4822252597599667/100000000000000 : ℝ)*(sp2) + (2056834414053429/100000000000000 : ℝ)*(sp3) + (1265213333/5000000000000 : ℝ)*(sp4) + (2936564223/25000000000000 : ℝ)*(sp7) + (2056846160310321/100000000000000 : ℝ)*(f.failure) + (482225403467199/10000000000000 : ℝ)*(f.sum) + (798730726797/917500000000000000000000000 : ℝ)*base66 + (238495407027375801/36700000000000000000000000000000 : ℝ)*base68 + (22711877650675801/36700000000000000000000000000000 : ℝ)*base70 + (51464882363424199/36700000000000000000000000000000 : ℝ)*base71 + (259473231839/114687500000000000000000000 : ℝ)*base74 + (464319289153875801/36700000000000000000000000000000 : ℝ)*base76 + (266943540147075801/36700000000000000000000000000000 : ℝ)*base78 + (84889366227275801/36700000000000000000000000000000 : ℝ)*base80 + (1740905181153/917500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (26381281/5000000000000000000000 : ℝ)*base90 + (26381281/5000000000000000000000 : ℝ)*base92 + (26381281/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4265870070861418483677/734000000000000000000000000 : ℝ) := by norm_num
    linear_combination (259773281/25000000000000 : ℝ)*(base19) + (3795087/312500000000 : ℝ)*(base23) + (191695507/50000000000000 : ℝ)*(lower1) + (485881/5000000000000 : ℝ)*(upper3) + (23688471/20000000000000 : ℝ)*(lower4) + (21090629/20000000000000 : ℝ)*(upper5) + (695154414339323/20000000000000 : ℝ)*(major0) + (695154414339323/20000000000000 : ℝ)*(major1) + (695154414339323/20000000000000 : ℝ)*(major2) + (72420403/2500000000000 : ℝ)*(sp1) + (4873037194395187/100000000000000 : ℝ)*(sp4) + (4873033258485943/100000000000000 : ℝ)*(sp5) + (4873035979967347/100000000000000 : ℝ)*(sp6) + (2078506755270969/100000000000000 : ℝ)*(sp7) + (2078506755270969/100000000000000 : ℝ)*(f.failure) + (4873037194395187/100000000000000 : ℝ)*(f.sum) + (5119962030043/734000000000000000000000000 : ℝ)*base66 + (35700311269222207/14680000000000000000000000000000 : ℝ)*base68 + (54697951735862207/14680000000000000000000000000000 : ℝ)*base70 + (41458060807502207/14680000000000000000000000000000 : ℝ)*base72 + (3358775514997/734000000000000000000000000 : ℝ)*base74 + (66940107329817793/14680000000000000000000000000000 : ℝ)*base75 + (55004469750737793/14680000000000000000000000000000 : ℝ)*base77 + (105716283244177793/14680000000000000000000000000000 : ℝ)*base79 + (702630358947/146800000000000000000000000 : ℝ)*base82 + (19789591/5000000000000000000000 : ℝ)*base89 + (19789591/5000000000000000000000 : ℝ)*base91 + (19789591/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1560_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83612239/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2217/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (693/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1560_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1560_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83612239/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15839/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5381/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (693/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1560_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1560_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1560_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83612239/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15839/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5381/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (693/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1560_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
