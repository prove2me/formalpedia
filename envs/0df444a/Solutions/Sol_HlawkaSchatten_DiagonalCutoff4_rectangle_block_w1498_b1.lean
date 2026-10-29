-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1498_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:51:39.894999+00:00
-- url     : https://prove2.me/submissions/31d23d23-99bd-4887-9a3a-b416bdb1052b

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
theorem support_rectangle_w1498_s3_0 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1888312913/10000000000 : ℝ)*x 0 + (5438903087/10000000000 : ℝ)*x 1 + (5213442167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1888312913/10000000000 : ℝ)^4493 ≤ (11544660893049/100000000000000 : ℝ)^3469 := by
    have hnat : (1888312913 : ℕ)^4493*100000000000000^3469 ≤ 11544660893049^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1888312913 10000000000 11544660893049 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438903087/10000000000 : ℝ)^4493 ≤ (22719982222499/50000000000000 : ℝ)^3469 := by
    have hnat : (5438903087 : ℕ)^4493*50000000000000^3469 ≤ 22719982222499^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438903087 10000000000 22719982222499 50000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5213442167/10000000000 : ℝ)^4493 ≤ (21507687322871/50000000000000 : ℝ)^3469 := by
    have hnat : (5213442167 : ℕ)^4493*50000000000000^3469 ≤ 21507687322871^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5213442167 10000000000 21507687322871 50000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1888312913/10000000000 : ℝ), (5438903087/10000000000 : ℝ), (5213442167/10000000000 : ℝ)] ![(11544660893049/100000000000000 : ℝ), (22719982222499/50000000000000 : ℝ), (21507687322871/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1888312913/10000000000 : ℝ)|^4493 ≤ (11544660893049/100000000000000 : ℝ)^3469
        have hw : |(-1888312913/10000000000 : ℝ)|=(1888312913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438903087/10000000000 : ℝ)|^4493 ≤ (22719982222499/50000000000000 : ℝ)^3469
        have hw : |(5438903087/10000000000 : ℝ)|=(5438903087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5213442167/10000000000 : ℝ)|^4493 ≤ (21507687322871/50000000000000 : ℝ)^3469
        have hw : |(5213442167/10000000000 : ℝ)|=(5213442167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s3_1 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338339949/2500000000 : ℝ)*x 0 + (-2003908373/10000000000 : ℝ)*x 1 + (41707537/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338339949/2500000000 : ℝ)^4493 ≤ (11129118899031/25000000000000 : ℝ)^3469 := by
    have hnat : (1338339949 : ℕ)^4493*25000000000000^3469 ≤ 11129118899031^3469*2500000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338339949 2500000000 11129118899031 25000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2003908373/10000000000 : ℝ)^4493 ≤ (2493630037133/20000000000000 : ℝ)^3469 := by
    have hnat : (2003908373 : ℕ)^4493*20000000000000^3469 ≤ 2493630037133^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2003908373 10000000000 2493630037133 20000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41707537/80000000 : ℝ)^4493 ≤ (43015374196913/100000000000000 : ℝ)^3469 := by
    have hnat : (41707537 : ℕ)^4493*100000000000000^3469 ≤ 43015374196913^3469*80000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41707537 80000000 43015374196913 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338339949/2500000000 : ℝ), (-2003908373/10000000000 : ℝ), (41707537/80000000 : ℝ)] ![(11129118899031/25000000000000 : ℝ), (2493630037133/20000000000000 : ℝ), (43015374196913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338339949/2500000000 : ℝ)|^4493 ≤ (11129118899031/25000000000000 : ℝ)^3469
        have hw : |(1338339949/2500000000 : ℝ)|=(1338339949/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2003908373/10000000000 : ℝ)|^4493 ≤ (2493630037133/20000000000000 : ℝ)^3469
        have hw : |(-2003908373/10000000000 : ℝ)|=(2003908373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41707537/80000000 : ℝ)|^4493 ≤ (43015374196913/100000000000000 : ℝ)^3469
        have hw : |(41707537/80000000 : ℝ)|=(41707537/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s3_2 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070672031/2000000000 : ℝ)*x 0 + (5213441779/10000000000 : ℝ)*x 1 + (-2003908353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070672031/2000000000 : ℝ)^4493 ≤ (890329589253/2000000000000 : ℝ)^3469 := by
    have hnat : (1070672031 : ℕ)^4493*2000000000000^3469 ≤ 890329589253^3469*2000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070672031 2000000000 890329589253 2000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5213441779/10000000000 : ℝ)^4493 ≤ (2150768524971/5000000000000 : ℝ)^3469 := by
    have hnat : (5213441779 : ℕ)^4493*5000000000000^3469 ≤ 2150768524971^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5213441779 10000000000 2150768524971 5000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2003908353/10000000000 : ℝ)^4493 ≤ (6234075012247/50000000000000 : ℝ)^3469 := by
    have hnat : (2003908353 : ℕ)^4493*50000000000000^3469 ≤ 6234075012247^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2003908353 10000000000 6234075012247 50000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070672031/2000000000 : ℝ), (5213441779/10000000000 : ℝ), (-2003908353/10000000000 : ℝ)] ![(890329589253/2000000000000 : ℝ), (2150768524971/5000000000000 : ℝ), (6234075012247/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070672031/2000000000 : ℝ)|^4493 ≤ (890329589253/2000000000000 : ℝ)^3469
        have hw : |(1070672031/2000000000 : ℝ)|=(1070672031/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5213441779/10000000000 : ℝ)|^4493 ≤ (2150768524971/5000000000000 : ℝ)^3469
        have hw : |(5213441779/10000000000 : ℝ)|=(5213441779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2003908353/10000000000 : ℝ)|^4493 ≤ (6234075012247/50000000000000 : ℝ)^3469
        have hw : |(-2003908353/10000000000 : ℝ)|=(2003908353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s3_3 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4275970051/10000000000 : ℝ)*x 0 + (2014648477/5000000000 : ℝ)*x 1 + (566938809/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4275970051/10000000000 : ℝ)^4493 ≤ (2079702876787/6250000000000 : ℝ)^3469 := by
    have hnat : (4275970051 : ℕ)^4493*6250000000000^3469 ≤ 2079702876787^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4275970051 10000000000 2079702876787 6250000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2014648477/5000000000 : ℝ)^4493 ≤ (3081048331801/10000000000000 : ℝ)^3469 := by
    have hnat : (2014648477 : ℕ)^4493*10000000000000^3469 ≤ 3081048331801^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014648477 5000000000 3081048331801 10000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (566938809/1250000000 : ℝ)^4493 ≤ (224464191467/625000000000 : ℝ)^3469 := by
    have hnat : (566938809 : ℕ)^4493*625000000000^3469 ≤ 224464191467^3469*1250000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566938809 1250000000 224464191467 625000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4275970051/10000000000 : ℝ), (2014648477/5000000000 : ℝ), (566938809/1250000000 : ℝ)] ![(2079702876787/6250000000000 : ℝ), (3081048331801/10000000000000 : ℝ), (224464191467/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4275970051/10000000000 : ℝ)|^4493 ≤ (2079702876787/6250000000000 : ℝ)^3469
        have hw : |(4275970051/10000000000 : ℝ)|=(4275970051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2014648477/5000000000 : ℝ)|^4493 ≤ (3081048331801/10000000000000 : ℝ)^3469
        have hw : |(2014648477/5000000000 : ℝ)|=(2014648477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(566938809/1250000000 : ℝ)|^4493 ≤ (224464191467/625000000000 : ℝ)^3469
        have hw : |(566938809/1250000000 : ℝ)|=(566938809/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s3_4 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1888344783/10000000000 : ℝ)*x 0 + (52146379/100000000 : ℝ)*x 1 + (1359424701/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1888344783/10000000000 : ℝ)^4493 ≤ (1154491325419/10000000000000 : ℝ)^3469 := by
    have hnat : (1888344783 : ℕ)^4493*10000000000000^3469 ≤ 1154491325419^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1888344783 10000000000 1154491325419 10000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52146379/100000000 : ℝ)^4493 ≤ (1075703828869/2500000000000 : ℝ)^3469 := by
    have hnat : (52146379 : ℕ)^4493*2500000000000^3469 ≤ 1075703828869^3469*100000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52146379 100000000 1075703828869 2500000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1359424701/2500000000 : ℝ)^4493 ≤ (22713466791533/50000000000000 : ℝ)^3469 := by
    have hnat : (1359424701 : ℕ)^4493*50000000000000^3469 ≤ 22713466791533^3469*2500000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359424701 2500000000 22713466791533 50000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1888344783/10000000000 : ℝ), (52146379/100000000 : ℝ), (1359424701/2500000000 : ℝ)] ![(1154491325419/10000000000000 : ℝ), (1075703828869/2500000000000 : ℝ), (22713466791533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1888344783/10000000000 : ℝ)|^4493 ≤ (1154491325419/10000000000000 : ℝ)^3469
        have hw : |(-1888344783/10000000000 : ℝ)|=(1888344783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(52146379/100000000 : ℝ)|^4493 ≤ (1075703828869/2500000000000 : ℝ)^3469
        have hw : |(52146379/100000000 : ℝ)|=(52146379/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1359424701/2500000000 : ℝ)|^4493 ≤ (22713466791533/50000000000000 : ℝ)^3469
        have hw : |(1359424701/2500000000 : ℝ)|=(1359424701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s3_5 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294299849/10000000000 : ℝ)*x 0 + (-355930353/2000000000 : ℝ)*x 1 + (5437698811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294299849/10000000000 : ℝ)^4493 ≤ (43881422653019/100000000000000 : ℝ)^3469 := by
    have hnat : (5294299849 : ℕ)^4493*100000000000000^3469 ≤ 43881422653019^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294299849 10000000000 43881422653019 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (355930353/2000000000 : ℝ)^4493 ≤ (10691643671857/100000000000000 : ℝ)^3469 := by
    have hnat : (355930353 : ℕ)^4493*100000000000000^3469 ≤ 10691643671857^3469*2000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      355930353 2000000000 10691643671857 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5437698811/10000000000 : ℝ)^4493 ≤ (45426933658807/100000000000000 : ℝ)^3469 := by
    have hnat : (5437698811 : ℕ)^4493*100000000000000^3469 ≤ 45426933658807^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437698811 10000000000 45426933658807 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294299849/10000000000 : ℝ), (-355930353/2000000000 : ℝ), (5437698811/10000000000 : ℝ)] ![(43881422653019/100000000000000 : ℝ), (10691643671857/100000000000000 : ℝ), (45426933658807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294299849/10000000000 : ℝ)|^4493 ≤ (43881422653019/100000000000000 : ℝ)^3469
        have hw : |(5294299849/10000000000 : ℝ)|=(5294299849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-355930353/2000000000 : ℝ)|^4493 ≤ (10691643671857/100000000000000 : ℝ)^3469
        have hw : |(-355930353/2000000000 : ℝ)|=(355930353/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5437698811/10000000000 : ℝ)|^4493 ≤ (45426933658807/100000000000000 : ℝ)^3469
        have hw : |(5437698811/10000000000 : ℝ)|=(5437698811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s3_6 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294299951/10000000000 : ℝ)*x 0 + (1359424681/2500000000 : ℝ)*x 1 + (-889825873/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294299951/10000000000 : ℝ)^4493 ≤ (8776284749599/20000000000000 : ℝ)^3469 := by
    have hnat : (5294299951 : ℕ)^4493*20000000000000^3469 ≤ 8776284749599^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294299951 10000000000 8776284749599 20000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1359424681/2500000000 : ℝ)^4493 ≤ (2271346635873/5000000000000 : ℝ)^3469 := by
    have hnat : (1359424681 : ℕ)^4493*5000000000000^3469 ≤ 2271346635873^3469*2500000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359424681 2500000000 2271346635873 5000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (889825873/5000000000 : ℝ)^4493 ≤ (668227720251/6250000000000 : ℝ)^3469 := by
    have hnat : (889825873 : ℕ)^4493*6250000000000^3469 ≤ 668227720251^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      889825873 5000000000 668227720251 6250000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294299951/10000000000 : ℝ), (1359424681/2500000000 : ℝ), (-889825873/5000000000 : ℝ)] ![(8776284749599/20000000000000 : ℝ), (2271346635873/5000000000000 : ℝ), (668227720251/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294299951/10000000000 : ℝ)|^4493 ≤ (8776284749599/20000000000000 : ℝ)^3469
        have hw : |(5294299951/10000000000 : ℝ)|=(5294299951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1359424681/2500000000 : ℝ)|^4493 ≤ (2271346635873/5000000000000 : ℝ)^3469
        have hw : |(1359424681/2500000000 : ℝ)|=(1359424681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-889825873/5000000000 : ℝ)|^4493 ≤ (668227720251/6250000000000 : ℝ)^3469
        have hw : |(-889825873/5000000000 : ℝ)|=(889825873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s3_7 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4276043111/10000000000 : ℝ)*x 0 + (4532825559/10000000000 : ℝ)*x 1 + (504000307/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4276043111/10000000000 : ℝ)^4493 ≤ (33275982404383/100000000000000 : ℝ)^3469 := by
    have hnat : (4276043111 : ℕ)^4493*100000000000000^3469 ≤ 33275982404383^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4276043111 10000000000 33275982404383 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4532825559/10000000000 : ℝ)^4493 ≤ (8971684222817/25000000000000 : ℝ)^3469 := by
    have hnat : (4532825559 : ℕ)^4493*25000000000000^3469 ≤ 8971684222817^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4532825559 10000000000 8971684222817 25000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (504000307/1250000000 : ℝ)^4493 ≤ (30837280692427/100000000000000 : ℝ)^3469 := by
    have hnat : (504000307 : ℕ)^4493*100000000000000^3469 ≤ 30837280692427^3469*1250000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504000307 1250000000 30837280692427 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4276043111/10000000000 : ℝ), (4532825559/10000000000 : ℝ), (504000307/1250000000 : ℝ)] ![(33275982404383/100000000000000 : ℝ), (8971684222817/25000000000000 : ℝ), (30837280692427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4276043111/10000000000 : ℝ)|^4493 ≤ (33275982404383/100000000000000 : ℝ)^3469
        have hw : |(4276043111/10000000000 : ℝ)|=(4276043111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4532825559/10000000000 : ℝ)|^4493 ≤ (8971684222817/25000000000000 : ℝ)^3469
        have hw : |(4532825559/10000000000 : ℝ)|=(4532825559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(504000307/1250000000 : ℝ)|^4493 ≤ (30837280692427/100000000000000 : ℝ)^3469
        have hw : |(504000307/1250000000 : ℝ)|=(504000307/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1498_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8113083/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4013/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5167/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10787/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (389/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4013/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5167/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4013/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5167/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4013/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5167/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4013/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5167/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4013/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5167/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4013/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5167/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5167/50000 : ℝ) ^ (4491/1024 : ℝ) ≤ (593944137826553/12500000000000000000 : ℝ) := by
    have hpowers : (5167/50000 : ℝ)^4491 ≤ (593944137826553/12500000000000000000 : ℝ)^1024 := by
      have hnat : (5167 : ℕ)^4491*12500000000000000000^1024 ≤ 593944137826553^1024*50000^4491 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5167 50000 593944137826553 12500000000000000000 4491 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5167/50000 : ℝ)) (X := (593944137826553/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4013/25000 : ℝ) ^ (4491/1024 : ℝ) ≤ (32783527450024449/100000000000000000000 : ℝ) := by
    have hpowers : (4013/25000 : ℝ)^4491 ≤ (32783527450024449/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4013 : ℕ)^4491*100000000000000000000^1024 ≤ 32783527450024449^1024*25000^4491 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4013 25000 32783527450024449 100000000000000000000 4491 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4013/25000 : ℝ)) (X := (32783527450024449/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250593944137826553/6250000000000000000 : ℝ) ≤ (5000108336938549/5000000000000000 : ℝ) ^ (4491/1024 : ℝ) := by
    have hpowers : (6250593944137826553/6250000000000000000 : ℝ)^1024 ≤ (5000108336938549/5000000000000000 : ℝ)^4491 := by
      have hnat : (6250593944137826553 : ℕ)^1024*5000000000000000^4491 ≤ 5000108336938549^4491*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250593944137826553 6250000000000000000 5000108336938549 5000000000000000 1024 4491 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000108336938549/5000000000000000 : ℝ)) (X := (6250593944137826553/6250000000000000000 : ℝ)) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037535080552636873/100000000000000000000 : ℝ) ≤ (10000855719327529/10000000000000000 : ℝ) ^ (4491/1024 : ℝ) := by
    have hpowers : (100037535080552636873/100000000000000000000 : ℝ)^1024 ≤ (10000855719327529/10000000000000000 : ℝ)^4491 := by
      have hnat : (100037535080552636873 : ℕ)^1024*10000000000000000^4491 ≤ 10000855719327529^4491*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037535080552636873 100000000000000000000 10000855719327529 10000000000000000 1024 4491 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000855719327529/10000000000000000 : ℝ)) (X := (100037535080552636873/100000000000000000000 : ℝ)) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032783527450024449/50000000000000000000 : ℝ) ≤ (250037369119449/250000000000000 : ℝ) ^ (4491/1024 : ℝ) := by
    have hpowers : (50032783527450024449/50000000000000000000 : ℝ)^1024 ≤ (250037369119449/250000000000000 : ℝ)^4491 := by
      have hnat : (50032783527450024449 : ℕ)^1024*250000000000000^4491 ≤ 250037369119449^4491*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032783527450024449 50000000000000000000 250037369119449 250000000000000 1024 4491 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250037369119449/250000000000000 : ℝ)) (X := (50032783527450024449/50000000000000000000 : ℝ)) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(593944137826553/12500000000000000000 : ℝ) ≤ ((7146003893732467307/7147500000000000000 : ℝ)+2*(639045450431/571800000000000 : ℝ)*(5167/50000 : ℝ))^(4491/1024 : ℝ) := by
    rw [show (7146003893732467307/7147500000000000000 : ℝ)+2*(639045450431/571800000000000 : ℝ)*(5167/50000 : ℝ)=(5000108336938549/5000000000000000 : ℝ) by norm_num, show 1+2*(593944137826553/12500000000000000000 : ℝ)=(6250593944137826553/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32783527450024449/100000000000000000000 : ℝ)+(593944137826553/12500000000000000000 : ℝ) ≤ ((7146003893732467307/7147500000000000000 : ℝ)+(639045450431/571800000000000 : ℝ)*((4013/25000 : ℝ)+(5167/50000 : ℝ)))^(4491/1024 : ℝ) := by
    rw [show (7146003893732467307/7147500000000000000 : ℝ)+(639045450431/571800000000000 : ℝ)*((4013/25000 : ℝ)+(5167/50000 : ℝ))=(10000855719327529/10000000000000000 : ℝ) by norm_num, show 1+(32783527450024449/100000000000000000000 : ℝ)+(593944137826553/12500000000000000000 : ℝ)=(100037535080552636873/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32783527450024449/100000000000000000000 : ℝ) ≤ ((7146003893732467307/7147500000000000000 : ℝ)+2*(639045450431/571800000000000 : ℝ)*(4013/25000 : ℝ))^(4491/1024 : ℝ) := by
    rw [show (7146003893732467307/7147500000000000000 : ℝ)+2*(639045450431/571800000000000 : ℝ)*(4013/25000 : ℝ)=(250037369119449/250000000000000 : ℝ) by norm_num, show 1+2*(32783527450024449/100000000000000000000 : ℝ)=(50032783527450024449/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7146003893732467307/7147500000000000000 : ℝ)*(X 1 0+X 2 0)+(639045450431/571800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4491/1024 : ℝ)) (lo := (5167/50000 : ℝ)) (hi := (4013/25000 : ℝ)) (c := (7146003893732467307/7147500000000000000 : ℝ)) (alpha := (639045450431/571800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7146003893732467307/7147500000000000000 : ℝ)*(X 0 1+X 2 1)+(639045450431/571800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4491/1024 : ℝ)) (lo := (5167/50000 : ℝ)) (hi := (4013/25000 : ℝ)) (c := (7146003893732467307/7147500000000000000 : ℝ)) (alpha := (639045450431/571800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7146003893732467307/7147500000000000000 : ℝ)*(X 0 2+X 1 2)+(639045450431/571800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4491/1024 : ℝ)) (lo := (5167/50000 : ℝ)) (hi := (4013/25000 : ℝ)) (c := (7146003893732467307/7147500000000000000 : ℝ)) (alpha := (639045450431/571800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1888312913/10000000000 : ℝ)*X 0 0+(5438903087/10000000000 : ℝ)*X 0 1+(5213442167/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338339949/2500000000 : ℝ)*X 1 0+(-2003908373/10000000000 : ℝ)*X 1 1+(41707537/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070672031/2000000000 : ℝ)*X 2 0+(5213441779/10000000000 : ℝ)*X 2 1+(-2003908353/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4275970051/10000000000 : ℝ)*X 0 0+(2014648477/5000000000 : ℝ)*X 0 1+(566938809/1250000000 : ℝ)*X 0 2+(4275970051/10000000000 : ℝ)*X 1 0+(2014648477/5000000000 : ℝ)*X 1 1+(566938809/1250000000 : ℝ)*X 1 2+(4275970051/10000000000 : ℝ)*X 2 0+(2014648477/5000000000 : ℝ)*X 2 1+(566938809/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1888344783/10000000000 : ℝ)*X 0 0+(52146379/100000000 : ℝ)*X 0 1+(1359424701/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294299849/10000000000 : ℝ)*X 1 0+(-355930353/2000000000 : ℝ)*X 1 1+(5437698811/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294299951/10000000000 : ℝ)*X 2 0+(1359424681/2500000000 : ℝ)*X 2 1+(-889825873/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4276043111/10000000000 : ℝ)*X 0 0+(4532825559/10000000000 : ℝ)*X 0 1+(504000307/1250000000 : ℝ)*X 0 2+(4276043111/10000000000 : ℝ)*X 1 0+(4532825559/10000000000 : ℝ)*X 1 1+(504000307/1250000000 : ℝ)*X 1 2+(4276043111/10000000000 : ℝ)*X 2 0+(4532825559/10000000000 : ℝ)*X 2 1+(504000307/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4870952953692477059989913/11912500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (187443171/12500000000000 : ℝ)*(base19) + (1204078151/100000000000000 : ℝ)*(base23) + (36659969/10000000000000 : ℝ)*(upper3) + (158702353/50000000000000 : ℝ)*(upper4) + (16049467/100000000000000 : ℝ)*(upper5) + (320543013765959/10000000000000 : ℝ)*(major0) + (320543013765959/10000000000000 : ℝ)*(major1) + (320543013765959/10000000000000 : ℝ)*(major2) + (2217687802021631/50000000000000 : ℝ)*(sp0) + (2217694466471843/50000000000000 : ℝ)*(sp1) + (4435389228410903/100000000000000 : ℝ)*(sp2) + (987728691359179/50000000000000 : ℝ)*(sp3) + (463388931/3125000000000 : ℝ)*(sp4) + (6223240977/50000000000000 : ℝ)*(sp7) + (246933728650039/12500000000000 : ℝ)*(f.failure) + (2217695216244527/50000000000000 : ℝ)*(f.sum) + (15790309308461/2859000000000000000000000000 : ℝ)*base66 + (88811433232804971/23825000000000000000000000000000 : ℝ)*base67 + (62886513762945029/23825000000000000000000000000000 : ℝ)*base70 + (269303399631895029/23825000000000000000000000000000 : ℝ)*base72 + (2669707250869/2859000000000000000000000000 : ℝ)*base73 + (222631023770045029/23825000000000000000000000000000 : ℝ)*base76 + (114996544113820029/23825000000000000000000000000000 : ℝ)*base78 + (16210705723329971/23825000000000000000000000000000 : ℝ)*base79 + (660914951969/285900000000000000000000000 : ℝ)*base82 + (610237/62500000000000000000 : ℝ)*base89 + (610237/62500000000000000000 : ℝ)*base91 + (610237/62500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (101193186934665112169017/9530000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1801532139/100000000000000 : ℝ)*(base19) + (1965123839/100000000000000 : ℝ)*(base23) + (156300781/100000000000000 : ℝ)*(upper3) + (21881427/50000000000000 : ℝ)*(lower4) + (52849101/20000000000000 : ℝ)*(upper5) + (3239897734054093/100000000000000 : ℝ)*(major0) + (3239897734054093/100000000000000 : ℝ)*(major1) + (3239897734054093/100000000000000 : ℝ)*(major2) + (14910382651/50000000000000 : ℝ)*(sp1) + (3666626137/12500000000000 : ℝ)*(sp2) + (896616660125899/20000000000000 : ℝ)*(sp4) + (2241525839166027/50000000000000 : ℝ)*(sp5) + (4483052002496561/100000000000000 : ℝ)*(sp6) + (399342362706519/20000000000000 : ℝ)*(sp7) + (399342362706519/20000000000000 : ℝ)*(f.failure) + (896616660125899/20000000000000 : ℝ)*(f.sum) + (116086635492683/28590000000000000000000000000 : ℝ)*base65 + (833408315435224983/238250000000000000000000000000000 : ℝ)*base68 + (1629376884856025017/238250000000000000000000000000000 : ℝ)*base69 + (1633168875906275017/238250000000000000000000000000000 : ℝ)*base71 + (74557722530827/28590000000000000000000000000 : ℝ)*base74 + (3469736492983025017/238250000000000000000000000000000 : ℝ)*base75 + (1182059870545974983/238250000000000000000000000000000 : ℝ)*base78 + (1060377046421224983/238250000000000000000000000000000 : ℝ)*base80 + (175854017169743/28590000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (288077/100000000000000000000 : ℝ)*base89 + (288077/100000000000000000000 : ℝ)*base91 + (288077/100000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1498_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8113083/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4013/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5167/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10787/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (389/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1498_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1498_s4_0 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1888824131/10000000000 : ℝ)*x 0 + (1358887153/2500000000 : ℝ)*x 1 + (2608229721/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1888824131/10000000000 : ℝ)^4493 ≤ (11548709101109/100000000000000 : ℝ)^3469 := by
    have hnat : (1888824131 : ℕ)^4493*100000000000000^3469 ≤ 11548709101109^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1888824131 10000000000 11548709101109 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358887153/2500000000 : ℝ)^4493 ≤ (45403669695783/100000000000000 : ℝ)^3469 := by
    have hnat : (1358887153 : ℕ)^4493*100000000000000^3469 ≤ 45403669695783^3469*2500000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358887153 2500000000 45403669695783 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608229721/5000000000 : ℝ)^4493 ≤ (43047621195451/100000000000000 : ℝ)^3469 := by
    have hnat : (2608229721 : ℕ)^4493*100000000000000^3469 ≤ 43047621195451^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608229721 5000000000 43047621195451 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1888824131/10000000000 : ℝ), (1358887153/2500000000 : ℝ), (2608229721/5000000000 : ℝ)] ![(11548709101109/100000000000000 : ℝ), (45403669695783/100000000000000 : ℝ), (43047621195451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1888824131/10000000000 : ℝ)|^4493 ≤ (11548709101109/100000000000000 : ℝ)^3469
        have hw : |(-1888824131/10000000000 : ℝ)|=(1888824131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1358887153/2500000000 : ℝ)|^4493 ≤ (45403669695783/100000000000000 : ℝ)^3469
        have hw : |(1358887153/2500000000 : ℝ)|=(1358887153/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608229721/5000000000 : ℝ)|^4493 ≤ (43047621195451/100000000000000 : ℝ)^3469
        have hw : |(2608229721/5000000000 : ℝ)|=(2608229721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s4_1 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676242731/5000000000 : ℝ)*x 0 + (-200107471/1000000000 : ℝ)*x 1 + (5216459443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676242731/5000000000 : ℝ)^4493 ≤ (4450705901273/10000000000000 : ℝ)^3469 := by
    have hnat : (2676242731 : ℕ)^4493*10000000000000^3469 ≤ 4450705901273^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676242731 5000000000 4450705901273 10000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (200107471/1000000000 : ℝ)^4493 ≤ (3111329942697/25000000000000 : ℝ)^3469 := by
    have hnat : (200107471 : ℕ)^4493*25000000000000^3469 ≤ 3111329942697^3469*1000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200107471 1000000000 3111329942697 25000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216459443/10000000000 : ℝ)^4493 ≤ (43047621206139/100000000000000 : ℝ)^3469 := by
    have hnat : (5216459443 : ℕ)^4493*100000000000000^3469 ≤ 43047621206139^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216459443 10000000000 43047621206139 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676242731/5000000000 : ℝ), (-200107471/1000000000 : ℝ), (5216459443/10000000000 : ℝ)] ![(4450705901273/10000000000000 : ℝ), (3111329942697/25000000000000 : ℝ), (43047621206139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676242731/5000000000 : ℝ)|^4493 ≤ (4450705901273/10000000000000 : ℝ)^3469
        have hw : |(2676242731/5000000000 : ℝ)|=(2676242731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-200107471/1000000000 : ℝ)|^4493 ≤ (3111329942697/25000000000000 : ℝ)^3469
        have hw : |(-200107471/1000000000 : ℝ)|=(200107471/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216459443/10000000000 : ℝ)|^4493 ≤ (43047621206139/100000000000000 : ℝ)^3469
        have hw : |(5216459443/10000000000 : ℝ)|=(5216459443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s4_2 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676242731/5000000000 : ℝ)*x 0 + (5216459443/10000000000 : ℝ)*x 1 + (-2001074709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676242731/5000000000 : ℝ)^4493 ≤ (4450705901273/10000000000000 : ℝ)^3469 := by
    have hnat : (2676242731 : ℕ)^4493*10000000000000^3469 ≤ 4450705901273^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676242731 5000000000 4450705901273 10000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216459443/10000000000 : ℝ)^4493 ≤ (43047621206139/100000000000000 : ℝ)^3469 := by
    have hnat : (5216459443 : ℕ)^4493*100000000000000^3469 ≤ 43047621206139^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216459443 10000000000 43047621206139 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2001074709/10000000000 : ℝ)^4493 ≤ (12445319762733/100000000000000 : ℝ)^3469 := by
    have hnat : (2001074709 : ℕ)^4493*100000000000000^3469 ≤ 12445319762733^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2001074709 10000000000 12445319762733 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676242731/5000000000 : ℝ), (5216459443/10000000000 : ℝ), (-2001074709/10000000000 : ℝ)] ![(4450705901273/10000000000000 : ℝ), (43047621206139/100000000000000 : ℝ), (12445319762733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676242731/5000000000 : ℝ)|^4493 ≤ (4450705901273/10000000000000 : ℝ)^3469
        have hw : |(2676242731/5000000000 : ℝ)|=(2676242731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216459443/10000000000 : ℝ)|^4493 ≤ (43047621206139/100000000000000 : ℝ)^3469
        have hw : |(5216459443/10000000000 : ℝ)|=(5216459443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2001074709/10000000000 : ℝ)|^4493 ≤ (12445319762733/100000000000000 : ℝ)^3469
        have hw : |(-2001074709/10000000000 : ℝ)|=(2001074709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s4_3 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (427629089/1000000000 : ℝ)*x 0 + (201820667/500000000 : ℝ)*x 1 + (2264159807/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (427629089/1000000000 : ℝ)^4493 ≤ (33278479810319/100000000000000 : ℝ)^3469 := by
    have hnat : (427629089 : ℕ)^4493*100000000000000^3469 ≤ 33278479810319^3469*1000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427629089 1000000000 33278479810319 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (201820667/500000000 : ℝ)^4493 ≤ (386012260797/1250000000000 : ℝ)^3469 := by
    have hnat : (201820667 : ℕ)^4493*1250000000000^3469 ≤ 386012260797^3469*500000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201820667 500000000 386012260797 1250000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2264159807/5000000000 : ℝ)^4493 ≤ (8960134827677/25000000000000 : ℝ)^3469 := by
    have hnat : (2264159807 : ℕ)^4493*25000000000000^3469 ≤ 8960134827677^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2264159807 5000000000 8960134827677 25000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(427629089/1000000000 : ℝ), (201820667/500000000 : ℝ), (2264159807/5000000000 : ℝ)] ![(33278479810319/100000000000000 : ℝ), (386012260797/1250000000000 : ℝ), (8960134827677/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(427629089/1000000000 : ℝ)|^4493 ≤ (33278479810319/100000000000000 : ℝ)^3469
        have hw : |(427629089/1000000000 : ℝ)|=(427629089/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(201820667/500000000 : ℝ)|^4493 ≤ (386012260797/1250000000000 : ℝ)^3469
        have hw : |(201820667/500000000 : ℝ)|=(201820667/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2264159807/5000000000 : ℝ)|^4493 ≤ (8960134827677/25000000000000 : ℝ)^3469
        have hw : |(2264159807/5000000000 : ℝ)|=(2264159807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s4_4 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-236106757/1250000000 : ℝ)*x 0 + (2608794421/5000000000 : ℝ)*x 1 + (5434410869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (236106757/1250000000 : ℝ)^4493 ≤ (2309789215951/20000000000000 : ℝ)^3469 := by
    have hnat : (236106757 : ℕ)^4493*20000000000000^3469 ≤ 2309789215951^3469*1250000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      236106757 1250000000 2309789215951 20000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608794421/5000000000 : ℝ)^4493 ≤ (43059692858409/100000000000000 : ℝ)^3469 := by
    have hnat : (2608794421 : ℕ)^4493*100000000000000^3469 ≤ 43059692858409^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608794421 5000000000 43059692858409 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5434410869/10000000000 : ℝ)^4493 ≤ (45391361045157/100000000000000 : ℝ)^3469 := by
    have hnat : (5434410869 : ℕ)^4493*100000000000000^3469 ≤ 45391361045157^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434410869 10000000000 45391361045157 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-236106757/1250000000 : ℝ), (2608794421/5000000000 : ℝ), (5434410869/10000000000 : ℝ)] ![(2309789215951/20000000000000 : ℝ), (43059692858409/100000000000000 : ℝ), (45391361045157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-236106757/1250000000 : ℝ)|^4493 ≤ (2309789215951/20000000000000 : ℝ)^3469
        have hw : |(-236106757/1250000000 : ℝ)|=(236106757/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608794421/5000000000 : ℝ)|^4493 ≤ (43059692858409/100000000000000 : ℝ)^3469
        have hw : |(2608794421/5000000000 : ℝ)|=(2608794421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5434410869/10000000000 : ℝ)|^4493 ≤ (45391361045157/100000000000000 : ℝ)^3469
        have hw : |(5434410869/10000000000 : ℝ)|=(5434410869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s4_5 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647548261/5000000000 : ℝ)*x 0 + (-891561643/5000000000 : ℝ)*x 1 + (679301359/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647548261/5000000000 : ℝ)^4493 ≤ (1371561724113/3125000000000 : ℝ)^3469 := by
    have hnat : (2647548261 : ℕ)^4493*3125000000000^3469 ≤ 1371561724113^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647548261 5000000000 1371561724113 3125000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (891561643/5000000000 : ℝ)^4493 ≤ (10718663732711/100000000000000 : ℝ)^3469 := by
    have hnat : (891561643 : ℕ)^4493*100000000000000^3469 ≤ 10718663732711^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      891561643 5000000000 10718663732711 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (679301359/1250000000 : ℝ)^4493 ≤ (45391361077611/100000000000000 : ℝ)^3469 := by
    have hnat : (679301359 : ℕ)^4493*100000000000000^3469 ≤ 45391361077611^3469*1250000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679301359 1250000000 45391361077611 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647548261/5000000000 : ℝ), (-891561643/5000000000 : ℝ), (679301359/1250000000 : ℝ)] ![(1371561724113/3125000000000 : ℝ), (10718663732711/100000000000000 : ℝ), (45391361077611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647548261/5000000000 : ℝ)|^4493 ≤ (1371561724113/3125000000000 : ℝ)^3469
        have hw : |(2647548261/5000000000 : ℝ)|=(2647548261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-891561643/5000000000 : ℝ)|^4493 ≤ (10718663732711/100000000000000 : ℝ)^3469
        have hw : |(-891561643/5000000000 : ℝ)|=(891561643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(679301359/1250000000 : ℝ)|^4493 ≤ (45391361077611/100000000000000 : ℝ)^3469
        have hw : |(679301359/1250000000 : ℝ)|=(679301359/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s4_6 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295096521/10000000000 : ℝ)*x 0 + (2717205439/5000000000 : ℝ)*x 1 + (-22289041/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295096521/10000000000 : ℝ)^4493 ≤ (548624689511/1250000000000 : ℝ)^3469 := by
    have hnat : (5295096521 : ℕ)^4493*1250000000000^3469 ≤ 548624689511^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295096521 10000000000 548624689511 1250000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2717205439/5000000000 : ℝ)^4493 ≤ (1134784028563/2500000000000 : ℝ)^3469 := by
    have hnat : (2717205439 : ℕ)^4493*2500000000000^3469 ≤ 1134784028563^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717205439 5000000000 1134784028563 2500000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (22289041/125000000 : ℝ)^4493 ≤ (5359331842999/50000000000000 : ℝ)^3469 := by
    have hnat : (22289041 : ℕ)^4493*50000000000000^3469 ≤ 5359331842999^3469*125000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22289041 125000000 5359331842999 50000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295096521/10000000000 : ℝ), (2717205439/5000000000 : ℝ), (-22289041/125000000 : ℝ)] ![(548624689511/1250000000000 : ℝ), (1134784028563/2500000000000 : ℝ), (5359331842999/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295096521/10000000000 : ℝ)|^4493 ≤ (548624689511/1250000000000 : ℝ)^3469
        have hw : |(5295096521/10000000000 : ℝ)|=(5295096521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2717205439/5000000000 : ℝ)|^4493 ≤ (1134784028563/2500000000000 : ℝ)^3469
        have hw : |(2717205439/5000000000 : ℝ)|=(2717205439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-22289041/125000000 : ℝ)|^4493 ≤ (5359331842999/50000000000000 : ℝ)^3469
        have hw : |(-22289041/125000000 : ℝ)|=(22289041/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s4_7 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2138179053/5000000000 : ℝ)*x 0 + (1131445963/2500000000 : ℝ)*x 1 + (1009741957/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2138179053/5000000000 : ℝ)^4493 ≤ (16639578649489/50000000000000 : ℝ)^3469 := by
    have hnat : (2138179053 : ℕ)^4493*50000000000000^3469 ≤ 16639578649489^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138179053 5000000000 16639578649489 50000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1131445963/2500000000 : ℝ)^4493 ≤ (1432581886507/4000000000000 : ℝ)^3469 := by
    have hnat : (1131445963 : ℕ)^4493*4000000000000^3469 ≤ 1432581886507^3469*2500000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131445963 2500000000 1432581886507 4000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1009741957/2500000000 : ℝ)^4493 ≤ (6181259103563/20000000000000 : ℝ)^3469 := by
    have hnat : (1009741957 : ℕ)^4493*20000000000000^3469 ≤ 6181259103563^3469*2500000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1009741957 2500000000 6181259103563 20000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2138179053/5000000000 : ℝ), (1131445963/2500000000 : ℝ), (1009741957/2500000000 : ℝ)] ![(16639578649489/50000000000000 : ℝ), (1432581886507/4000000000000 : ℝ), (6181259103563/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2138179053/5000000000 : ℝ)|^4493 ≤ (16639578649489/50000000000000 : ℝ)^3469
        have hw : |(2138179053/5000000000 : ℝ)|=(2138179053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1131445963/2500000000 : ℝ)|^4493 ≤ (1432581886507/4000000000000 : ℝ)^3469
        have hw : |(1131445963/2500000000 : ℝ)|=(1131445963/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1009741957/2500000000 : ℝ)|^4493 ≤ (6181259103563/20000000000000 : ℝ)^3469
        have hw : |(1009741957/2500000000 : ℝ)|=(1009741957/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1498_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8113083/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (389/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10787/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10851/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (389/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10787/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (389/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10787/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (389/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10787/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (389/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10787/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (389/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10787/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (389/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10787/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10787/100000 : ℝ) ^ (4491/1024 : ℝ) ≤ (2867620732084727/50000000000000000000 : ℝ) := by
    have hpowers : (10787/100000 : ℝ)^4491 ≤ (2867620732084727/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10787 : ℕ)^4491*50000000000000000000^1024 ≤ 2867620732084727^1024*100000^4491 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10787 100000 2867620732084727 50000000000000000000 4491 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10787/100000 : ℝ)) (X := (2867620732084727/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (389/2500 : ℝ) ^ (4491/1024 : ℝ) ≤ (71499399130959/250000000000000000 : ℝ) := by
    have hpowers : (389/2500 : ℝ)^4491 ≤ (71499399130959/250000000000000000 : ℝ)^1024 := by
      have hnat : (389 : ℕ)^4491*250000000000000000^1024 ≤ 71499399130959^1024*2500^4491 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        389 2500 71499399130959 250000000000000000 4491 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (389/2500 : ℝ)) (X := (71499399130959/250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002867620732084727/25000000000000000000 : ℝ) ≤ (10000261528713093/10000000000000000 : ℝ) ^ (4491/1024 : ℝ) := by
    have hpowers : (25002867620732084727/25000000000000000000 : ℝ)^1024 ≤ (10000261528713093/10000000000000000 : ℝ)^4491 := by
      have hnat : (25002867620732084727 : ℕ)^1024*10000000000000000^4491 ≤ 10000261528713093^4491*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002867620732084727 25000000000000000000 10000261528713093 10000000000000000 1024 4491 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000261528713093/10000000000000000 : ℝ)) (X := (25002867620732084727/25000000000000000000 : ℝ)) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50017167500558276527/50000000000000000000 : ℝ) ≤ (10000782774046341/10000000000000000 : ℝ) ^ (4491/1024 : ℝ) := by
    have hpowers : (50017167500558276527/50000000000000000000 : ℝ)^1024 ≤ (10000782774046341/10000000000000000 : ℝ)^4491 := by
      have hnat : (50017167500558276527 : ℕ)^1024*10000000000000000^4491 ≤ 10000782774046341^4491*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017167500558276527 50000000000000000000 10000782774046341 10000000000000000 1024 4491 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000782774046341/10000000000000000 : ℝ)) (X := (50017167500558276527/50000000000000000000 : ℝ)) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (125071499399130959/125000000000000000 : ℝ) ≤ (10001304019379589/10000000000000000 : ℝ) ^ (4491/1024 : ℝ) := by
    have hpowers : (125071499399130959/125000000000000000 : ℝ)^1024 ≤ (10001304019379589/10000000000000000 : ℝ)^4491 := by
      have hnat : (125071499399130959 : ℕ)^1024*10000000000000000^4491 ≤ 10001304019379589^4491*125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        125071499399130959 125000000000000000 10001304019379589 10000000000000000 1024 4491 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001304019379589/10000000000000000 : ℝ)) (X := (125071499399130959/125000000000000000 : ℝ)) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2867620732084727/50000000000000000000 : ℝ) ≤ ((15906667643242700179/15910000000000000000 : ℝ)+2*(678704861/621484375000 : ℝ)*(10787/100000 : ℝ))^(4491/1024 : ℝ) := by
    rw [show (15906667643242700179/15910000000000000000 : ℝ)+2*(678704861/621484375000 : ℝ)*(10787/100000 : ℝ)=(10000261528713093/10000000000000000 : ℝ) by norm_num, show 1+2*(2867620732084727/50000000000000000000 : ℝ)=(25002867620732084727/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(71499399130959/250000000000000000 : ℝ)+(2867620732084727/50000000000000000000 : ℝ) ≤ ((15906667643242700179/15910000000000000000 : ℝ)+(678704861/621484375000 : ℝ)*((389/2500 : ℝ)+(10787/100000 : ℝ)))^(4491/1024 : ℝ) := by
    rw [show (15906667643242700179/15910000000000000000 : ℝ)+(678704861/621484375000 : ℝ)*((389/2500 : ℝ)+(10787/100000 : ℝ))=(10000782774046341/10000000000000000 : ℝ) by norm_num, show 1+(71499399130959/250000000000000000 : ℝ)+(2867620732084727/50000000000000000000 : ℝ)=(50017167500558276527/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(71499399130959/250000000000000000 : ℝ) ≤ ((15906667643242700179/15910000000000000000 : ℝ)+2*(678704861/621484375000 : ℝ)*(389/2500 : ℝ))^(4491/1024 : ℝ) := by
    rw [show (15906667643242700179/15910000000000000000 : ℝ)+2*(678704861/621484375000 : ℝ)*(389/2500 : ℝ)=(10001304019379589/10000000000000000 : ℝ) by norm_num, show 1+2*(71499399130959/250000000000000000 : ℝ)=(125071499399130959/125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15906667643242700179/15910000000000000000 : ℝ)*(X 1 0+X 2 0)+(678704861/621484375000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4491/1024 : ℝ)) (lo := (10787/100000 : ℝ)) (hi := (389/2500 : ℝ)) (c := (15906667643242700179/15910000000000000000 : ℝ)) (alpha := (678704861/621484375000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15906667643242700179/15910000000000000000 : ℝ)*(X 0 1+X 2 1)+(678704861/621484375000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4491/1024 : ℝ)) (lo := (10787/100000 : ℝ)) (hi := (389/2500 : ℝ)) (c := (15906667643242700179/15910000000000000000 : ℝ)) (alpha := (678704861/621484375000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15906667643242700179/15910000000000000000 : ℝ)*(X 0 2+X 1 2)+(678704861/621484375000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4491/1024 : ℝ)) (lo := (10787/100000 : ℝ)) (hi := (389/2500 : ℝ)) (c := (15906667643242700179/15910000000000000000 : ℝ)) (alpha := (678704861/621484375000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1888824131/10000000000 : ℝ)*X 0 0+(1358887153/2500000000 : ℝ)*X 0 1+(2608229721/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676242731/5000000000 : ℝ)*X 1 0+(-200107471/1000000000 : ℝ)*X 1 1+(5216459443/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676242731/5000000000 : ℝ)*X 2 0+(5216459443/10000000000 : ℝ)*X 2 1+(-2001074709/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((427629089/1000000000 : ℝ)*X 0 0+(201820667/500000000 : ℝ)*X 0 1+(2264159807/5000000000 : ℝ)*X 0 2+(427629089/1000000000 : ℝ)*X 1 0+(201820667/500000000 : ℝ)*X 1 1+(2264159807/5000000000 : ℝ)*X 1 2+(427629089/1000000000 : ℝ)*X 2 0+(201820667/500000000 : ℝ)*X 2 1+(2264159807/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-236106757/1250000000 : ℝ)*X 0 0+(2608794421/5000000000 : ℝ)*X 0 1+(5434410869/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647548261/5000000000 : ℝ)*X 1 0+(-891561643/5000000000 : ℝ)*X 1 1+(679301359/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295096521/10000000000 : ℝ)*X 2 0+(2717205439/5000000000 : ℝ)*X 2 1+(-22289041/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2138179053/5000000000 : ℝ)*X 0 0+(1131445963/2500000000 : ℝ)*X 0 1+(1009741957/2500000000 : ℝ)*X 0 2+(2138179053/5000000000 : ℝ)*X 1 0+(1131445963/2500000000 : ℝ)*X 1 1+(1009741957/2500000000 : ℝ)*X 1 2+(2138179053/5000000000 : ℝ)*X 2 0+(1131445963/2500000000 : ℝ)*X 2 1+(1009741957/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (379967079087613456578428511/39775000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (52808787/3125000000000 : ℝ)*(base19) + (315347829/20000000000000 : ℝ)*(base23) + (7569889/12500000000000 : ℝ)*(lower2) + (238398973/100000000000000 : ℝ)*(upper3) + (38942007/25000000000000 : ℝ)*(upper5) + (329866838326297/10000000000000 : ℝ)*(major0) + (329866838326297/10000000000000 : ℝ)*(major1) + (329866838326297/10000000000000 : ℝ)*(major2) + (456437878568479/10000000000000 : ℝ)*(sp0) + (4564403267643513/100000000000000 : ℝ)*(sp1) + (285275211299097/6250000000000 : ℝ)*(sp2) + (101645943129207/5000000000000 : ℝ)*(sp3) + (26171839907/100000000000000 : ℝ)*(sp4) + (49328073/390625000000 : ℝ)*(sp7) + (508232872642707/25000000000000 : ℝ)*(f.failure) + (4564404957524697/100000000000000 : ℝ)*(f.sum) + (1798589248359/795500000000000000000000000 : ℝ)*base65 + (611877803152507163/159100000000000000000000000000000 : ℝ)*base67 + (2444723638965807163/159100000000000000000000000000000 : ℝ)*base69 + (1070600239638107163/159100000000000000000000000000000 : ℝ)*base71 + (2045136528291/795500000000000000000000000 : ℝ)*base74 + (2415050391812207163/159100000000000000000000000000000 : ℝ)*base75 + (1247434000074307163/159100000000000000000000000000000 : ℝ)*base77 + (718331580241692837/159100000000000000000000000000000 : ℝ)*base80 + (1031616415851/198875000000000000000000000 : ℝ)*base81 + (1264319/125000000000000000000 : ℝ)*base90 + (1264319/125000000000000000000 : ℝ)*base92 + (1264319/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4139798998091617950114954141/397750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (845580997/50000000000000 : ℝ)*(base19) + (37008021/2000000000000 : ℝ)*(base23) + (215935183/100000000000000 : ℝ)*(upper3) + (35784747/50000000000000 : ℝ)*(lower4) + (42848411/20000000000000 : ℝ)*(upper5) + (3333120191286693/100000000000000 : ℝ)*(major0) + (3333120191286693/100000000000000 : ℝ)*(major1) + (3333120191286693/100000000000000 : ℝ)*(major2) + (25582008037/100000000000000 : ℝ)*(sp1) + (27883902401/100000000000000 : ℝ)*(sp2) + (4612076290927339/100000000000000 : ℝ)*(sp4) + (1153012254439327/25000000000000 : ℝ)*(sp5) + (288252909788993/6250000000000 : ℝ)*(sp6) + (410832748942257/20000000000000 : ℝ)*(sp7) + (410832748942257/20000000000000 : ℝ)*(f.failure) + (4612076290927339/100000000000000 : ℝ)*(f.sum) + (865438331729/3977500000000000000000000000 : ℝ)*base65 + (75094367782218047/1591000000000000000000000000000000 : ℝ)*base67 + (14094137345200781953/1591000000000000000000000000000000 : ℝ)*base70 + (5928776135019781953/1591000000000000000000000000000000 : ℝ)*base72 + (5486250288039/3977500000000000000000000000 : ℝ)*base73 + (20477783611416781953/1591000000000000000000000000000000 : ℝ)*base76 + (4963273075659781953/1591000000000000000000000000000000 : ℝ)*base78 + (11840739698796781953/1591000000000000000000000000000000 : ℝ)*base80 + (10465417540317/7955000000000000000000000000 : ℝ)*base82 + (248331/100000000000000000000 : ℝ)*base89 + (248331/100000000000000000000 : ℝ)*base91 + (248331/100000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1498_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8113083/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (389/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10787/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10851/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1498_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1498_s5_0 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-944445533/5000000000 : ℝ)*x 0 + (1087023399/2000000000 : ℝ)*x 1 + (5216846729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (944445533/5000000000 : ℝ)^4493 ≤ (11549239166657/100000000000000 : ℝ)^3469 := by
    have hnat : (944445533 : ℕ)^4493*100000000000000^3469 ≤ 11549239166657^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      944445533 5000000000 11549239166657 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087023399/2000000000 : ℝ)^4493 ≤ (45399000166083/100000000000000 : ℝ)^3469 := by
    have hnat : (1087023399 : ℕ)^4493*100000000000000^3469 ≤ 45399000166083^3469*2000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087023399 2000000000 45399000166083 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216846729/10000000000 : ℝ)^4493 ≤ (43051760650007/100000000000000 : ℝ)^3469 := by
    have hnat : (5216846729 : ℕ)^4493*100000000000000^3469 ≤ 43051760650007^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216846729 10000000000 43051760650007 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-944445533/5000000000 : ℝ), (1087023399/2000000000 : ℝ), (5216846729/10000000000 : ℝ)] ![(11549239166657/100000000000000 : ℝ), (45399000166083/100000000000000 : ℝ), (43051760650007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-944445533/5000000000 : ℝ)|^4493 ≤ (11549239166657/100000000000000 : ℝ)^3469
        have hw : |(-944445533/5000000000 : ℝ)|=(944445533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1087023399/2000000000 : ℝ)|^4493 ≤ (45399000166083/100000000000000 : ℝ)^3469
        have hw : |(1087023399/2000000000 : ℝ)|=(1087023399/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216846729/10000000000 : ℝ)|^4493 ≤ (43051760650007/100000000000000 : ℝ)^3469
        have hw : |(5216846729/10000000000 : ℝ)|=(5216846729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s5_1 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352372391/10000000000 : ℝ)*x 0 + (-200071201/1000000000 : ℝ)*x 1 + (5216846713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352372391/10000000000 : ℝ)^4493 ≤ (11126460317603/25000000000000 : ℝ)^3469 := by
    have hnat : (5352372391 : ℕ)^4493*25000000000000^3469 ≤ 11126460317603^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352372391 10000000000 11126460317603 25000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (200071201/1000000000 : ℝ)^4493 ≤ (12442398237681/100000000000000 : ℝ)^3469 := by
    have hnat : (200071201 : ℕ)^4493*100000000000000^3469 ≤ 12442398237681^3469*1000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200071201 1000000000 12442398237681 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216846713/10000000000 : ℝ)^4493 ≤ (2690735029937/6250000000000 : ℝ)^3469 := by
    have hnat : (5216846713 : ℕ)^4493*6250000000000^3469 ≤ 2690735029937^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216846713 10000000000 2690735029937 6250000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352372391/10000000000 : ℝ), (-200071201/1000000000 : ℝ), (5216846713/10000000000 : ℝ)] ![(11126460317603/25000000000000 : ℝ), (12442398237681/100000000000000 : ℝ), (2690735029937/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352372391/10000000000 : ℝ)|^4493 ≤ (11126460317603/25000000000000 : ℝ)^3469
        have hw : |(5352372391/10000000000 : ℝ)|=(5352372391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-200071201/1000000000 : ℝ)|^4493 ≤ (12442398237681/100000000000000 : ℝ)^3469
        have hw : |(-200071201/1000000000 : ℝ)|=(200071201/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216846713/10000000000 : ℝ)|^4493 ≤ (2690735029937/6250000000000 : ℝ)^3469
        have hw : |(5216846713/10000000000 : ℝ)|=(5216846713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s5_2 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676186177/5000000000 : ℝ)*x 0 + (5216846767/10000000000 : ℝ)*x 1 + (-2000711987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676186177/5000000000 : ℝ)^4493 ≤ (44505840871933/100000000000000 : ℝ)^3469 := by
    have hnat : (2676186177 : ℕ)^4493*100000000000000^3469 ≤ 44505840871933^3469*5000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676186177 5000000000 44505840871933 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216846767/10000000000 : ℝ)^4493 ≤ (43051761056169/100000000000000 : ℝ)^3469 := by
    have hnat : (5216846767 : ℕ)^4493*100000000000000^3469 ≤ 43051761056169^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216846767 10000000000 43051761056169 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2000711987/10000000000 : ℝ)^4493 ≤ (6221199026211/50000000000000 : ℝ)^3469 := by
    have hnat : (2000711987 : ℕ)^4493*50000000000000^3469 ≤ 6221199026211^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2000711987 10000000000 6221199026211 50000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676186177/5000000000 : ℝ), (5216846767/10000000000 : ℝ), (-2000711987/10000000000 : ℝ)] ![(44505840871933/100000000000000 : ℝ), (43051761056169/100000000000000 : ℝ), (6221199026211/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676186177/5000000000 : ℝ)|^4493 ≤ (44505840871933/100000000000000 : ℝ)^3469
        have hw : |(2676186177/5000000000 : ℝ)|=(2676186177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216846767/10000000000 : ℝ)|^4493 ≤ (43051761056169/100000000000000 : ℝ)^3469
        have hw : |(5216846767/10000000000 : ℝ)|=(5216846767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2000711987/10000000000 : ℝ)|^4493 ≤ (6221199026211/50000000000000 : ℝ)^3469
        have hw : |(-2000711987/10000000000 : ℝ)|=(2000711987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s5_3 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069082871/2500000000 : ℝ)*x 0 + (4037327987/10000000000 : ℝ)*x 1 + (4527395523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069082871/2500000000 : ℝ)^4493 ≤ (33278888968099/100000000000000 : ℝ)^3469 := by
    have hnat : (1069082871 : ℕ)^4493*100000000000000^3469 ≤ 33278888968099^3469*2500000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069082871 2500000000 33278888968099 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4037327987/10000000000 : ℝ)^4493 ≤ (965313886153/3125000000000 : ℝ)^3469 := by
    have hnat : (4037327987 : ℕ)^4493*3125000000000^3469 ≤ 965313886153^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4037327987 10000000000 965313886153 3125000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4527395523/10000000000 : ℝ)^4493 ≤ (8957766666537/25000000000000 : ℝ)^3469 := by
    have hnat : (4527395523 : ℕ)^4493*25000000000000^3469 ≤ 8957766666537^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4527395523 10000000000 8957766666537 25000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069082871/2500000000 : ℝ), (4037327987/10000000000 : ℝ), (4527395523/10000000000 : ℝ)] ![(33278888968099/100000000000000 : ℝ), (965313886153/3125000000000 : ℝ), (8957766666537/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069082871/2500000000 : ℝ)|^4493 ≤ (33278888968099/100000000000000 : ℝ)^3469
        have hw : |(1069082871/2500000000 : ℝ)|=(1069082871/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4037327987/10000000000 : ℝ)|^4493 ≤ (965313886153/3125000000000 : ℝ)^3469
        have hw : |(4037327987/10000000000 : ℝ)|=(4037327987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4527395523/10000000000 : ℝ)|^4493 ≤ (8957766666537/25000000000000 : ℝ)^3469
        have hw : |(4527395523/10000000000 : ℝ)|=(4527395523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s5_4 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1888920701/10000000000 : ℝ)*x 0 + (5217967783/10000000000 : ℝ)*x 1 + (5433987661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1888920701/10000000000 : ℝ)^4493 ≤ (11549473851217/100000000000000 : ℝ)^3469 := by
    have hnat : (1888920701 : ℕ)^4493*100000000000000^3469 ≤ 11549473851217^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1888920701 10000000000 11549473851217 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217967783/10000000000 : ℝ)^4493 ≤ (43063743365957/100000000000000 : ℝ)^3469 := by
    have hnat : (5217967783 : ℕ)^4493*100000000000000^3469 ≤ 43063743365957^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217967783 10000000000 43063743365957 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5433987661/10000000000 : ℝ)^4493 ≤ (22693391385843/50000000000000 : ℝ)^3469 := by
    have hnat : (5433987661 : ℕ)^4493*50000000000000^3469 ≤ 22693391385843^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433987661 10000000000 22693391385843 50000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1888920701/10000000000 : ℝ), (5217967783/10000000000 : ℝ), (5433987661/10000000000 : ℝ)] ![(11549473851217/100000000000000 : ℝ), (43063743365957/100000000000000 : ℝ), (22693391385843/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1888920701/10000000000 : ℝ)|^4493 ≤ (11549473851217/100000000000000 : ℝ)^3469
        have hw : |(-1888920701/10000000000 : ℝ)|=(1888920701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217967783/10000000000 : ℝ)|^4493 ≤ (43063743365957/100000000000000 : ℝ)^3469
        have hw : |(5217967783/10000000000 : ℝ)|=(5217967783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5433987661/10000000000 : ℝ)|^4493 ≤ (22693391385843/50000000000000 : ℝ)^3469
        have hw : |(5433987661/10000000000 : ℝ)|=(5433987661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s5_5 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295198201/10000000000 : ℝ)*x 0 + (-445892777/2500000000 : ℝ)*x 1 + (1086797533/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295198201/10000000000 : ℝ)^4493 ≤ (43891066752873/100000000000000 : ℝ)^3469 := by
    have hnat : (5295198201 : ℕ)^4493*100000000000000^3469 ≤ 43891066752873^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295198201 10000000000 43891066752873 100000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (445892777/2500000000 : ℝ)^4493 ≤ (2144430083867/20000000000000 : ℝ)^3469 := by
    have hnat : (445892777 : ℕ)^4493*20000000000000^3469 ≤ 2144430083867^3469*2500000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445892777 2500000000 2144430083867 20000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086797533/2000000000 : ℝ)^4493 ≤ (22693391407479/50000000000000 : ℝ)^3469 := by
    have hnat : (1086797533 : ℕ)^4493*50000000000000^3469 ≤ 22693391407479^3469*2000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086797533 2000000000 22693391407479 50000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295198201/10000000000 : ℝ), (-445892777/2500000000 : ℝ), (1086797533/2000000000 : ℝ)] ![(43891066752873/100000000000000 : ℝ), (2144430083867/20000000000000 : ℝ), (22693391407479/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295198201/10000000000 : ℝ)|^4493 ≤ (43891066752873/100000000000000 : ℝ)^3469
        have hw : |(5295198201/10000000000 : ℝ)|=(5295198201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-445892777/2500000000 : ℝ)|^4493 ≤ (2144430083867/20000000000000 : ℝ)^3469
        have hw : |(-445892777/2500000000 : ℝ)|=(445892777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1086797533/2000000000 : ℝ)|^4493 ≤ (22693391407479/50000000000000 : ℝ)^3469
        have hw : |(1086797533/2000000000 : ℝ)|=(1086797533/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s5_6 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295198203/10000000000 : ℝ)*x 0 + (5433987663/10000000000 : ℝ)*x 1 + (-445892777/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295198203/10000000000 : ℝ)^4493 ≤ (5486383346793/12500000000000 : ℝ)^3469 := by
    have hnat : (5295198203 : ℕ)^4493*12500000000000^3469 ≤ 5486383346793^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295198203 10000000000 5486383346793 12500000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5433987663/10000000000 : ℝ)^4493 ≤ (22693391396661/50000000000000 : ℝ)^3469 := by
    have hnat : (5433987663 : ℕ)^4493*50000000000000^3469 ≤ 22693391396661^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433987663 10000000000 22693391396661 50000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (445892777/2500000000 : ℝ)^4493 ≤ (2144430083867/20000000000000 : ℝ)^3469 := by
    have hnat : (445892777 : ℕ)^4493*20000000000000^3469 ≤ 2144430083867^3469*2500000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445892777 2500000000 2144430083867 20000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295198203/10000000000 : ℝ), (5433987663/10000000000 : ℝ), (-445892777/2500000000 : ℝ)] ![(5486383346793/12500000000000 : ℝ), (22693391396661/50000000000000 : ℝ), (2144430083867/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295198203/10000000000 : ℝ)|^4493 ≤ (5486383346793/12500000000000 : ℝ)^3469
        have hw : |(5295198203/10000000000 : ℝ)|=(5295198203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5433987663/10000000000 : ℝ)|^4493 ≤ (22693391396661/50000000000000 : ℝ)^3469
        have hw : |(5433987663/10000000000 : ℝ)|=(5433987663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-445892777/2500000000 : ℝ)|^4493 ≤ (2144430083867/20000000000000 : ℝ)^3469
        have hw : |(-445892777/2500000000 : ℝ)|=(445892777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1498_s5_7 (p : ℝ) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4276397943/10000000000 : ℝ)*x 0 + (4524878499/10000000000 : ℝ)*x 1 + (201993177/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4276397943/10000000000 : ℝ)^4493 ≤ (16639779414303/50000000000000 : ℝ)^3469 := by
    have hnat : (4276397943 : ℕ)^4493*50000000000000^3469 ≤ 16639779414303^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4276397943 10000000000 16639779414303 50000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4524878499/10000000000 : ℝ)^4493 ≤ (17902634062947/50000000000000 : ℝ)^3469 := by
    have hnat : (4524878499 : ℕ)^4493*50000000000000^3469 ≤ 17902634062947^3469*10000000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4524878499 10000000000 17902634062947 50000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (201993177/500000000 : ℝ)^4493 ≤ (618303460603/2000000000000 : ℝ)^3469 := by
    have hnat : (201993177 : ℕ)^4493*2000000000000^3469 ≤ 618303460603^3469*500000000^4493 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201993177 500000000 618303460603 2000000000000 4493 3469 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4493/1024 : ℝ)) 4493 3469 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4276397943/10000000000 : ℝ), (4524878499/10000000000 : ℝ), (201993177/500000000 : ℝ)] ![(16639779414303/50000000000000 : ℝ), (17902634062947/50000000000000 : ℝ), (618303460603/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4276397943/10000000000 : ℝ)|^4493 ≤ (16639779414303/50000000000000 : ℝ)^3469
        have hw : |(4276397943/10000000000 : ℝ)|=(4276397943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4524878499/10000000000 : ℝ)|^4493 ≤ (17902634062947/50000000000000 : ℝ)^3469
        have hw : |(4524878499/10000000000 : ℝ)|=(4524878499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(201993177/500000000 : ℝ)|^4493 ≤ (618303460603/2000000000000 : ℝ)^3469
        have hw : |(201993177/500000000 : ℝ)|=(201993177/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1498_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8113083/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10851/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (543/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15481/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10851/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10851/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10851/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10851/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10851/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10851/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10851/100000 : ℝ) ^ (4491/1024 : ℝ) ≤ (5885983639051231/100000000000000000000 : ℝ) := by
    have hpowers : (10851/100000 : ℝ)^4491 ≤ (5885983639051231/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10851 : ℕ)^4491*100000000000000000000^1024 ≤ 5885983639051231^1024*100000^4491 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10851 100000 5885983639051231 100000000000000000000 4491 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10851/100000 : ℝ)) (X := (5885983639051231/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4491/1024 : ℝ) ≤ (14019881326654887/50000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4491 ≤ (14019881326654887/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4491*50000000000000000000^1024 ≤ 14019881326654887^1024*10000^4491 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 14019881326654887 50000000000000000000 4491 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (14019881326654887/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005885983639051231/50000000000000000000 : ℝ) ≤ (1250033550286087/1250000000000000 : ℝ) ^ (4491/1024 : ℝ) := by
    have hpowers : (50005885983639051231/50000000000000000000 : ℝ)^1024 ≤ (1250033550286087/1250000000000000 : ℝ)^4491 := by
      have hnat : (50005885983639051231 : ℕ)^1024*1250000000000000^4491 ≤ 1250033550286087^4491*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005885983639051231 50000000000000000000 1250033550286087 1250000000000000 1024 4491 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250033550286087/1250000000000000 : ℝ)) (X := (50005885983639051231/50000000000000000000 : ℝ)) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20006785149258472201/20000000000000000000 : ℝ) ≤ (400030937800817/400000000000000 : ℝ) ^ (4491/1024 : ℝ) := by
    have hpowers : (20006785149258472201/20000000000000000000 : ℝ)^1024 ≤ (400030937800817/400000000000000 : ℝ)^4491 := by
      have hnat : (20006785149258472201 : ℕ)^1024*400000000000000^4491 ≤ 400030937800817^4491*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20006785149258472201 20000000000000000000 400030937800817 400000000000000 1024 4491 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400030937800817/400000000000000 : ℝ)) (X := (20006785149258472201/20000000000000000000 : ℝ)) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014019881326654887/25000000000000000000 : ℝ) ≤ (5000639243876077/5000000000000000 : ℝ) ^ (4491/1024 : ℝ) := by
    have hpowers : (25014019881326654887/25000000000000000000 : ℝ)^1024 ≤ (5000639243876077/5000000000000000 : ℝ)^4491 := by
      have hnat : (25014019881326654887 : ℕ)^1024*5000000000000000^4491 ≤ 5000639243876077^4491*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014019881326654887 25000000000000000000 5000639243876077 5000000000000000 1024 4491 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000639243876077/5000000000000000 : ℝ)) (X := (25014019881326654887/25000000000000000000 : ℝ)) (by norm_num) 4491 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5885983639051231/100000000000000000000 : ℝ) ≤ ((23190142340426638993/23195000000000000000 : ℝ)+2*(505042731729/463900000000000 : ℝ)*(10851/100000 : ℝ))^(4491/1024 : ℝ) := by
    rw [show (23190142340426638993/23195000000000000000 : ℝ)+2*(505042731729/463900000000000 : ℝ)*(10851/100000 : ℝ)=(1250033550286087/1250000000000000 : ℝ) by norm_num, show 1+2*(5885983639051231/100000000000000000000 : ℝ)=(50005885983639051231/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14019881326654887/50000000000000000000 : ℝ)+(5885983639051231/100000000000000000000 : ℝ) ≤ ((23190142340426638993/23195000000000000000 : ℝ)+(505042731729/463900000000000 : ℝ)*((1549/10000 : ℝ)+(10851/100000 : ℝ)))^(4491/1024 : ℝ) := by
    rw [show (23190142340426638993/23195000000000000000 : ℝ)+(505042731729/463900000000000 : ℝ)*((1549/10000 : ℝ)+(10851/100000 : ℝ))=(400030937800817/400000000000000 : ℝ) by norm_num, show 1+(14019881326654887/50000000000000000000 : ℝ)+(5885983639051231/100000000000000000000 : ℝ)=(20006785149258472201/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14019881326654887/50000000000000000000 : ℝ) ≤ ((23190142340426638993/23195000000000000000 : ℝ)+2*(505042731729/463900000000000 : ℝ)*(1549/10000 : ℝ))^(4491/1024 : ℝ) := by
    rw [show (23190142340426638993/23195000000000000000 : ℝ)+2*(505042731729/463900000000000 : ℝ)*(1549/10000 : ℝ)=(5000639243876077/5000000000000000 : ℝ) by norm_num, show 1+2*(14019881326654887/50000000000000000000 : ℝ)=(25014019881326654887/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23190142340426638993/23195000000000000000 : ℝ)*(X 1 0+X 2 0)+(505042731729/463900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4491/1024 : ℝ)) (lo := (10851/100000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (23190142340426638993/23195000000000000000 : ℝ)) (alpha := (505042731729/463900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23190142340426638993/23195000000000000000 : ℝ)*(X 0 1+X 2 1)+(505042731729/463900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4491/1024 : ℝ)) (lo := (10851/100000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (23190142340426638993/23195000000000000000 : ℝ)) (alpha := (505042731729/463900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23190142340426638993/23195000000000000000 : ℝ)*(X 0 2+X 1 2)+(505042731729/463900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4491/1024 : ℝ)) (lo := (10851/100000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (23190142340426638993/23195000000000000000 : ℝ)) (alpha := (505042731729/463900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-944445533/5000000000 : ℝ)*X 0 0+(1087023399/2000000000 : ℝ)*X 0 1+(5216846729/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352372391/10000000000 : ℝ)*X 1 0+(-200071201/1000000000 : ℝ)*X 1 1+(5216846713/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676186177/5000000000 : ℝ)*X 2 0+(5216846767/10000000000 : ℝ)*X 2 1+(-2000711987/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1069082871/2500000000 : ℝ)*X 0 0+(4037327987/10000000000 : ℝ)*X 0 1+(4527395523/10000000000 : ℝ)*X 0 2+(1069082871/2500000000 : ℝ)*X 1 0+(4037327987/10000000000 : ℝ)*X 1 1+(4527395523/10000000000 : ℝ)*X 1 2+(1069082871/2500000000 : ℝ)*X 2 0+(4037327987/10000000000 : ℝ)*X 2 1+(4527395523/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1888920701/10000000000 : ℝ)*X 0 0+(5217967783/10000000000 : ℝ)*X 0 1+(5433987661/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295198201/10000000000 : ℝ)*X 1 0+(-445892777/2500000000 : ℝ)*X 1 1+(1086797533/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295198203/10000000000 : ℝ)*X 2 0+(5433987663/10000000000 : ℝ)*X 2 1+(-445892777/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4276397943/10000000000 : ℝ)*X 0 0+(4524878499/10000000000 : ℝ)*X 0 1+(201993177/500000000 : ℝ)*X 0 2+(4276397943/10000000000 : ℝ)*X 1 0+(4524878499/10000000000 : ℝ)*X 1 1+(201993177/500000000 : ℝ)*X 1 2+(4276397943/10000000000 : ℝ)*X 2 0+(4524878499/10000000000 : ℝ)*X 2 1+(201993177/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1498_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (69165500441376685996275147/28993750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (119183747/25000000000000 : ℝ)*(base19) + (39365727/10000000000000 : ℝ)*(base23) + (6878693/25000000000000 : ℝ)*(lower2) + (14368433/25000000000000 : ℝ)*(upper3) + (901531/2500000000000 : ℝ)*(upper5) + (82775410532831/2500000000000 : ℝ)*(major0) + (82775410532831/2500000000000 : ℝ)*(major1) + (82775410532831/2500000000000 : ℝ)*(major2) + (4581483801281133/100000000000000 : ℝ)*(sp0) + (4581490841578221/100000000000000 : ℝ)*(sp1) + (2290745462327969/50000000000000 : ℝ)*(sp2) + (408107617991991/20000000000000 : ℝ)*(sp3) + (1879258019/25000000000000 : ℝ)*(sp4) + (1677417797/50000000000000 : ℝ)*(sp7) + (2040541444795549/100000000000000 : ℝ)*(f.failure) + (572686414789151/12500000000000 : ℝ)*(f.sum) + (1060296337371/231950000000000000000000000 : ℝ)*base66 + (1201426187810345817/57987500000000000000000000000000 : ℝ)*base68 + (758377656862545817/57987500000000000000000000000000 : ℝ)*base70 + (492852914948108317/57987500000000000000000000000000 : ℝ)*base72 + (19615104505667/4639000000000000000000000000 : ℝ)*base74 + (348438468910295817/57987500000000000000000000000000 : ℝ)*base76 + (177739657105595817/57987500000000000000000000000000 : ℝ)*base78 + (369647086164308317/57987500000000000000000000000000 : ℝ)*base80 + (12710767790349/4639000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (7067567/500000000000000000000 : ℝ)*base89 + (7067567/500000000000000000000 : ℝ)*base91 + (7067567/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1206273541151856716077302393/115975000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1718596383/100000000000000 : ℝ)*(base19) + (371110741/20000000000000 : ℝ)*(base23) + (284815823/50000000000000 : ℝ)*(lower1) + (216933251/100000000000000 : ℝ)*(upper3) + (12386509/20000000000000 : ℝ)*(lower4) + (55983509/25000000000000 : ℝ)*(upper5) + (334547834911267/10000000000000 : ℝ)*(major0) + (334547834911267/10000000000000 : ℝ)*(major1) + (334547834911267/10000000000000 : ℝ)*(major2) + (1690139913/100000000000000 : ℝ)*(sp2) + (2314588207941287/50000000000000 : ℝ)*(sp4) + (4629174697286191/100000000000000 : ℝ)*(sp5) + (1157293217547239/25000000000000 : ℝ)*(sp6) + (257722491954713/12500000000000 : ℝ)*(sp7) + (257722491954713/12500000000000 : ℝ)*(f.failure) + (2314588207941287/50000000000000 : ℝ)*(f.sum) + (862325228633/579875000000000000000000000 : ℝ)*base65 + (5053052030500284131/231950000000000000000000000000000 : ℝ)*base67 + (947005480859915869/231950000000000000000000000000000 : ℝ)*base70 + (11529365564023465869/231950000000000000000000000000000 : ℝ)*base72 + (17729817199217/2319500000000000000000000000 : ℝ)*base73 + (5430115272561865869/231950000000000000000000000000000 : ℝ)*base76 + (381390129492484131/231950000000000000000000000000000 : ℝ)*base77 + (3680201253540865869/231950000000000000000000000000000 : ℝ)*base80 + (23574353509227/4639000000000000000000000000 : ℝ)*base81 + (60179/62500000000000000000 : ℝ)*base89 + (60179/62500000000000000000 : ℝ)*base91 + (60179/62500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1498_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8113083/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10851/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (543/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1498_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1498_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8113083/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4013/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5167/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (543/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1498_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1498_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1498_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4491/1024 : ℝ) ≤ p) (hpb : p ≤ (4493/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (8113083/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4013/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5167/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (543/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1498_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
