-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1210_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:07:06.928586+00:00
-- url     : https://prove2.me/submissions/dccac24a-6398-4da0-8a78-c78a867abe0c

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
theorem support_rectangle_w1210_s6_0 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-33355697/156250000 : ℝ)*x 0 + (5392027123/10000000000 : ℝ)*x 1 + (105331009/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33355697/156250000 : ℝ)^8403 ≤ (1622304443251/12500000000000 : ℝ)^6355 := by
    have hnat : (33355697 : ℕ)^8403*12500000000000^6355 ≤ 1622304443251^6355*156250000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33355697 156250000 1622304443251 12500000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392027123/10000000000 : ℝ)^8403 ≤ (22094028129027/50000000000000 : ℝ)^6355 := by
    have hnat : (5392027123 : ℕ)^8403*50000000000000^6355 ≤ 22094028129027^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392027123 10000000000 22094028129027 50000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105331009/200000000 : ℝ)^8403 ≤ (21416754088991/50000000000000 : ℝ)^6355 := by
    have hnat : (105331009 : ℕ)^8403*50000000000000^6355 ≤ 21416754088991^6355*200000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105331009 200000000 21416754088991 50000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-33355697/156250000 : ℝ), (5392027123/10000000000 : ℝ), (105331009/200000000 : ℝ)] ![(1622304443251/12500000000000 : ℝ), (22094028129027/50000000000000 : ℝ), (21416754088991/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-33355697/156250000 : ℝ)|^8403 ≤ (1622304443251/12500000000000 : ℝ)^6355
        have hw : |(-33355697/156250000 : ℝ)|=(33355697/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392027123/10000000000 : ℝ)|^8403 ≤ (22094028129027/50000000000000 : ℝ)^6355
        have hw : |(5392027123/10000000000 : ℝ)|=(5392027123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105331009/200000000 : ℝ)|^8403 ≤ (21416754088991/50000000000000 : ℝ)^6355
        have hw : |(105331009/200000000 : ℝ)|=(105331009/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_s6_1 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534452959/1000000000 : ℝ)*x 0 + (-274799407/1250000000 : ℝ)*x 1 + (1316637613/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534452959/1000000000 : ℝ)^8403 ≤ (43674101861597/100000000000000 : ℝ)^6355 := by
    have hnat : (534452959 : ℕ)^8403*100000000000000^6355 ≤ 43674101861597^6355*1000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534452959 1000000000 43674101861597 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (274799407/1250000000 : ℝ)^8403 ≤ (13492389918377/100000000000000 : ℝ)^6355 := by
    have hnat : (274799407 : ℕ)^8403*100000000000000^6355 ≤ 13492389918377^6355*1250000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274799407 1250000000 13492389918377 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316637613/2500000000 : ℝ)^8403 ≤ (4283350819949/10000000000000 : ℝ)^6355 := by
    have hnat : (1316637613 : ℕ)^8403*10000000000000^6355 ≤ 4283350819949^6355*2500000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316637613 2500000000 4283350819949 10000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534452959/1000000000 : ℝ), (-274799407/1250000000 : ℝ), (1316637613/2500000000 : ℝ)] ![(43674101861597/100000000000000 : ℝ), (13492389918377/100000000000000 : ℝ), (4283350819949/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534452959/1000000000 : ℝ)|^8403 ≤ (43674101861597/100000000000000 : ℝ)^6355
        have hw : |(534452959/1000000000 : ℝ)|=(534452959/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-274799407/1250000000 : ℝ)|^8403 ≤ (13492389918377/100000000000000 : ℝ)^6355
        have hw : |(-274799407/1250000000 : ℝ)|=(274799407/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316637613/2500000000 : ℝ)|^8403 ≤ (4283350819949/10000000000000 : ℝ)^6355
        have hw : |(1316637613/2500000000 : ℝ)|=(1316637613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_s6_2 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672264793/5000000000 : ℝ)*x 0 + (5266550449/10000000000 : ℝ)*x 1 + (-1099197633/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672264793/5000000000 : ℝ)^8403 ≤ (5459262727297/12500000000000 : ℝ)^6355 := by
    have hnat : (2672264793 : ℕ)^8403*12500000000000^6355 ≤ 5459262727297^6355*5000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672264793 5000000000 5459262727297 12500000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266550449/10000000000 : ℝ)^8403 ≤ (10708377041807/25000000000000 : ℝ)^6355 := by
    have hnat : (5266550449 : ℕ)^8403*25000000000000^6355 ≤ 10708377041807^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266550449 10000000000 10708377041807 25000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1099197633/5000000000 : ℝ)^8403 ≤ (1349238999953/10000000000000 : ℝ)^6355 := by
    have hnat : (1099197633 : ℕ)^8403*10000000000000^6355 ≤ 1349238999953^6355*5000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099197633 5000000000 1349238999953 10000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672264793/5000000000 : ℝ), (5266550449/10000000000 : ℝ), (-1099197633/5000000000 : ℝ)] ![(5459262727297/12500000000000 : ℝ), (10708377041807/25000000000000 : ℝ), (1349238999953/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672264793/5000000000 : ℝ)|^8403 ≤ (5459262727297/12500000000000 : ℝ)^6355
        have hw : |(2672264793/5000000000 : ℝ)|=(2672264793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266550449/10000000000 : ℝ)|^8403 ≤ (10708377041807/25000000000000 : ℝ)^6355
        have hw : |(5266550449/10000000000 : ℝ)|=(5266550449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1099197633/5000000000 : ℝ)|^8403 ≤ (1349238999953/10000000000000 : ℝ)^6355
        have hw : |(-1099197633/5000000000 : ℝ)|=(1099197633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_s6_3 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1088792259/2500000000 : ℝ)*x 0 + (4230484763/10000000000 : ℝ)*x 1 + (1120862809/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088792259/2500000000 : ℝ)^8403 ≤ (8329302585601/25000000000000 : ℝ)^6355 := by
    have hnat : (1088792259 : ℕ)^8403*25000000000000^6355 ≤ 8329302585601^6355*2500000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088792259 2500000000 8329302585601 25000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4230484763/10000000000 : ℝ)^8403 ≤ (32061837140641/100000000000000 : ℝ)^6355 := by
    have hnat : (4230484763 : ℕ)^8403*100000000000000^6355 ≤ 32061837140641^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230484763 10000000000 32061837140641 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1120862809/2500000000 : ℝ)^8403 ≤ (17310476249307/50000000000000 : ℝ)^6355 := by
    have hnat : (1120862809 : ℕ)^8403*50000000000000^6355 ≤ 17310476249307^6355*2500000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120862809 2500000000 17310476249307 50000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1088792259/2500000000 : ℝ), (4230484763/10000000000 : ℝ), (1120862809/2500000000 : ℝ)] ![(8329302585601/25000000000000 : ℝ), (32061837140641/100000000000000 : ℝ), (17310476249307/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1088792259/2500000000 : ℝ)|^8403 ≤ (8329302585601/25000000000000 : ℝ)^6355
        have hw : |(1088792259/2500000000 : ℝ)|=(1088792259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4230484763/10000000000 : ℝ)|^8403 ≤ (32061837140641/100000000000000 : ℝ)^6355
        have hw : |(4230484763/10000000000 : ℝ)|=(4230484763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1120862809/2500000000 : ℝ)|^8403 ≤ (17310476249307/50000000000000 : ℝ)^6355
        have hw : |(1120862809/2500000000 : ℝ)|=(1120862809/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_s6_4 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2134769389/10000000000 : ℝ)*x 0 + (1316716909/2500000000 : ℝ)*x 1 + (2695854391/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2134769389/10000000000 : ℝ)^8403 ≤ (12978473979519/100000000000000 : ℝ)^6355 := by
    have hnat : (2134769389 : ℕ)^8403*100000000000000^6355 ≤ 12978473979519^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134769389 10000000000 12978473979519 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316716909/2500000000 : ℝ)^8403 ≤ (5354614909727/12500000000000 : ℝ)^6355 := by
    have hnat : (1316716909 : ℕ)^8403*12500000000000^6355 ≤ 5354614909727^6355*2500000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316716909 2500000000 5354614909727 12500000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695854391/5000000000 : ℝ)^8403 ≤ (22092303363403/50000000000000 : ℝ)^6355 := by
    have hnat : (2695854391 : ℕ)^8403*50000000000000^6355 ≤ 22092303363403^6355*5000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695854391 5000000000 22092303363403 50000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2134769389/10000000000 : ℝ), (1316716909/2500000000 : ℝ), (2695854391/5000000000 : ℝ)] ![(12978473979519/100000000000000 : ℝ), (5354614909727/12500000000000 : ℝ), (22092303363403/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2134769389/10000000000 : ℝ)|^8403 ≤ (12978473979519/100000000000000 : ℝ)^6355
        have hw : |(-2134769389/10000000000 : ℝ)|=(2134769389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316716909/2500000000 : ℝ)|^8403 ≤ (5354614909727/12500000000000 : ℝ)^6355
        have hw : |(1316716909/2500000000 : ℝ)|=(1316716909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695854391/5000000000 : ℝ)|^8403 ≤ (22092303363403/50000000000000 : ℝ)^6355
        have hw : |(2695854391/5000000000 : ℝ)|=(2695854391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_s6_5 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062516769/2000000000 : ℝ)*x 0 + (-2073236929/10000000000 : ℝ)*x 1 + (5391708779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062516769/2000000000 : ℝ)^8403 ≤ (43329254209997/100000000000000 : ℝ)^6355 := by
    have hnat : (1062516769 : ℕ)^8403*100000000000000^6355 ≤ 43329254209997^6355*2000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062516769 2000000000 43329254209997 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2073236929/10000000000 : ℝ)^8403 ≤ (12486139083449/100000000000000 : ℝ)^6355 := by
    have hnat : (2073236929 : ℕ)^8403*100000000000000^6355 ≤ 12486139083449^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073236929 10000000000 12486139083449 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391708779/10000000000 : ℝ)^8403 ≤ (22092303347149/50000000000000 : ℝ)^6355 := by
    have hnat : (5391708779 : ℕ)^8403*50000000000000^6355 ≤ 22092303347149^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391708779 10000000000 22092303347149 50000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062516769/2000000000 : ℝ), (-2073236929/10000000000 : ℝ), (5391708779/10000000000 : ℝ)] ![(43329254209997/100000000000000 : ℝ), (12486139083449/100000000000000 : ℝ), (22092303347149/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062516769/2000000000 : ℝ)|^8403 ≤ (43329254209997/100000000000000 : ℝ)^6355
        have hw : |(1062516769/2000000000 : ℝ)|=(1062516769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2073236929/10000000000 : ℝ)|^8403 ≤ (12486139083449/100000000000000 : ℝ)^6355
        have hw : |(-2073236929/10000000000 : ℝ)|=(2073236929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391708779/10000000000 : ℝ)|^8403 ≤ (22092303347149/50000000000000 : ℝ)^6355
        have hw : |(5391708779/10000000000 : ℝ)|=(5391708779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_s6_6 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062516769/2000000000 : ℝ)*x 0 + (5391708779/10000000000 : ℝ)*x 1 + (-207323693/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062516769/2000000000 : ℝ)^8403 ≤ (43329254209997/100000000000000 : ℝ)^6355 := by
    have hnat : (1062516769 : ℕ)^8403*100000000000000^6355 ≤ 43329254209997^6355*2000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062516769 2000000000 43329254209997 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391708779/10000000000 : ℝ)^8403 ≤ (22092303347149/50000000000000 : ℝ)^6355 := by
    have hnat : (5391708779 : ℕ)^8403*50000000000000^6355 ≤ 22092303347149^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391708779 10000000000 22092303347149 50000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207323693/1000000000 : ℝ)^8403 ≤ (3121534772853/25000000000000 : ℝ)^6355 := by
    have hnat : (207323693 : ℕ)^8403*25000000000000^6355 ≤ 3121534772853^6355*1000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207323693 1000000000 3121534772853 25000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062516769/2000000000 : ℝ), (5391708779/10000000000 : ℝ), (-207323693/1000000000 : ℝ)] ![(43329254209997/100000000000000 : ℝ), (22092303347149/50000000000000 : ℝ), (3121534772853/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062516769/2000000000 : ℝ)|^8403 ≤ (43329254209997/100000000000000 : ℝ)^6355
        have hw : |(1062516769/2000000000 : ℝ)|=(1062516769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391708779/10000000000 : ℝ)|^8403 ≤ (22092303347149/50000000000000 : ℝ)^6355
        have hw : |(5391708779/10000000000 : ℝ)|=(5391708779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-207323693/1000000000 : ℝ)|^8403 ≤ (3121534772853/25000000000000 : ℝ)^6355
        have hw : |(-207323693/1000000000 : ℝ)|=(207323693/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_s6_7 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1088794671/2500000000 : ℝ)*x 0 + (56035147/125000000 : ℝ)*x 1 + (4231126551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088794671/2500000000 : ℝ)^8403 ≤ (1332692317427/4000000000000 : ℝ)^6355 := by
    have hnat : (1088794671 : ℕ)^8403*4000000000000^6355 ≤ 1332692317427^6355*2500000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088794671 2500000000 1332692317427 4000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56035147/125000000 : ℝ)^8403 ≤ (34614423303629/100000000000000 : ℝ)^6355 := by
    have hnat : (56035147 : ℕ)^8403*100000000000000^6355 ≤ 34614423303629^6355*125000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56035147 125000000 34614423303629 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4231126551/10000000000 : ℝ)^8403 ≤ (8017067186119/25000000000000 : ℝ)^6355 := by
    have hnat : (4231126551 : ℕ)^8403*25000000000000^6355 ≤ 8017067186119^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4231126551 10000000000 8017067186119 25000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1088794671/2500000000 : ℝ), (56035147/125000000 : ℝ), (4231126551/10000000000 : ℝ)] ![(1332692317427/4000000000000 : ℝ), (34614423303629/100000000000000 : ℝ), (8017067186119/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1088794671/2500000000 : ℝ)|^8403 ≤ (1332692317427/4000000000000 : ℝ)^6355
        have hw : |(1088794671/2500000000 : ℝ)|=(1088794671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(56035147/125000000 : ℝ)|^8403 ≤ (34614423303629/100000000000000 : ℝ)^6355
        have hw : |(56035147/125000000 : ℝ)|=(56035147/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4231126551/10000000000 : ℝ)|^8403 ≤ (8017067186119/25000000000000 : ℝ)^6355
        have hw : |(4231126551/10000000000 : ℝ)|=(4231126551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1210_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37700547/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14117/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11411/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5717/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14093/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14117/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11411/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14117/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11411/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14117/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11411/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14117/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11411/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14117/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11411/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14117/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11411/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11411/100000 : ℝ) ^ (4201/1024 : ℝ) ≤ (13571682090870159/100000000000000000000 : ℝ) := by
    have hpowers : (11411/100000 : ℝ)^4201 ≤ (13571682090870159/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11411 : ℕ)^4201*100000000000000000000^1024 ≤ 13571682090870159^1024*100000^4201 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11411 100000 13571682090870159 100000000000000000000 4201 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11411/100000 : ℝ)) (X := (13571682090870159/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4201 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14117/100000 : ℝ) ^ (4201/1024 : ℝ) ≤ (6498528663335631/20000000000000000000 : ℝ) := by
    have hpowers : (14117/100000 : ℝ)^4201 ≤ (6498528663335631/20000000000000000000 : ℝ)^1024 := by
      have hnat : (14117 : ℕ)^4201*20000000000000000000^1024 ≤ 6498528663335631^1024*100000^4201 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14117 100000 6498528663335631 20000000000000000000 4201 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14117/100000 : ℝ)) (X := (6498528663335631/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4201 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013571682090870159/50000000000000000000 : ℝ) ≤ (1000066155564479/1000000000000000 : ℝ) ^ (4201/1024 : ℝ) := by
    have hpowers : (50013571682090870159/50000000000000000000 : ℝ)^1024 ≤ (1000066155564479/1000000000000000 : ℝ)^4201 := by
      have hnat : (50013571682090870159 : ℕ)^1024*1000000000000000^4201 ≤ 1000066155564479^4201*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013571682090870159 50000000000000000000 1000066155564479 1000000000000000 1024 4201 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000066155564479/1000000000000000 : ℝ)) (X := (50013571682090870159/50000000000000000000 : ℝ)) (by norm_num) 4201 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023032162703774157/50000000000000000000 : ℝ) ≤ (2000224525852731/2000000000000000 : ℝ) ^ (4201/1024 : ℝ) := by
    have hpowers : (50023032162703774157/50000000000000000000 : ℝ)^1024 ≤ (2000224525852731/2000000000000000 : ℝ)^4201 := by
      have hnat : (50023032162703774157 : ℕ)^1024*2000000000000000^4201 ≤ 2000224525852731^4201*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023032162703774157 50000000000000000000 2000224525852731 2000000000000000 1024 4201 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000224525852731/2000000000000000 : ℝ)) (X := (50023032162703774157/50000000000000000000 : ℝ)) (by norm_num) 4201 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006498528663335631/10000000000000000000 : ℝ) ≤ (250039592572063/250000000000000 : ℝ) ^ (4201/1024 : ℝ) := by
    have hpowers : (10006498528663335631/10000000000000000000 : ℝ)^1024 ≤ (250039592572063/250000000000000 : ℝ)^4201 := by
      have hnat : (10006498528663335631 : ℕ)^1024*250000000000000^4201 ≤ 250039592572063^4201*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006498528663335631 10000000000000000000 250039592572063 250000000000000 1024 4201 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250039592572063/250000000000000 : ℝ)) (X := (10006498528663335631/10000000000000000000 : ℝ)) (by norm_num) 4201 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13571682090870159/100000000000000000000 : ℝ) ≤ ((2705126754744506471/2706000000000000000 : ℝ)+2*(92214723773/54120000000000 : ℝ)*(11411/100000 : ℝ))^(4201/1024 : ℝ) := by
    rw [show (2705126754744506471/2706000000000000000 : ℝ)+2*(92214723773/54120000000000 : ℝ)*(11411/100000 : ℝ)=(1000066155564479/1000000000000000 : ℝ) by norm_num, show 1+2*(13571682090870159/100000000000000000000 : ℝ)=(50013571682090870159/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6498528663335631/20000000000000000000 : ℝ)+(13571682090870159/100000000000000000000 : ℝ) ≤ ((2705126754744506471/2706000000000000000 : ℝ)+(92214723773/54120000000000 : ℝ)*((14117/100000 : ℝ)+(11411/100000 : ℝ)))^(4201/1024 : ℝ) := by
    rw [show (2705126754744506471/2706000000000000000 : ℝ)+(92214723773/54120000000000 : ℝ)*((14117/100000 : ℝ)+(11411/100000 : ℝ))=(2000224525852731/2000000000000000 : ℝ) by norm_num, show 1+(6498528663335631/20000000000000000000 : ℝ)+(13571682090870159/100000000000000000000 : ℝ)=(50023032162703774157/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6498528663335631/20000000000000000000 : ℝ) ≤ ((2705126754744506471/2706000000000000000 : ℝ)+2*(92214723773/54120000000000 : ℝ)*(14117/100000 : ℝ))^(4201/1024 : ℝ) := by
    rw [show (2705126754744506471/2706000000000000000 : ℝ)+2*(92214723773/54120000000000 : ℝ)*(14117/100000 : ℝ)=(250039592572063/250000000000000 : ℝ) by norm_num, show 1+2*(6498528663335631/20000000000000000000 : ℝ)=(10006498528663335631/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2705126754744506471/2706000000000000000 : ℝ)*(X 1 0+X 2 0)+(92214723773/54120000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4201/1024 : ℝ)) (lo := (11411/100000 : ℝ)) (hi := (14117/100000 : ℝ)) (c := (2705126754744506471/2706000000000000000 : ℝ)) (alpha := (92214723773/54120000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2705126754744506471/2706000000000000000 : ℝ)*(X 0 1+X 2 1)+(92214723773/54120000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4201/1024 : ℝ)) (lo := (11411/100000 : ℝ)) (hi := (14117/100000 : ℝ)) (c := (2705126754744506471/2706000000000000000 : ℝ)) (alpha := (92214723773/54120000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2705126754744506471/2706000000000000000 : ℝ)*(X 0 2+X 1 2)+(92214723773/54120000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4201/1024 : ℝ)) (lo := (11411/100000 : ℝ)) (hi := (14117/100000 : ℝ)) (c := (2705126754744506471/2706000000000000000 : ℝ)) (alpha := (92214723773/54120000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-33355697/156250000 : ℝ)*X 0 0+(5392027123/10000000000 : ℝ)*X 0 1+(105331009/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534452959/1000000000 : ℝ)*X 1 0+(-274799407/1250000000 : ℝ)*X 1 1+(1316637613/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672264793/5000000000 : ℝ)*X 2 0+(5266550449/10000000000 : ℝ)*X 2 1+(-1099197633/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1088792259/2500000000 : ℝ)*X 0 0+(4230484763/10000000000 : ℝ)*X 0 1+(1120862809/2500000000 : ℝ)*X 0 2+(1088792259/2500000000 : ℝ)*X 1 0+(4230484763/10000000000 : ℝ)*X 1 1+(1120862809/2500000000 : ℝ)*X 1 2+(1088792259/2500000000 : ℝ)*X 2 0+(4230484763/10000000000 : ℝ)*X 2 1+(1120862809/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2134769389/10000000000 : ℝ)*X 0 0+(1316716909/2500000000 : ℝ)*X 0 1+(2695854391/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062516769/2000000000 : ℝ)*X 1 0+(-2073236929/10000000000 : ℝ)*X 1 1+(5391708779/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062516769/2000000000 : ℝ)*X 2 0+(5391708779/10000000000 : ℝ)*X 2 1+(-207323693/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1088794671/2500000000 : ℝ)*X 0 0+(56035147/125000000 : ℝ)*X 0 1+(4231126551/10000000000 : ℝ)*X 0 2+(1088794671/2500000000 : ℝ)*X 1 0+(56035147/125000000 : ℝ)*X 1 1+(4231126551/10000000000 : ℝ)*X 1 2+(1088794671/2500000000 : ℝ)*X 2 0+(56035147/125000000 : ℝ)*X 2 1+(4231126551/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (126431282817832760632702269/11275000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1081023963/50000000000000 : ℝ)*(base19) + (402660603/20000000000000 : ℝ)*(base23) + (4769329/6250000000000 : ℝ)*(lower2) + (284794053/100000000000000 : ℝ)*(upper3) + (81406691/50000000000000 : ℝ)*(upper5) + (2980721229743061/50000000000000 : ℝ)*(major0) + (2980721229743061/50000000000000 : ℝ)*(major1) + (2980721229743061/50000000000000 : ℝ)*(major2) + (3984835790976571/50000000000000 : ℝ)*(sp0) + (1593945712108787/20000000000000 : ℝ)*(sp1) + (3984864354644423/50000000000000 : ℝ)*(sp2) + (3953121735440599/100000000000000 : ℝ)*(sp3) + (59140638719/100000000000000 : ℝ)*(sp4) + (32087159191/100000000000000 : ℝ)*(sp7) + (395315382259979/10000000000000 : ℝ)*(f.failure) + (7969730722591861/100000000000000 : ℝ)*(f.sum) + (52550061229/22550000000000000000000000 : ℝ)*base66 + (193545549270132577/45100000000000000000000000000000 : ℝ)*base67 + (731177831868532577/45100000000000000000000000000000 : ℝ)*base69 + (559055526684032577/45100000000000000000000000000000 : ℝ)*base71 + (829860330109/112750000000000000000000000 : ℝ)*base74 + (97993474632332577/45100000000000000000000000000000 : ℝ)*base75 + (494672649196567423/45100000000000000000000000000000 : ℝ)*base78 + (557803677279732577/45100000000000000000000000000000 : ℝ)*base79 + (214094268821/56375000000000000000000000 : ℝ)*base82 + (491487/250000000000000000000 : ℝ)*base90 + (491487/250000000000000000000 : ℝ)*base92 + (491487/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (43582838414804454020988921/4100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (959959339/50000000000000 : ℝ)*(base19) + (2085954947/100000000000000 : ℝ)*(base23) + (212959251/100000000000000 : ℝ)*(upper3) + (9478783/12500000000000 : ℝ)*(lower4) + (2727401/1250000000000 : ℝ)*(upper5) + (5991697258645461/100000000000000 : ℝ)*(major0) + (5991697258645461/100000000000000 : ℝ)*(major1) + (5991697258645461/100000000000000 : ℝ)*(major2) + (10696725521/20000000000000 : ℝ)*(sp1) + (57358296251/100000000000000 : ℝ)*(sp2) + (1001272220911081/12500000000000 : ℝ)*(sp4) + (4005061181871183/50000000000000 : ℝ)*(sp5) + (2002529580759363/25000000000000 : ℝ)*(sp6) + (1986608197835121/50000000000000 : ℝ)*(sp7) + (1986608197835121/50000000000000 : ℝ)*(f.failure) + (1001272220911081/12500000000000 : ℝ)*(f.sum) + (528690516351/82000000000000000000000000 : ℝ)*base66 + (39281942289753693/8200000000000000000000000000000 : ℝ)*base68 + (90873705464246307/8200000000000000000000000000000 : ℝ)*base69 + (135748289629753693/8200000000000000000000000000000 : ℝ)*base72 + (44485828909/82000000000000000000000000 : ℝ)*base73 + (107123220392646307/8200000000000000000000000000000 : ℝ)*base75 + (70398683238953693/8200000000000000000000000000000 : ℝ)*base78 + (144667208057553693/8200000000000000000000000000000 : ℝ)*base80 + (242462936671/82000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/50000000000000 : ℝ)*base87 + (15011187/1250000000000000000000 : ℝ)*base89 + (15011187/1250000000000000000000 : ℝ)*base91 + (15011187/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1210_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37700547/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14117/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11411/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5717/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1210_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1210_s7_0 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2134783831/10000000000 : ℝ)*x 0 + (2695900167/5000000000 : ℝ)*x 1 + (1053352919/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2134783831/10000000000 : ℝ)^8403 ≤ (6489295038031/50000000000000 : ℝ)^6355 := by
    have hnat : (2134783831 : ℕ)^8403*50000000000000^6355 ≤ 6489295038031^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134783831 10000000000 6489295038031 50000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695900167/5000000000 : ℝ)^8403 ≤ (44185598774153/100000000000000 : ℝ)^6355 := by
    have hnat : (2695900167 : ℕ)^8403*100000000000000^6355 ≤ 44185598774153^6355*5000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695900167 5000000000 44185598774153 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053352919/2000000000 : ℝ)^8403 ≤ (42835811141137/100000000000000 : ℝ)^6355 := by
    have hnat : (1053352919 : ℕ)^8403*100000000000000^6355 ≤ 42835811141137^6355*2000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053352919 2000000000 42835811141137 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2134783831/10000000000 : ℝ), (2695900167/5000000000 : ℝ), (1053352919/2000000000 : ℝ)] ![(6489295038031/50000000000000 : ℝ), (44185598774153/100000000000000 : ℝ), (42835811141137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2134783831/10000000000 : ℝ)|^8403 ≤ (6489295038031/50000000000000 : ℝ)^6355
        have hw : |(-2134783831/10000000000 : ℝ)|=(2134783831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695900167/5000000000 : ℝ)|^8403 ≤ (44185598774153/100000000000000 : ℝ)^6355
        have hw : |(2695900167/5000000000 : ℝ)|=(2695900167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053352919/2000000000 : ℝ)|^8403 ≤ (42835811141137/100000000000000 : ℝ)^6355
        have hw : |(1053352919/2000000000 : ℝ)|=(1053352919/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_s7_1 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668059037/1250000000 : ℝ)*x 0 + (-2198187759/10000000000 : ℝ)*x 1 + (1053352919/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668059037/1250000000 : ℝ)^8403 ≤ (43673482788831/100000000000000 : ℝ)^6355 := by
    have hnat : (668059037 : ℕ)^8403*100000000000000^6355 ≤ 43673482788831^6355*1250000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668059037 1250000000 43673482788831 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2198187759/10000000000 : ℝ)^8403 ≤ (13490706053917/100000000000000 : ℝ)^6355 := by
    have hnat : (2198187759 : ℕ)^8403*100000000000000^6355 ≤ 13490706053917^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2198187759 10000000000 13490706053917 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053352919/2000000000 : ℝ)^8403 ≤ (42835811141137/100000000000000 : ℝ)^6355 := by
    have hnat : (1053352919 : ℕ)^8403*100000000000000^6355 ≤ 42835811141137^6355*2000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053352919 2000000000 42835811141137 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668059037/1250000000 : ℝ), (-2198187759/10000000000 : ℝ), (1053352919/2000000000 : ℝ)] ![(43673482788831/100000000000000 : ℝ), (13490706053917/100000000000000 : ℝ), (42835811141137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668059037/1250000000 : ℝ)|^8403 ≤ (43673482788831/100000000000000 : ℝ)^6355
        have hw : |(668059037/1250000000 : ℝ)|=(668059037/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2198187759/10000000000 : ℝ)|^8403 ≤ (13490706053917/100000000000000 : ℝ)^6355
        have hw : |(-2198187759/10000000000 : ℝ)|=(2198187759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053352919/2000000000 : ℝ)|^8403 ≤ (42835811141137/100000000000000 : ℝ)^6355
        have hw : |(1053352919/2000000000 : ℝ)|=(1053352919/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_s7_2 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068894459/2000000000 : ℝ)*x 0 + (5266764597/10000000000 : ℝ)*x 1 + (-2198187759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068894459/2000000000 : ℝ)^8403 ≤ (21836741389013/50000000000000 : ℝ)^6355 := by
    have hnat : (1068894459 : ℕ)^8403*50000000000000^6355 ≤ 21836741389013^6355*2000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068894459 2000000000 21836741389013 50000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266764597/10000000000 : ℝ)^8403 ≤ (8567162232529/20000000000000 : ℝ)^6355 := by
    have hnat : (5266764597 : ℕ)^8403*20000000000000^6355 ≤ 8567162232529^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266764597 10000000000 8567162232529 20000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2198187759/10000000000 : ℝ)^8403 ≤ (13490706053917/100000000000000 : ℝ)^6355 := by
    have hnat : (2198187759 : ℕ)^8403*100000000000000^6355 ≤ 13490706053917^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2198187759 10000000000 13490706053917 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068894459/2000000000 : ℝ), (5266764597/10000000000 : ℝ), (-2198187759/10000000000 : ℝ)] ![(21836741389013/50000000000000 : ℝ), (8567162232529/20000000000000 : ℝ), (13490706053917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068894459/2000000000 : ℝ)|^8403 ≤ (21836741389013/50000000000000 : ℝ)^6355
        have hw : |(1068894459/2000000000 : ℝ)|=(1068894459/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266764597/10000000000 : ℝ)|^8403 ≤ (8567162232529/20000000000000 : ℝ)^6355
        have hw : |(5266764597/10000000000 : ℝ)|=(5266764597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2198187759/10000000000 : ℝ)|^8403 ≤ (13490706053917/100000000000000 : ℝ)^6355
        have hw : |(-2198187759/10000000000 : ℝ)|=(2198187759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_s7_3 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4355180223/10000000000 : ℝ)*x 0 + (21154639/50000000 : ℝ)*x 1 + (4483005317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4355180223/10000000000 : ℝ)^8403 ≤ (6663464700653/20000000000000 : ℝ)^6355 := by
    have hnat : (4355180223 : ℕ)^8403*20000000000000^6355 ≤ 6663464700653^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355180223 10000000000 6663464700653 20000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21154639/50000000 : ℝ)^8403 ≤ (16033138475413/50000000000000 : ℝ)^6355 := by
    have hnat : (21154639 : ℕ)^8403*50000000000000^6355 ≤ 16033138475413^6355*50000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21154639 50000000 16033138475413 50000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4483005317/10000000000 : ℝ)^8403 ≤ (34616399532821/100000000000000 : ℝ)^6355 := by
    have hnat : (4483005317 : ℕ)^8403*100000000000000^6355 ≤ 34616399532821^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483005317 10000000000 34616399532821 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4355180223/10000000000 : ℝ), (21154639/50000000 : ℝ), (4483005317/10000000000 : ℝ)] ![(6663464700653/20000000000000 : ℝ), (16033138475413/50000000000000 : ℝ), (34616399532821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4355180223/10000000000 : ℝ)|^8403 ≤ (6663464700653/20000000000000 : ℝ)^6355
        have hw : |(4355180223/10000000000 : ℝ)|=(4355180223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21154639/50000000 : ℝ)|^8403 ≤ (16033138475413/50000000000000 : ℝ)^6355
        have hw : |(21154639/50000000 : ℝ)|=(21154639/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4483005317/10000000000 : ℝ)|^8403 ≤ (34616399532821/100000000000000 : ℝ)^6355
        have hw : |(4483005317/10000000000 : ℝ)|=(4483005317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_s7_4 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2134788563/10000000000 : ℝ)*x 0 + (5267079559/10000000000 : ℝ)*x 1 + (215659369/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2134788563/10000000000 : ℝ)^8403 ≤ (6489314057891/50000000000000 : ℝ)^6355 := by
    have hnat : (2134788563 : ℕ)^8403*50000000000000^6355 ≤ 6489314057891^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134788563 10000000000 6489314057891 50000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267079559/10000000000 : ℝ)^8403 ≤ (10709799597291/25000000000000 : ℝ)^6355 := by
    have hnat : (5267079559 : ℕ)^8403*25000000000000^6355 ≤ 10709799597291^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267079559 10000000000 10709799597291 25000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215659369/400000000 : ℝ)^8403 ≤ (1380692921093/3125000000000 : ℝ)^6355 := by
    have hnat : (215659369 : ℕ)^8403*3125000000000^6355 ≤ 1380692921093^6355*400000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215659369 400000000 1380692921093 3125000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2134788563/10000000000 : ℝ), (5267079559/10000000000 : ℝ), (215659369/400000000 : ℝ)] ![(6489314057891/50000000000000 : ℝ), (10709799597291/25000000000000 : ℝ), (1380692921093/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2134788563/10000000000 : ℝ)|^8403 ≤ (6489314057891/50000000000000 : ℝ)^6355
        have hw : |(-2134788563/10000000000 : ℝ)|=(2134788563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267079559/10000000000 : ℝ)|^8403 ≤ (10709799597291/25000000000000 : ℝ)^6355
        have hw : |(5267079559/10000000000 : ℝ)|=(5267079559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215659369/400000000 : ℝ)|^8403 ≤ (1380692921093/3125000000000 : ℝ)^6355
        have hw : |(215659369/400000000 : ℝ)|=(215659369/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_s7_5 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656319369/5000000000 : ℝ)*x 0 + (-2073468139/10000000000 : ℝ)*x 1 + (5391484223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656319369/5000000000 : ℝ)^8403 ≤ (43329846196649/100000000000000 : ℝ)^6355 := by
    have hnat : (2656319369 : ℕ)^8403*100000000000000^6355 ≤ 43329846196649^6355*5000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656319369 5000000000 43329846196649 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2073468139/10000000000 : ℝ)^8403 ≤ (12487980332171/100000000000000 : ℝ)^6355 := by
    have hnat : (2073468139 : ℕ)^8403*100000000000000^6355 ≤ 12487980332171^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073468139 10000000000 12487980332171 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391484223/10000000000 : ℝ)^8403 ≤ (8836434690661/20000000000000 : ℝ)^6355 := by
    have hnat : (5391484223 : ℕ)^8403*20000000000000^6355 ≤ 8836434690661^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391484223 10000000000 8836434690661 20000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656319369/5000000000 : ℝ), (-2073468139/10000000000 : ℝ), (5391484223/10000000000 : ℝ)] ![(43329846196649/100000000000000 : ℝ), (12487980332171/100000000000000 : ℝ), (8836434690661/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656319369/5000000000 : ℝ)|^8403 ≤ (43329846196649/100000000000000 : ℝ)^6355
        have hw : |(2656319369/5000000000 : ℝ)|=(2656319369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2073468139/10000000000 : ℝ)|^8403 ≤ (12487980332171/100000000000000 : ℝ)^6355
        have hw : |(-2073468139/10000000000 : ℝ)|=(2073468139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391484223/10000000000 : ℝ)|^8403 ≤ (8836434690661/20000000000000 : ℝ)^6355
        have hw : |(5391484223/10000000000 : ℝ)|=(5391484223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_s7_6 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656319373/5000000000 : ℝ)*x 0 + (673935527/1250000000 : ℝ)*x 1 + (-1036734069/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656319373/5000000000 : ℝ)^8403 ≤ (10832461570731/25000000000000 : ℝ)^6355 := by
    have hnat : (2656319373 : ℕ)^8403*25000000000000^6355 ≤ 10832461570731^6355*5000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656319373 5000000000 10832461570731 25000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (673935527/1250000000 : ℝ)^8403 ≤ (8836434675491/20000000000000 : ℝ)^6355 := by
    have hnat : (673935527 : ℕ)^8403*20000000000000^6355 ≤ 8836434675491^6355*1250000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673935527 1250000000 8836434675491 20000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036734069/5000000000 : ℝ)^8403 ≤ (12487980324207/100000000000000 : ℝ)^6355 := by
    have hnat : (1036734069 : ℕ)^8403*100000000000000^6355 ≤ 12487980324207^6355*5000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036734069 5000000000 12487980324207 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656319373/5000000000 : ℝ), (673935527/1250000000 : ℝ), (-1036734069/5000000000 : ℝ)] ![(10832461570731/25000000000000 : ℝ), (8836434675491/20000000000000 : ℝ), (12487980324207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656319373/5000000000 : ℝ)|^8403 ≤ (10832461570731/25000000000000 : ℝ)^6355
        have hw : |(2656319373/5000000000 : ℝ)|=(2656319373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(673935527/1250000000 : ℝ)|^8403 ≤ (8836434675491/20000000000000 : ℝ)^6355
        have hw : |(673935527/1250000000 : ℝ)|=(673935527/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1036734069/5000000000 : ℝ)|^8403 ≤ (12487980324207/100000000000000 : ℝ)^6355
        have hw : |(-1036734069/5000000000 : ℝ)|=(1036734069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_s7_7 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (871037951/2000000000 : ℝ)*x 0 + (560296291/1250000000 : ℝ)*x 1 + (4231565091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871037951/2000000000 : ℝ)^8403 ≤ (3331741992323/10000000000000 : ℝ)^6355 := by
    have hnat : (871037951 : ℕ)^8403*10000000000000^6355 ≤ 3331741992323^6355*2000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871037951 2000000000 3331741992323 10000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (560296291/1250000000 : ℝ)^8403 ≤ (34609916357907/100000000000000 : ℝ)^6355 := by
    have hnat : (560296291 : ℕ)^8403*100000000000000^6355 ≤ 34609916357907^6355*1250000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560296291 1250000000 34609916357907 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4231565091/10000000000 : ℝ)^8403 ≤ (32072663702921/100000000000000 : ℝ)^6355 := by
    have hnat : (4231565091 : ℕ)^8403*100000000000000^6355 ≤ 32072663702921^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4231565091 10000000000 32072663702921 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871037951/2000000000 : ℝ), (560296291/1250000000 : ℝ), (4231565091/10000000000 : ℝ)] ![(3331741992323/10000000000000 : ℝ), (34609916357907/100000000000000 : ℝ), (32072663702921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871037951/2000000000 : ℝ)|^8403 ≤ (3331741992323/10000000000000 : ℝ)^6355
        have hw : |(871037951/2000000000 : ℝ)|=(871037951/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(560296291/1250000000 : ℝ)|^8403 ≤ (34609916357907/100000000000000 : ℝ)^6355
        have hw : |(560296291/1250000000 : ℝ)|=(560296291/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4231565091/10000000000 : ℝ)|^8403 ≤ (32072663702921/100000000000000 : ℝ)^6355
        have hw : |(4231565091/10000000000 : ℝ)|=(4231565091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1210_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37700547/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5717/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11439/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1761/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14093/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5717/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14093/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5717/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14093/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5717/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14093/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5717/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14093/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5717/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14093/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5717/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5717/50000 : ℝ) ^ (4201/1024 : ℝ) ≤ (2736851744652893/20000000000000000000 : ℝ) := by
    have hpowers : (5717/50000 : ℝ)^4201 ≤ (2736851744652893/20000000000000000000 : ℝ)^1024 := by
      have hnat : (5717 : ℕ)^4201*20000000000000000000^1024 ≤ 2736851744652893^1024*50000^4201 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5717 50000 2736851744652893 20000000000000000000 4201 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5717/50000 : ℝ)) (X := (2736851744652893/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4201 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14093/100000 : ℝ) ^ (4201/1024 : ℝ) ≤ (32266615914263481/100000000000000000000 : ℝ) := by
    have hpowers : (14093/100000 : ℝ)^4201 ≤ (32266615914263481/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14093 : ℕ)^4201*100000000000000000000^1024 ≤ 32266615914263481^1024*100000^4201 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14093 100000 32266615914263481 100000000000000000000 4201 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14093/100000 : ℝ)) (X := (32266615914263481/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4201 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002736851744652893/10000000000000000000 : ℝ) ≤ (2500166760664539/2500000000000000 : ℝ) ^ (4201/1024 : ℝ) := by
    have hpowers : (10002736851744652893/10000000000000000000 : ℝ)^1024 ≤ (2500166760664539/2500000000000000 : ℝ)^4201 := by
      have hnat : (10002736851744652893 : ℕ)^1024*2500000000000000^4201 ≤ 2500166760664539^4201*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002736851744652893 10000000000000000000 2500166760664539 2500000000000000 1024 4201 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500166760664539/2500000000000000 : ℝ)) (X := (10002736851744652893/10000000000000000000 : ℝ)) (by norm_num) 4201 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022975437318763973/50000000000000000000 : ℝ) ≤ (625069991552877/625000000000000 : ℝ) ^ (4201/1024 : ℝ) := by
    have hpowers : (50022975437318763973/50000000000000000000 : ℝ)^1024 ≤ (625069991552877/625000000000000 : ℝ)^4201 := by
      have hnat : (50022975437318763973 : ℕ)^1024*625000000000000^4201 ≤ 625069991552877^4201*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022975437318763973 50000000000000000000 625069991552877 625000000000000 1024 4201 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625069991552877/625000000000000 : ℝ)) (X := (50022975437318763973/50000000000000000000 : ℝ)) (by norm_num) 4201 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032266615914263481/50000000000000000000 : ℝ) ≤ (2500393171758477/2500000000000000 : ℝ) ^ (4201/1024 : ℝ) := by
    have hpowers : (50032266615914263481/50000000000000000000 : ℝ)^1024 ≤ (2500393171758477/2500000000000000 : ℝ)^4201 := by
      have hnat : (50032266615914263481 : ℕ)^1024*2500000000000000^4201 ≤ 2500393171758477^4201*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032266615914263481 50000000000000000000 2500393171758477 2500000000000000 1024 4201 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500393171758477/2500000000000000 : ℝ)) (X := (50032266615914263481/50000000000000000000 : ℝ)) (by norm_num) 4201 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2736851744652893/20000000000000000000 : ℝ) ≤ ((6645354632158922109/6647500000000000000 : ℝ)+2*(113205546969/66475000000000 : ℝ)*(5717/50000 : ℝ))^(4201/1024 : ℝ) := by
    rw [show (6645354632158922109/6647500000000000000 : ℝ)+2*(113205546969/66475000000000 : ℝ)*(5717/50000 : ℝ)=(2500166760664539/2500000000000000 : ℝ) by norm_num, show 1+2*(2736851744652893/20000000000000000000 : ℝ)=(10002736851744652893/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32266615914263481/100000000000000000000 : ℝ)+(2736851744652893/20000000000000000000 : ℝ) ≤ ((6645354632158922109/6647500000000000000 : ℝ)+(113205546969/66475000000000 : ℝ)*((14093/100000 : ℝ)+(5717/50000 : ℝ)))^(4201/1024 : ℝ) := by
    rw [show (6645354632158922109/6647500000000000000 : ℝ)+(113205546969/66475000000000 : ℝ)*((14093/100000 : ℝ)+(5717/50000 : ℝ))=(625069991552877/625000000000000 : ℝ) by norm_num, show 1+(32266615914263481/100000000000000000000 : ℝ)+(2736851744652893/20000000000000000000 : ℝ)=(50022975437318763973/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32266615914263481/100000000000000000000 : ℝ) ≤ ((6645354632158922109/6647500000000000000 : ℝ)+2*(113205546969/66475000000000 : ℝ)*(14093/100000 : ℝ))^(4201/1024 : ℝ) := by
    rw [show (6645354632158922109/6647500000000000000 : ℝ)+2*(113205546969/66475000000000 : ℝ)*(14093/100000 : ℝ)=(2500393171758477/2500000000000000 : ℝ) by norm_num, show 1+2*(32266615914263481/100000000000000000000 : ℝ)=(50032266615914263481/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6645354632158922109/6647500000000000000 : ℝ)*(X 1 0+X 2 0)+(113205546969/66475000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4201/1024 : ℝ)) (lo := (5717/50000 : ℝ)) (hi := (14093/100000 : ℝ)) (c := (6645354632158922109/6647500000000000000 : ℝ)) (alpha := (113205546969/66475000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6645354632158922109/6647500000000000000 : ℝ)*(X 0 1+X 2 1)+(113205546969/66475000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4201/1024 : ℝ)) (lo := (5717/50000 : ℝ)) (hi := (14093/100000 : ℝ)) (c := (6645354632158922109/6647500000000000000 : ℝ)) (alpha := (113205546969/66475000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6645354632158922109/6647500000000000000 : ℝ)*(X 0 2+X 1 2)+(113205546969/66475000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4201/1024 : ℝ)) (lo := (5717/50000 : ℝ)) (hi := (14093/100000 : ℝ)) (c := (6645354632158922109/6647500000000000000 : ℝ)) (alpha := (113205546969/66475000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2134783831/10000000000 : ℝ)*X 0 0+(2695900167/5000000000 : ℝ)*X 0 1+(1053352919/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668059037/1250000000 : ℝ)*X 1 0+(-2198187759/10000000000 : ℝ)*X 1 1+(1053352919/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068894459/2000000000 : ℝ)*X 2 0+(5266764597/10000000000 : ℝ)*X 2 1+(-2198187759/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4355180223/10000000000 : ℝ)*X 0 0+(21154639/50000000 : ℝ)*X 0 1+(4483005317/10000000000 : ℝ)*X 0 2+(4355180223/10000000000 : ℝ)*X 1 0+(21154639/50000000 : ℝ)*X 1 1+(4483005317/10000000000 : ℝ)*X 1 2+(4355180223/10000000000 : ℝ)*X 2 0+(21154639/50000000 : ℝ)*X 2 1+(4483005317/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2134788563/10000000000 : ℝ)*X 0 0+(5267079559/10000000000 : ℝ)*X 0 1+(215659369/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656319369/5000000000 : ℝ)*X 1 0+(-2073468139/10000000000 : ℝ)*X 1 1+(5391484223/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656319373/5000000000 : ℝ)*X 2 0+(673935527/1250000000 : ℝ)*X 2 1+(-1036734069/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((871037951/2000000000 : ℝ)*X 0 0+(560296291/1250000000 : ℝ)*X 0 1+(4231565091/10000000000 : ℝ)*X 0 2+(871037951/2000000000 : ℝ)*X 1 0+(560296291/1250000000 : ℝ)*X 1 1+(4231565091/10000000000 : ℝ)*X 1 2+(871037951/2000000000 : ℝ)*X 2 0+(560296291/1250000000 : ℝ)*X 2 1+(4231565091/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (117263604303812000006730333/16618750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1370576157/100000000000000 : ℝ)*(base19) + (79623193/6250000000000 : ℝ)*(base23) + (50830533/100000000000000 : ℝ)*(lower2) + (35336407/20000000000000 : ℝ)*(upper3) + (107363421/100000000000000 : ℝ)*(upper5) + (299121582335921/5000000000000 : ℝ)*(major0) + (299121582335921/5000000000000 : ℝ)*(major1) + (299121582335921/5000000000000 : ℝ)*(major2) + (199943825749999/2500000000000 : ℝ)*(sp0) + (3998894753915127/50000000000000 : ℝ)*(sp1) + (7997789604435323/100000000000000 : ℝ)*(sp2) + (1983525962621859/50000000000000 : ℝ)*(sp3) + (37848406451/100000000000000 : ℝ)*(sp4) + (2531822911/12500000000000 : ℝ)*(sp7) + (1983536089913503/50000000000000 : ℝ)*(f.failure) + (7997790878406411/100000000000000 : ℝ)*(f.sum) + (961878918279/531800000000000000000000000 : ℝ)*base66 + (92699235182089889/33237500000000000000000000000000 : ℝ)*base67 + (55159075708960111/33237500000000000000000000000000 : ℝ)*base70 + (48955822602402389/33237500000000000000000000000000 : ℝ)*base71 + (4863358532891/1329500000000000000000000000 : ℝ)*base73 + (180730604230477389/33237500000000000000000000000000 : ℝ)*base75 + (204532812407914889/33237500000000000000000000000000 : ℝ)*base77 + (180474395568385111/33237500000000000000000000000000 : ℝ)*base80 + (1007821695779/2659000000000000000000000000 : ℝ)*base82 + (4213859/1250000000000000000000 : ℝ)*base90 + (4213859/1250000000000000000000 : ℝ)*base92 + (4213859/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (552949636775430297581220237/66475000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (744745067/50000000000000 : ℝ)*(base19) + (1625887887/100000000000000 : ℝ)*(base23) + (165504041/100000000000000 : ℝ)*(upper3) + (56655669/100000000000000 : ℝ)*(lower4) + (172912749/100000000000000 : ℝ)*(upper5) + (1202543990641669/20000000000000 : ℝ)*(major0) + (1202543990641669/20000000000000 : ℝ)*(major1) + (1202543990641669/20000000000000 : ℝ)*(major2) + (41639170311/100000000000000 : ℝ)*(sp1) + (44584786043/100000000000000 : ℝ)*(sp2) + (8038282656854389/100000000000000 : ℝ)*(sp4) + (1004779941024243/12500000000000 : ℝ)*(sp5) + (4019118223090229/50000000000000 : ℝ)*(sp6) + (498394621536289/12500000000000 : ℝ)*(sp7) + (498394621536289/12500000000000 : ℝ)*(f.failure) + (8038282656854389/100000000000000 : ℝ)*(f.sum) + (7429389334617/2659000000000000000000000000 : ℝ)*base65 + (1006222525595209921/132950000000000000000000000000000 : ℝ)*base67 + (122578165938290079/132950000000000000000000000000000 : ℝ)*base70 + (1662624216862740079/132950000000000000000000000000000 : ℝ)*base72 + (133569753051/531800000000000000000000000 : ℝ)*base73 + (3135418615357309921/132950000000000000000000000000000 : ℝ)*base75 + (1719836818893509921/132950000000000000000000000000000 : ℝ)*base77 + (2954546789718609921/132950000000000000000000000000000 : ℝ)*base79 + (2366589287413/531800000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (2474917/312500000000000000000 : ℝ)*base90 + (2474917/312500000000000000000 : ℝ)*base92 + (2474917/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1210_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37700547/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5717/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11439/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1761/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1210_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1210_s8_0 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-85391489/400000000 : ℝ)*x 0 + (539175281/1000000000 : ℝ)*x 1 + (2633404971/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85391489/400000000 : ℝ)^8403 ≤ (12978617359831/100000000000000 : ℝ)^6355 := by
    have hnat : (85391489 : ℕ)^8403*100000000000000^6355 ≤ 12978617359831^6355*400000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85391489 400000000 12978617359831 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539175281/1000000000 : ℝ)^8403 ≤ (44185083808667/100000000000000 : ℝ)^6355 := by
    have hnat : (539175281 : ℕ)^8403*100000000000000^6355 ≤ 44185083808667^6355*1000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539175281 1000000000 44185083808667 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633404971/5000000000 : ℝ)^8403 ≤ (42836298816773/100000000000000 : ℝ)^6355 := by
    have hnat : (2633404971 : ℕ)^8403*100000000000000^6355 ≤ 42836298816773^6355*5000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633404971 5000000000 42836298816773 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-85391489/400000000 : ℝ), (539175281/1000000000 : ℝ), (2633404971/5000000000 : ℝ)] ![(12978617359831/100000000000000 : ℝ), (44185083808667/100000000000000 : ℝ), (42836298816773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-85391489/400000000 : ℝ)|^8403 ≤ (12978617359831/100000000000000 : ℝ)^6355
        have hw : |(-85391489/400000000 : ℝ)|=(85391489/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539175281/1000000000 : ℝ)|^8403 ≤ (44185083808667/100000000000000 : ℝ)^6355
        have hw : |(539175281/1000000000 : ℝ)|=(539175281/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633404971/5000000000 : ℝ)|^8403 ≤ (42836298816773/100000000000000 : ℝ)^6355
        have hw : |(2633404971/5000000000 : ℝ)|=(2633404971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_s8_1 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (267223023/500000000 : ℝ)*x 0 + (-2198143399/10000000000 : ℝ)*x 1 + (5266809961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267223023/500000000 : ℝ)^8403 ≤ (21836677449413/50000000000000 : ℝ)^6355 := by
    have hnat : (267223023 : ℕ)^8403*50000000000000^6355 ≤ 21836677449413^6355*500000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267223023 500000000 21836677449413 50000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2198143399/10000000000 : ℝ)^8403 ≤ (674517303677/5000000000000 : ℝ)^6355 := by
    have hnat : (2198143399 : ℕ)^8403*5000000000000^6355 ≤ 674517303677^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2198143399 10000000000 674517303677 5000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266809961/10000000000 : ℝ)^8403 ≤ (21418149510553/50000000000000 : ℝ)^6355 := by
    have hnat : (5266809961 : ℕ)^8403*50000000000000^6355 ≤ 21418149510553^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266809961 10000000000 21418149510553 50000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267223023/500000000 : ℝ), (-2198143399/10000000000 : ℝ), (5266809961/10000000000 : ℝ)] ![(21836677449413/50000000000000 : ℝ), (674517303677/5000000000000 : ℝ), (21418149510553/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267223023/500000000 : ℝ)|^8403 ≤ (21836677449413/50000000000000 : ℝ)^6355
        have hw : |(267223023/500000000 : ℝ)|=(267223023/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2198143399/10000000000 : ℝ)|^8403 ≤ (674517303677/5000000000000 : ℝ)^6355
        have hw : |(-2198143399/10000000000 : ℝ)|=(2198143399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266809961/10000000000 : ℝ)|^8403 ≤ (21418149510553/50000000000000 : ℝ)^6355
        have hw : |(5266809961/10000000000 : ℝ)|=(5266809961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_s8_2 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672230249/5000000000 : ℝ)*x 0 + (5266809911/10000000000 : ℝ)*x 1 + (-1099071707/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672230249/5000000000 : ℝ)^8403 ≤ (21836677654711/50000000000000 : ℝ)^6355 := by
    have hnat : (2672230249 : ℕ)^8403*50000000000000^6355 ≤ 21836677654711^6355*5000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672230249 5000000000 21836677654711 50000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266809911/10000000000 : ℝ)^8403 ≤ (42836298483389/100000000000000 : ℝ)^6355 := by
    have hnat : (5266809911 : ℕ)^8403*100000000000000^6355 ≤ 42836298483389^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266809911 10000000000 42836298483389 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1099071707/5000000000 : ℝ)^8403 ≤ (210786659301/1562500000000 : ℝ)^6355 := by
    have hnat : (1099071707 : ℕ)^8403*1562500000000^6355 ≤ 210786659301^6355*5000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099071707 5000000000 210786659301 1562500000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672230249/5000000000 : ℝ), (5266809911/10000000000 : ℝ), (-1099071707/5000000000 : ℝ)] ![(21836677654711/50000000000000 : ℝ), (42836298483389/100000000000000 : ℝ), (210786659301/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672230249/5000000000 : ℝ)|^8403 ≤ (21836677654711/50000000000000 : ℝ)^6355
        have hw : |(2672230249/5000000000 : ℝ)|=(2672230249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266809911/10000000000 : ℝ)|^8403 ≤ (42836298483389/100000000000000 : ℝ)^6355
        have hw : |(5266809911/10000000000 : ℝ)|=(5266809911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1099071707/5000000000 : ℝ)|^8403 ≤ (210786659301/1562500000000 : ℝ)^6355
        have hw : |(-1099071707/5000000000 : ℝ)|=(1099071707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_s8_3 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (871036523/2000000000 : ℝ)*x 0 + (2115510529/5000000000 : ℝ)*x 1 + (4482911411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871036523/2000000000 : ℝ)^8403 ≤ (4164668462411/12500000000000 : ℝ)^6355 := by
    have hnat : (871036523 : ℕ)^8403*12500000000000^6355 ≤ 4164668462411^6355*2000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871036523 2000000000 4164668462411 12500000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2115510529/5000000000 : ℝ)^8403 ≤ (32067211537047/100000000000000 : ℝ)^6355 := by
    have hnat : (2115510529 : ℕ)^8403*100000000000000^6355 ≤ 32067211537047^6355*5000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115510529 5000000000 32067211537047 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4482911411/10000000000 : ℝ)^8403 ≤ (34615440743197/100000000000000 : ℝ)^6355 := by
    have hnat : (4482911411 : ℕ)^8403*100000000000000^6355 ≤ 34615440743197^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4482911411 10000000000 34615440743197 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871036523/2000000000 : ℝ), (2115510529/5000000000 : ℝ), (4482911411/10000000000 : ℝ)] ![(4164668462411/12500000000000 : ℝ), (32067211537047/100000000000000 : ℝ), (34615440743197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871036523/2000000000 : ℝ)|^8403 ≤ (4164668462411/12500000000000 : ℝ)^6355
        have hw : |(871036523/2000000000 : ℝ)|=(871036523/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2115510529/5000000000 : ℝ)|^8403 ≤ (32067211537047/100000000000000 : ℝ)^6355
        have hw : |(2115510529/5000000000 : ℝ)|=(2115510529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4482911411/10000000000 : ℝ)|^8403 ≤ (34615440743197/100000000000000 : ℝ)^6355
        have hw : |(4482911411/10000000000 : ℝ)|=(4482911411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_s8_4 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2134791987/10000000000 : ℝ)*x 0 + (2633562191/5000000000 : ℝ)*x 1 + (2695718599/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2134791987/10000000000 : ℝ)^8403 ≤ (2595731128147/20000000000000 : ℝ)^6355 := by
    have hnat : (2134791987 : ℕ)^8403*20000000000000^6355 ≤ 2595731128147^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134791987 10000000000 2595731128147 20000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633562191/5000000000 : ℝ)^8403 ≤ (1713587217553/4000000000000 : ℝ)^6355 := by
    have hnat : (2633562191 : ℕ)^8403*4000000000000^6355 ≤ 1713587217553^6355*5000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633562191 5000000000 1713587217553 4000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695718599/5000000000 : ℝ)^8403 ≤ (8836332780911/20000000000000 : ℝ)^6355 := by
    have hnat : (2695718599 : ℕ)^8403*20000000000000^6355 ≤ 8836332780911^6355*5000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695718599 5000000000 8836332780911 20000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2134791987/10000000000 : ℝ), (2633562191/5000000000 : ℝ), (2695718599/5000000000 : ℝ)] ![(2595731128147/20000000000000 : ℝ), (1713587217553/4000000000000 : ℝ), (8836332780911/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2134791987/10000000000 : ℝ)|^8403 ≤ (2595731128147/20000000000000 : ℝ)^6355
        have hw : |(-2134791987/10000000000 : ℝ)|=(2134791987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633562191/5000000000 : ℝ)|^8403 ≤ (1713587217553/4000000000000 : ℝ)^6355
        have hw : |(2633562191/5000000000 : ℝ)|=(2633562191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695718599/5000000000 : ℝ)|^8403 ≤ (8836332780911/20000000000000 : ℝ)^6355
        have hw : |(2695718599/5000000000 : ℝ)|=(2695718599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_s8_5 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (66408131/125000000 : ℝ)*x 0 + (-1036758127/5000000000 : ℝ)*x 1 + (215657487/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66408131/125000000 : ℝ)^8403 ≤ (43329972827027/100000000000000 : ℝ)^6355 := by
    have hnat : (66408131 : ℕ)^8403*100000000000000^6355 ≤ 43329972827027^6355*125000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66408131 125000000 43329972827027 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036758127/5000000000 : ℝ)^8403 ≤ (3122090876483/25000000000000 : ℝ)^6355 := by
    have hnat : (1036758127 : ℕ)^8403*25000000000000^6355 ≤ 3122090876483^6355*5000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036758127 5000000000 3122090876483 25000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215657487/400000000 : ℝ)^8403 ≤ (8836332731067/20000000000000 : ℝ)^6355 := by
    have hnat : (215657487 : ℕ)^8403*20000000000000^6355 ≤ 8836332731067^6355*400000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215657487 400000000 8836332731067 20000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66408131/125000000 : ℝ), (-1036758127/5000000000 : ℝ), (215657487/400000000 : ℝ)] ![(43329972827027/100000000000000 : ℝ), (3122090876483/25000000000000 : ℝ), (8836332731067/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66408131/125000000 : ℝ)|^8403 ≤ (43329972827027/100000000000000 : ℝ)^6355
        have hw : |(66408131/125000000 : ℝ)|=(66408131/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1036758127/5000000000 : ℝ)|^8403 ≤ (3122090876483/25000000000000 : ℝ)^6355
        have hw : |(-1036758127/5000000000 : ℝ)|=(1036758127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215657487/400000000 : ℝ)|^8403 ≤ (8836332731067/20000000000000 : ℝ)^6355
        have hw : |(215657487/400000000 : ℝ)|=(215657487/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_s8_6 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656325289/5000000000 : ℝ)*x 0 + (5391437113/10000000000 : ℝ)*x 1 + (-518379051/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656325289/5000000000 : ℝ)^8403 ≤ (21664986941949/50000000000000 : ℝ)^6355 := by
    have hnat : (2656325289 : ℕ)^8403*50000000000000^6355 ≤ 21664986941949^6355*5000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656325289 5000000000 21664986941949 50000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391437113/10000000000 : ℝ)^8403 ≤ (22090831491761/50000000000000 : ℝ)^6355 := by
    have hnat : (5391437113 : ℕ)^8403*50000000000000^6355 ≤ 22090831491761^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391437113 10000000000 22090831491761 50000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (518379051/2500000000 : ℝ)^8403 ≤ (6244181553873/50000000000000 : ℝ)^6355 := by
    have hnat : (518379051 : ℕ)^8403*50000000000000^6355 ≤ 6244181553873^6355*2500000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518379051 2500000000 6244181553873 50000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656325289/5000000000 : ℝ), (5391437113/10000000000 : ℝ), (-518379051/2500000000 : ℝ)] ![(21664986941949/50000000000000 : ℝ), (22090831491761/50000000000000 : ℝ), (6244181553873/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656325289/5000000000 : ℝ)|^8403 ≤ (21664986941949/50000000000000 : ℝ)^6355
        have hw : |(2656325289/5000000000 : ℝ)|=(2656325289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391437113/10000000000 : ℝ)|^8403 ≤ (22090831491761/50000000000000 : ℝ)^6355
        have hw : |(5391437113/10000000000 : ℝ)|=(5391437113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-518379051/2500000000 : ℝ)|^8403 ≤ (6244181553873/50000000000000 : ℝ)^6355
        have hw : |(-518379051/2500000000 : ℝ)|=(518379051/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1210_s8_7 (p : ℝ) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2177596031/5000000000 : ℝ)*x 0 + (2241138697/5000000000 : ℝ)*x 1 + (4231657437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177596031/5000000000 : ℝ)^8403 ≤ (33317443259461/100000000000000 : ℝ)^6355 := by
    have hnat : (2177596031 : ℕ)^8403*100000000000000^6355 ≤ 33317443259461^6355*5000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177596031 5000000000 33317443259461 100000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2241138697/5000000000 : ℝ)^8403 ≤ (17304483767891/50000000000000 : ℝ)^6355 := by
    have hnat : (2241138697 : ℕ)^8403*50000000000000^6355 ≤ 17304483767891^6355*5000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241138697 5000000000 17304483767891 50000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4231657437/10000000000 : ℝ)^8403 ≤ (3207358919441/10000000000000 : ℝ)^6355 := by
    have hnat : (4231657437 : ℕ)^8403*10000000000000^6355 ≤ 3207358919441^6355*10000000000^8403 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4231657437 10000000000 3207358919441 10000000000000 8403 6355 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8403/2048 : ℝ)) 8403 6355 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2177596031/5000000000 : ℝ), (2241138697/5000000000 : ℝ), (4231657437/10000000000 : ℝ)] ![(33317443259461/100000000000000 : ℝ), (17304483767891/50000000000000 : ℝ), (3207358919441/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2177596031/5000000000 : ℝ)|^8403 ≤ (33317443259461/100000000000000 : ℝ)^6355
        have hw : |(2177596031/5000000000 : ℝ)|=(2177596031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2241138697/5000000000 : ℝ)|^8403 ≤ (17304483767891/50000000000000 : ℝ)^6355
        have hw : |(2241138697/5000000000 : ℝ)|=(2241138697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4231657437/10000000000 : ℝ)|^8403 ≤ (3207358919441/10000000000000 : ℝ)^6355
        have hw : |(4231657437/10000000000 : ℝ)|=(4231657437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1210_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37700547/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1761/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11439/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (143/1250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14087/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1761/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11439/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1761/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11439/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1761/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11439/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1761/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11439/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1761/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11439/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1761/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11439/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11439/100000 : ℝ) ^ (4201/1024 : ℝ) ≤ (2741765012170431/20000000000000000000 : ℝ) := by
    have hpowers : (11439/100000 : ℝ)^4201 ≤ (2741765012170431/20000000000000000000 : ℝ)^1024 := by
      have hnat : (11439 : ℕ)^4201*20000000000000000000^1024 ≤ 2741765012170431^1024*100000^4201 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11439 100000 2741765012170431 20000000000000000000 4201 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11439/100000 : ℝ)) (X := (2741765012170431/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4201 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1761/12500 : ℝ) ^ (4201/1024 : ℝ) ≤ (32219676932067879/100000000000000000000 : ℝ) := by
    have hpowers : (1761/12500 : ℝ)^4201 ≤ (32219676932067879/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1761 : ℕ)^4201*100000000000000000000^1024 ≤ 32219676932067879^1024*12500^4201 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1761 12500 32219676932067879 100000000000000000000 4201 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1761/12500 : ℝ)) (X := (32219676932067879/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4201 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002741765012170431/10000000000000000000 : ℝ) ≤ (2000133648005277/2000000000000000 : ℝ) ^ (4201/1024 : ℝ) := by
    have hpowers : (10002741765012170431/10000000000000000000 : ℝ)^1024 ≤ (2000133648005277/2000000000000000 : ℝ)^4201 := by
      have hnat : (10002741765012170431 : ℕ)^1024*2000000000000000^4201 ≤ 2000133648005277^4201*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002741765012170431 10000000000000000000 2000133648005277 2000000000000000 1024 4201 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000133648005277/2000000000000000 : ℝ)) (X := (10002741765012170431/10000000000000000000 : ℝ)) (by norm_num) 4201 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022964250996460017/50000000000000000000 : ℝ) ≤ (80008954557591/80000000000000 : ℝ) ^ (4201/1024 : ℝ) := by
    have hpowers : (50022964250996460017/50000000000000000000 : ℝ)^1024 ≤ (80008954557591/80000000000000 : ℝ)^4201 := by
      have hnat : (50022964250996460017 : ℕ)^1024*80000000000000^4201 ≤ 80008954557591^4201*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022964250996460017 50000000000000000000 80008954557591 80000000000000 1024 4201 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80008954557591/80000000000000 : ℝ)) (X := (50022964250996460017/50000000000000000000 : ℝ)) (by norm_num) 4201 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032219676932067879/50000000000000000000 : ℝ) ≤ (2000314079874273/2000000000000000 : ℝ) ^ (4201/1024 : ℝ) := by
    have hpowers : (50032219676932067879/50000000000000000000 : ℝ)^1024 ≤ (2000314079874273/2000000000000000 : ℝ)^4201 := by
      have hnat : (50032219676932067879 : ℕ)^1024*2000000000000000^4201 ≤ 2000314079874273^4201*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032219676932067879 50000000000000000000 2000314079874273 2000000000000000 1024 4201 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000314079874273/2000000000000000 : ℝ)) (X := (50032219676932067879/50000000000000000000 : ℝ)) (by norm_num) 4201 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2741765012170431/20000000000000000000 : ℝ) ≤ ((1765430024472177843/1766000000000000000 : ℝ)+2*(15035989083/8830000000000 : ℝ)*(11439/100000 : ℝ))^(4201/1024 : ℝ) := by
    rw [show (1765430024472177843/1766000000000000000 : ℝ)+2*(15035989083/8830000000000 : ℝ)*(11439/100000 : ℝ)=(2000133648005277/2000000000000000 : ℝ) by norm_num, show 1+2*(2741765012170431/20000000000000000000 : ℝ)=(10002741765012170431/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32219676932067879/100000000000000000000 : ℝ)+(2741765012170431/20000000000000000000 : ℝ) ≤ ((1765430024472177843/1766000000000000000 : ℝ)+(15035989083/8830000000000 : ℝ)*((1761/12500 : ℝ)+(11439/100000 : ℝ)))^(4201/1024 : ℝ) := by
    rw [show (1765430024472177843/1766000000000000000 : ℝ)+(15035989083/8830000000000 : ℝ)*((1761/12500 : ℝ)+(11439/100000 : ℝ))=(80008954557591/80000000000000 : ℝ) by norm_num, show 1+(32219676932067879/100000000000000000000 : ℝ)+(2741765012170431/20000000000000000000 : ℝ)=(50022964250996460017/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32219676932067879/100000000000000000000 : ℝ) ≤ ((1765430024472177843/1766000000000000000 : ℝ)+2*(15035989083/8830000000000 : ℝ)*(1761/12500 : ℝ))^(4201/1024 : ℝ) := by
    rw [show (1765430024472177843/1766000000000000000 : ℝ)+2*(15035989083/8830000000000 : ℝ)*(1761/12500 : ℝ)=(2000314079874273/2000000000000000 : ℝ) by norm_num, show 1+2*(32219676932067879/100000000000000000000 : ℝ)=(50032219676932067879/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1765430024472177843/1766000000000000000 : ℝ)*(X 1 0+X 2 0)+(15035989083/8830000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4201/1024 : ℝ)) (lo := (11439/100000 : ℝ)) (hi := (1761/12500 : ℝ)) (c := (1765430024472177843/1766000000000000000 : ℝ)) (alpha := (15035989083/8830000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1765430024472177843/1766000000000000000 : ℝ)*(X 0 1+X 2 1)+(15035989083/8830000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4201/1024 : ℝ)) (lo := (11439/100000 : ℝ)) (hi := (1761/12500 : ℝ)) (c := (1765430024472177843/1766000000000000000 : ℝ)) (alpha := (15035989083/8830000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1765430024472177843/1766000000000000000 : ℝ)*(X 0 2+X 1 2)+(15035989083/8830000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4201/1024 : ℝ)) (lo := (11439/100000 : ℝ)) (hi := (1761/12500 : ℝ)) (c := (1765430024472177843/1766000000000000000 : ℝ)) (alpha := (15035989083/8830000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-85391489/400000000 : ℝ)*X 0 0+(539175281/1000000000 : ℝ)*X 0 1+(2633404971/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267223023/500000000 : ℝ)*X 1 0+(-2198143399/10000000000 : ℝ)*X 1 1+(5266809961/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672230249/5000000000 : ℝ)*X 2 0+(5266809911/10000000000 : ℝ)*X 2 1+(-1099071707/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((871036523/2000000000 : ℝ)*X 0 0+(2115510529/5000000000 : ℝ)*X 0 1+(4482911411/10000000000 : ℝ)*X 0 2+(871036523/2000000000 : ℝ)*X 1 0+(2115510529/5000000000 : ℝ)*X 1 1+(4482911411/10000000000 : ℝ)*X 1 2+(871036523/2000000000 : ℝ)*X 2 0+(2115510529/5000000000 : ℝ)*X 2 1+(4482911411/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2134791987/10000000000 : ℝ)*X 0 0+(2633562191/5000000000 : ℝ)*X 0 1+(2695718599/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((66408131/125000000 : ℝ)*X 1 0+(-1036758127/5000000000 : ℝ)*X 1 1+(215657487/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656325289/5000000000 : ℝ)*X 2 0+(5391437113/10000000000 : ℝ)*X 2 1+(-518379051/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2177596031/5000000000 : ℝ)*X 0 0+(2241138697/5000000000 : ℝ)*X 0 1+(4231657437/10000000000 : ℝ)*X 0 2+(2177596031/5000000000 : ℝ)*X 1 0+(2241138697/5000000000 : ℝ)*X 1 1+(4231657437/10000000000 : ℝ)*X 1 2+(2177596031/5000000000 : ℝ)*X 2 0+(2241138697/5000000000 : ℝ)*X 2 1+(4231657437/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1210_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (291665425938022398173795601/44150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (330888401/25000000000000 : ℝ)*(base19) + (7834239/625000000000 : ℝ)*(base23) + (848321/1250000000000 : ℝ)*(lower2) + (97468811/50000000000000 : ℝ)*(upper3) + (10860261/12500000000000 : ℝ)*(upper5) + (2993437985835031/50000000000000 : ℝ)*(major0) + (2993437985835031/50000000000000 : ℝ)*(major1) + (2993437985835031/50000000000000 : ℝ)*(major2) + (4001848287742731/50000000000000 : ℝ)*(sp0) + (1600746219484979/20000000000000 : ℝ)*(sp1) + (400186558375013/5000000000000 : ℝ)*(sp2) + (1984999332980113/50000000000000 : ℝ)*(sp3) + (35845493037/100000000000000 : ℝ)*(sp4) + (10318096721/50000000000000 : ℝ)*(sp7) + (992504825538417/25000000000000 : ℝ)*(f.failure) + (16007464841957/200000000000 : ℝ)*(f.sum) + (3669380180483/883000000000000000000000000 : ℝ)*base66 + (1426947093443018133/88300000000000000000000000000000 : ℝ)*base67 + (499456700475018133/88300000000000000000000000000000 : ℝ)*base69 + (567715865494181867/88300000000000000000000000000000 : ℝ)*base72 + (5785112539959/883000000000000000000000000 : ℝ)*base73 + (1085280793085518133/88300000000000000000000000000000 : ℝ)*base75 + (729090983468181867/88300000000000000000000000000000 : ℝ)*base78 + (224610098763218133/88300000000000000000000000000000 : ℝ)*base79 + (499325885977/220750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (2914099/625000000000000000000 : ℝ)*base89 + (2914099/625000000000000000000 : ℝ)*base91 + (2914099/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3676620736869963737163/441500000000000000000000000 : ℝ) := by norm_num
    linear_combination (361176361/25000000000000 : ℝ)*(base19) + (1650663781/100000000000000 : ℝ)*(base23) + (243867941/50000000000000 : ℝ)*(lower1) + (79782033/50000000000000 : ℝ)*(upper3) + (9504813/50000000000000 : ℝ)*(lower4) + (200408627/100000000000000 : ℝ)*(upper5) + (6017136438652167/100000000000000 : ℝ)*(major0) + (6017136438652167/100000000000000 : ℝ)*(major1) + (6017136438652167/100000000000000 : ℝ)*(major2) + (113720503/3125000000000 : ℝ)*(sp2) + (8044186966046001/100000000000000 : ℝ)*(sp4) + (8044185521340557/100000000000000 : ℝ)*(sp5) + (4022090838163063/50000000000000 : ℝ)*(sp6) + (1995042816836373/50000000000000 : ℝ)*(sp7) + (1995042816836373/50000000000000 : ℝ)*(f.failure) + (8044186966046001/100000000000000 : ℝ)*(f.sum) + (1163123867727/883000000000000000000000000 : ℝ)*base65 + (988384665426064219/176600000000000000000000000000000 : ℝ)*base68 + (3062844607093535781/176600000000000000000000000000000 : ℝ)*base69 + (24420495498865664219/176600000000000000000000000000000 : ℝ)*base72 + (265628413869/55187500000000000000000000 : ℝ)*base73 + (835505254424664219/176600000000000000000000000000000 : ℝ)*base76 + (851144760992735781/176600000000000000000000000000000 : ℝ)*base77 + (1783354928474735781/176600000000000000000000000000000 : ℝ)*base79 + (150435596727/44150000000000000000000000 : ℝ)*base81 + (1/50000000000000 : ℝ)*base87 + (15903969/1250000000000000000000 : ℝ)*base90 + (15903969/1250000000000000000000 : ℝ)*base92 + (15903969/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1210_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37700547/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1761/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11439/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (143/1250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14087/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1210_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1210_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37700547/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14117/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11411/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (143/1250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14087/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1210_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1210_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1210_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4201/1024 : ℝ) ≤ p) (hpb : p ≤ (8403/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37700547/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14117/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11411/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (143/1250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14087/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1210_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
