-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1354_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:08:40.087506+00:00
-- url     : https://prove2.me/submissions/ae54b054-7fb3-4984-96f0-fcecf162fc69

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
theorem support_rectangle_w1354_s3_0 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2032009807/10000000000 : ℝ)*x 0 + (2712829027/5000000000 : ℝ)*x 1 + (523247659/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2032009807/10000000000 : ℝ)^2157 ≤ (6187145633073/50000000000000 : ℝ)^1645 := by
    have hnat : (2032009807 : ℕ)^2157*50000000000000^1645 ≤ 6187145633073^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2032009807 10000000000 6187145633073 50000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2712829027/5000000000 : ℝ)^2157 ≤ (22427029181649/50000000000000 : ℝ)^1645 := by
    have hnat : (2712829027 : ℕ)^2157*50000000000000^1645 ≤ 22427029181649^1645*5000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712829027 5000000000 22427029181649 50000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (523247659/1000000000 : ℝ)^2157 ≤ (2138582517959/5000000000000 : ℝ)^1645 := by
    have hnat : (523247659 : ℕ)^2157*5000000000000^1645 ≤ 2138582517959^1645*1000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523247659 1000000000 2138582517959 5000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2032009807/10000000000 : ℝ), (2712829027/5000000000 : ℝ), (523247659/1000000000 : ℝ)] ![(6187145633073/50000000000000 : ℝ), (22427029181649/50000000000000 : ℝ), (2138582517959/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2032009807/10000000000 : ℝ)|^2157 ≤ (6187145633073/50000000000000 : ℝ)^1645
        have hw : |(-2032009807/10000000000 : ℝ)|=(2032009807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2712829027/5000000000 : ℝ)|^2157 ≤ (22427029181649/50000000000000 : ℝ)^1645
        have hw : |(2712829027/5000000000 : ℝ)|=(2712829027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(523247659/1000000000 : ℝ)|^2157 ≤ (2138582517959/5000000000000 : ℝ)^1645
        have hw : |(523247659/1000000000 : ℝ)|=(523247659/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1354_s3_1 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5352254853/10000000000 : ℝ)*x 0 + (-2130710397/10000000000 : ℝ)*x 1 + (1308119017/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352254853/10000000000 : ℝ)^2157 ≤ (44060040318477/100000000000000 : ℝ)^1645 := by
    have hnat : (5352254853 : ℕ)^2157*100000000000000^1645 ≤ 44060040318477^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352254853 10000000000 44060040318477 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2130710397/10000000000 : ℝ)^2157 ≤ (13168314902599/100000000000000 : ℝ)^1645 := by
    have hnat : (2130710397 : ℕ)^2157*100000000000000^1645 ≤ 13168314902599^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130710397 10000000000 13168314902599 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1308119017/2500000000 : ℝ)^2157 ≤ (5346455595517/12500000000000 : ℝ)^1645 := by
    have hnat : (1308119017 : ℕ)^2157*12500000000000^1645 ≤ 5346455595517^1645*2500000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308119017 2500000000 5346455595517 12500000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352254853/10000000000 : ℝ), (-2130710397/10000000000 : ℝ), (1308119017/2500000000 : ℝ)] ![(44060040318477/100000000000000 : ℝ), (13168314902599/100000000000000 : ℝ), (5346455595517/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352254853/10000000000 : ℝ)|^2157 ≤ (44060040318477/100000000000000 : ℝ)^1645
        have hw : |(5352254853/10000000000 : ℝ)|=(5352254853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2130710397/10000000000 : ℝ)|^2157 ≤ (13168314902599/100000000000000 : ℝ)^1645
        have hw : |(-2130710397/10000000000 : ℝ)|=(2130710397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1308119017/2500000000 : ℝ)|^2157 ≤ (5346455595517/12500000000000 : ℝ)^1645
        have hw : |(1308119017/2500000000 : ℝ)|=(1308119017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1354_s3_2 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5352253889/10000000000 : ℝ)*x 0 + (2616237869/5000000000 : ℝ)*x 1 + (-2130712117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352253889/10000000000 : ℝ)^2157 ≤ (44060029912823/100000000000000 : ℝ)^1645 := by
    have hnat : (5352253889 : ℕ)^2157*100000000000000^1645 ≤ 44060029912823^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352253889 10000000000 44060029912823 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2616237869/5000000000 : ℝ)^2157 ≤ (267322757669/625000000000 : ℝ)^1645 := by
    have hnat : (2616237869 : ℕ)^2157*625000000000^1645 ≤ 267322757669^1645*5000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2616237869 5000000000 267322757669 625000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2130712117/10000000000 : ℝ)^2157 ≤ (13168328841179/100000000000000 : ℝ)^1645 := by
    have hnat : (2130712117 : ℕ)^2157*100000000000000^1645 ≤ 13168328841179^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130712117 10000000000 13168328841179 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352253889/10000000000 : ℝ), (2616237869/5000000000 : ℝ), (-2130712117/10000000000 : ℝ)] ![(44060029912823/100000000000000 : ℝ), (267322757669/625000000000 : ℝ), (13168328841179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352253889/10000000000 : ℝ)|^2157 ≤ (44060029912823/100000000000000 : ℝ)^1645
        have hw : |(5352253889/10000000000 : ℝ)|=(5352253889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2616237869/5000000000 : ℝ)|^2157 ≤ (267322757669/625000000000 : ℝ)^1645
        have hw : |(2616237869/5000000000 : ℝ)|=(2616237869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2130712117/10000000000 : ℝ)|^2157 ≤ (13168328841179/100000000000000 : ℝ)^1645
        have hw : |(-2130712117/10000000000 : ℝ)|=(2130712117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1354_s3_3 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4322498833/10000000000 : ℝ)*x 0 + (824740953/2000000000 : ℝ)*x 1 + (1132541727/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4322498833/10000000000 : ℝ)^2157 ≤ (33293446222689/100000000000000 : ℝ)^1645 := by
    have hnat : (4322498833 : ℕ)^2157*100000000000000^1645 ≤ 33293446222689^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4322498833 10000000000 33293446222689 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (824740953/2000000000 : ℝ)^2157 ≤ (626004242379/2000000000000 : ℝ)^1645 := by
    have hnat : (824740953 : ℕ)^2157*2000000000000^1645 ≤ 626004242379^1645*2000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      824740953 2000000000 626004242379 2000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1132541727/2500000000 : ℝ)^2157 ≤ (3540634164397/10000000000000 : ℝ)^1645 := by
    have hnat : (1132541727 : ℕ)^2157*10000000000000^1645 ≤ 3540634164397^1645*2500000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132541727 2500000000 3540634164397 10000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4322498833/10000000000 : ℝ), (824740953/2000000000 : ℝ), (1132541727/2500000000 : ℝ)] ![(33293446222689/100000000000000 : ℝ), (626004242379/2000000000000 : ℝ), (3540634164397/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4322498833/10000000000 : ℝ)|^2157 ≤ (33293446222689/100000000000000 : ℝ)^1645
        have hw : |(4322498833/10000000000 : ℝ)|=(4322498833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(824740953/2000000000 : ℝ)|^2157 ≤ (626004242379/2000000000000 : ℝ)^1645
        have hw : |(824740953/2000000000 : ℝ)|=(824740953/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1132541727/2500000000 : ℝ)|^2157 ≤ (3540634164397/10000000000000 : ℝ)^1645
        have hw : |(1132541727/2500000000 : ℝ)|=(1132541727/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1354_s3_4 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-508007143/2500000000 : ℝ)*x 0 + (5233275517/10000000000 : ℝ)*x 1 + (5424854231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (508007143/2500000000 : ℝ)^2157 ≤ (12374441106217/100000000000000 : ℝ)^1645 := by
    have hnat : (508007143 : ℕ)^2157*100000000000000^1645 ≤ 12374441106217^1645*2500000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508007143 2500000000 12374441106217 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5233275517/10000000000 : ℝ)^2157 ≤ (42780213840887/100000000000000 : ℝ)^1645 := by
    have hnat : (5233275517 : ℕ)^2157*100000000000000^1645 ≤ 42780213840887^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233275517 10000000000 42780213840887 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5424854231/10000000000 : ℝ)^2157 ≤ (44845345036909/100000000000000 : ℝ)^1645 := by
    have hnat : (5424854231 : ℕ)^2157*100000000000000^1645 ≤ 44845345036909^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424854231 10000000000 44845345036909 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-508007143/2500000000 : ℝ), (5233275517/10000000000 : ℝ), (5424854231/10000000000 : ℝ)] ![(12374441106217/100000000000000 : ℝ), (42780213840887/100000000000000 : ℝ), (44845345036909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-508007143/2500000000 : ℝ)|^2157 ≤ (12374441106217/100000000000000 : ℝ)^1645
        have hw : |(-508007143/2500000000 : ℝ)|=(508007143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5233275517/10000000000 : ℝ)|^2157 ≤ (42780213840887/100000000000000 : ℝ)^1645
        have hw : |(5233275517/10000000000 : ℝ)|=(5233275517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5424854231/10000000000 : ℝ)|^2157 ≤ (44845345036909/100000000000000 : ℝ)^1645
        have hw : |(5424854231/10000000000 : ℝ)|=(5424854231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1354_s3_5 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (662803269/1250000000 : ℝ)*x 0 + (-969166329/5000000000 : ℝ)*x 1 + (216994169/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (662803269/1250000000 : ℝ)^2157 ≤ (43522957959771/100000000000000 : ℝ)^1645 := by
    have hnat : (662803269 : ℕ)^2157*100000000000000^1645 ≤ 43522957959771^1645*1250000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662803269 1250000000 43522957959771 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (969166329/5000000000 : ℝ)^2157 ≤ (465267882463/4000000000000 : ℝ)^1645 := by
    have hnat : (969166329 : ℕ)^2157*4000000000000^1645 ≤ 465267882463^1645*5000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      969166329 5000000000 465267882463 4000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216994169/400000000 : ℝ)^2157 ≤ (1401417030371/3125000000000 : ℝ)^1645 := by
    have hnat : (216994169 : ℕ)^2157*3125000000000^1645 ≤ 1401417030371^1645*400000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216994169 400000000 1401417030371 3125000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(662803269/1250000000 : ℝ), (-969166329/5000000000 : ℝ), (216994169/400000000 : ℝ)] ![(43522957959771/100000000000000 : ℝ), (465267882463/4000000000000 : ℝ), (1401417030371/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(662803269/1250000000 : ℝ)|^2157 ≤ (43522957959771/100000000000000 : ℝ)^1645
        have hw : |(662803269/1250000000 : ℝ)|=(662803269/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-969166329/5000000000 : ℝ)|^2157 ≤ (465267882463/4000000000000 : ℝ)^1645
        have hw : |(-969166329/5000000000 : ℝ)|=(969166329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216994169/400000000 : ℝ)|^2157 ≤ (1401417030371/3125000000000 : ℝ)^1645
        have hw : |(216994169/400000000 : ℝ)|=(216994169/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1354_s3_6 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5302425969/10000000000 : ℝ)*x 0 + (5424854351/10000000000 : ℝ)*x 1 + (-1938332733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302425969/10000000000 : ℝ)^2157 ≤ (21761477995083/50000000000000 : ℝ)^1645 := by
    have hnat : (5302425969 : ℕ)^2157*50000000000000^1645 ≤ 21761477995083^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302425969 10000000000 21761477995083 50000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5424854351/10000000000 : ℝ)^2157 ≤ (22422673168831/50000000000000 : ℝ)^1645 := by
    have hnat : (5424854351 : ℕ)^2157*50000000000000^1645 ≤ 22422673168831^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424854351 10000000000 22422673168831 50000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1938332733/10000000000 : ℝ)^2157 ≤ (5815848825861/50000000000000 : ℝ)^1645 := by
    have hnat : (1938332733 : ℕ)^2157*50000000000000^1645 ≤ 5815848825861^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1938332733 10000000000 5815848825861 50000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302425969/10000000000 : ℝ), (5424854351/10000000000 : ℝ), (-1938332733/10000000000 : ℝ)] ![(21761477995083/50000000000000 : ℝ), (22422673168831/50000000000000 : ℝ), (5815848825861/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302425969/10000000000 : ℝ)|^2157 ≤ (21761477995083/50000000000000 : ℝ)^1645
        have hw : |(5302425969/10000000000 : ℝ)|=(5302425969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5424854351/10000000000 : ℝ)|^2157 ≤ (22422673168831/50000000000000 : ℝ)^1645
        have hw : |(5424854351/10000000000 : ℝ)|=(5424854351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1938332733/10000000000 : ℝ)|^2157 ≤ (5815848825861/50000000000000 : ℝ)^1645
        have hw : |(-1938332733/10000000000 : ℝ)|=(1938332733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1354_s3_7 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4322536647/10000000000 : ℝ)*x 0 + (181139417/400000000 : ℝ)*x 1 + (4125397593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4322536647/10000000000 : ℝ)^2157 ≤ (2080864258309/6250000000000 : ℝ)^1645 := by
    have hnat : (4322536647 : ℕ)^2157*6250000000000^1645 ≤ 2080864258309^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4322536647 10000000000 2080864258309 6250000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (181139417/400000000 : ℝ)^2157 ≤ (2211819395399/6250000000000 : ℝ)^1645 := by
    have hnat : (181139417 : ℕ)^2157*6250000000000^1645 ≤ 2211819395399^1645*400000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181139417 400000000 2211819395399 6250000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4125397593/10000000000 : ℝ)^2157 ≤ (31317061522587/100000000000000 : ℝ)^1645 := by
    have hnat : (4125397593 : ℕ)^2157*100000000000000^1645 ≤ 31317061522587^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4125397593 10000000000 31317061522587 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4322536647/10000000000 : ℝ), (181139417/400000000 : ℝ), (4125397593/10000000000 : ℝ)] ![(2080864258309/6250000000000 : ℝ), (2211819395399/6250000000000 : ℝ), (31317061522587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4322536647/10000000000 : ℝ)|^2157 ≤ (2080864258309/6250000000000 : ℝ)^1645
        have hw : |(4322536647/10000000000 : ℝ)|=(4322536647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(181139417/400000000 : ℝ)|^2157 ≤ (2211819395399/6250000000000 : ℝ)^1645
        have hw : |(181139417/400000000 : ℝ)|=(181139417/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4125397593/10000000000 : ℝ)|^2157 ≤ (31317061522587/100000000000000 : ℝ)^1645
        have hw : |(4125397593/10000000000 : ℝ)|=(4125397593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1354_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155201657/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16057/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9929/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1091/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7499/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16057/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9929/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16057/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9929/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16057/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9929/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16057/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9929/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16057/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9929/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16057/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9929/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9929/100000 : ℝ) ^ (4313/1024 : ℝ) ≤ (1489334408187719/25000000000000000000 : ℝ) := by
    have hpowers : (9929/100000 : ℝ)^4313 ≤ (1489334408187719/25000000000000000000 : ℝ)^1024 := by
      have hnat : (9929 : ℕ)^4313*25000000000000000000^1024 ≤ 1489334408187719^1024*100000^4313 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9929 100000 1489334408187719 25000000000000000000 4313 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9929/100000 : ℝ)) (X := (1489334408187719/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4313 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16057/100000 : ℝ) ^ (4313/1024 : ℝ) ≤ (9023120198761231/20000000000000000000 : ℝ) := by
    have hpowers : (16057/100000 : ℝ)^4313 ≤ (9023120198761231/20000000000000000000 : ℝ)^1024 := by
      have hnat : (16057 : ℕ)^4313*20000000000000000000^1024 ≤ 9023120198761231^1024*100000^4313 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16057 100000 9023120198761231 20000000000000000000 4313 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16057/100000 : ℝ)) (X := (9023120198761231/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4313 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501489334408187719/12500000000000000000 : ℝ) ≤ (10000282867452909/10000000000000000 : ℝ) ^ (4313/1024 : ℝ) := by
    have hpowers : (12501489334408187719/12500000000000000000 : ℝ)^1024 ≤ (10000282867452909/10000000000000000 : ℝ)^4313 := by
      have hnat : (12501489334408187719 : ℕ)^1024*10000000000000000^4313 ≤ 10000282867452909^4313*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501489334408187719 12500000000000000000 10000282867452909 10000000000000000 1024 4313 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000282867452909/10000000000000000 : ℝ)) (X := (12501489334408187719/12500000000000000000 : ℝ)) (by norm_num) 4313 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051072938626557031/100000000000000000000 : ℝ) ≤ (10001212346575329/10000000000000000 : ℝ) ^ (4313/1024 : ℝ) := by
    have hpowers : (100051072938626557031/100000000000000000000 : ℝ)^1024 ≤ (10001212346575329/10000000000000000 : ℝ)^4313 := by
      have hnat : (100051072938626557031 : ℕ)^1024*10000000000000000^4313 ≤ 10001212346575329^4313*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051072938626557031 100000000000000000000 10001212346575329 10000000000000000 1024 4313 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001212346575329/10000000000000000 : ℝ)) (X := (100051072938626557031/100000000000000000000 : ℝ)) (by norm_num) 4313 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10009023120198761231/10000000000000000000 : ℝ) ≤ (10002141825697749/10000000000000000 : ℝ) ^ (4313/1024 : ℝ) := by
    have hpowers : (10009023120198761231/10000000000000000000 : ℝ)^1024 ≤ (10002141825697749/10000000000000000 : ℝ)^4313 := by
      have hnat : (10009023120198761231 : ℕ)^1024*10000000000000000^4313 ≤ 10002141825697749^4313*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10009023120198761231 10000000000000000000 10002141825697749 10000000000000000 1024 4313 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002141825697749/10000000000000000 : ℝ)) (X := (10009023120198761231/10000000000000000000 : ℝ)) (by norm_num) 4313 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1489334408187719/25000000000000000000 : ℝ) ≤ ((7657909476917301249/7660000000000000000 : ℝ)+2*(46473956121/30640000000000 : ℝ)*(9929/100000 : ℝ))^(4313/1024 : ℝ) := by
    rw [show (7657909476917301249/7660000000000000000 : ℝ)+2*(46473956121/30640000000000 : ℝ)*(9929/100000 : ℝ)=(10000282867452909/10000000000000000 : ℝ) by norm_num, show 1+2*(1489334408187719/25000000000000000000 : ℝ)=(12501489334408187719/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9023120198761231/20000000000000000000 : ℝ)+(1489334408187719/25000000000000000000 : ℝ) ≤ ((7657909476917301249/7660000000000000000 : ℝ)+(46473956121/30640000000000 : ℝ)*((16057/100000 : ℝ)+(9929/100000 : ℝ)))^(4313/1024 : ℝ) := by
    rw [show (7657909476917301249/7660000000000000000 : ℝ)+(46473956121/30640000000000 : ℝ)*((16057/100000 : ℝ)+(9929/100000 : ℝ))=(10001212346575329/10000000000000000 : ℝ) by norm_num, show 1+(9023120198761231/20000000000000000000 : ℝ)+(1489334408187719/25000000000000000000 : ℝ)=(100051072938626557031/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9023120198761231/20000000000000000000 : ℝ) ≤ ((7657909476917301249/7660000000000000000 : ℝ)+2*(46473956121/30640000000000 : ℝ)*(16057/100000 : ℝ))^(4313/1024 : ℝ) := by
    rw [show (7657909476917301249/7660000000000000000 : ℝ)+2*(46473956121/30640000000000 : ℝ)*(16057/100000 : ℝ)=(10002141825697749/10000000000000000 : ℝ) by norm_num, show 1+2*(9023120198761231/20000000000000000000 : ℝ)=(10009023120198761231/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7657909476917301249/7660000000000000000 : ℝ)*(X 1 0+X 2 0)+(46473956121/30640000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4313/1024 : ℝ)) (lo := (9929/100000 : ℝ)) (hi := (16057/100000 : ℝ)) (c := (7657909476917301249/7660000000000000000 : ℝ)) (alpha := (46473956121/30640000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7657909476917301249/7660000000000000000 : ℝ)*(X 0 1+X 2 1)+(46473956121/30640000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4313/1024 : ℝ)) (lo := (9929/100000 : ℝ)) (hi := (16057/100000 : ℝ)) (c := (7657909476917301249/7660000000000000000 : ℝ)) (alpha := (46473956121/30640000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7657909476917301249/7660000000000000000 : ℝ)*(X 0 2+X 1 2)+(46473956121/30640000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4313/1024 : ℝ)) (lo := (9929/100000 : ℝ)) (hi := (16057/100000 : ℝ)) (c := (7657909476917301249/7660000000000000000 : ℝ)) (alpha := (46473956121/30640000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2032009807/10000000000 : ℝ)*X 0 0+(2712829027/5000000000 : ℝ)*X 0 1+(523247659/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352254853/10000000000 : ℝ)*X 1 0+(-2130710397/10000000000 : ℝ)*X 1 1+(1308119017/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352253889/10000000000 : ℝ)*X 2 0+(2616237869/5000000000 : ℝ)*X 2 1+(-2130712117/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4322498833/10000000000 : ℝ)*X 0 0+(824740953/2000000000 : ℝ)*X 0 1+(1132541727/2500000000 : ℝ)*X 0 2+(4322498833/10000000000 : ℝ)*X 1 0+(824740953/2000000000 : ℝ)*X 1 1+(1132541727/2500000000 : ℝ)*X 1 2+(4322498833/10000000000 : ℝ)*X 2 0+(824740953/2000000000 : ℝ)*X 2 1+(1132541727/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-508007143/2500000000 : ℝ)*X 0 0+(5233275517/10000000000 : ℝ)*X 0 1+(5424854231/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((662803269/1250000000 : ℝ)*X 1 0+(-969166329/5000000000 : ℝ)*X 1 1+(216994169/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5302425969/10000000000 : ℝ)*X 2 0+(5424854351/10000000000 : ℝ)*X 2 1+(-1938332733/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4322536647/10000000000 : ℝ)*X 0 0+(181139417/400000000 : ℝ)*X 0 1+(4125397593/10000000000 : ℝ)*X 0 2+(4322536647/10000000000 : ℝ)*X 1 0+(181139417/400000000 : ℝ)*X 1 1+(4125397593/10000000000 : ℝ)*X 1 2+(4322536647/10000000000 : ℝ)*X 2 0+(181139417/400000000 : ℝ)*X 2 1+(4125397593/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1078720166700225541057966017/191500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1363035161/100000000000000 : ℝ)*(base19) + (1006043341/100000000000000 : ℝ)*(base23) + (37961669/10000000000000 : ℝ)*(upper3) + (90790041/20000000000000 : ℝ)*(lower4) + (2229277/2000000000000 : ℝ)*(upper5) + (1909195827158411/50000000000000 : ℝ)*(major0) + (1909195827158411/50000000000000 : ℝ)*(major1) + (1909195827158411/50000000000000 : ℝ)*(major2) + (1035301097431563/20000000000000 : ℝ)*(sp0) + (2588252062061327/50000000000000 : ℝ)*(sp1) + (5176475179009541/100000000000000 : ℝ)*(sp2) + (2460267289952621/100000000000000 : ℝ)*(sp3) + (29302104933/100000000000000 : ℝ)*(sp6) + (517187821/5000000000000 : ℝ)*(sp7) + (2460277633709041/100000000000000 : ℝ)*(f.failure) + (1035301097431563/20000000000000 : ℝ)*(f.sum) + (940820614483/766000000000000000000000000 : ℝ)*base65 + (6684891211761094661/383000000000000000000000000000000 : ℝ)*base68 + (2264306821510094661/383000000000000000000000000000000 : ℝ)*base70 + (2194271869321094661/383000000000000000000000000000000 : ℝ)*base72 + (1225780204351/766000000000000000000000000 : ℝ)*base74 + (3125041821263905339/383000000000000000000000000000000 : ℝ)*base75 + (1310630007866905339/383000000000000000000000000000000 : ℝ)*base77 + (1657188062734094661/383000000000000000000000000000000 : ℝ)*base80 + (2378839096641/766000000000000000000000000 : ℝ)*base82 + (19080937/10000000000000000000000 : ℝ)*base89 + (19080937/10000000000000000000000 : ℝ)*base91 + (19080937/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (247542836079670262191358763/76600000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (67876833/10000000000000 : ℝ)*(base19) + (525673011/100000000000000 : ℝ)*(base23) + (13181963/25000000000000 : ℝ)*(upper3) + (13635741/50000000000000 : ℝ)*(lower4) + (81322849/100000000000000 : ℝ)*(upper5) + (770063350641671/20000000000000 : ℝ)*(major0) + (770063350641671/20000000000000 : ℝ)*(major1) + (770063350641671/20000000000000 : ℝ)*(major2) + (413714267/3125000000000 : ℝ)*(sp1) + (10644720303/100000000000000 : ℝ)*(sp2) + (521978568892651/10000000000000 : ℝ)*(sp4) + (5219771771301637/100000000000000 : ℝ)*(sp5) + (1304943629633299/25000000000000 : ℝ)*(sp6) + (620211927442301/25000000000000 : ℝ)*(sp7) + (620211927442301/25000000000000 : ℝ)*(f.failure) + (521978568892651/10000000000000 : ℝ)*(f.sum) + (4314383119621/1532000000000000000000000000 : ℝ)*base66 + (648479586223497079/153200000000000000000000000000000 : ℝ)*base67 + (724266319294902921/153200000000000000000000000000000 : ℝ)*base70 + (366694157606697079/153200000000000000000000000000000 : ℝ)*base71 + (2279609429203/1532000000000000000000000000 : ℝ)*base73 + (1608612018167302921/153200000000000000000000000000000 : ℝ)*base76 + (304808031764697079/153200000000000000000000000000000 : ℝ)*base77 + (815959551255497079/153200000000000000000000000000000 : ℝ)*base79 + (10842900903841/1532000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (12092757/2500000000000000000000 : ℝ)*base89 + (12092757/2500000000000000000000 : ℝ)*base91 + (12092757/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1354_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155201657/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16057/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9929/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1091/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7499/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1354_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1354_s4_0 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-63543027/312500000 : ℝ)*x 0 + (1082887293/2000000000 : ℝ)*x 1 + (2621400079/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (63543027/312500000 : ℝ)^2157 ≤ (6192604227969/50000000000000 : ℝ)^1645 := by
    have hnat : (63543027 : ℕ)^2157*50000000000000^1645 ≤ 6192604227969^1645*312500000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63543027 312500000 6192604227969 50000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082887293/2000000000 : ℝ)^2157 ≤ (44732454309831/100000000000000 : ℝ)^1645 := by
    have hnat : (1082887293 : ℕ)^2157*100000000000000^1645 ≤ 44732454309831^1645*2000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082887293 2000000000 44732454309831 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621400079/5000000000 : ℝ)^2157 ≤ (42882337213481/100000000000000 : ℝ)^1645 := by
    have hnat : (2621400079 : ℕ)^2157*100000000000000^1645 ≤ 42882337213481^1645*5000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621400079 5000000000 42882337213481 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-63543027/312500000 : ℝ), (1082887293/2000000000 : ℝ), (2621400079/5000000000 : ℝ)] ![(6192604227969/50000000000000 : ℝ), (44732454309831/100000000000000 : ℝ), (42882337213481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-63543027/312500000 : ℝ)|^2157 ≤ (6192604227969/50000000000000 : ℝ)^1645
        have hw : |(-63543027/312500000 : ℝ)|=(63543027/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082887293/2000000000 : ℝ)|^2157 ≤ (44732454309831/100000000000000 : ℝ)^1645
        have hw : |(1082887293/2000000000 : ℝ)|=(1082887293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621400079/5000000000 : ℝ)|^2157 ≤ (42882337213481/100000000000000 : ℝ)^1645
        have hw : |(2621400079/5000000000 : ℝ)|=(2621400079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1354_s4_1 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1337347293/2500000000 : ℝ)*x 0 + (-212086087/1000000000 : ℝ)*x 1 + (5242800083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337347293/2500000000 : ℝ)^2157 ≤ (343977422093/781250000000 : ℝ)^1645 := by
    have hnat : (1337347293 : ℕ)^2157*781250000000^1645 ≤ 343977422093^1645*2500000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337347293 2500000000 343977422093 781250000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (212086087/1000000000 : ℝ)^2157 ≤ (523542141899/4000000000000 : ℝ)^1645 := by
    have hnat : (212086087 : ℕ)^2157*4000000000000^1645 ≤ 523542141899^1645*1000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212086087 1000000000 523542141899 4000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242800083/10000000000 : ℝ)^2157 ≤ (21441168204551/50000000000000 : ℝ)^1645 := by
    have hnat : (5242800083 : ℕ)^2157*50000000000000^1645 ≤ 21441168204551^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242800083 10000000000 21441168204551 50000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337347293/2500000000 : ℝ), (-212086087/1000000000 : ℝ), (5242800083/10000000000 : ℝ)] ![(343977422093/781250000000 : ℝ), (523542141899/4000000000000 : ℝ), (21441168204551/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337347293/2500000000 : ℝ)|^2157 ≤ (343977422093/781250000000 : ℝ)^1645
        have hw : |(1337347293/2500000000 : ℝ)|=(1337347293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-212086087/1000000000 : ℝ)|^2157 ≤ (523542141899/4000000000000 : ℝ)^1645
        have hw : |(-212086087/1000000000 : ℝ)|=(212086087/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242800083/10000000000 : ℝ)|^2157 ≤ (21441168204551/50000000000000 : ℝ)^1645
        have hw : |(5242800083/10000000000 : ℝ)|=(5242800083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1354_s4_2 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349389161/10000000000 : ℝ)*x 0 + (1310700043/2500000000 : ℝ)*x 1 + (-2120860767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349389161/10000000000 : ℝ)^2157 ≤ (44029109909187/100000000000000 : ℝ)^1645 := by
    have hnat : (5349389161 : ℕ)^2157*100000000000000^1645 ≤ 44029109909187^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349389161 10000000000 44029109909187 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310700043/2500000000 : ℝ)^2157 ≤ (2680146085227/6250000000000 : ℝ)^1645 := by
    have hnat : (1310700043 : ℕ)^2157*6250000000000^1645 ≤ 2680146085227^1645*2500000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310700043 2500000000 2680146085227 6250000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2120860767/10000000000 : ℝ)^2157 ≤ (51127159039/390625000000 : ℝ)^1645 := by
    have hnat : (2120860767 : ℕ)^2157*390625000000^1645 ≤ 51127159039^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120860767 10000000000 51127159039 390625000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349389161/10000000000 : ℝ), (1310700043/2500000000 : ℝ), (-2120860767/10000000000 : ℝ)] ![(44029109909187/100000000000000 : ℝ), (2680146085227/6250000000000 : ℝ), (51127159039/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349389161/10000000000 : ℝ)|^2157 ≤ (44029109909187/100000000000000 : ℝ)^1645
        have hw : |(5349389161/10000000000 : ℝ)|=(5349389161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310700043/2500000000 : ℝ)|^2157 ≤ (2680146085227/6250000000000 : ℝ)^1645
        have hw : |(1310700043/2500000000 : ℝ)|=(1310700043/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2120860767/10000000000 : ℝ)|^2157 ≤ (51127159039/390625000000 : ℝ)^1645
        have hw : |(-2120860767/10000000000 : ℝ)|=(2120860767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1354_s4_3 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (540416111/1250000000 : ℝ)*x 0 + (1036567431/2500000000 : ℝ)*x 1 + (2253699053/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540416111/1250000000 : ℝ)^2157 ≤ (4162728721583/12500000000000 : ℝ)^1645 := by
    have hnat : (540416111 : ℕ)^2157*12500000000000^1645 ≤ 4162728721583^1645*1250000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540416111 1250000000 4162728721583 12500000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036567431/2500000000 : ℝ)^2157 ≤ (7881246742679/25000000000000 : ℝ)^1645 := by
    have hnat : (1036567431 : ℕ)^2157*25000000000000^1645 ≤ 7881246742679^1645*2500000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036567431 2500000000 7881246742679 25000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2253699053/5000000000 : ℝ)^2157 ≤ (35173183248309/100000000000000 : ℝ)^1645 := by
    have hnat : (2253699053 : ℕ)^2157*100000000000000^1645 ≤ 35173183248309^1645*5000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253699053 5000000000 35173183248309 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540416111/1250000000 : ℝ), (1036567431/2500000000 : ℝ), (2253699053/5000000000 : ℝ)] ![(4162728721583/12500000000000 : ℝ), (7881246742679/25000000000000 : ℝ), (35173183248309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540416111/1250000000 : ℝ)|^2157 ≤ (4162728721583/12500000000000 : ℝ)^1645
        have hw : |(540416111/1250000000 : ℝ)|=(540416111/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036567431/2500000000 : ℝ)|^2157 ≤ (7881246742679/25000000000000 : ℝ)^1645
        have hw : |(1036567431/2500000000 : ℝ)|=(1036567431/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2253699053/5000000000 : ℝ)|^2157 ≤ (35173183248309/100000000000000 : ℝ)^1645
        have hw : |(2253699053/5000000000 : ℝ)|=(2253699053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1354_s4_4 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-203338997/1000000000 : ℝ)*x 0 + (5243431811/10000000000 : ℝ)*x 1 + (1353450357/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (203338997/1000000000 : ℝ)^2157 ≤ (12385313130291/100000000000000 : ℝ)^1645 := by
    have hnat : (203338997 : ℕ)^2157*100000000000000^1645 ≤ 12385313130291^1645*1000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203338997 1000000000 12385313130291 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243431811/10000000000 : ℝ)^2157 ≤ (42889111851457/100000000000000 : ℝ)^1645 := by
    have hnat : (5243431811 : ℕ)^2157*100000000000000^1645 ≤ 42889111851457^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243431811 10000000000 42889111851457 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353450357/2500000000 : ℝ)^2157 ≤ (5590696875117/12500000000000 : ℝ)^1645 := by
    have hnat : (1353450357 : ℕ)^2157*12500000000000^1645 ≤ 5590696875117^1645*2500000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353450357 2500000000 5590696875117 12500000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-203338997/1000000000 : ℝ), (5243431811/10000000000 : ℝ), (1353450357/2500000000 : ℝ)] ![(12385313130291/100000000000000 : ℝ), (42889111851457/100000000000000 : ℝ), (5590696875117/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-203338997/1000000000 : ℝ)|^2157 ≤ (12385313130291/100000000000000 : ℝ)^1645
        have hw : |(-203338997/1000000000 : ℝ)|=(203338997/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243431811/10000000000 : ℝ)|^2157 ≤ (42889111851457/100000000000000 : ℝ)^1645
        have hw : |(5243431811/10000000000 : ℝ)|=(5243431811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353450357/2500000000 : ℝ)|^2157 ≤ (5590696875117/12500000000000 : ℝ)^1645
        have hw : |(1353450357/2500000000 : ℝ)|=(1353450357/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1354_s4_5 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305118639/10000000000 : ℝ)*x 0 + (-77994391/400000000 : ℝ)*x 1 + (5413801647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305118639/10000000000 : ℝ)^2157 ≤ (10887984782983/25000000000000 : ℝ)^1645 := by
    have hnat : (5305118639 : ℕ)^2157*25000000000000^1645 ≤ 10887984782983^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305118639 10000000000 10887984782983 25000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (77994391/400000000 : ℝ)^2157 ≤ (293062087147/2500000000000 : ℝ)^1645 := by
    have hnat : (77994391 : ℕ)^2157*2500000000000^1645 ≤ 293062087147^1645*400000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77994391 400000000 293062087147 2500000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413801647/10000000000 : ℝ)^2157 ≤ (44725577373303/100000000000000 : ℝ)^1645 := by
    have hnat : (5413801647 : ℕ)^2157*100000000000000^1645 ≤ 44725577373303^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413801647 10000000000 44725577373303 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305118639/10000000000 : ℝ), (-77994391/400000000 : ℝ), (5413801647/10000000000 : ℝ)] ![(10887984782983/25000000000000 : ℝ), (293062087147/2500000000000 : ℝ), (44725577373303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305118639/10000000000 : ℝ)|^2157 ≤ (10887984782983/25000000000000 : ℝ)^1645
        have hw : |(5305118639/10000000000 : ℝ)|=(5305118639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-77994391/400000000 : ℝ)|^2157 ≤ (293062087147/2500000000000 : ℝ)^1645
        have hw : |(-77994391/400000000 : ℝ)|=(77994391/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413801647/10000000000 : ℝ)|^2157 ≤ (44725577373303/100000000000000 : ℝ)^1645
        have hw : |(5413801647/10000000000 : ℝ)|=(5413801647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1354_s4_6 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1326279751/2500000000 : ℝ)*x 0 + (2706900707/5000000000 : ℝ)*x 1 + (-1949859597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326279751/2500000000 : ℝ)^2157 ≤ (43551943060999/100000000000000 : ℝ)^1645 := by
    have hnat : (1326279751 : ℕ)^2157*100000000000000^1645 ≤ 43551943060999^1645*2500000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326279751 2500000000 43551943060999 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706900707/5000000000 : ℝ)^2157 ≤ (44725574849277/100000000000000 : ℝ)^1645 := by
    have hnat : (2706900707 : ℕ)^2157*100000000000000^1645 ≤ 44725574849277^1645*5000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706900707 5000000000 44725574849277 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1949859597/10000000000 : ℝ)^2157 ≤ (11722482082677/100000000000000 : ℝ)^1645 := by
    have hnat : (1949859597 : ℕ)^2157*100000000000000^1645 ≤ 11722482082677^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1949859597 10000000000 11722482082677 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326279751/2500000000 : ℝ), (2706900707/5000000000 : ℝ), (-1949859597/10000000000 : ℝ)] ![(43551943060999/100000000000000 : ℝ), (44725574849277/100000000000000 : ℝ), (11722482082677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326279751/2500000000 : ℝ)|^2157 ≤ (43551943060999/100000000000000 : ℝ)^1645
        have hw : |(1326279751/2500000000 : ℝ)|=(1326279751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706900707/5000000000 : ℝ)|^2157 ≤ (44725574849277/100000000000000 : ℝ)^1645
        have hw : |(2706900707/5000000000 : ℝ)|=(2706900707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1949859597/10000000000 : ℝ)|^2157 ≤ (11722482082677/100000000000000 : ℝ)^1645
        have hw : |(-1949859597/10000000000 : ℝ)|=(1949859597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1354_s4_7 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (864671333/2000000000 : ℝ)*x 0 + (4506069351/10000000000 : ℝ)*x 1 + (2073802599/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (864671333/2000000000 : ℝ)^2157 ≤ (16651055164421/50000000000000 : ℝ)^1645 := by
    have hnat : (864671333 : ℕ)^2157*50000000000000^1645 ≤ 16651055164421^1645*2000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864671333 2000000000 16651055164421 50000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4506069351/10000000000 : ℝ)^2157 ≤ (35159587754529/100000000000000 : ℝ)^1645 := by
    have hnat : (4506069351 : ℕ)^2157*100000000000000^1645 ≤ 35159587754529^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506069351 10000000000 35159587754529 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2073802599/5000000000 : ℝ)^2157 ≤ (31538301898401/100000000000000 : ℝ)^1645 := by
    have hnat : (2073802599 : ℕ)^2157*100000000000000^1645 ≤ 31538301898401^1645*5000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073802599 5000000000 31538301898401 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(864671333/2000000000 : ℝ), (4506069351/10000000000 : ℝ), (2073802599/5000000000 : ℝ)] ![(16651055164421/50000000000000 : ℝ), (35159587754529/100000000000000 : ℝ), (31538301898401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(864671333/2000000000 : ℝ)|^2157 ≤ (16651055164421/50000000000000 : ℝ)^1645
        have hw : |(864671333/2000000000 : ℝ)|=(864671333/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4506069351/10000000000 : ℝ)|^2157 ≤ (35159587754529/100000000000000 : ℝ)^1645
        have hw : |(4506069351/10000000000 : ℝ)|=(4506069351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2073802599/5000000000 : ℝ)|^2157 ≤ (31538301898401/100000000000000 : ℝ)^1645
        have hw : |(2073802599/5000000000 : ℝ)|=(2073802599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1354_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155201657/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7499/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1091/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (1113/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3691/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7499/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1091/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7499/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1091/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7499/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1091/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7499/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1091/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7499/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1091/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7499/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1091/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1091/10000 : ℝ) ^ (4313/1024 : ℝ) ≤ (8859323012209757/100000000000000000000 : ℝ) := by
    have hpowers : (1091/10000 : ℝ)^4313 ≤ (8859323012209757/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1091 : ℕ)^4313*100000000000000000000^1024 ≤ 8859323012209757^1024*10000^4313 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1091 10000 8859323012209757 100000000000000000000 4313 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1091/10000 : ℝ)) (X := (8859323012209757/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4313 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7499/50000 : ℝ) ^ (4313/1024 : ℝ) ≤ (33847241237130443/100000000000000000000 : ℝ) := by
    have hpowers : (7499/50000 : ℝ)^4313 ≤ (33847241237130443/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7499 : ℕ)^4313*100000000000000000000^1024 ≤ 33847241237130443^1024*50000^4313 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7499 50000 33847241237130443 100000000000000000000 4313 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7499/50000 : ℝ)) (X := (33847241237130443/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4313 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008859323012209757/50000000000000000000 : ℝ) ≤ (1000042065077367/1000000000000000 : ℝ) ^ (4313/1024 : ℝ) := by
    have hpowers : (50008859323012209757/50000000000000000000 : ℝ)^1024 ≤ (1000042065077367/1000000000000000 : ℝ)^4313 := by
      have hnat : (50008859323012209757 : ℕ)^1024*1000000000000000^4313 ≤ 1000042065077367^4313*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008859323012209757 50000000000000000000 1000042065077367 1000000000000000 1024 4313 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000042065077367/1000000000000000 : ℝ)) (X := (50008859323012209757/50000000000000000000 : ℝ)) (by norm_num) 4313 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (500213532821246701/500000000000000000 : ℝ) ≤ (10001013781649293/10000000000000000 : ℝ) ^ (4313/1024 : ℝ) := by
    have hpowers : (500213532821246701/500000000000000000 : ℝ)^1024 ≤ (10001013781649293/10000000000000000 : ℝ)^4313 := by
      have hnat : (500213532821246701 : ℕ)^1024*10000000000000000^4313 ≤ 10001013781649293^4313*500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500213532821246701 500000000000000000 10001013781649293 10000000000000000 1024 4313 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001013781649293/10000000000000000 : ℝ)) (X := (500213532821246701/500000000000000000 : ℝ)) (by norm_num) 4313 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033847241237130443/50000000000000000000 : ℝ) ≤ (2500401728131229/2500000000000000 : ℝ) ^ (4313/1024 : ℝ) := by
    have hpowers : (50033847241237130443/50000000000000000000 : ℝ)^1024 ≤ (2500401728131229/2500000000000000 : ℝ)^4313 := by
      have hnat : (50033847241237130443 : ℕ)^1024*2500000000000000^4313 ≤ 2500401728131229^4313*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033847241237130443 50000000000000000000 2500401728131229 2500000000000000 1024 4313 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500401728131229/2500000000000000 : ℝ)) (X := (50033847241237130443/50000000000000000000 : ℝ)) (by norm_num) 4313 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8859323012209757/100000000000000000000 : ℝ) ≤ ((408687775046566691/408800000000000000 : ℝ)+2*(593130875623/408800000000000 : ℝ)*(1091/10000 : ℝ))^(4313/1024 : ℝ) := by
    rw [show (408687775046566691/408800000000000000 : ℝ)+2*(593130875623/408800000000000 : ℝ)*(1091/10000 : ℝ)=(1000042065077367/1000000000000000 : ℝ) by norm_num, show 1+2*(8859323012209757/100000000000000000000 : ℝ)=(50008859323012209757/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33847241237130443/100000000000000000000 : ℝ)+(8859323012209757/100000000000000000000 : ℝ) ≤ ((408687775046566691/408800000000000000 : ℝ)+(593130875623/408800000000000 : ℝ)*((7499/50000 : ℝ)+(1091/10000 : ℝ)))^(4313/1024 : ℝ) := by
    rw [show (408687775046566691/408800000000000000 : ℝ)+(593130875623/408800000000000 : ℝ)*((7499/50000 : ℝ)+(1091/10000 : ℝ))=(10001013781649293/10000000000000000 : ℝ) by norm_num, show 1+(33847241237130443/100000000000000000000 : ℝ)+(8859323012209757/100000000000000000000 : ℝ)=(500213532821246701/500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33847241237130443/100000000000000000000 : ℝ) ≤ ((408687775046566691/408800000000000000 : ℝ)+2*(593130875623/408800000000000 : ℝ)*(7499/50000 : ℝ))^(4313/1024 : ℝ) := by
    rw [show (408687775046566691/408800000000000000 : ℝ)+2*(593130875623/408800000000000 : ℝ)*(7499/50000 : ℝ)=(2500401728131229/2500000000000000 : ℝ) by norm_num, show 1+2*(33847241237130443/100000000000000000000 : ℝ)=(50033847241237130443/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (408687775046566691/408800000000000000 : ℝ)*(X 1 0+X 2 0)+(593130875623/408800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4313/1024 : ℝ)) (lo := (1091/10000 : ℝ)) (hi := (7499/50000 : ℝ)) (c := (408687775046566691/408800000000000000 : ℝ)) (alpha := (593130875623/408800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (408687775046566691/408800000000000000 : ℝ)*(X 0 1+X 2 1)+(593130875623/408800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4313/1024 : ℝ)) (lo := (1091/10000 : ℝ)) (hi := (7499/50000 : ℝ)) (c := (408687775046566691/408800000000000000 : ℝ)) (alpha := (593130875623/408800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (408687775046566691/408800000000000000 : ℝ)*(X 0 2+X 1 2)+(593130875623/408800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4313/1024 : ℝ)) (lo := (1091/10000 : ℝ)) (hi := (7499/50000 : ℝ)) (c := (408687775046566691/408800000000000000 : ℝ)) (alpha := (593130875623/408800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-63543027/312500000 : ℝ)*X 0 0+(1082887293/2000000000 : ℝ)*X 0 1+(2621400079/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337347293/2500000000 : ℝ)*X 1 0+(-212086087/1000000000 : ℝ)*X 1 1+(5242800083/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349389161/10000000000 : ℝ)*X 2 0+(1310700043/2500000000 : ℝ)*X 2 1+(-2120860767/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((540416111/1250000000 : ℝ)*X 0 0+(1036567431/2500000000 : ℝ)*X 0 1+(2253699053/5000000000 : ℝ)*X 0 2+(540416111/1250000000 : ℝ)*X 1 0+(1036567431/2500000000 : ℝ)*X 1 1+(2253699053/5000000000 : ℝ)*X 1 2+(540416111/1250000000 : ℝ)*X 2 0+(1036567431/2500000000 : ℝ)*X 2 1+(2253699053/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-203338997/1000000000 : ℝ)*X 0 0+(5243431811/10000000000 : ℝ)*X 0 1+(1353450357/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305118639/10000000000 : ℝ)*X 1 0+(-77994391/400000000 : ℝ)*X 1 1+(5413801647/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326279751/2500000000 : ℝ)*X 2 0+(2706900707/5000000000 : ℝ)*X 2 1+(-1949859597/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((864671333/2000000000 : ℝ)*X 0 0+(4506069351/10000000000 : ℝ)*X 0 1+(2073802599/5000000000 : ℝ)*X 0 2+(864671333/2000000000 : ℝ)*X 1 0+(4506069351/10000000000 : ℝ)*X 1 1+(2073802599/5000000000 : ℝ)*X 1 2+(864671333/2000000000 : ℝ)*X 2 0+(4506069351/10000000000 : ℝ)*X 2 1+(2073802599/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1956717765135453188101647/182500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (402403959/20000000000000 : ℝ)*(base19) + (236985341/12500000000000 : ℝ)*(base23) + (435291/781250000000 : ℝ)*(lower2) + (9044259/5000000000000 : ℝ)*(upper3) + (225666437/100000000000000 : ℝ)*(upper5) + (537218314206973/12500000000000 : ℝ)*(major0) + (537218314206973/12500000000000 : ℝ)*(major1) + (537218314206973/12500000000000 : ℝ)*(major2) + (728289103290789/12500000000000 : ℝ)*(sp0) + (1456588413660723/25000000000000 : ℝ)*(sp1) + (145658844269499/2500000000000 : ℝ)*(sp2) + (34613971579457/1250000000000 : ℝ)*(sp3) + (5355042047/12500000000000 : ℝ)*(sp4) + (19276900941/100000000000000 : ℝ)*(sp7) + (1107654801303/40000000000 : ℝ)*(f.failure) + (182073614583209/3125000000000 : ℝ)*(f.sum) + (746467477677/91250000000000000000000000 : ℝ)*base66 + (6719533199464951/730000000000000000000000000000 : ℝ)*base68 + (5356255392614951/730000000000000000000000000000 : ℝ)*base70 + (7041039596524951/730000000000000000000000000000 : ℝ)*base72 + (262863043309/182500000000000000000000000 : ℝ)*base74 + (984035595374951/730000000000000000000000000000 : ℝ)*base76 + (8901406735804951/730000000000000000000000000000 : ℝ)*base78 + (1075750554615049/730000000000000000000000000000 : ℝ)*base79 + (635235090073/365000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (929/4000000000000000000 : ℝ)*base90 + (929/4000000000000000000 : ℝ)*base92 + (929/4000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2696600241568095211961793/319375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (832820777/100000000000000 : ℝ)*(base19) + (1565611647/100000000000000 : ℝ)*(base23) + (317262717/100000000000000 : ℝ)*(upper3) + (48187769/50000000000000 : ℝ)*(lower4) + (6010771/5000000000000 : ℝ)*(upper5) + (33825269946883/781250000000 : ℝ)*(major0) + (33825269946883/781250000000 : ℝ)*(major1) + (33825269946883/781250000000 : ℝ)*(major2) + (11299857781/100000000000000 : ℝ)*(sp1) + (28950420749/100000000000000 : ℝ)*(sp2) + (733698202978583/12500000000000 : ℝ)*(sp4) + (2934786745575053/50000000000000 : ℝ)*(sp5) + (1467388776949067/25000000000000 : ℝ)*(sp6) + (2789683201127823/100000000000000 : ℝ)*(sp7) + (2789683201127823/100000000000000 : ℝ)*(f.failure) + (733698202978583/12500000000000 : ℝ)*(f.sum) + (3009173030419/2555000000000000000000000000 : ℝ)*base65 + (121148941673111/159687500000000000000000000000 : ℝ)*base68 + (191668248945597/319375000000000000000000000000 : ℝ)*base70 + (1241866910881889/159687500000000000000000000000 : ℝ)*base71 + (14061924151671/2555000000000000000000000000 : ℝ)*base74 + (180112474621559/39921875000000000000000000000 : ℝ)*base76 + (1427111784860653/319375000000000000000000000000 : ℝ)*base77 + (2360073289184361/159687500000000000000000000000 : ℝ)*base80 + (2876580641119/2555000000000000000000000000 : ℝ)*base81 + (1597289/10000000000000000000000 : ℝ)*base90 + (1597289/10000000000000000000000 : ℝ)*base92 + (1597289/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1354_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155201657/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7499/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1091/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1113/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3691/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1354_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1354_s5_0 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1016803763/5000000000 : ℝ)*x 0 + (5412438489/10000000000 : ℝ)*x 1 + (5244646277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1016803763/5000000000 : ℝ)^2157 ≤ (1238705072647/10000000000000 : ℝ)^1645 := by
    have hnat : (1016803763 : ℕ)^2157*10000000000000^1645 ≤ 1238705072647^1645*5000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016803763 5000000000 1238705072647 10000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412438489/10000000000 : ℝ)^2157 ≤ (894216224629/2000000000000 : ℝ)^1645 := by
    have hnat : (5412438489 : ℕ)^2157*2000000000000^1645 ≤ 894216224629^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412438489 10000000000 894216224629 2000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244646277/10000000000 : ℝ)^2157 ≤ (42902138019759/100000000000000 : ℝ)^1645 := by
    have hnat : (5244646277 : ℕ)^2157*100000000000000^1645 ≤ 42902138019759^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244646277 10000000000 42902138019759 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1016803763/5000000000 : ℝ), (5412438489/10000000000 : ℝ), (5244646277/10000000000 : ℝ)] ![(1238705072647/10000000000000 : ℝ), (894216224629/2000000000000 : ℝ), (42902138019759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1016803763/5000000000 : ℝ)|^2157 ≤ (1238705072647/10000000000000 : ℝ)^1645
        have hw : |(-1016803763/5000000000 : ℝ)|=(1016803763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412438489/10000000000 : ℝ)|^2157 ≤ (894216224629/2000000000000 : ℝ)^1645
        have hw : |(5412438489/10000000000 : ℝ)|=(5412438489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244646277/10000000000 : ℝ)|^2157 ≤ (42902138019759/100000000000000 : ℝ)^1645
        have hw : |(5244646277/10000000000 : ℝ)|=(5244646277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1354_s5_1 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5348877731/10000000000 : ℝ)*x 0 + (-84763829/400000000 : ℝ)*x 1 + (2622323137/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348877731/10000000000 : ℝ)^2157 ≤ (5502948801219/12500000000000 : ℝ)^1645 := by
    have hnat : (5348877731 : ℕ)^2157*12500000000000^1645 ≤ 5502948801219^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348877731 10000000000 5502948801219 12500000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84763829/400000000 : ℝ)^2157 ≤ (13074271586587/100000000000000 : ℝ)^1645 := by
    have hnat : (84763829 : ℕ)^2157*100000000000000^1645 ≤ 13074271586587^1645*400000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84763829 400000000 13074271586587 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622323137/5000000000 : ℝ)^2157 ≤ (42902137987581/100000000000000 : ℝ)^1645 := by
    have hnat : (2622323137 : ℕ)^2157*100000000000000^1645 ≤ 42902137987581^1645*5000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622323137 5000000000 42902137987581 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348877731/10000000000 : ℝ), (-84763829/400000000 : ℝ), (2622323137/5000000000 : ℝ)] ![(5502948801219/12500000000000 : ℝ), (13074271586587/100000000000000 : ℝ), (42902137987581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348877731/10000000000 : ℝ)|^2157 ≤ (5502948801219/12500000000000 : ℝ)^1645
        have hw : |(5348877731/10000000000 : ℝ)|=(5348877731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-84763829/400000000 : ℝ)|^2157 ≤ (13074271586587/100000000000000 : ℝ)^1645
        have hw : |(-84763829/400000000 : ℝ)|=(84763829/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622323137/5000000000 : ℝ)|^2157 ≤ (42902137987581/100000000000000 : ℝ)^1645
        have hw : |(2622323137/5000000000 : ℝ)|=(2622323137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1354_s5_2 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5348877729/10000000000 : ℝ)*x 0 + (2622323137/5000000000 : ℝ)*x 1 + (-2119095729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348877729/10000000000 : ℝ)^2157 ≤ (5502948798521/12500000000000 : ℝ)^1645 := by
    have hnat : (5348877729 : ℕ)^2157*12500000000000^1645 ≤ 5502948798521^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348877729 10000000000 5502948798521 12500000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622323137/5000000000 : ℝ)^2157 ≤ (42902137987581/100000000000000 : ℝ)^1645 := by
    have hnat : (2622323137 : ℕ)^2157*100000000000000^1645 ≤ 42902137987581^1645*5000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622323137 5000000000 42902137987581 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2119095729/10000000000 : ℝ)^2157 ≤ (13074271618947/100000000000000 : ℝ)^1645 := by
    have hnat : (2119095729 : ℕ)^2157*100000000000000^1645 ≤ 13074271618947^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119095729 10000000000 13074271618947 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348877729/10000000000 : ℝ), (2622323137/5000000000 : ℝ), (-2119095729/10000000000 : ℝ)] ![(5502948798521/12500000000000 : ℝ), (42902137987581/100000000000000 : ℝ), (13074271618947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348877729/10000000000 : ℝ)|^2157 ≤ (5502948798521/12500000000000 : ℝ)^1645
        have hw : |(5348877729/10000000000 : ℝ)|=(5348877729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622323137/5000000000 : ℝ)|^2157 ≤ (42902137987581/100000000000000 : ℝ)^1645
        have hw : |(2622323137/5000000000 : ℝ)|=(2622323137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2119095729/10000000000 : ℝ)|^2157 ≤ (13074271618947/100000000000000 : ℝ)^1645
        have hw : |(-2119095729/10000000000 : ℝ)|=(2119095729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1354_s5_3 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4323467007/10000000000 : ℝ)*x 0 + (830059327/2000000000 : ℝ)*x 1 + (4503337013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4323467007/10000000000 : ℝ)^2157 ≤ (4162903102783/12500000000000 : ℝ)^1645 := by
    have hnat : (4323467007 : ℕ)^2157*12500000000000^1645 ≤ 4162903102783^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4323467007 10000000000 4162903102783 12500000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (830059327/2000000000 : ℝ)^2157 ≤ (7891285021839/25000000000000 : ℝ)^1645 := by
    have hnat : (830059327 : ℕ)^2157*25000000000000^1645 ≤ 7891285021839^1645*2000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      830059327 2000000000 7891285021839 25000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4503337013/10000000000 : ℝ)^2157 ≤ (3513163506647/10000000000000 : ℝ)^1645 := by
    have hnat : (4503337013 : ℕ)^2157*10000000000000^1645 ≤ 3513163506647^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503337013 10000000000 3513163506647 10000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4323467007/10000000000 : ℝ), (830059327/2000000000 : ℝ), (4503337013/10000000000 : ℝ)] ![(4162903102783/12500000000000 : ℝ), (7891285021839/25000000000000 : ℝ), (3513163506647/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4323467007/10000000000 : ℝ)|^2157 ≤ (4162903102783/12500000000000 : ℝ)^1645
        have hw : |(4323467007/10000000000 : ℝ)|=(4323467007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(830059327/2000000000 : ℝ)|^2157 ≤ (7891285021839/25000000000000 : ℝ)^1645
        have hw : |(830059327/2000000000 : ℝ)|=(830059327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4503337013/10000000000 : ℝ)|^2157 ≤ (3513163506647/10000000000000 : ℝ)^1645
        have hw : |(4503337013/10000000000 : ℝ)|=(4503337013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1354_s5_4 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2033619719/10000000000 : ℝ)*x 0 + (5245250159/10000000000 : ℝ)*x 1 + (2705915743/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2033619719/10000000000 : ℝ)^2157 ≤ (12387148112351/100000000000000 : ℝ)^1645 := by
    have hnat : (2033619719 : ℕ)^2157*100000000000000^1645 ≤ 12387148112351^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2033619719 10000000000 12387148112351 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245250159/10000000000 : ℝ)^2157 ≤ (21454307755559/50000000000000 : ℝ)^1645 := by
    have hnat : (5245250159 : ℕ)^2157*50000000000000^1645 ≤ 21454307755559^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245250159 10000000000 21454307755559 50000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705915743/5000000000 : ℝ)^2157 ≤ (5588029545359/12500000000000 : ℝ)^1645 := by
    have hnat : (2705915743 : ℕ)^2157*12500000000000^1645 ≤ 5588029545359^1645*5000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705915743 5000000000 5588029545359 12500000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2033619719/10000000000 : ℝ), (5245250159/10000000000 : ℝ), (2705915743/5000000000 : ℝ)] ![(12387148112351/100000000000000 : ℝ), (21454307755559/50000000000000 : ℝ), (5588029545359/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2033619719/10000000000 : ℝ)|^2157 ≤ (12387148112351/100000000000000 : ℝ)^1645
        have hw : |(-2033619719/10000000000 : ℝ)|=(2033619719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245250159/10000000000 : ℝ)|^2157 ≤ (21454307755559/50000000000000 : ℝ)^1645
        have hw : |(5245250159/10000000000 : ℝ)|=(5245250159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705915743/5000000000 : ℝ)|^2157 ≤ (5588029545359/12500000000000 : ℝ)^1645
        have hw : |(2705915743/5000000000 : ℝ)|=(2705915743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1354_s5_5 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1061119691/2000000000 : ℝ)*x 0 + (-243988829/1250000000 : ℝ)*x 1 + (5411832043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061119691/2000000000 : ℝ)^2157 ≤ (5444638027123/12500000000000 : ℝ)^1645 := by
    have hnat : (1061119691 : ℕ)^2157*12500000000000^1645 ≤ 5444638027123^1645*2000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061119691 2000000000 5444638027123 12500000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (243988829/1250000000 : ℝ)^2157 ≤ (11738653371053/100000000000000 : ℝ)^1645 := by
    have hnat : (243988829 : ℕ)^2157*100000000000000^1645 ≤ 11738653371053^1645*1250000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243988829 1250000000 11738653371053 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411832043/10000000000 : ℝ)^2157 ≤ (44704242396019/100000000000000 : ℝ)^1645 := by
    have hnat : (5411832043 : ℕ)^2157*100000000000000^1645 ≤ 44704242396019^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411832043 10000000000 44704242396019 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061119691/2000000000 : ℝ), (-243988829/1250000000 : ℝ), (5411832043/10000000000 : ℝ)] ![(5444638027123/12500000000000 : ℝ), (11738653371053/100000000000000 : ℝ), (44704242396019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061119691/2000000000 : ℝ)|^2157 ≤ (5444638027123/12500000000000 : ℝ)^1645
        have hw : |(1061119691/2000000000 : ℝ)|=(1061119691/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-243988829/1250000000 : ℝ)|^2157 ≤ (11738653371053/100000000000000 : ℝ)^1645
        have hw : |(-243988829/1250000000 : ℝ)|=(243988829/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411832043/10000000000 : ℝ)|^2157 ≤ (44704242396019/100000000000000 : ℝ)^1645
        have hw : |(5411832043/10000000000 : ℝ)|=(5411832043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1354_s5_6 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (530559849/1000000000 : ℝ)*x 0 + (216473281/400000000 : ℝ)*x 1 + (-195191061/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530559849/1000000000 : ℝ)^2157 ≤ (8711420918751/20000000000000 : ℝ)^1645 := by
    have hnat : (530559849 : ℕ)^2157*20000000000000^1645 ≤ 8711420918751^1645*1000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530559849 1000000000 8711420918751 20000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216473281/400000000 : ℝ)^2157 ≤ (11176060550263/25000000000000 : ℝ)^1645 := by
    have hnat : (216473281 : ℕ)^2157*25000000000000^1645 ≤ 11176060550263^1645*400000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216473281 400000000 11176060550263 25000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (195191061/1000000000 : ℝ)^2157 ≤ (11738653197567/100000000000000 : ℝ)^1645 := by
    have hnat : (195191061 : ℕ)^2157*100000000000000^1645 ≤ 11738653197567^1645*1000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195191061 1000000000 11738653197567 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530559849/1000000000 : ℝ), (216473281/400000000 : ℝ), (-195191061/1000000000 : ℝ)] ![(8711420918751/20000000000000 : ℝ), (11176060550263/25000000000000 : ℝ), (11738653197567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530559849/1000000000 : ℝ)|^2157 ≤ (8711420918751/20000000000000 : ℝ)^1645
        have hw : |(530559849/1000000000 : ℝ)|=(530559849/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216473281/400000000 : ℝ)|^2157 ≤ (11176060550263/25000000000000 : ℝ)^1645
        have hw : |(216473281/400000000 : ℝ)|=(216473281/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-195191061/1000000000 : ℝ)|^2157 ≤ (11738653197567/100000000000000 : ℝ)^1645
        have hw : |(-195191061/1000000000 : ℝ)|=(195191061/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1354_s5_7 (p : ℝ) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4323492461/10000000000 : ℝ)*x 0 + (4502066983/10000000000 : ℝ)*x 1 + (1037893363/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4323492461/10000000000 : ℝ)^2157 ≤ (33303481917969/100000000000000 : ℝ)^1645 := by
    have hnat : (4323492461 : ℕ)^2157*100000000000000^1645 ≤ 33303481917969^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4323492461 10000000000 33303481917969 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4502066983/10000000000 : ℝ)^2157 ≤ (17559322025889/50000000000000 : ℝ)^1645 := by
    have hnat : (4502066983 : ℕ)^2157*50000000000000^1645 ≤ 17559322025889^1645*10000000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502066983 10000000000 17559322025889 50000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1037893363/2500000000 : ℝ)^2157 ≤ (31577874011917/100000000000000 : ℝ)^1645 := by
    have hnat : (1037893363 : ℕ)^2157*100000000000000^1645 ≤ 31577874011917^1645*2500000000^2157 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037893363 2500000000 31577874011917 100000000000000 2157 1645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2157/512 : ℝ)) 2157 1645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4323492461/10000000000 : ℝ), (4502066983/10000000000 : ℝ), (1037893363/2500000000 : ℝ)] ![(33303481917969/100000000000000 : ℝ), (17559322025889/50000000000000 : ℝ), (31577874011917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4323492461/10000000000 : ℝ)|^2157 ≤ (33303481917969/100000000000000 : ℝ)^1645
        have hw : |(4323492461/10000000000 : ℝ)|=(4323492461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4502066983/10000000000 : ℝ)|^2157 ≤ (17559322025889/50000000000000 : ℝ)^1645
        have hw : |(4502066983/10000000000 : ℝ)|=(4502066983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1037893363/2500000000 : ℝ)|^2157 ≤ (31577874011917/100000000000000 : ℝ)^1645
        have hw : |(1037893363/2500000000 : ℝ)|=(1037893363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1354_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155201657/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3691/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1113/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (1117/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7361/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3691/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1113/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3691/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1113/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3691/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1113/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3691/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1113/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3691/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1113/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3691/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1113/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1113/10000 : ℝ) ^ (4313/1024 : ℝ) ≤ (602281594287897/6250000000000000000 : ℝ) := by
    have hpowers : (1113/10000 : ℝ)^4313 ≤ (602281594287897/6250000000000000000 : ℝ)^1024 := by
      have hnat : (1113 : ℕ)^4313*6250000000000000000^1024 ≤ 602281594287897^1024*10000^4313 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1113 10000 602281594287897 6250000000000000000 4313 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1113/10000 : ℝ)) (X := (602281594287897/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4313 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3691/25000 : ℝ) ^ (4313/1024 : ℝ) ≤ (31678076143107911/100000000000000000000 : ℝ) := by
    have hpowers : (3691/25000 : ℝ)^4313 ≤ (31678076143107911/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3691 : ℕ)^4313*100000000000000000000^1024 ≤ 31678076143107911^1024*25000^4313 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3691 25000 31678076143107911 100000000000000000000 4313 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3691/25000 : ℝ)) (X := (31678076143107911/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4313 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125602281594287897/3125000000000000000 : ℝ) ≤ (10000457549574781/10000000000000000 : ℝ) ^ (4313/1024 : ℝ) := by
    have hpowers : (3125602281594287897/3125000000000000000 : ℝ)^1024 ≤ (10000457549574781/10000000000000000 : ℝ)^4313 := by
      have hnat : (3125602281594287897 : ℕ)^1024*10000000000000000^4313 ≤ 10000457549574781^4313*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125602281594287897 3125000000000000000 10000457549574781 10000000000000000 1024 4313 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000457549574781/10000000000000000 : ℝ)) (X := (3125602281594287897/3125000000000000000 : ℝ)) (by norm_num) 4313 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100041314581651714263/100000000000000000000 : ℝ) ≤ (10000980743538789/10000000000000000 : ℝ) ^ (4313/1024 : ℝ) := by
    have hpowers : (100041314581651714263/100000000000000000000 : ℝ)^1024 ≤ (10000980743538789/10000000000000000 : ℝ)^4313 := by
      have hnat : (100041314581651714263 : ℕ)^1024*10000000000000000^4313 ≤ 10000980743538789^4313*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100041314581651714263 100000000000000000000 10000980743538789 10000000000000000 1024 4313 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000980743538789/10000000000000000 : ℝ)) (X := (100041314581651714263/100000000000000000000 : ℝ)) (by norm_num) 4313 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031678076143107911/50000000000000000000 : ℝ) ≤ (10001503937502797/10000000000000000 : ℝ) ^ (4313/1024 : ℝ) := by
    have hpowers : (50031678076143107911/50000000000000000000 : ℝ)^1024 ≤ (10001503937502797/10000000000000000 : ℝ)^4313 := by
      have hnat : (50031678076143107911 : ℕ)^1024*10000000000000000^4313 ≤ 10001503937502797^4313*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031678076143107911 50000000000000000000 10001503937502797 10000000000000000 1024 4313 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001503937502797/10000000000000000 : ℝ)) (X := (50031678076143107911/50000000000000000000 : ℝ)) (by norm_num) 4313 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(602281594287897/6250000000000000000 : ℝ) ≤ ((18165008218757968037/18170000000000000000 : ℝ)+2*(65399245501/45425000000000 : ℝ)*(1113/10000 : ℝ))^(4313/1024 : ℝ) := by
    rw [show (18165008218757968037/18170000000000000000 : ℝ)+2*(65399245501/45425000000000 : ℝ)*(1113/10000 : ℝ)=(10000457549574781/10000000000000000 : ℝ) by norm_num, show 1+2*(602281594287897/6250000000000000000 : ℝ)=(3125602281594287897/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31678076143107911/100000000000000000000 : ℝ)+(602281594287897/6250000000000000000 : ℝ) ≤ ((18165008218757968037/18170000000000000000 : ℝ)+(65399245501/45425000000000 : ℝ)*((3691/25000 : ℝ)+(1113/10000 : ℝ)))^(4313/1024 : ℝ) := by
    rw [show (18165008218757968037/18170000000000000000 : ℝ)+(65399245501/45425000000000 : ℝ)*((3691/25000 : ℝ)+(1113/10000 : ℝ))=(10000980743538789/10000000000000000 : ℝ) by norm_num, show 1+(31678076143107911/100000000000000000000 : ℝ)+(602281594287897/6250000000000000000 : ℝ)=(100041314581651714263/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31678076143107911/100000000000000000000 : ℝ) ≤ ((18165008218757968037/18170000000000000000 : ℝ)+2*(65399245501/45425000000000 : ℝ)*(3691/25000 : ℝ))^(4313/1024 : ℝ) := by
    rw [show (18165008218757968037/18170000000000000000 : ℝ)+2*(65399245501/45425000000000 : ℝ)*(3691/25000 : ℝ)=(10001503937502797/10000000000000000 : ℝ) by norm_num, show 1+2*(31678076143107911/100000000000000000000 : ℝ)=(50031678076143107911/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18165008218757968037/18170000000000000000 : ℝ)*(X 1 0+X 2 0)+(65399245501/45425000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4313/1024 : ℝ)) (lo := (1113/10000 : ℝ)) (hi := (3691/25000 : ℝ)) (c := (18165008218757968037/18170000000000000000 : ℝ)) (alpha := (65399245501/45425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18165008218757968037/18170000000000000000 : ℝ)*(X 0 1+X 2 1)+(65399245501/45425000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4313/1024 : ℝ)) (lo := (1113/10000 : ℝ)) (hi := (3691/25000 : ℝ)) (c := (18165008218757968037/18170000000000000000 : ℝ)) (alpha := (65399245501/45425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18165008218757968037/18170000000000000000 : ℝ)*(X 0 2+X 1 2)+(65399245501/45425000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4313/1024 : ℝ)) (lo := (1113/10000 : ℝ)) (hi := (3691/25000 : ℝ)) (c := (18165008218757968037/18170000000000000000 : ℝ)) (alpha := (65399245501/45425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1016803763/5000000000 : ℝ)*X 0 0+(5412438489/10000000000 : ℝ)*X 0 1+(5244646277/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348877731/10000000000 : ℝ)*X 1 0+(-84763829/400000000 : ℝ)*X 1 1+(2622323137/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348877729/10000000000 : ℝ)*X 2 0+(2622323137/5000000000 : ℝ)*X 2 1+(-2119095729/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4323467007/10000000000 : ℝ)*X 0 0+(830059327/2000000000 : ℝ)*X 0 1+(4503337013/10000000000 : ℝ)*X 0 2+(4323467007/10000000000 : ℝ)*X 1 0+(830059327/2000000000 : ℝ)*X 1 1+(4503337013/10000000000 : ℝ)*X 1 2+(4323467007/10000000000 : ℝ)*X 2 0+(830059327/2000000000 : ℝ)*X 2 1+(4503337013/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2033619719/10000000000 : ℝ)*X 0 0+(5245250159/10000000000 : ℝ)*X 0 1+(2705915743/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061119691/2000000000 : ℝ)*X 1 0+(-243988829/1250000000 : ℝ)*X 1 1+(5411832043/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((530559849/1000000000 : ℝ)*X 2 0+(216473281/400000000 : ℝ)*X 2 1+(-195191061/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4323492461/10000000000 : ℝ)*X 0 0+(4502066983/10000000000 : ℝ)*X 0 1+(1037893363/2500000000 : ℝ)*X 0 2+(4323492461/10000000000 : ℝ)*X 1 0+(4502066983/10000000000 : ℝ)*X 1 1+(1037893363/2500000000 : ℝ)*X 1 2+(4323492461/10000000000 : ℝ)*X 2 0+(4502066983/10000000000 : ℝ)*X 2 1+(1037893363/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1354_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (113073625535452499841509961/22712500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2932073/312500000000 : ℝ)*(base19) + (864000683/100000000000000 : ℝ)*(base23) + (38530241/100000000000000 : ℝ)*(lower2) + (7997199/6250000000000 : ℝ)*(upper3) + (70295271/100000000000000 : ℝ)*(upper5) + (109904340525883/2500000000000 : ℝ)*(major0) + (109904340525883/2500000000000 : ℝ)*(major1) + (109904340525883/2500000000000 : ℝ)*(major2) + (2979886147418481/50000000000000 : ℝ)*(sp0) + (1191958056748831/20000000000000 : ℝ)*(sp1) + (5959790358006833/100000000000000 : ℝ)*(sp2) + (1416272962951717/50000000000000 : ℝ)*(sp3) + (18927170553/100000000000000 : ℝ)*(sp4) + (4964105247/50000000000000 : ℝ)*(sp7) + (354069481764241/12500000000000 : ℝ)*(f.failure) + (1191958244401503/20000000000000 : ℝ)*(f.sum) + (863512237851/363400000000000000000000000 : ℝ)*base65 + (15534689447616377/1975000000000000000000000000000 : ℝ)*base67 + (15261215888241377/1975000000000000000000000000000 : ℝ)*base69 + (6501162806116377/1975000000000000000000000000000 : ℝ)*base71 + (2311671850233/1817000000000000000000000000 : ℝ)*base74 + (41731536068191377/1975000000000000000000000000000 : ℝ)*base75 + (18583008150916377/1975000000000000000000000000000 : ℝ)*base77 + (13346405451041377/1975000000000000000000000000000 : ℝ)*base79 + (778007178717/363400000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (13452663/1250000000000000000000 : ℝ)*base90 + (13452663/1250000000000000000000 : ℝ)*base92 + (13452663/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (81898854600480921612777/9085000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5261417/25000000000000 : ℝ)*(base23) + (11716287/50000000000000 : ℝ)*(lower2) + (132277339/50000000000000 : ℝ)*(upper3) + (7353599/50000000000000 : ℝ)*(upper4) + (4082191/12500000000000 : ℝ)*(upper5) + (1107023813673877/25000000000000 : ℝ)*(major0) + (1107023813673877/25000000000000 : ℝ)*(major1) + (1107023813673877/25000000000000 : ℝ)*(major2) + (4175961091/100000000000000 : ℝ)*(sp1) + (2142749459/20000000000000 : ℝ)*(sp2) + (600306651145411/10000000000000 : ℝ)*(sp4) + (6003062335493019/100000000000000 : ℝ)*(sp5) + (6003055776661147/100000000000000 : ℝ)*(sp6) + (1426561848722887/50000000000000 : ℝ)*(sp7) + (1426561848722887/50000000000000 : ℝ)*(f.failure) + (600306651145411/10000000000000 : ℝ)*(f.sum) + (106765889342623/2271250000000000000000000000 : ℝ)*base65 + (390126810465116063/19750000000000000000000000000000 : ℝ)*base67 + (234050530060883937/19750000000000000000000000000000 : ℝ)*base70 + (139942171667116063/19750000000000000000000000000000 : ℝ)*base71 + (75290075809017/9085000000000000000000000000 : ℝ)*base73 + (245249279558133937/19750000000000000000000000000000 : ℝ)*base76 + (126466531016866063/19750000000000000000000000000000 : ℝ)*base77 + (170940235331133937/19750000000000000000000000000000 : ℝ)*base80 + (4262153405577/9085000000000000000000000000 : ℝ)*base81 + (3776241/5000000000000000000000 : ℝ)*base90 + (3776241/5000000000000000000000 : ℝ)*base92 + (3776241/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1354_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155201657/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3691/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1113/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1117/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7361/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1354_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1354_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155201657/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16057/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9929/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1117/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7361/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1354_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1354_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1354_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4313/1024 : ℝ) ≤ p) (hpb : p ≤ (2157/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155201657/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16057/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9929/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1117/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7361/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1354_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
