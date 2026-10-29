-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1503_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:53:03.962818+00:00
-- url     : https://prove2.me/submissions/02a59659-4223-4801-b306-088d2455192b

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
theorem support_rectangle_w1503_s0_0 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-211927639/1250000000 : ℝ)*x 0 + (2959895837/5000000000 : ℝ)*x 1 + (4851448901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211927639/1250000000 : ℝ)^4503 ≤ (314249891381/3125000000000 : ℝ)^3479 := by
    have hnat : (211927639 : ℕ)^4503*3125000000000^3479 ≤ 314249891381^3479*1250000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211927639 1250000000 314249891381 3125000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2959895837/5000000000 : ℝ)^4503 ≤ (6341583119161/12500000000000 : ℝ)^3479 := by
    have hnat : (2959895837 : ℕ)^4503*12500000000000^3479 ≤ 6341583119161^3479*5000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2959895837 5000000000 6341583119161 12500000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4851448901/10000000000 : ℝ)^4503 ≤ (19605669248169/50000000000000 : ℝ)^3479 := by
    have hnat : (4851448901 : ℕ)^4503*50000000000000^3479 ≤ 19605669248169^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4851448901 10000000000 19605669248169 50000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-211927639/1250000000 : ℝ), (2959895837/5000000000 : ℝ), (4851448901/10000000000 : ℝ)] ![(314249891381/3125000000000 : ℝ), (6341583119161/12500000000000 : ℝ), (19605669248169/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-211927639/1250000000 : ℝ)|^4503 ≤ (314249891381/3125000000000 : ℝ)^3479
        have hw : |(-211927639/1250000000 : ℝ)|=(211927639/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2959895837/5000000000 : ℝ)|^4503 ≤ (6341583119161/12500000000000 : ℝ)^3479
        have hw : |(2959895837/5000000000 : ℝ)|=(2959895837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4851448901/10000000000 : ℝ)|^4503 ≤ (19605669248169/50000000000000 : ℝ)^3479
        have hw : |(4851448901/10000000000 : ℝ)|=(4851448901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s0_1 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5479941269/10000000000 : ℝ)*x 0 + (-2294945729/10000000000 : ℝ)*x 1 + (4851448871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5479941269/10000000000 : ℝ)^4503 ≤ (9181589341557/20000000000000 : ℝ)^3479 := by
    have hnat : (5479941269 : ℕ)^4503*20000000000000^3479 ≤ 9181589341557^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5479941269 10000000000 9181589341557 20000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2294945729/10000000000 : ℝ)^4503 ≤ (14880715092971/100000000000000 : ℝ)^3479 := by
    have hnat : (2294945729 : ℕ)^4503*100000000000000^3479 ≤ 14880715092971^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2294945729 10000000000 14880715092971 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4851448871/10000000000 : ℝ)^4503 ≤ (19605669091249/50000000000000 : ℝ)^3479 := by
    have hnat : (4851448871 : ℕ)^4503*50000000000000^3479 ≤ 19605669091249^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4851448871 10000000000 19605669091249 50000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5479941269/10000000000 : ℝ), (-2294945729/10000000000 : ℝ), (4851448871/10000000000 : ℝ)] ![(9181589341557/20000000000000 : ℝ), (14880715092971/100000000000000 : ℝ), (19605669091249/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5479941269/10000000000 : ℝ)|^4503 ≤ (9181589341557/20000000000000 : ℝ)^3479
        have hw : |(5479941269/10000000000 : ℝ)|=(5479941269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2294945729/10000000000 : ℝ)|^4503 ≤ (14880715092971/100000000000000 : ℝ)^3479
        have hw : |(-2294945729/10000000000 : ℝ)|=(2294945729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4851448871/10000000000 : ℝ)|^4503 ≤ (19605669091249/50000000000000 : ℝ)^3479
        have hw : |(4851448871/10000000000 : ℝ)|=(4851448871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s0_2 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1095988259/2000000000 : ℝ)*x 0 + (4851448873/10000000000 : ℝ)*x 1 + (-2294945693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1095988259/2000000000 : ℝ)^4503 ≤ (4590794698971/10000000000000 : ℝ)^3479 := by
    have hnat : (1095988259 : ℕ)^4503*10000000000000^3479 ≤ 4590794698971^3479*2000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095988259 2000000000 4590794698971 10000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4851448873/10000000000 : ℝ)^4503 ≤ (1960566910171/5000000000000 : ℝ)^3479 := by
    have hnat : (4851448873 : ℕ)^4503*5000000000000^3479 ≤ 1960566910171^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4851448873 10000000000 1960566910171 5000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2294945693/10000000000 : ℝ)^4503 ≤ (2976142958167/20000000000000 : ℝ)^3479 := by
    have hnat : (2294945693 : ℕ)^4503*20000000000000^3479 ≤ 2976142958167^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2294945693 10000000000 2976142958167 20000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1095988259/2000000000 : ℝ), (4851448873/10000000000 : ℝ), (-2294945693/10000000000 : ℝ)] ![(4590794698971/10000000000000 : ℝ), (1960566910171/5000000000000 : ℝ), (2976142958167/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1095988259/2000000000 : ℝ)|^4503 ≤ (4590794698971/10000000000000 : ℝ)^3479
        have hw : |(1095988259/2000000000 : ℝ)|=(1095988259/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4851448873/10000000000 : ℝ)|^4503 ≤ (1960566910171/5000000000000 : ℝ)^3479
        have hw : |(4851448873/10000000000 : ℝ)|=(4851448873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2294945693/10000000000 : ℝ)|^4503 ≤ (2976142958167/20000000000000 : ℝ)^3479
        have hw : |(-2294945693/10000000000 : ℝ)|=(2294945693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s0_3 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (829515873/2000000000 : ℝ)*x 0 + (386404077/1250000000 : ℝ)*x 1 + (5498435347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (829515873/2000000000 : ℝ)^4503 ≤ (6402172441891/20000000000000 : ℝ)^3479 := by
    have hnat : (829515873 : ℕ)^4503*20000000000000^3479 ≤ 6402172441891^3479*2000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      829515873 2000000000 6402172441891 20000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (386404077/1250000000 : ℝ)^4503 ≤ (21880555636677/100000000000000 : ℝ)^3479 := by
    have hnat : (386404077 : ℕ)^4503*100000000000000^3479 ≤ 21880555636677^3479*1250000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      386404077 1250000000 21880555636677 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5498435347/10000000000 : ℝ)^4503 ≤ (9221716429379/20000000000000 : ℝ)^3479 := by
    have hnat : (5498435347 : ℕ)^4503*20000000000000^3479 ≤ 9221716429379^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5498435347 10000000000 9221716429379 20000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(829515873/2000000000 : ℝ), (386404077/1250000000 : ℝ), (5498435347/10000000000 : ℝ)] ![(6402172441891/20000000000000 : ℝ), (21880555636677/100000000000000 : ℝ), (9221716429379/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(829515873/2000000000 : ℝ)|^4503 ≤ (6402172441891/20000000000000 : ℝ)^3479
        have hw : |(829515873/2000000000 : ℝ)|=(829515873/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(386404077/1250000000 : ℝ)|^4503 ≤ (21880555636677/100000000000000 : ℝ)^3479
        have hw : |(386404077/1250000000 : ℝ)|=(386404077/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5498435347/10000000000 : ℝ)|^4503 ≤ (9221716429379/20000000000000 : ℝ)^3479
        have hw : |(5498435347/10000000000 : ℝ)|=(5498435347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s0_4 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-849509593/5000000000 : ℝ)*x 0 + (4878745479/10000000000 : ℝ)*x 1 + (736439503/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (849509593/5000000000 : ℝ)^4503 ≤ (10083627784203/100000000000000 : ℝ)^3479 := by
    have hnat : (849509593 : ℕ)^4503*100000000000000^3479 ≤ 10083627784203^3479*5000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849509593 5000000000 10083627784203 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4878745479/10000000000 : ℝ)^4503 ≤ (4937141711237/12500000000000 : ℝ)^3479 := by
    have hnat : (4878745479 : ℕ)^4503*12500000000000^3479 ≤ 4937141711237^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4878745479 10000000000 4937141711237 12500000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (736439503/1250000000 : ℝ)^4503 ≤ (50419238512187/100000000000000 : ℝ)^3479 := by
    have hnat : (736439503 : ℕ)^4503*100000000000000^3479 ≤ 50419238512187^3479*1250000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      736439503 1250000000 50419238512187 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-849509593/5000000000 : ℝ), (4878745479/10000000000 : ℝ), (736439503/1250000000 : ℝ)] ![(10083627784203/100000000000000 : ℝ), (4937141711237/12500000000000 : ℝ), (50419238512187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-849509593/5000000000 : ℝ)|^4503 ≤ (10083627784203/100000000000000 : ℝ)^3479
        have hw : |(-849509593/5000000000 : ℝ)|=(849509593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4878745479/10000000000 : ℝ)|^4503 ≤ (4937141711237/12500000000000 : ℝ)^3479
        have hw : |(4878745479/10000000000 : ℝ)|=(4878745479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(736439503/1250000000 : ℝ)|^4503 ≤ (50419238512187/100000000000000 : ℝ)^3479
        have hw : |(736439503/1250000000 : ℝ)|=(736439503/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s0_5 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1037620327/2000000000 : ℝ)*x 0 + (-627439253/5000000000 : ℝ)*x 1 + (235660643/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1037620327/2000000000 : ℝ)^4503 ≤ (42768576521373/100000000000000 : ℝ)^3479 := by
    have hnat : (1037620327 : ℕ)^4503*100000000000000^3479 ≤ 42768576521373^3479*2000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037620327 2000000000 42768576521373 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (627439253/5000000000 : ℝ)^4503 ≤ (681218439149/10000000000000 : ℝ)^3479 := by
    have hnat : (627439253 : ℕ)^4503*10000000000000^3479 ≤ 681218439149^3479*5000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      627439253 5000000000 681218439149 10000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (235660643/400000000 : ℝ)^4503 ≤ (50419239077107/100000000000000 : ℝ)^3479 := by
    have hnat : (235660643 : ℕ)^4503*100000000000000^3479 ≤ 50419239077107^3479*400000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235660643 400000000 50419239077107 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1037620327/2000000000 : ℝ), (-627439253/5000000000 : ℝ), (235660643/400000000 : ℝ)] ![(42768576521373/100000000000000 : ℝ), (681218439149/10000000000000 : ℝ), (50419239077107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1037620327/2000000000 : ℝ)|^4503 ≤ (42768576521373/100000000000000 : ℝ)^3479
        have hw : |(1037620327/2000000000 : ℝ)|=(1037620327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-627439253/5000000000 : ℝ)|^4503 ≤ (681218439149/10000000000000 : ℝ)^3479
        have hw : |(-627439253/5000000000 : ℝ)|=(627439253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(235660643/400000000 : ℝ)|^4503 ≤ (50419239077107/100000000000000 : ℝ)^3479
        have hw : |(235660643/400000000 : ℝ)|=(235660643/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s0_6 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5188101649/10000000000 : ℝ)*x 0 + (1472879009/2500000000 : ℝ)*x 1 + (-627439273/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5188101649/10000000000 : ℝ)^4503 ≤ (42768576670753/100000000000000 : ℝ)^3479 := by
    have hnat : (5188101649 : ℕ)^4503*100000000000000^3479 ≤ 42768576670753^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5188101649 10000000000 42768576670753 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1472879009/2500000000 : ℝ)^4503 ≤ (5041923864511/10000000000000 : ℝ)^3479 := by
    have hnat : (1472879009 : ℕ)^4503*10000000000000^3479 ≤ 5041923864511^3479*2500000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1472879009 2500000000 5041923864511 10000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (627439273/5000000000 : ℝ)^4503 ≤ (1362436934509/20000000000000 : ℝ)^3479 := by
    have hnat : (627439273 : ℕ)^4503*20000000000000^3479 ≤ 1362436934509^3479*5000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      627439273 5000000000 1362436934509 20000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5188101649/10000000000 : ℝ), (1472879009/2500000000 : ℝ), (-627439273/5000000000 : ℝ)] ![(42768576670753/100000000000000 : ℝ), (5041923864511/10000000000000 : ℝ), (1362436934509/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5188101649/10000000000 : ℝ)|^4503 ≤ (42768576670753/100000000000000 : ℝ)^3479
        have hw : |(5188101649/10000000000 : ℝ)|=(5188101649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1472879009/2500000000 : ℝ)|^4503 ≤ (5041923864511/10000000000000 : ℝ)^3479
        have hw : |(1472879009/2500000000 : ℝ)|=(1472879009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-627439273/5000000000 : ℝ)|^4503 ≤ (1362436934509/20000000000000 : ℝ)^3479
        have hw : |(-627439273/5000000000 : ℝ)|=(627439273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s0_7 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4155686729/10000000000 : ℝ)*x 0 + (543693027/1000000000 : ℝ)*x 1 + (3154943753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4155686729/10000000000 : ℝ)^4503 ≤ (2005742200617/6250000000000 : ℝ)^3479 := by
    have hnat : (4155686729 : ℕ)^4503*6250000000000^3479 ≤ 2005742200617^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4155686729 10000000000 2005742200617 6250000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543693027/1000000000 : ℝ)^4503 ≤ (9088421478327/20000000000000 : ℝ)^3479 := by
    have hnat : (543693027 : ℕ)^4503*20000000000000^3479 ≤ 9088421478327^3479*1000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543693027 1000000000 9088421478327 20000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3154943753/10000000000 : ℝ)^4503 ≤ (4493203476691/20000000000000 : ℝ)^3479 := by
    have hnat : (3154943753 : ℕ)^4503*20000000000000^3479 ≤ 4493203476691^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3154943753 10000000000 4493203476691 20000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4155686729/10000000000 : ℝ), (543693027/1000000000 : ℝ), (3154943753/10000000000 : ℝ)] ![(2005742200617/6250000000000 : ℝ), (9088421478327/20000000000000 : ℝ), (4493203476691/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4155686729/10000000000 : ℝ)|^4503 ≤ (2005742200617/6250000000000 : ℝ)^3479
        have hw : |(4155686729/10000000000 : ℝ)|=(4155686729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(543693027/1000000000 : ℝ)|^4503 ≤ (9088421478327/20000000000000 : ℝ)^3479
        have hw : |(543693027/1000000000 : ℝ)|=(543693027/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3154943753/10000000000 : ℝ)|^4503 ≤ (4493203476691/20000000000000 : ℝ)^3479
        have hw : |(3154943753/10000000000 : ℝ)|=(3154943753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1503_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162660593/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2711/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (25601/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4501/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4501 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4501*1^1024 ≤ 0^1024*1^4501 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4501 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4501 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4501/1024 : ℝ) ≤ (1781769756356751161/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4501 ≤ (1781769756356751161/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4501*100000000000000000000^1024 ≤ 1781769756356751161^1024*5^4501 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1781769756356751161 100000000000000000000 4501 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1781769756356751161/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4501 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4501/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4501 := by
      have hnat : (1 : ℕ)^1024*1^4501 ≤ 1^4501*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4501 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4501 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101781769756356751161/100000000000000000000 : ℝ) ≤ (2510065020547581/2500000000000000 : ℝ) ^ (4501/1024 : ℝ) := by
    have hpowers : (101781769756356751161/100000000000000000000 : ℝ)^1024 ≤ (2510065020547581/2500000000000000 : ℝ)^4501 := by
      have hnat : (101781769756356751161 : ℕ)^1024*2500000000000000^4501 ≤ 2510065020547581^4501*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101781769756356751161 100000000000000000000 2510065020547581 2500000000000000 1024 4501 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2510065020547581/2500000000000000 : ℝ)) (X := (101781769756356751161/100000000000000000000 : ℝ)) (by norm_num) 4501 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51781769756356751161/50000000000000000000 : ℝ) ≤ (1260065020547581/1250000000000000 : ℝ) ^ (4501/1024 : ℝ) := by
    have hpowers : (51781769756356751161/50000000000000000000 : ℝ)^1024 ≤ (1260065020547581/1250000000000000 : ℝ)^4501 := by
      have hnat : (51781769756356751161 : ℕ)^1024*1250000000000000^4501 ≤ 1260065020547581^4501*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51781769756356751161 50000000000000000000 1260065020547581 1250000000000000 1024 4501 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1260065020547581/1250000000000000 : ℝ)) (X := (51781769756356751161/50000000000000000000 : ℝ)) (by norm_num) 4501 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(10065020547581/1000000000000000 : ℝ)*(0 : ℝ))^(4501/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(10065020547581/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1781769756356751161/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(10065020547581/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4501/1024 : ℝ) := by
    rw [show (1 : ℝ)+(10065020547581/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2510065020547581/2500000000000000 : ℝ) by norm_num, show 1+(1781769756356751161/100000000000000000000 : ℝ)+(0 : ℝ)=(101781769756356751161/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1781769756356751161/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(10065020547581/1000000000000000 : ℝ)*(2/5 : ℝ))^(4501/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(10065020547581/1000000000000000 : ℝ)*(2/5 : ℝ)=(1260065020547581/1250000000000000 : ℝ) by norm_num, show 1+2*(1781769756356751161/100000000000000000000 : ℝ)=(51781769756356751161/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(10065020547581/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4501/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (10065020547581/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(10065020547581/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4501/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (10065020547581/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(10065020547581/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4501/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (10065020547581/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-211927639/1250000000 : ℝ)*X 0 0+(2959895837/5000000000 : ℝ)*X 0 1+(4851448901/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5479941269/10000000000 : ℝ)*X 1 0+(-2294945729/10000000000 : ℝ)*X 1 1+(4851448871/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1095988259/2000000000 : ℝ)*X 2 0+(4851448873/10000000000 : ℝ)*X 2 1+(-2294945693/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((829515873/2000000000 : ℝ)*X 0 0+(386404077/1250000000 : ℝ)*X 0 1+(5498435347/10000000000 : ℝ)*X 0 2+(829515873/2000000000 : ℝ)*X 1 0+(386404077/1250000000 : ℝ)*X 1 1+(5498435347/10000000000 : ℝ)*X 1 2+(829515873/2000000000 : ℝ)*X 2 0+(386404077/1250000000 : ℝ)*X 2 1+(5498435347/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-849509593/5000000000 : ℝ)*X 0 0+(4878745479/10000000000 : ℝ)*X 0 1+(736439503/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1037620327/2000000000 : ℝ)*X 1 0+(-627439253/5000000000 : ℝ)*X 1 1+(235660643/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5188101649/10000000000 : ℝ)*X 2 0+(1472879009/2500000000 : ℝ)*X 2 1+(-627439273/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4155686729/10000000000 : ℝ)*X 0 0+(543693027/1000000000 : ℝ)*X 0 1+(3154943753/10000000000 : ℝ)*X 0 2+(4155686729/10000000000 : ℝ)*X 1 0+(543693027/1000000000 : ℝ)*X 1 1+(3154943753/10000000000 : ℝ)*X 1 2+(4155686729/10000000000 : ℝ)*X 2 0+(543693027/1000000000 : ℝ)*X 2 1+(3154943753/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (164817549994273551173841/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29407993/100000000000000 : ℝ)*(base1) + (749300581/100000000000000 : ℝ)*(base19) + (23554427/3125000000000 : ℝ)*(base23) + (4497133/5000000000000 : ℝ)*(upper3) + (101380403/100000000000000 : ℝ)*(upper5) + (675728329868829/100000000000000 : ℝ)*(major0) + (675728329868829/100000000000000 : ℝ)*(major1) + (675728329868829/100000000000000 : ℝ)*(major2) + (23400790694347/2500000000000 : ℝ)*(sp0) + (187206705861801/20000000000000 : ℝ)*(sp1) + (936033524867923/100000000000000 : ℝ)*(sp2) + (20771053610853/5000000000000 : ℝ)*(sp3) + (26802437/1000000000000 : ℝ)*(sp4) + (1169624647/100000000000000 : ℝ)*(sp7) + (415422271249699/100000000000000 : ℝ)*(f.failure) + (468017139304793/50000000000000 : ℝ)*(f.sum) + (99039793102649/50000000000000000000000000000 : ℝ)*base65 + (752930623747351/100000000000000000000000000000 : ℝ)*base68 + (818685985847351/100000000000000000000000000000 : ℝ)*base70 + (30040907547351/100000000000000000000000000000 : ℝ)*base72 + (32640716997351/50000000000000000000000000000 : ℝ)*base74 + (207331146652649/100000000000000000000000000000 : ℝ)*base75 + (341616201547351/100000000000000000000000000000 : ℝ)*base78 + (406959959647351/100000000000000000000000000000 : ℝ)*base80 + (18400235347351/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (9588493/10000000000000000000000 : ℝ)*base90 + (9588493/10000000000000000000000 : ℝ)*base92 + (9588493/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11384977304304832616709/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1021066167/100000000000000 : ℝ)*(base19) + (257738679/25000000000000 : ℝ)*(base23) + (36650017/50000000000000 : ℝ)*(base32) + (77184651/50000000000000 : ℝ)*(upper3) + (105684723/100000000000000 : ℝ)*(upper5) + (71280243254863/10000000000000 : ℝ)*(major0) + (71280243254863/10000000000000 : ℝ)*(major1) + (71280243254863/10000000000000 : ℝ)*(major2) + (5195237/200000000000 : ℝ)*(sp1) + (340755357/12500000000000 : ℝ)*(sp2) + (987390134460607/100000000000000 : ℝ)*(sp4) + (49369325788797/5000000000000 : ℝ)*(sp5) + (246846594365759/25000000000000 : ℝ)*(sp6) + (438214505536913/100000000000000 : ℝ)*(sp7) + (219107289418473/50000000000000 : ℝ)*(f.failure) + (987390134460607/100000000000000 : ℝ)*(f.sum) + (8523607238597/5000000000000000000000000000 : ℝ)*base66 + (14104978506403/10000000000000000000000000000 : ℝ)*base67 + (4898790566403/10000000000000000000000000000 : ℝ)*base69 + (35581341366403/10000000000000000000000000000 : ℝ)*base71 + (10564620713597/5000000000000000000000000000 : ℝ)*base74 + (5051966246403/10000000000000000000000000000 : ℝ)*base75 + (16086123473597/10000000000000000000000000000 : ℝ)*base78 + (71668029803597/10000000000000000000000000000 : ℝ)*base80 + (4352046988597/5000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (56665511/5000000000000000000000 : ℝ)*base90 + (56665511/5000000000000000000000 : ℝ)*base92 + (56665511/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1503_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162660593/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2711/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (25601/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1503_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1503_s1_0 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-925777973/5000000000 : ℝ)*x 0 + (1115313191/2000000000 : ℝ)*x 1 + (2547181613/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (925777973/5000000000 : ℝ)^4503 ≤ (11270560059879/100000000000000 : ℝ)^3479 := by
    have hnat : (925777973 : ℕ)^4503*100000000000000^3479 ≤ 11270560059879^3479*5000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      925777973 5000000000 11270560059879 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1115313191/2000000000 : ℝ)^4503 ≤ (1878335198363/4000000000000 : ℝ)^3479 := by
    have hnat : (1115313191 : ℕ)^4503*4000000000000^3479 ≤ 1878335198363^3479*2000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115313191 2000000000 1878335198363 4000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2547181613/5000000000 : ℝ)^4503 ≤ (10442764990719/25000000000000 : ℝ)^3479 := by
    have hnat : (2547181613 : ℕ)^4503*25000000000000^3479 ≤ 10442764990719^3479*5000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2547181613 5000000000 10442764990719 25000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-925777973/5000000000 : ℝ), (1115313191/2000000000 : ℝ), (2547181613/5000000000 : ℝ)] ![(11270560059879/100000000000000 : ℝ), (1878335198363/4000000000000 : ℝ), (10442764990719/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-925777973/5000000000 : ℝ)|^4503 ≤ (11270560059879/100000000000000 : ℝ)^3479
        have hw : |(-925777973/5000000000 : ℝ)|=(925777973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1115313191/2000000000 : ℝ)|^4503 ≤ (1878335198363/4000000000000 : ℝ)^3479
        have hw : |(1115313191/2000000000 : ℝ)|=(1115313191/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2547181613/5000000000 : ℝ)|^4503 ≤ (10442764990719/25000000000000 : ℝ)^3479
        have hw : |(2547181613/5000000000 : ℝ)|=(2547181613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s1_1 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (538826939/1000000000 : ℝ)*x 0 + (-263219331/1250000000 : ℝ)*x 1 + (50943637/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538826939/1000000000 : ℝ)^4503 ≤ (11229095621923/25000000000000 : ℝ)^3479 := by
    have hnat : (538826939 : ℕ)^4503*25000000000000^3479 ≤ 11229095621923^3479*1000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538826939 1000000000 11229095621923 25000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263219331/1250000000 : ℝ)^4503 ≤ (13312552499867/100000000000000 : ℝ)^3479 := by
    have hnat : (263219331 : ℕ)^4503*100000000000000^3479 ≤ 13312552499867^3479*1250000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263219331 1250000000 13312552499867 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (50943637/100000000 : ℝ)^4503 ≤ (2088553249669/5000000000000 : ℝ)^3479 := by
    have hnat : (50943637 : ℕ)^4503*5000000000000^3479 ≤ 2088553249669^3479*100000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50943637 100000000 2088553249669 5000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538826939/1000000000 : ℝ), (-263219331/1250000000 : ℝ), (50943637/100000000 : ℝ)] ![(11229095621923/25000000000000 : ℝ), (13312552499867/100000000000000 : ℝ), (2088553249669/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538826939/1000000000 : ℝ)|^4503 ≤ (11229095621923/25000000000000 : ℝ)^3479
        have hw : |(538826939/1000000000 : ℝ)|=(538826939/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-263219331/1250000000 : ℝ)|^4503 ≤ (13312552499867/100000000000000 : ℝ)^3479
        have hw : |(-263219331/1250000000 : ℝ)|=(263219331/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(50943637/100000000 : ℝ)|^4503 ≤ (2088553249669/5000000000000 : ℝ)^3479
        have hw : |(50943637/100000000 : ℝ)|=(50943637/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s1_2 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (26941349/50000000 : ℝ)*x 0 + (254718173/500000000 : ℝ)*x 1 + (-2105754419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26941349/50000000 : ℝ)^4503 ≤ (11229096727851/25000000000000 : ℝ)^3479 := by
    have hnat : (26941349 : ℕ)^4503*25000000000000^3479 ≤ 11229096727851^3479*50000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26941349 50000000 11229096727851 25000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (254718173/500000000 : ℝ)^4503 ≤ (41771062446289/100000000000000 : ℝ)^3479 := by
    have hnat : (254718173 : ℕ)^4503*100000000000000^3479 ≤ 41771062446289^3479*500000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254718173 500000000 41771062446289 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2105754419/10000000000 : ℝ)^4503 ≤ (1331255062601/10000000000000 : ℝ)^3479 := by
    have hnat : (2105754419 : ℕ)^4503*10000000000000^3479 ≤ 1331255062601^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105754419 10000000000 1331255062601 10000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26941349/50000000 : ℝ), (254718173/500000000 : ℝ), (-2105754419/10000000000 : ℝ)] ![(11229096727851/25000000000000 : ℝ), (41771062446289/100000000000000 : ℝ), (1331255062601/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26941349/50000000 : ℝ)|^4503 ≤ (11229096727851/25000000000000 : ℝ)^3479
        have hw : |(26941349/50000000 : ℝ)|=(26941349/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(254718173/500000000 : ℝ)|^4503 ≤ (41771062446289/100000000000000 : ℝ)^3479
        have hw : |(254718173/500000000 : ℝ)|=(254718173/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2105754419/10000000000 : ℝ)|^4503 ≤ (1331255062601/10000000000000 : ℝ)^3479
        have hw : |(-2105754419/10000000000 : ℝ)|=(2105754419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s1_3 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4252894937/10000000000 : ℝ)*x 0 + (3739155171/10000000000 : ℝ)*x 1 + (1206414861/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4252894937/10000000000 : ℝ)^4503 ≤ (33066835951881/100000000000000 : ℝ)^3479 := by
    have hnat : (4252894937 : ℕ)^4503*100000000000000^3479 ≤ 33066835951881^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4252894937 10000000000 33066835951881 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3739155171/10000000000 : ℝ)^4503 ≤ (27991406732193/100000000000000 : ℝ)^3479 := by
    have hnat : (3739155171 : ℕ)^4503*100000000000000^3479 ≤ 27991406732193^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3739155171 10000000000 27991406732193 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1206414861/2500000000 : ℝ)^4503 ≤ (19470878647453/50000000000000 : ℝ)^3479 := by
    have hnat : (1206414861 : ℕ)^4503*50000000000000^3479 ≤ 19470878647453^3479*2500000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1206414861 2500000000 19470878647453 50000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4252894937/10000000000 : ℝ), (3739155171/10000000000 : ℝ), (1206414861/2500000000 : ℝ)] ![(33066835951881/100000000000000 : ℝ), (27991406732193/100000000000000 : ℝ), (19470878647453/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4252894937/10000000000 : ℝ)|^4503 ≤ (33066835951881/100000000000000 : ℝ)^3479
        have hw : |(4252894937/10000000000 : ℝ)|=(4252894937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3739155171/10000000000 : ℝ)|^4503 ≤ (27991406732193/100000000000000 : ℝ)^3479
        have hw : |(3739155171/10000000000 : ℝ)|=(3739155171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1206414861/2500000000 : ℝ)|^4503 ≤ (19470878647453/50000000000000 : ℝ)^3479
        have hw : |(1206414861/2500000000 : ℝ)|=(1206414861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s1_4 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-231484393/1250000000 : ℝ)*x 0 + (5099825009/10000000000 : ℝ)*x 1 + (2785507623/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (231484393/1250000000 : ℝ)^4503 ≤ (11273074998303/100000000000000 : ℝ)^3479 := by
    have hnat : (231484393 : ℕ)^4503*100000000000000^3479 ≤ 11273074998303^3479*1250000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      231484393 1250000000 11273074998303 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5099825009/10000000000 : ℝ)^4503 ≤ (20914517167263/50000000000000 : ℝ)^3479 := by
    have hnat : (5099825009 : ℕ)^4503*50000000000000^3479 ≤ 20914517167263^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5099825009 10000000000 20914517167263 50000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2785507623/5000000000 : ℝ)^4503 ≤ (23448945326479/50000000000000 : ℝ)^3479 := by
    have hnat : (2785507623 : ℕ)^4503*50000000000000^3479 ≤ 23448945326479^3479*5000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2785507623 5000000000 23448945326479 50000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-231484393/1250000000 : ℝ), (5099825009/10000000000 : ℝ), (2785507623/5000000000 : ℝ)] ![(11273074998303/100000000000000 : ℝ), (20914517167263/50000000000000 : ℝ), (23448945326479/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-231484393/1250000000 : ℝ)|^4503 ≤ (11273074998303/100000000000000 : ℝ)^3479
        have hw : |(-231484393/1250000000 : ℝ)|=(231484393/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5099825009/10000000000 : ℝ)|^4503 ≤ (20914517167263/50000000000000 : ℝ)^3479
        have hw : |(5099825009/10000000000 : ℝ)|=(5099825009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2785507623/5000000000 : ℝ)|^4503 ≤ (23448945326479/50000000000000 : ℝ)^3479
        have hw : |(2785507623/5000000000 : ℝ)|=(2785507623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s1_5 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1315349849/2500000000 : ℝ)*x 0 + (-2545473/15625000 : ℝ)*x 1 + (5571015389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1315349849/2500000000 : ℝ)^4503 ≤ (43552283332673/100000000000000 : ℝ)^3479 := by
    have hnat : (1315349849 : ℕ)^4503*100000000000000^3479 ≤ 43552283332673^3479*2500000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315349849 2500000000 43552283332673 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2545473/15625000 : ℝ)^4503 ≤ (4774912222917/50000000000000 : ℝ)^3479 := by
    have hnat : (2545473 : ℕ)^4503*50000000000000^3479 ≤ 4774912222917^3479*15625000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2545473 15625000 4774912222917 50000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5571015389/10000000000 : ℝ)^4503 ≤ (11724473052771/25000000000000 : ℝ)^3479 := by
    have hnat : (5571015389 : ℕ)^4503*25000000000000^3479 ≤ 11724473052771^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5571015389 10000000000 11724473052771 25000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1315349849/2500000000 : ℝ), (-2545473/15625000 : ℝ), (5571015389/10000000000 : ℝ)] ![(43552283332673/100000000000000 : ℝ), (4774912222917/50000000000000 : ℝ), (11724473052771/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1315349849/2500000000 : ℝ)|^4503 ≤ (43552283332673/100000000000000 : ℝ)^3479
        have hw : |(1315349849/2500000000 : ℝ)|=(1315349849/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2545473/15625000 : ℝ)|^4503 ≤ (4774912222917/50000000000000 : ℝ)^3479
        have hw : |(-2545473/15625000 : ℝ)|=(2545473/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5571015389/10000000000 : ℝ)|^4503 ≤ (11724473052771/25000000000000 : ℝ)^3479
        have hw : |(5571015389/10000000000 : ℝ)|=(5571015389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s1_6 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1052279851/2000000000 : ℝ)*x 0 + (5571015433/10000000000 : ℝ)*x 1 + (-814551427/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052279851/2000000000 : ℝ)^4503 ≤ (2177614091099/5000000000000 : ℝ)^3479 := by
    have hnat : (1052279851 : ℕ)^4503*5000000000000^3479 ≤ 2177614091099^3479*2000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052279851 2000000000 2177614091099 5000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5571015433/10000000000 : ℝ)^4503 ≤ (46897892690507/100000000000000 : ℝ)^3479 := by
    have hnat : (5571015433 : ℕ)^4503*100000000000000^3479 ≤ 46897892690507^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5571015433 10000000000 46897892690507 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (814551427/5000000000 : ℝ)^4503 ≤ (9549825462549/100000000000000 : ℝ)^3479 := by
    have hnat : (814551427 : ℕ)^4503*100000000000000^3479 ≤ 9549825462549^3479*5000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      814551427 5000000000 9549825462549 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1052279851/2000000000 : ℝ), (5571015433/10000000000 : ℝ), (-814551427/5000000000 : ℝ)] ![(2177614091099/5000000000000 : ℝ), (46897892690507/100000000000000 : ℝ), (9549825462549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1052279851/2000000000 : ℝ)|^4503 ≤ (2177614091099/5000000000000 : ℝ)^3479
        have hw : |(1052279851/2000000000 : ℝ)|=(1052279851/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5571015433/10000000000 : ℝ)|^4503 ≤ (46897892690507/100000000000000 : ℝ)^3479
        have hw : |(5571015433/10000000000 : ℝ)|=(5571015433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-814551427/5000000000 : ℝ)|^4503 ≤ (9549825462549/100000000000000 : ℝ)^3479
        have hw : |(-814551427/5000000000 : ℝ)|=(814551427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s1_7 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4253614561/10000000000 : ℝ)*x 0 + (601669259/1250000000 : ℝ)*x 1 + (3751661457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4253614561/10000000000 : ℝ)^4503 ≤ (16537039087981/50000000000000 : ℝ)^3479 := by
    have hnat : (4253614561 : ℕ)^4503*50000000000000^3479 ≤ 16537039087981^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4253614561 10000000000 16537039087981 50000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (601669259/1250000000 : ℝ)^4503 ≤ (1212914892319/3125000000000 : ℝ)^3479 := by
    have hnat : (601669259 : ℕ)^4503*3125000000000^3479 ≤ 1212914892319^3479*1250000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      601669259 1250000000 1212914892319 3125000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3751661457/10000000000 : ℝ)^4503 ≤ (1405632263143/5000000000000 : ℝ)^3479 := by
    have hnat : (3751661457 : ℕ)^4503*5000000000000^3479 ≤ 1405632263143^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3751661457 10000000000 1405632263143 5000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4253614561/10000000000 : ℝ), (601669259/1250000000 : ℝ), (3751661457/10000000000 : ℝ)] ![(16537039087981/50000000000000 : ℝ), (1212914892319/3125000000000 : ℝ), (1405632263143/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4253614561/10000000000 : ℝ)|^4503 ≤ (16537039087981/50000000000000 : ℝ)^3479
        have hw : |(4253614561/10000000000 : ℝ)|=(4253614561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(601669259/1250000000 : ℝ)|^4503 ≤ (1212914892319/3125000000000 : ℝ)^3479
        have hw : |(601669259/1250000000 : ℝ)|=(601669259/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3751661457/10000000000 : ℝ)|^4503 ≤ (1405632263143/5000000000000 : ℝ)^3479
        have hw : |(3751661457/10000000000 : ℝ)|=(3751661457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1503_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162660593/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25601/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2711/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4117/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18431/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (25601/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2711/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (25601/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2711/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (25601/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2711/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (25601/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2711/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (25601/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2711/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (25601/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2711/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2711/100000 : ℝ) ^ (4501/1024 : ℝ) ≤ (3241518928943/25000000000000000000 : ℝ) := by
    have hpowers : (2711/100000 : ℝ)^4501 ≤ (3241518928943/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2711 : ℕ)^4501*25000000000000000000^1024 ≤ 3241518928943^1024*100000^4501 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2711 100000 3241518928943 25000000000000000000 4501 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2711/100000 : ℝ)) (X := (3241518928943/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4501 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (25601/100000 : ℝ) ^ (4501/1024 : ℝ) ≤ (125302205547927047/50000000000000000000 : ℝ) := by
    have hpowers : (25601/100000 : ℝ)^4501 ≤ (125302205547927047/50000000000000000000 : ℝ)^1024 := by
      have hnat : (25601 : ℕ)^4501*50000000000000000000^1024 ≤ 125302205547927047^1024*100000^4501 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25601 100000 125302205547927047 50000000000000000000 4501 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (25601/100000 : ℝ)) (X := (125302205547927047/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4501 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500003241518928943/12500000000000000000 : ℝ) ≤ (200000011799387/200000000000000 : ℝ) ^ (4501/1024 : ℝ) := by
    have hpowers : (12500003241518928943/12500000000000000000 : ℝ)^1024 ≤ (200000011799387/200000000000000 : ℝ)^4501 := by
      have hnat : (12500003241518928943 : ℕ)^1024*200000000000000^4501 ≤ 200000011799387^4501*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500003241518928943 12500000000000000000 200000011799387 200000000000000 1024 4501 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200000011799387/200000000000000 : ℝ)) (X := (12500003241518928943/12500000000000000000 : ℝ)) (by norm_num) 4501 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50125308688585784933/50000000000000000000 : ℝ) ≤ (10005696159533531/10000000000000000 : ℝ) ^ (4501/1024 : ℝ) := by
    have hpowers : (50125308688585784933/50000000000000000000 : ℝ)^1024 ≤ (10005696159533531/10000000000000000 : ℝ)^4501 := by
      have hnat : (50125308688585784933 : ℕ)^1024*10000000000000000^4501 ≤ 10005696159533531^4501*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50125308688585784933 50000000000000000000 10005696159533531 10000000000000000 1024 4501 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005696159533531/10000000000000000 : ℝ)) (X := (50125308688585784933/50000000000000000000 : ℝ)) (by norm_num) 4501 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25125302205547927047/25000000000000000000 : ℝ) ≤ (625711983068607/625000000000000 : ℝ) ^ (4501/1024 : ℝ) := by
    have hpowers : (25125302205547927047/25000000000000000000 : ℝ)^1024 ≤ (625711983068607/625000000000000 : ℝ)^4501 := by
      have hnat : (25125302205547927047 : ℕ)^1024*625000000000000^4501 ≤ 625711983068607^4501*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25125302205547927047 25000000000000000000 625711983068607 625000000000000 1024 4501 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625711983068607/625000000000000 : ℝ)) (X := (25125302205547927047/25000000000000000000 : ℝ)) (by norm_num) 4501 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3241518928943/25000000000000000000 : ℝ) ≤ ((16347795151872959437/16350000000000000000 : ℝ)+2*(813652794883/327000000000000 : ℝ)*(2711/100000 : ℝ))^(4501/1024 : ℝ) := by
    rw [show (16347795151872959437/16350000000000000000 : ℝ)+2*(813652794883/327000000000000 : ℝ)*(2711/100000 : ℝ)=(200000011799387/200000000000000 : ℝ) by norm_num, show 1+2*(3241518928943/25000000000000000000 : ℝ)=(12500003241518928943/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(125302205547927047/50000000000000000000 : ℝ)+(3241518928943/25000000000000000000 : ℝ) ≤ ((16347795151872959437/16350000000000000000 : ℝ)+(813652794883/327000000000000 : ℝ)*((25601/100000 : ℝ)+(2711/100000 : ℝ)))^(4501/1024 : ℝ) := by
    rw [show (16347795151872959437/16350000000000000000 : ℝ)+(813652794883/327000000000000 : ℝ)*((25601/100000 : ℝ)+(2711/100000 : ℝ))=(10005696159533531/10000000000000000 : ℝ) by norm_num, show 1+(125302205547927047/50000000000000000000 : ℝ)+(3241518928943/25000000000000000000 : ℝ)=(50125308688585784933/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(125302205547927047/50000000000000000000 : ℝ) ≤ ((16347795151872959437/16350000000000000000 : ℝ)+2*(813652794883/327000000000000 : ℝ)*(25601/100000 : ℝ))^(4501/1024 : ℝ) := by
    rw [show (16347795151872959437/16350000000000000000 : ℝ)+2*(813652794883/327000000000000 : ℝ)*(25601/100000 : ℝ)=(625711983068607/625000000000000 : ℝ) by norm_num, show 1+2*(125302205547927047/50000000000000000000 : ℝ)=(25125302205547927047/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16347795151872959437/16350000000000000000 : ℝ)*(X 1 0+X 2 0)+(813652794883/327000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4501/1024 : ℝ)) (lo := (2711/100000 : ℝ)) (hi := (25601/100000 : ℝ)) (c := (16347795151872959437/16350000000000000000 : ℝ)) (alpha := (813652794883/327000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16347795151872959437/16350000000000000000 : ℝ)*(X 0 1+X 2 1)+(813652794883/327000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4501/1024 : ℝ)) (lo := (2711/100000 : ℝ)) (hi := (25601/100000 : ℝ)) (c := (16347795151872959437/16350000000000000000 : ℝ)) (alpha := (813652794883/327000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16347795151872959437/16350000000000000000 : ℝ)*(X 0 2+X 1 2)+(813652794883/327000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4501/1024 : ℝ)) (lo := (2711/100000 : ℝ)) (hi := (25601/100000 : ℝ)) (c := (16347795151872959437/16350000000000000000 : ℝ)) (alpha := (813652794883/327000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-925777973/5000000000 : ℝ)*X 0 0+(1115313191/2000000000 : ℝ)*X 0 1+(2547181613/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((538826939/1000000000 : ℝ)*X 1 0+(-263219331/1250000000 : ℝ)*X 1 1+(50943637/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((26941349/50000000 : ℝ)*X 2 0+(254718173/500000000 : ℝ)*X 2 1+(-2105754419/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4252894937/10000000000 : ℝ)*X 0 0+(3739155171/10000000000 : ℝ)*X 0 1+(1206414861/2500000000 : ℝ)*X 0 2+(4252894937/10000000000 : ℝ)*X 1 0+(3739155171/10000000000 : ℝ)*X 1 1+(1206414861/2500000000 : ℝ)*X 1 2+(4252894937/10000000000 : ℝ)*X 2 0+(3739155171/10000000000 : ℝ)*X 2 1+(1206414861/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-231484393/1250000000 : ℝ)*X 0 0+(5099825009/10000000000 : ℝ)*X 0 1+(2785507623/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1315349849/2500000000 : ℝ)*X 1 0+(-2545473/15625000 : ℝ)*X 1 1+(5571015389/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1052279851/2000000000 : ℝ)*X 2 0+(5571015433/10000000000 : ℝ)*X 2 1+(-814551427/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4253614561/10000000000 : ℝ)*X 0 0+(601669259/1250000000 : ℝ)*X 0 1+(3751661457/10000000000 : ℝ)*X 0 2+(4253614561/10000000000 : ℝ)*X 1 0+(601669259/1250000000 : ℝ)*X 1 1+(3751661457/10000000000 : ℝ)*X 1 2+(4253614561/10000000000 : ℝ)*X 2 0+(601669259/1250000000 : ℝ)*X 2 1+(3751661457/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (253159963370585709191861807/68125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (909559869/100000000000000 : ℝ)*(base19) + (1036154269/100000000000000 : ℝ)*(base23) + (6093677/12500000000000 : ℝ)*(upper3) + (16814713/100000000000000 : ℝ)*(upper4) + (170772293/100000000000000 : ℝ)*(upper5) + (748556384915989/50000000000000 : ℝ)*(major0) + (748556384915989/50000000000000 : ℝ)*(major1) + (748556384915989/50000000000000 : ℝ)*(major2) + (2073824438568813/100000000000000 : ℝ)*(sp0) + (2073833929622509/100000000000000 : ℝ)*(sp1) + (207383380302811/10000000000000 : ℝ)*(sp2) + (920386938409827/100000000000000 : ℝ)*(sp3) + (5200306783/50000000000000 : ℝ)*(sp4) + (1819100711/50000000000000 : ℝ)*(sp7) + (920390576611249/100000000000000 : ℝ)*(f.failure) + (1036917419591189/50000000000000 : ℝ)*(f.sum) + (7168460982731/4087500000000000000000000000 : ℝ)*base65 + (255372733553637269/272500000000000000000000000000000 : ℝ)*base68 + (914236314061362731/272500000000000000000000000000000 : ℝ)*base69 + (2160459164773862731/272500000000000000000000000000000 : ℝ)*base71 + (834716553893/510937500000000000000000000 : ℝ)*base74 + (2659755412726362731/272500000000000000000000000000000 : ℝ)*base75 + (1025666026248862731/272500000000000000000000000000000 : ℝ)*base77 + (669811884148862731/272500000000000000000000000000000 : ℝ)*base79 + (1038699226687/8175000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (107189343/10000000000000000000000 : ℝ)*base90 + (107189343/10000000000000000000000 : ℝ)*base92 + (107189343/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (171344998025380626354621201/68125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (103541321/20000000000000 : ℝ)*(base19) + (493176087/100000000000000 : ℝ)*(base23) + (87682073/100000000000000 : ℝ)*(upper3) + (258041/2000000000000 : ℝ)*(lower4) + (383022033965991/25000000000000 : ℝ)*(major0) + (383022033965991/25000000000000 : ℝ)*(major1) + (383022033965991/25000000000000 : ℝ)*(major2) + (3607624687/100000000000000 : ℝ)*(sp1) + (39320071/1000000000000 : ℝ)*(sp2) + (23530229/100000000000000 : ℝ)*(sp3) + (212228355882221/10000000000000 : ℝ)*(sp4) + (1061139716745459/50000000000000 : ℝ)*(sp5) + (2122279133639023/100000000000000 : ℝ)*(sp6) + (941892605536951/100000000000000 : ℝ)*(sp7) + (47094631453359/5000000000000 : ℝ)*(f.failure) + (212228355882221/10000000000000 : ℝ)*(f.sum) + (2915624271099/1362500000000000000000000000 : ℝ)*base66 + (994514059791864311/136250000000000000000000000000000 : ℝ)*base68 + (555777536039364311/136250000000000000000000000000000 : ℝ)*base70 + (1150790360153114311/136250000000000000000000000000000 : ℝ)*base72 + (7520859316173/2725000000000000000000000000 : ℝ)*base74 + (1255146788886864311/136250000000000000000000000000000 : ℝ)*base76 + (1376909689356864311/136250000000000000000000000000000 : ℝ)*base78 + (1286355846693114311/136250000000000000000000000000000 : ℝ)*base80 + (4124980688477/2725000000000000000000000000 : ℝ)*base81 + (6781887/500000000000000000000 : ℝ)*base89 + (6781887/500000000000000000000 : ℝ)*base91 + (6781887/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1503_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162660593/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25601/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2711/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4117/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18431/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1503_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1503_s2_0 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-375425661/2000000000 : ℝ)*x 0 + (1092170431/2000000000 : ℝ)*x 1 + (5193528421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (375425661/2000000000 : ℝ)^4503 ≤ (11472445951563/100000000000000 : ℝ)^3479 := by
    have hnat : (375425661 : ℕ)^4503*100000000000000^3479 ≤ 11472445951563^3479*2000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375425661 2000000000 11472445951563 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1092170431/2000000000 : ℝ)^4503 ≤ (22850532433597/50000000000000 : ℝ)^3479 := by
    have hnat : (1092170431 : ℕ)^4503*50000000000000^3479 ≤ 22850532433597^3479*2000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092170431 2000000000 22850532433597 50000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5193528421/10000000000 : ℝ)^4503 ≤ (4282648916203/10000000000000 : ℝ)^3479 := by
    have hnat : (5193528421 : ℕ)^4503*10000000000000^3479 ≤ 4282648916203^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5193528421 10000000000 4282648916203 10000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-375425661/2000000000 : ℝ), (1092170431/2000000000 : ℝ), (5193528421/10000000000 : ℝ)] ![(11472445951563/100000000000000 : ℝ), (22850532433597/50000000000000 : ℝ), (4282648916203/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-375425661/2000000000 : ℝ)|^4503 ≤ (11472445951563/100000000000000 : ℝ)^3479
        have hw : |(-375425661/2000000000 : ℝ)|=(375425661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1092170431/2000000000 : ℝ)|^4503 ≤ (22850532433597/50000000000000 : ℝ)^3479
        have hw : |(1092170431/2000000000 : ℝ)|=(1092170431/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5193528421/10000000000 : ℝ)|^4503 ≤ (4282648916203/10000000000000 : ℝ)^3479
        have hw : |(5193528421/10000000000 : ℝ)|=(5193528421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s2_1 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2679475319/5000000000 : ℝ)*x 0 + (-50370403/250000000 : ℝ)*x 1 + (2596764683/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2679475319/5000000000 : ℝ)^4503 ≤ (2230015011811/5000000000000 : ℝ)^3479 := by
    have hnat : (2679475319 : ℕ)^4503*5000000000000^3479 ≤ 2230015011811^3479*5000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2679475319 5000000000 2230015011811 5000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (50370403/250000000 : ℝ)^4503 ≤ (2514640101439/20000000000000 : ℝ)^3479 := by
    have hnat : (50370403 : ℕ)^4503*20000000000000^3479 ≤ 2514640101439^3479*250000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50370403 250000000 2514640101439 20000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2596764683/5000000000 : ℝ)^4503 ≤ (4282649924827/10000000000000 : ℝ)^3479 := by
    have hnat : (2596764683 : ℕ)^4503*10000000000000^3479 ≤ 4282649924827^3479*5000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596764683 5000000000 4282649924827 10000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2679475319/5000000000 : ℝ), (-50370403/250000000 : ℝ), (2596764683/5000000000 : ℝ)] ![(2230015011811/5000000000000 : ℝ), (2514640101439/20000000000000 : ℝ), (4282649924827/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2679475319/5000000000 : ℝ)|^4503 ≤ (2230015011811/5000000000000 : ℝ)^3479
        have hw : |(2679475319/5000000000 : ℝ)|=(2679475319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-50370403/250000000 : ℝ)|^4503 ≤ (2514640101439/20000000000000 : ℝ)^3479
        have hw : |(-50370403/250000000 : ℝ)|=(50370403/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2596764683/5000000000 : ℝ)|^4503 ≤ (4282649924827/10000000000000 : ℝ)^3479
        have hw : |(2596764683/5000000000 : ℝ)|=(2596764683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s2_2 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5358951583/10000000000 : ℝ)*x 0 + (5193528719/10000000000 : ℝ)*x 1 + (-2014815713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5358951583/10000000000 : ℝ)^4503 ≤ (5575038801997/12500000000000 : ℝ)^3479 := by
    have hnat : (5358951583 : ℕ)^4503*12500000000000^3479 ≤ 5575038801997^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5358951583 10000000000 5575038801997 12500000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5193528719/10000000000 : ℝ)^4503 ≤ (5353311542833/12500000000000 : ℝ)^3479 := by
    have hnat : (5193528719 : ℕ)^4503*12500000000000^3479 ≤ 5353311542833^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5193528719 10000000000 5353311542833 12500000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2014815713/10000000000 : ℝ)^4503 ≤ (12573197219797/100000000000000 : ℝ)^3479 := by
    have hnat : (2014815713 : ℕ)^4503*100000000000000^3479 ≤ 12573197219797^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014815713 10000000000 12573197219797 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5358951583/10000000000 : ℝ), (5193528719/10000000000 : ℝ), (-2014815713/10000000000 : ℝ)] ![(5575038801997/12500000000000 : ℝ), (5353311542833/12500000000000 : ℝ), (12573197219797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5358951583/10000000000 : ℝ)|^4503 ≤ (5575038801997/12500000000000 : ℝ)^3479
        have hw : |(5358951583/10000000000 : ℝ)|=(5358951583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5193528719/10000000000 : ℝ)|^4503 ≤ (5353311542833/12500000000000 : ℝ)^3479
        have hw : |(5193528719/10000000000 : ℝ)|=(5193528719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2014815713/10000000000 : ℝ)|^4503 ≤ (12573197219797/100000000000000 : ℝ)^3479
        have hw : |(-2014815713/10000000000 : ℝ)|=(2014815713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s2_3 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4271221949/10000000000 : ℝ)*x 0 + (994781637/2500000000 : ℝ)*x 1 + (2290732119/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4271221949/10000000000 : ℝ)^4503 ≤ (1662569471419/5000000000000 : ℝ)^3479 := by
    have hnat : (4271221949 : ℕ)^4503*5000000000000^3479 ≤ 1662569471419^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4271221949 10000000000 1662569471419 5000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (994781637/2500000000 : ℝ)^4503 ≤ (30338234027329/100000000000000 : ℝ)^3479 := by
    have hnat : (994781637 : ℕ)^4503*100000000000000^3479 ≤ 30338234027329^3479*2500000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      994781637 2500000000 30338234027329 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2290732119/5000000000 : ℝ)^4503 ≤ (36410376532361/100000000000000 : ℝ)^3479 := by
    have hnat : (2290732119 : ℕ)^4503*100000000000000^3479 ≤ 36410376532361^3479*5000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2290732119 5000000000 36410376532361 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4271221949/10000000000 : ℝ), (994781637/2500000000 : ℝ), (2290732119/5000000000 : ℝ)] ![(1662569471419/5000000000000 : ℝ), (30338234027329/100000000000000 : ℝ), (36410376532361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4271221949/10000000000 : ℝ)|^4503 ≤ (1662569471419/5000000000000 : ℝ)^3479
        have hw : |(4271221949/10000000000 : ℝ)|=(4271221949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(994781637/2500000000 : ℝ)|^4503 ≤ (30338234027329/100000000000000 : ℝ)^3479
        have hw : |(994781637/2500000000 : ℝ)|=(994781637/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2290732119/5000000000 : ℝ)|^4503 ≤ (36410376532361/100000000000000 : ℝ)^3479
        have hw : |(2290732119/5000000000 : ℝ)|=(2290732119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s2_4 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-375436421/2000000000 : ℝ)*x 0 + (1298804153/2500000000 : ℝ)*x 1 + (5459149273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (375436421/2000000000 : ℝ)^4503 ≤ (1147287154379/10000000000000 : ℝ)^3479 := by
    have hnat : (375436421 : ℕ)^4503*10000000000000^3479 ≤ 1147287154379^3479*2000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375436421 2000000000 1147287154379 10000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1298804153/2500000000 : ℝ)^4503 ≤ (8568901708317/20000000000000 : ℝ)^3479 := by
    have hnat : (1298804153 : ℕ)^4503*20000000000000^3479 ≤ 8568901708317^3479*2500000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298804153 2500000000 8568901708317 20000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5459149273/10000000000 : ℝ)^4503 ≤ (45682619893457/100000000000000 : ℝ)^3479 := by
    have hnat : (5459149273 : ℕ)^4503*100000000000000^3479 ≤ 45682619893457^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5459149273 10000000000 45682619893457 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-375436421/2000000000 : ℝ), (1298804153/2500000000 : ℝ), (5459149273/10000000000 : ℝ)] ![(1147287154379/10000000000000 : ℝ), (8568901708317/20000000000000 : ℝ), (45682619893457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-375436421/2000000000 : ℝ)|^4503 ≤ (1147287154379/10000000000000 : ℝ)^3479
        have hw : |(-375436421/2000000000 : ℝ)|=(375436421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1298804153/2500000000 : ℝ)|^4503 ≤ (8568901708317/20000000000000 : ℝ)^3479
        have hw : |(1298804153/2500000000 : ℝ)|=(1298804153/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5459149273/10000000000 : ℝ)|^4503 ≤ (45682619893457/100000000000000 : ℝ)^3479
        have hw : |(5459149273/10000000000 : ℝ)|=(5459149273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s2_5 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (21155407/40000000 : ℝ)*x 0 + (-1749195333/10000000000 : ℝ)*x 1 + (1091829957/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21155407/40000000 : ℝ)^4503 ≤ (43846637180529/100000000000000 : ℝ)^3479 := by
    have hnat : (21155407 : ℕ)^4503*100000000000000^3479 ≤ 43846637180529^3479*40000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21155407 40000000 43846637180529 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1749195333/10000000000 : ℝ)^4503 ≤ (2094147472687/20000000000000 : ℝ)^3479 := by
    have hnat : (1749195333 : ℕ)^4503*20000000000000^3479 ≤ 2094147472687^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1749195333 10000000000 2094147472687 20000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1091829957/2000000000 : ℝ)^4503 ≤ (45682625438993/100000000000000 : ℝ)^3479 := by
    have hnat : (1091829957 : ℕ)^4503*100000000000000^3479 ≤ 45682625438993^3479*2000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091829957 2000000000 45682625438993 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21155407/40000000 : ℝ), (-1749195333/10000000000 : ℝ), (1091829957/2000000000 : ℝ)] ![(43846637180529/100000000000000 : ℝ), (2094147472687/20000000000000 : ℝ), (45682625438993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21155407/40000000 : ℝ)|^4503 ≤ (43846637180529/100000000000000 : ℝ)^3479
        have hw : |(21155407/40000000 : ℝ)|=(21155407/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1749195333/10000000000 : ℝ)|^4503 ≤ (2094147472687/20000000000000 : ℝ)^3479
        have hw : |(-1749195333/10000000000 : ℝ)|=(1749195333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1091829957/2000000000 : ℝ)|^4503 ≤ (45682625438993/100000000000000 : ℝ)^3479
        have hw : |(1091829957/2000000000 : ℝ)|=(1091829957/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s2_6 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661106469/1250000000 : ℝ)*x 0 + (218365977/400000000 : ℝ)*x 1 + (-1749195833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661106469/1250000000 : ℝ)^4503 ≤ (4384663720199/10000000000000 : ℝ)^3479 := by
    have hnat : (661106469 : ℕ)^4503*10000000000000^3479 ≤ 4384663720199^3479*1250000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661106469 1250000000 4384663720199 10000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (218365977/400000000 : ℝ)^4503 ≤ (11420655384947/25000000000000 : ℝ)^3479 := by
    have hnat : (218365977 : ℕ)^4503*25000000000000^3479 ≤ 11420655384947^3479*400000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218365977 400000000 11420655384947 25000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1749195833/10000000000 : ℝ)^4503 ≤ (10470741237407/100000000000000 : ℝ)^3479 := by
    have hnat : (1749195833 : ℕ)^4503*100000000000000^3479 ≤ 10470741237407^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1749195833 10000000000 10470741237407 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661106469/1250000000 : ℝ), (218365977/400000000 : ℝ), (-1749195833/10000000000 : ℝ)] ![(4384663720199/10000000000000 : ℝ), (11420655384947/25000000000000 : ℝ), (10470741237407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661106469/1250000000 : ℝ)|^4503 ≤ (4384663720199/10000000000000 : ℝ)^3479
        have hw : |(661106469/1250000000 : ℝ)|=(661106469/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(218365977/400000000 : ℝ)|^4503 ≤ (11420655384947/25000000000000 : ℝ)^3479
        have hw : |(218365977/400000000 : ℝ)|=(218365977/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1749195833/10000000000 : ℝ)|^4503 ≤ (10470741237407/100000000000000 : ℝ)^3479
        have hw : |(-1749195833/10000000000 : ℝ)|=(1749195833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1503_s2_7 (p : ℝ) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2135672863/5000000000 : ℝ)*x 0 + (457766151/1000000000 : ℝ)*x 1 + (3982962951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2135672863/5000000000 : ℝ)^4503 ≤ (33252636659621/100000000000000 : ℝ)^3479 := by
    have hnat : (2135672863 : ℕ)^4503*100000000000000^3479 ≤ 33252636659621^3479*5000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135672863 5000000000 33252636659621 100000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (457766151/1000000000 : ℝ)^4503 ≤ (181856322409/500000000000 : ℝ)^3479 := by
    have hnat : (457766151 : ℕ)^4503*500000000000^3479 ≤ 181856322409^3479*1000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      457766151 1000000000 181856322409 500000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3982962951/10000000000 : ℝ)^4503 ≤ (7594024711683/25000000000000 : ℝ)^3479 := by
    have hnat : (3982962951 : ℕ)^4503*25000000000000^3479 ≤ 7594024711683^3479*10000000000^4503 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3982962951 10000000000 7594024711683 25000000000000 4503 3479 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4503/1024 : ℝ)) 4503 3479 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2135672863/5000000000 : ℝ), (457766151/1000000000 : ℝ), (3982962951/10000000000 : ℝ)] ![(33252636659621/100000000000000 : ℝ), (181856322409/500000000000 : ℝ), (7594024711683/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2135672863/5000000000 : ℝ)|^4503 ≤ (33252636659621/100000000000000 : ℝ)^3479
        have hw : |(2135672863/5000000000 : ℝ)|=(2135672863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(457766151/1000000000 : ℝ)|^4503 ≤ (181856322409/500000000000 : ℝ)^3479
        have hw : |(457766151/1000000000 : ℝ)|=(457766151/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3982962951/10000000000 : ℝ)|^4503 ≤ (7594024711683/25000000000000 : ℝ)^3479
        have hw : |(3982962951/10000000000 : ℝ)|=(3982962951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1503_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162660593/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18431/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4117/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5187/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16031/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18431/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4117/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18431/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4117/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18431/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4117/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18431/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4117/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18431/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4117/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18431/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4117/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4117/50000 : ℝ) ^ (4501/1024 : ℝ) ≤ (1712218065843717/100000000000000000000 : ℝ) := by
    have hpowers : (4117/50000 : ℝ)^4501 ≤ (1712218065843717/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4117 : ℕ)^4501*100000000000000000000^1024 ≤ 1712218065843717^1024*50000^4501 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4117 50000 1712218065843717 100000000000000000000 4501 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4117/50000 : ℝ)) (X := (1712218065843717/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4501 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18431/100000 : ℝ) ^ (4501/1024 : ℝ) ≤ (2955864029465721/5000000000000000000 : ℝ) := by
    have hpowers : (18431/100000 : ℝ)^4501 ≤ (2955864029465721/5000000000000000000 : ℝ)^1024 := by
      have hnat : (18431 : ℕ)^4501*5000000000000000000^1024 ≤ 2955864029465721^1024*100000^4501 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18431 100000 2955864029465721 5000000000000000000 4501 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18431/100000 : ℝ)) (X := (2955864029465721/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4501 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001712218065843717/50000000000000000000 : ℝ) ≤ (5000038953301693/5000000000000000 : ℝ) ^ (4501/1024 : ℝ) := by
    have hpowers : (50001712218065843717/50000000000000000000 : ℝ)^1024 ≤ (5000038953301693/5000000000000000 : ℝ)^4501 := by
      have hnat : (50001712218065843717 : ℕ)^1024*5000000000000000^4501 ≤ 5000038953301693^4501*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001712218065843717 50000000000000000000 5000038953301693 5000000000000000 1024 4501 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000038953301693/5000000000000000 : ℝ)) (X := (50001712218065843717/50000000000000000000 : ℝ)) (by norm_num) 4501 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100060829498655158137/100000000000000000000 : ℝ) ≤ (10001383576468203/10000000000000000 : ℝ) ^ (4501/1024 : ℝ) := by
    have hpowers : (100060829498655158137/100000000000000000000 : ℝ)^1024 ≤ (10001383576468203/10000000000000000 : ℝ)^4501 := by
      have hnat : (100060829498655158137 : ℕ)^1024*10000000000000000^4501 ≤ 10001383576468203^4501*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100060829498655158137 100000000000000000000 10001383576468203 10000000000000000 1024 4501 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001383576468203/10000000000000000 : ℝ)) (X := (100060829498655158137/100000000000000000000 : ℝ)) (by norm_num) 4501 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2502955864029465721/2500000000000000000 : ℝ) ≤ (500134462316651/500000000000000 : ℝ) ^ (4501/1024 : ℝ) := by
    have hpowers : (2502955864029465721/2500000000000000000 : ℝ)^1024 ≤ (500134462316651/500000000000000 : ℝ)^4501 := by
      have hnat : (2502955864029465721 : ℕ)^1024*500000000000000^4501 ≤ 500134462316651^4501*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2502955864029465721 2500000000000000000 500134462316651 500000000000000 1024 4501 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500134462316651/500000000000000 : ℝ)) (X := (2502955864029465721/2500000000000000000 : ℝ)) (by norm_num) 4501 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1712218065843717/100000000000000000000 : ℝ) ≤ ((50974646321150460343/50985000000000000000 : ℝ)+2*(1305669864817/1019700000000000 : ℝ)*(4117/50000 : ℝ))^(4501/1024 : ℝ) := by
    rw [show (50974646321150460343/50985000000000000000 : ℝ)+2*(1305669864817/1019700000000000 : ℝ)*(4117/50000 : ℝ)=(5000038953301693/5000000000000000 : ℝ) by norm_num, show 1+2*(1712218065843717/100000000000000000000 : ℝ)=(50001712218065843717/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2955864029465721/5000000000000000000 : ℝ)+(1712218065843717/100000000000000000000 : ℝ) ≤ ((50974646321150460343/50985000000000000000 : ℝ)+(1305669864817/1019700000000000 : ℝ)*((18431/100000 : ℝ)+(4117/50000 : ℝ)))^(4501/1024 : ℝ) := by
    rw [show (50974646321150460343/50985000000000000000 : ℝ)+(1305669864817/1019700000000000 : ℝ)*((18431/100000 : ℝ)+(4117/50000 : ℝ))=(10001383576468203/10000000000000000 : ℝ) by norm_num, show 1+(2955864029465721/5000000000000000000 : ℝ)+(1712218065843717/100000000000000000000 : ℝ)=(100060829498655158137/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2955864029465721/5000000000000000000 : ℝ) ≤ ((50974646321150460343/50985000000000000000 : ℝ)+2*(1305669864817/1019700000000000 : ℝ)*(18431/100000 : ℝ))^(4501/1024 : ℝ) := by
    rw [show (50974646321150460343/50985000000000000000 : ℝ)+2*(1305669864817/1019700000000000 : ℝ)*(18431/100000 : ℝ)=(500134462316651/500000000000000 : ℝ) by norm_num, show 1+2*(2955864029465721/5000000000000000000 : ℝ)=(2502955864029465721/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (50974646321150460343/50985000000000000000 : ℝ)*(X 1 0+X 2 0)+(1305669864817/1019700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4501/1024 : ℝ)) (lo := (4117/50000 : ℝ)) (hi := (18431/100000 : ℝ)) (c := (50974646321150460343/50985000000000000000 : ℝ)) (alpha := (1305669864817/1019700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (50974646321150460343/50985000000000000000 : ℝ)*(X 0 1+X 2 1)+(1305669864817/1019700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4501/1024 : ℝ)) (lo := (4117/50000 : ℝ)) (hi := (18431/100000 : ℝ)) (c := (50974646321150460343/50985000000000000000 : ℝ)) (alpha := (1305669864817/1019700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (50974646321150460343/50985000000000000000 : ℝ)*(X 0 2+X 1 2)+(1305669864817/1019700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4501/1024 : ℝ)) (lo := (4117/50000 : ℝ)) (hi := (18431/100000 : ℝ)) (c := (50974646321150460343/50985000000000000000 : ℝ)) (alpha := (1305669864817/1019700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-375425661/2000000000 : ℝ)*X 0 0+(1092170431/2000000000 : ℝ)*X 0 1+(5193528421/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2679475319/5000000000 : ℝ)*X 1 0+(-50370403/250000000 : ℝ)*X 1 1+(2596764683/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5358951583/10000000000 : ℝ)*X 2 0+(5193528719/10000000000 : ℝ)*X 2 1+(-2014815713/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4271221949/10000000000 : ℝ)*X 0 0+(994781637/2500000000 : ℝ)*X 0 1+(2290732119/5000000000 : ℝ)*X 0 2+(4271221949/10000000000 : ℝ)*X 1 0+(994781637/2500000000 : ℝ)*X 1 1+(2290732119/5000000000 : ℝ)*X 1 2+(4271221949/10000000000 : ℝ)*X 2 0+(994781637/2500000000 : ℝ)*X 2 1+(2290732119/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-375436421/2000000000 : ℝ)*X 0 0+(1298804153/2500000000 : ℝ)*X 0 1+(5459149273/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((21155407/40000000 : ℝ)*X 1 0+(-1749195333/10000000000 : ℝ)*X 1 1+(1091829957/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((661106469/1250000000 : ℝ)*X 2 0+(218365977/400000000 : ℝ)*X 2 1+(-1749195833/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2135672863/5000000000 : ℝ)*X 0 0+(457766151/1000000000 : ℝ)*X 0 1+(3982962951/10000000000 : ℝ)*X 0 2+(2135672863/5000000000 : ℝ)*X 1 0+(457766151/1000000000 : ℝ)*X 1 1+(3982962951/10000000000 : ℝ)*X 1 2+(2135672863/5000000000 : ℝ)*X 2 0+(457766151/1000000000 : ℝ)*X 2 1+(3982962951/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1503_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (914690357108158383801967389/141625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (318664273/25000000000000 : ℝ)*(base19) + (157526853/10000000000000 : ℝ)*(base23) + (104010483/100000000000000 : ℝ)*(upper3) + (192412729/100000000000000 : ℝ)*(upper4) + (36101267/12500000000000 : ℝ)*(upper5) + (1350265265344569/50000000000000 : ℝ)*(major0) + (1350265265344569/50000000000000 : ℝ)*(major1) + (1350265265344569/50000000000000 : ℝ)*(major2) + (935201046678479/25000000000000 : ℝ)*(sp0) + (3740835370305633/100000000000000 : ℝ)*(sp1) + (748167013938839/20000000000000 : ℝ)*(sp2) + (415052731588039/25000000000000 : ℝ)*(sp3) + (32458248809/100000000000000 : ℝ)*(sp4) + (1659347351/12500000000000 : ℝ)*(sp7) + (415056050282741/25000000000000 : ℝ)*(f.failure) + (149633465798509/4000000000000 : ℝ)*(f.sum) + (147902898349783/16995000000000000000000000000 : ℝ)*base66 + (950429032916602537/283250000000000000000000000000000 : ℝ)*base68 + (1146038756068852537/283250000000000000000000000000000 : ℝ)*base70 + (2765911084679102537/283250000000000000000000000000000 : ℝ)*base72 + (34720380507689/8497500000000000000000000000 : ℝ)*base74 + (5217725912029897463/283250000000000000000000000000000 : ℝ)*base75 + (896692452059852537/283250000000000000000000000000000 : ℝ)*base78 + (2228490782443147463/283250000000000000000000000000000 : ℝ)*base79 + (139367366496913/16995000000000000000000000000 : ℝ)*base82 + (18725413/2500000000000000000000 : ℝ)*base89 + (18725413/2500000000000000000000 : ℝ)*base91 + (18725413/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (484913233795517918698430979/141625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (180257881/100000000000000 : ℝ)*(base23) + (9964441/20000000000000 : ℝ)*(lower2) + (78251257/100000000000000 : ℝ)*(upper3) + (82633151/50000000000000 : ℝ)*(lower4) + (2735185295968959/100000000000000 : ℝ)*(major0) + (2735185295968959/100000000000000 : ℝ)*(major1) + (2735185295968959/100000000000000 : ℝ)*(major2) + (4357248577/100000000000000 : ℝ)*(sp1) + (276111389/20000000000000 : ℝ)*(sp2) + (620633233/25000000000000 : ℝ)*(sp3) + (1894420661102907/50000000000000 : ℝ)*(sp4) + (1894418482478619/50000000000000 : ℝ)*(sp5) + (3788839761390989/100000000000000 : ℝ)*(sp6) + (840763336534181/50000000000000 : ℝ)*(sp7) + (336305831120259/20000000000000 : ℝ)*(f.failure) + (1894420661102907/50000000000000 : ℝ)*(f.sum) + (95784779402551/16995000000000000000000000000 : ℝ)*base65 + (30559890583373007/566500000000000000000000000000000 : ℝ)*base68 + (1585663445687373007/566500000000000000000000000000000 : ℝ)*base70 + (1498217715986373007/566500000000000000000000000000000 : ℝ)*base72 + (81333811053811/16995000000000000000000000000 : ℝ)*base73 + (1426268921222373007/566500000000000000000000000000000 : ℝ)*base76 + (14676009871053126993/566500000000000000000000000000000 : ℝ)*base77 + (9942130345281373007/566500000000000000000000000000000 : ℝ)*base80 + (48347831568781/16995000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (3253587/2000000000000000000000 : ℝ)*base89 + (3253587/2000000000000000000000 : ℝ)*base91 + (3253587/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1503_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162660593/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18431/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4117/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5187/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16031/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1503_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1503_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162660593/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5187/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16031/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1503_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1503_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1503_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4501/1024 : ℝ) ≤ p) (hpb : p ≤ (4503/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162660593/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5187/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16031/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1503_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
