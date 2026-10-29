-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1314_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:41:06.655578+00:00
-- url     : https://prove2.me/submissions/55fa6013-fa1e-4d5d-8193-7935901fb47c

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
theorem support_rectangle_w1314_s6_0 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-517100827/2500000000 : ℝ)*x 0 + (2707086933/5000000000 : ℝ)*x 1 + (2621844089/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (517100827/2500000000 : ℝ)^2137 ≤ (12589476621191/100000000000000 : ℝ)^1625 := by
    have hnat : (517100827 : ℕ)^2137*100000000000000^1625 ≤ 12589476621191^1625*2500000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517100827 2500000000 12589476621191 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707086933/5000000000 : ℝ)^2137 ≤ (5578075088023/12500000000000 : ℝ)^1625 := by
    have hnat : (2707086933 : ℕ)^2137*12500000000000^1625 ≤ 5578075088023^1625*5000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707086933 5000000000 5578075088023 12500000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621844089/5000000000 : ℝ)^2137 ≤ (334265020799/781250000000 : ℝ)^1625 := by
    have hnat : (2621844089 : ℕ)^2137*781250000000^1625 ≤ 334265020799^1625*5000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621844089 5000000000 334265020799 781250000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-517100827/2500000000 : ℝ), (2707086933/5000000000 : ℝ), (2621844089/5000000000 : ℝ)] ![(12589476621191/100000000000000 : ℝ), (5578075088023/12500000000000 : ℝ), (334265020799/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-517100827/2500000000 : ℝ)|^2137 ≤ (12589476621191/100000000000000 : ℝ)^1625
        have hw : |(-517100827/2500000000 : ℝ)|=(517100827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707086933/5000000000 : ℝ)|^2137 ≤ (5578075088023/12500000000000 : ℝ)^1625
        have hw : |(2707086933/5000000000 : ℝ)|=(2707086933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621844089/5000000000 : ℝ)|^2137 ≤ (334265020799/781250000000 : ℝ)^1625
        have hw : |(2621844089/5000000000 : ℝ)|=(2621844089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s6_1 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (267473339/500000000 : ℝ)*x 0 + (-2155289651/10000000000 : ℝ)*x 1 + (5243689933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267473339/500000000 : ℝ)^2137 ≤ (43924558162157/100000000000000 : ℝ)^1625 := by
    have hnat : (267473339 : ℕ)^2137*100000000000000^1625 ≤ 43924558162157^1625*500000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267473339 500000000 43924558162157 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2155289651/10000000000 : ℝ)^2137 ≤ (13289500337309/100000000000000 : ℝ)^1625 := by
    have hnat : (2155289651 : ℕ)^2137*100000000000000^1625 ≤ 13289500337309^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155289651 10000000000 13289500337309 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243689933/10000000000 : ℝ)^2137 ≤ (8557188298819/20000000000000 : ℝ)^1625 := by
    have hnat : (5243689933 : ℕ)^2137*20000000000000^1625 ≤ 8557188298819^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243689933 10000000000 8557188298819 20000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267473339/500000000 : ℝ), (-2155289651/10000000000 : ℝ), (5243689933/10000000000 : ℝ)] ![(43924558162157/100000000000000 : ℝ), (13289500337309/100000000000000 : ℝ), (8557188298819/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267473339/500000000 : ℝ)|^2137 ≤ (43924558162157/100000000000000 : ℝ)^1625
        have hw : |(267473339/500000000 : ℝ)|=(267473339/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2155289651/10000000000 : ℝ)|^2137 ≤ (13289500337309/100000000000000 : ℝ)^1625
        have hw : |(-2155289651/10000000000 : ℝ)|=(2155289651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243689933/10000000000 : ℝ)|^2137 ≤ (8557188298819/20000000000000 : ℝ)^1625
        have hw : |(5243689933/10000000000 : ℝ)|=(5243689933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s6_2 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674734163/5000000000 : ℝ)*x 0 + (5243687419/10000000000 : ℝ)*x 1 + (-1077645459/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674734163/5000000000 : ℝ)^2137 ≤ (2745285928503/6250000000000 : ℝ)^1625 := by
    have hnat : (2674734163 : ℕ)^2137*6250000000000^1625 ≤ 2745285928503^1625*5000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674734163 5000000000 2745285928503 6250000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243687419/10000000000 : ℝ)^2137 ≤ (5348239314739/12500000000000 : ℝ)^1625 := by
    have hnat : (5243687419 : ℕ)^2137*12500000000000^1625 ≤ 5348239314739^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243687419 10000000000 5348239314739 12500000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077645459/5000000000 : ℝ)^2137 ≤ (6644755305551/50000000000000 : ℝ)^1625 := by
    have hnat : (1077645459 : ℕ)^2137*50000000000000^1625 ≤ 6644755305551^1625*5000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077645459 5000000000 6644755305551 50000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674734163/5000000000 : ℝ), (5243687419/10000000000 : ℝ), (-1077645459/5000000000 : ℝ)] ![(2745285928503/6250000000000 : ℝ), (5348239314739/12500000000000 : ℝ), (6644755305551/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674734163/5000000000 : ℝ)|^2137 ≤ (2745285928503/6250000000000 : ℝ)^1625
        have hw : |(2674734163/5000000000 : ℝ)|=(2674734163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243687419/10000000000 : ℝ)|^2137 ≤ (5348239314739/12500000000000 : ℝ)^1625
        have hw : |(5243687419/10000000000 : ℝ)|=(5243687419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1077645459/5000000000 : ℝ)|^2137 ≤ (6644755305551/50000000000000 : ℝ)^1625
        have hw : |(-1077645459/5000000000 : ℝ)|=(1077645459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s6_3 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (34671927/80000000 : ℝ)*x 0 + (832146781/2000000000 : ℝ)*x 1 + (112851641/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34671927/80000000 : ℝ)^2137 ≤ (6660545113647/20000000000000 : ℝ)^1625 := by
    have hnat : (34671927 : ℕ)^2137*20000000000000^1625 ≤ 6660545113647^1625*80000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34671927 80000000 6660545113647 20000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (832146781/2000000000 : ℝ)^2137 ≤ (6312613134413/20000000000000 : ℝ)^1625 := by
    have hnat : (832146781 : ℕ)^2137*20000000000000^1625 ≤ 6312613134413^1625*2000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      832146781 2000000000 6312613134413 20000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (112851641/250000000 : ℝ)^2137 ≤ (17567104373429/50000000000000 : ℝ)^1625 := by
    have hnat : (112851641 : ℕ)^2137*50000000000000^1625 ≤ 17567104373429^1625*250000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112851641 250000000 17567104373429 50000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34671927/80000000 : ℝ), (832146781/2000000000 : ℝ), (112851641/250000000 : ℝ)] ![(6660545113647/20000000000000 : ℝ), (6312613134413/20000000000000 : ℝ), (17567104373429/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34671927/80000000 : ℝ)|^2137 ≤ (6660545113647/20000000000000 : ℝ)^1625
        have hw : |(34671927/80000000 : ℝ)|=(34671927/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(832146781/2000000000 : ℝ)|^2137 ≤ (6312613134413/20000000000000 : ℝ)^1625
        have hw : |(832146781/2000000000 : ℝ)|=(832146781/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(112851641/250000000 : ℝ)|^2137 ≤ (17567104373429/50000000000000 : ℝ)^1625
        have hw : |(112851641/250000000 : ℝ)|=(112851641/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s6_4 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1034207989/5000000000 : ℝ)*x 0 + (5244297923/10000000000 : ℝ)*x 1 + (2706780429/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1034207989/5000000000 : ℝ)^2137 ≤ (12589578035829/100000000000000 : ℝ)^1625 := by
    have hnat : (1034207989 : ℕ)^2137*100000000000000^1625 ≤ 12589578035829^1625*5000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034207989 5000000000 12589578035829 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244297923/10000000000 : ℝ)^2137 ≤ (10698116394791/25000000000000 : ℝ)^1625 := by
    have hnat : (5244297923 : ℕ)^2137*25000000000000^1625 ≤ 10698116394791^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244297923 10000000000 10698116394791 25000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706780429/5000000000 : ℝ)^2137 ≤ (22308978183243/50000000000000 : ℝ)^1625 := by
    have hnat : (2706780429 : ℕ)^2137*50000000000000^1625 ≤ 22308978183243^1625*5000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706780429 5000000000 22308978183243 50000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1034207989/5000000000 : ℝ), (5244297923/10000000000 : ℝ), (2706780429/5000000000 : ℝ)] ![(12589578035829/100000000000000 : ℝ), (10698116394791/25000000000000 : ℝ), (22308978183243/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1034207989/5000000000 : ℝ)|^2137 ≤ (12589578035829/100000000000000 : ℝ)^1625
        have hw : |(-1034207989/5000000000 : ℝ)|=(1034207989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244297923/10000000000 : ℝ)|^2137 ≤ (10698116394791/25000000000000 : ℝ)^1625
        have hw : |(5244297923/10000000000 : ℝ)|=(5244297923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706780429/5000000000 : ℝ)|^2137 ≤ (22308978183243/50000000000000 : ℝ)^1625
        have hw : |(2706780429/5000000000 : ℝ)|=(2706780429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s6_5 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305700019/10000000000 : ℝ)*x 0 + (-1985417809/10000000000 : ℝ)*x 1 + (338347559/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305700019/10000000000 : ℝ)^2137 ≤ (43452569794333/100000000000000 : ℝ)^1625 := by
    have hnat : (5305700019 : ℕ)^2137*100000000000000^1625 ≤ 43452569794333^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305700019 10000000000 43452569794333 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1985417809/10000000000 : ℝ)^2137 ≤ (11929472885093/100000000000000 : ℝ)^1625 := by
    have hnat : (1985417809 : ℕ)^2137*100000000000000^1625 ≤ 11929472885093^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1985417809 10000000000 11929472885093 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338347559/625000000 : ℝ)^2137 ≤ (5577244662327/12500000000000 : ℝ)^1625 := by
    have hnat : (338347559 : ℕ)^2137*12500000000000^1625 ≤ 5577244662327^1625*625000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338347559 625000000 5577244662327 12500000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305700019/10000000000 : ℝ), (-1985417809/10000000000 : ℝ), (338347559/625000000 : ℝ)] ![(43452569794333/100000000000000 : ℝ), (11929472885093/100000000000000 : ℝ), (5577244662327/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305700019/10000000000 : ℝ)|^2137 ≤ (43452569794333/100000000000000 : ℝ)^1625
        have hw : |(5305700019/10000000000 : ℝ)|=(5305700019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1985417809/10000000000 : ℝ)|^2137 ≤ (11929472885093/100000000000000 : ℝ)^1625
        have hw : |(-1985417809/10000000000 : ℝ)|=(1985417809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338347559/625000000 : ℝ)|^2137 ≤ (5577244662327/12500000000000 : ℝ)^1625
        have hw : |(338347559/625000000 : ℝ)|=(338347559/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s6_6 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305700089/10000000000 : ℝ)*x 0 + (5413560827/10000000000 : ℝ)*x 1 + (-15883343/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305700089/10000000000 : ℝ)^2137 ≤ (5431571318531/12500000000000 : ℝ)^1625 := by
    have hnat : (5305700089 : ℕ)^2137*12500000000000^1625 ≤ 5431571318531^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305700089 10000000000 5431571318531 12500000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413560827/10000000000 : ℝ)^2137 ≤ (22308978015243/50000000000000 : ℝ)^1625 := by
    have hnat : (5413560827 : ℕ)^2137*50000000000000^1625 ≤ 22308978015243^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413560827 10000000000 22308978015243 50000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (15883343/80000000 : ℝ)^2137 ≤ (5964736703303/50000000000000 : ℝ)^1625 := by
    have hnat : (15883343 : ℕ)^2137*50000000000000^1625 ≤ 5964736703303^1625*80000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15883343 80000000 5964736703303 50000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305700089/10000000000 : ℝ), (5413560827/10000000000 : ℝ), (-15883343/80000000 : ℝ)] ![(5431571318531/12500000000000 : ℝ), (22308978015243/50000000000000 : ℝ), (5964736703303/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305700089/10000000000 : ℝ)|^2137 ≤ (5431571318531/12500000000000 : ℝ)^1625
        have hw : |(5305700089/10000000000 : ℝ)|=(5305700089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413560827/10000000000 : ℝ)|^2137 ≤ (22308978015243/50000000000000 : ℝ)^1625
        have hw : |(5413560827/10000000000 : ℝ)|=(5413560827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-15883343/80000000 : ℝ)|^2137 ≤ (5964736703303/50000000000000 : ℝ)^1625
        have hw : |(-15883343/80000000 : ℝ)|=(15883343/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s6_7 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4334017589/10000000000 : ℝ)*x 0 + (2256401797/5000000000 : ℝ)*x 1 + (1040500401/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4334017589/10000000000 : ℝ)^2137 ≤ (16651497758793/50000000000000 : ℝ)^1625 := by
    have hnat : (4334017589 : ℕ)^2137*50000000000000^1625 ≤ 16651497758793^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4334017589 10000000000 16651497758793 50000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2256401797/5000000000 : ℝ)^2137 ≤ (17560645756551/50000000000000 : ℝ)^1625 := by
    have hnat : (2256401797 : ℕ)^2137*50000000000000^1625 ≤ 17560645756551^1625*5000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2256401797 5000000000 17560645756551 50000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1040500401/2500000000 : ℝ)^2137 ≤ (157878564797/500000000000 : ℝ)^1625 := by
    have hnat : (1040500401 : ℕ)^2137*500000000000^1625 ≤ 157878564797^1625*2500000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040500401 2500000000 157878564797 500000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4334017589/10000000000 : ℝ), (2256401797/5000000000 : ℝ), (1040500401/2500000000 : ℝ)] ![(16651497758793/50000000000000 : ℝ), (17560645756551/50000000000000 : ℝ), (157878564797/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4334017589/10000000000 : ℝ)|^2137 ≤ (16651497758793/50000000000000 : ℝ)^1625
        have hw : |(4334017589/10000000000 : ℝ)|=(4334017589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2256401797/5000000000 : ℝ)|^2137 ≤ (17560645756551/50000000000000 : ℝ)^1625
        have hw : |(2256401797/5000000000 : ℝ)|=(2256401797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1040500401/2500000000 : ℝ)|^2137 ≤ (157878564797/500000000000 : ℝ)^1625
        have hw : |(1040500401/2500000000 : ℝ)|=(1040500401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1314_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76813193/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14699/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (346/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (11081/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14689/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14699/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (346/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14699/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (346/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14699/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (346/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14699/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (346/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14699/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (346/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14699/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (346/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (346/3125 : ℝ) ^ (4273/1024 : ℝ) ≤ (10273000103340657/100000000000000000000 : ℝ) := by
    have hpowers : (346/3125 : ℝ)^4273 ≤ (10273000103340657/100000000000000000000 : ℝ)^1024 := by
      have hnat : (346 : ℕ)^4273*100000000000000000000^1024 ≤ 10273000103340657^1024*3125^4273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        346 3125 10273000103340657 100000000000000000000 4273 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (346/3125 : ℝ)) (X := (10273000103340657/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14699/100000 : ℝ) ^ (4273/1024 : ℝ) ≤ (4189146668835931/12500000000000000000 : ℝ) := by
    have hpowers : (14699/100000 : ℝ)^4273 ≤ (4189146668835931/12500000000000000000 : ℝ)^1024 := by
      have hnat : (14699 : ℕ)^4273*12500000000000000000^1024 ≤ 4189146668835931^1024*100000^4273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14699 100000 4189146668835931 12500000000000000000 4273 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14699/100000 : ℝ)) (X := (4189146668835931/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010273000103340657/50000000000000000000 : ℝ) ≤ (2500123083670823/2500000000000000 : ℝ) ^ (4273/1024 : ℝ) := by
    have hpowers : (50010273000103340657/50000000000000000000 : ℝ)^1024 ≤ (2500123083670823/2500000000000000 : ℝ)^4273 := by
      have hnat : (50010273000103340657 : ℕ)^1024*2500000000000000^4273 ≤ 2500123083670823^4273*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010273000103340657 50000000000000000000 2500123083670823 2500000000000000 1024 4273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500123083670823/2500000000000000 : ℝ)) (X := (50010273000103340657/50000000000000000000 : ℝ)) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008757234690805621/20000000000000000000 : ℝ) ≤ (1000104913596351/1000000000000000 : ℝ) ^ (4273/1024 : ℝ) := by
    have hpowers : (20008757234690805621/20000000000000000000 : ℝ)^1024 ≤ (1000104913596351/1000000000000000 : ℝ)^4273 := by
      have hnat : (20008757234690805621 : ℕ)^1024*1000000000000000^4273 ≤ 1000104913596351^4273*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008757234690805621 20000000000000000000 1000104913596351 1000000000000000 1024 4273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000104913596351/1000000000000000 : ℝ)) (X := (20008757234690805621/20000000000000000000 : ℝ)) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254189146668835931/6250000000000000000 : ℝ) ≤ (625100371077733/625000000000000 : ℝ) ^ (4273/1024 : ℝ) := by
    have hpowers : (6254189146668835931/6250000000000000000 : ℝ)^1024 ≤ (625100371077733/625000000000000 : ℝ)^4273 := by
      have hnat : (6254189146668835931 : ℕ)^1024*625000000000000^4273 ≤ 625100371077733^4273*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254189146668835931 6250000000000000000 625100371077733 625000000000000 1024 4273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625100371077733/625000000000000 : ℝ)) (X := (6254189146668835931/6250000000000000000 : ℝ)) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10273000103340657/100000000000000000000 : ℝ) ≤ ((9064863972586788173/9067500000000000000 : ℝ)+2*(278400640109/181350000000000 : ℝ)*(346/3125 : ℝ))^(4273/1024 : ℝ) := by
    rw [show (9064863972586788173/9067500000000000000 : ℝ)+2*(278400640109/181350000000000 : ℝ)*(346/3125 : ℝ)=(2500123083670823/2500000000000000 : ℝ) by norm_num, show 1+2*(10273000103340657/100000000000000000000 : ℝ)=(50010273000103340657/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4189146668835931/12500000000000000000 : ℝ)+(10273000103340657/100000000000000000000 : ℝ) ≤ ((9064863972586788173/9067500000000000000 : ℝ)+(278400640109/181350000000000 : ℝ)*((14699/100000 : ℝ)+(346/3125 : ℝ)))^(4273/1024 : ℝ) := by
    rw [show (9064863972586788173/9067500000000000000 : ℝ)+(278400640109/181350000000000 : ℝ)*((14699/100000 : ℝ)+(346/3125 : ℝ))=(1000104913596351/1000000000000000 : ℝ) by norm_num, show 1+(4189146668835931/12500000000000000000 : ℝ)+(10273000103340657/100000000000000000000 : ℝ)=(20008757234690805621/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4189146668835931/12500000000000000000 : ℝ) ≤ ((9064863972586788173/9067500000000000000 : ℝ)+2*(278400640109/181350000000000 : ℝ)*(14699/100000 : ℝ))^(4273/1024 : ℝ) := by
    rw [show (9064863972586788173/9067500000000000000 : ℝ)+2*(278400640109/181350000000000 : ℝ)*(14699/100000 : ℝ)=(625100371077733/625000000000000 : ℝ) by norm_num, show 1+2*(4189146668835931/12500000000000000000 : ℝ)=(6254189146668835931/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9064863972586788173/9067500000000000000 : ℝ)*(X 1 0+X 2 0)+(278400640109/181350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4273/1024 : ℝ)) (lo := (346/3125 : ℝ)) (hi := (14699/100000 : ℝ)) (c := (9064863972586788173/9067500000000000000 : ℝ)) (alpha := (278400640109/181350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9064863972586788173/9067500000000000000 : ℝ)*(X 0 1+X 2 1)+(278400640109/181350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4273/1024 : ℝ)) (lo := (346/3125 : ℝ)) (hi := (14699/100000 : ℝ)) (c := (9064863972586788173/9067500000000000000 : ℝ)) (alpha := (278400640109/181350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9064863972586788173/9067500000000000000 : ℝ)*(X 0 2+X 1 2)+(278400640109/181350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4273/1024 : ℝ)) (lo := (346/3125 : ℝ)) (hi := (14699/100000 : ℝ)) (c := (9064863972586788173/9067500000000000000 : ℝ)) (alpha := (278400640109/181350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-517100827/2500000000 : ℝ)*X 0 0+(2707086933/5000000000 : ℝ)*X 0 1+(2621844089/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267473339/500000000 : ℝ)*X 1 0+(-2155289651/10000000000 : ℝ)*X 1 1+(5243689933/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674734163/5000000000 : ℝ)*X 2 0+(5243687419/10000000000 : ℝ)*X 2 1+(-1077645459/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((34671927/80000000 : ℝ)*X 0 0+(832146781/2000000000 : ℝ)*X 0 1+(112851641/250000000 : ℝ)*X 0 2+(34671927/80000000 : ℝ)*X 1 0+(832146781/2000000000 : ℝ)*X 1 1+(112851641/250000000 : ℝ)*X 1 2+(34671927/80000000 : ℝ)*X 2 0+(832146781/2000000000 : ℝ)*X 2 1+(112851641/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1034207989/5000000000 : ℝ)*X 0 0+(5244297923/10000000000 : ℝ)*X 0 1+(2706780429/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305700019/10000000000 : ℝ)*X 1 0+(-1985417809/10000000000 : ℝ)*X 1 1+(338347559/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305700089/10000000000 : ℝ)*X 2 0+(5413560827/10000000000 : ℝ)*X 2 1+(-15883343/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4334017589/10000000000 : ℝ)*X 0 0+(2256401797/5000000000 : ℝ)*X 0 1+(1040500401/2500000000 : ℝ)*X 0 2+(4334017589/10000000000 : ℝ)*X 1 0+(2256401797/5000000000 : ℝ)*X 1 1+(1040500401/2500000000 : ℝ)*X 1 2+(4334017589/10000000000 : ℝ)*X 2 0+(2256401797/5000000000 : ℝ)*X 2 1+(1040500401/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (221605606622853182153366889/25187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (162999813/20000000000000 : ℝ)*(base23) + (52294963/50000000000000 : ℝ)*(lower2) + (32872459/50000000000000 : ℝ)*(upper3) + (164959459/100000000000000 : ℝ)*(upper4) + (2173976744645079/50000000000000 : ℝ)*(major0) + (2173976744645079/50000000000000 : ℝ)*(major1) + (2173976744645079/50000000000000 : ℝ)*(major2) + (5865637254091551/100000000000000 : ℝ)*(sp0) + (5865693983895061/100000000000000 : ℝ)*(sp1) + (5865647175326613/100000000000000 : ℝ)*(sp2) + (1415101550870579/50000000000000 : ℝ)*(sp3) + (56729803509/100000000000000 : ℝ)*(sp4) + (45993569383/100000000000000 : ℝ)*(sp6) + (1919933899/20000000000000 : ℝ)*(sp7) + (2830212701410653/100000000000000 : ℝ)*(f.failure) + (5865693983895061/100000000000000 : ℝ)*(f.sum) + (41387706206709/2015000000000000000000000000 : ℝ)*base66 + (110474602102113963/50375000000000000000000000000000 : ℝ)*base67 + (220036655161988963/50375000000000000000000000000000 : ℝ)*base69 + (4308022908519886037/50375000000000000000000000000000 : ℝ)*base72 + (8245673015081/2015000000000000000000000000 : ℝ)*base73 + (234964757780386037/50375000000000000000000000000000 : ℝ)*base76 + (274676061274261037/50375000000000000000000000000000 : ℝ)*base78 + (497900425003511037/50375000000000000000000000000000 : ℝ)*base80 + (13104752962101/2015000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (38854971/5000000000000000000000 : ℝ)*base90 + (38854971/5000000000000000000000 : ℝ)*base92 + (38854971/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12431738961837441299806489/6296875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (44160451/12500000000000 : ℝ)*(base19) + (226876887/50000000000000 : ℝ)*(base23) + (12230939/25000000000000 : ℝ)*(upper3) + (2684949/12500000000000 : ℝ)*(lower4) + (41758463/50000000000000 : ℝ)*(upper5) + (1094822469655571/25000000000000 : ℝ)*(major0) + (1094822469655571/25000000000000 : ℝ)*(major1) + (1094822469655571/25000000000000 : ℝ)*(major2) + (120618103/1250000000000 : ℝ)*(sp1) + (1494398501/20000000000000 : ℝ)*(sp2) + (5907969198897943/100000000000000 : ℝ)*(sp4) + (369247449760381/6250000000000 : ℝ)*(sp5) + (369247579571979/6250000000000 : ℝ)*(sp6) + (142530524626879/5000000000000 : ℝ)*(sp7) + (142530524626879/5000000000000 : ℝ)*(f.failure) + (5907969198897943/100000000000000 : ℝ)*(f.sum) + (17814189402751/9067500000000000000000000000 : ℝ)*base65 + (857458959208124761/75562500000000000000000000000000 : ℝ)*base67 + (474866488424062261/75562500000000000000000000000000 : ℝ)*base69 + (719649376294687261/75562500000000000000000000000000 : ℝ)*base71 + (1682119269797/1133437500000000000000000000 : ℝ)*base73 + (23485775483437261/75562500000000000000000000000000 : ℝ)*base75 + (30642414562312261/75562500000000000000000000000000 : ℝ)*base77 + (51345459279750239/75562500000000000000000000000000 : ℝ)*base80 + (2969301274681/9067500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (385353/250000000000000000000 : ℝ)*base90 + (385353/250000000000000000000 : ℝ)*base92 + (385353/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1314_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76813193/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14699/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (346/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11081/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14689/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1314_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1314_s7_0 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2068413989/10000000000 : ℝ)*x 0 + (5414089907/10000000000 : ℝ)*x 1 + (262188251/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2068413989/10000000000 : ℝ)^2137 ≤ (12589562115239/100000000000000 : ℝ)^1625 := by
    have hnat : (2068413989 : ℕ)^2137*100000000000000^1625 ≤ 12589562115239^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068413989 10000000000 12589562115239 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414089907/10000000000 : ℝ)^2137 ≤ (8924738133249/20000000000000 : ℝ)^1625 := by
    have hnat : (5414089907 : ℕ)^2137*20000000000000^1625 ≤ 8924738133249^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414089907 10000000000 8924738133249 20000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262188251/500000000 : ℝ)^2137 ≤ (42786747208223/100000000000000 : ℝ)^1625 := by
    have hnat : (262188251 : ℕ)^2137*100000000000000^1625 ≤ 42786747208223^1625*500000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262188251 500000000 42786747208223 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2068413989/10000000000 : ℝ), (5414089907/10000000000 : ℝ), (262188251/500000000 : ℝ)] ![(12589562115239/100000000000000 : ℝ), (8924738133249/20000000000000 : ℝ), (42786747208223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2068413989/10000000000 : ℝ)|^2137 ≤ (12589562115239/100000000000000 : ℝ)^1625
        have hw : |(-2068413989/10000000000 : ℝ)|=(2068413989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414089907/10000000000 : ℝ)|^2137 ≤ (8924738133249/20000000000000 : ℝ)^1625
        have hw : |(5414089907/10000000000 : ℝ)|=(5414089907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262188251/500000000 : ℝ)|^2137 ≤ (42786747208223/100000000000000 : ℝ)^1625
        have hw : |(262188251/500000000 : ℝ)|=(262188251/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s7_1 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (267472347/500000000 : ℝ)*x 0 + (-2155217473/10000000000 : ℝ)*x 1 + (5243764441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267472347/500000000 : ℝ)^2137 ≤ (5490542990953/12500000000000 : ℝ)^1625 := by
    have hnat : (267472347 : ℕ)^2137*12500000000000^1625 ≤ 5490542990953^1625*500000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267472347 500000000 5490542990953 12500000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2155217473/10000000000 : ℝ)^2137 ≤ (1661114383337/12500000000000 : ℝ)^1625 := by
    have hnat : (2155217473 : ℕ)^2137*12500000000000^1625 ≤ 1661114383337^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155217473 10000000000 1661114383337 12500000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243764441/10000000000 : ℝ)^2137 ≤ (42786740995303/100000000000000 : ℝ)^1625 := by
    have hnat : (5243764441 : ℕ)^2137*100000000000000^1625 ≤ 42786740995303^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243764441 10000000000 42786740995303 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267472347/500000000 : ℝ), (-2155217473/10000000000 : ℝ), (5243764441/10000000000 : ℝ)] ![(5490542990953/12500000000000 : ℝ), (1661114383337/12500000000000 : ℝ), (42786740995303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267472347/500000000 : ℝ)|^2137 ≤ (5490542990953/12500000000000 : ℝ)^1625
        have hw : |(267472347/500000000 : ℝ)|=(267472347/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2155217473/10000000000 : ℝ)|^2137 ≤ (1661114383337/12500000000000 : ℝ)^1625
        have hw : |(-2155217473/10000000000 : ℝ)|=(2155217473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243764441/10000000000 : ℝ)|^2137 ≤ (42786740995303/100000000000000 : ℝ)^1625
        have hw : |(5243764441/10000000000 : ℝ)|=(5243764441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s7_2 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349446149/10000000000 : ℝ)*x 0 + (5243765027/10000000000 : ℝ)*x 1 + (-2155217749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349446149/10000000000 : ℝ)^2137 ≤ (43924335386323/100000000000000 : ℝ)^1625 := by
    have hnat : (5349446149 : ℕ)^2137*100000000000000^1625 ≤ 43924335386323^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349446149 10000000000 43924335386323 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243765027/10000000000 : ℝ)^2137 ≤ (5348343410417/12500000000000 : ℝ)^1625 := by
    have hnat : (5243765027 : ℕ)^2137*12500000000000^1625 ≤ 5348343410417^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243765027 10000000000 5348343410417 12500000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2155217749/10000000000 : ℝ)^2137 ≤ (830557331543/6250000000000 : ℝ)^1625 := by
    have hnat : (2155217749 : ℕ)^2137*6250000000000^1625 ≤ 830557331543^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155217749 10000000000 830557331543 6250000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349446149/10000000000 : ℝ), (5243765027/10000000000 : ℝ), (-2155217749/10000000000 : ℝ)] ![(43924335386323/100000000000000 : ℝ), (5348343410417/12500000000000 : ℝ), (830557331543/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349446149/10000000000 : ℝ)|^2137 ≤ (43924335386323/100000000000000 : ℝ)^1625
        have hw : |(5349446149/10000000000 : ℝ)|=(5349446149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243765027/10000000000 : ℝ)|^2137 ≤ (5348343410417/12500000000000 : ℝ)^1625
        have hw : |(5243765027/10000000000 : ℝ)|=(5243765027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2155217749/10000000000 : ℝ)|^2137 ≤ (830557331543/6250000000000 : ℝ)^1625
        have hw : |(-2155217749/10000000000 : ℝ)|=(2155217749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s7_3 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (173359919/400000000 : ℝ)*x 0 + (2080448633/5000000000 : ℝ)*x 1 + (4513899409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (173359919/400000000 : ℝ)^2137 ≤ (1040712416089/3125000000000 : ℝ)^1625 := by
    have hnat : (173359919 : ℕ)^2137*3125000000000^1625 ≤ 1040712416089^1625*400000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173359919 400000000 1040712416089 3125000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2080448633/5000000000 : ℝ)^2137 ≤ (31564695386317/100000000000000 : ℝ)^1625 := by
    have hnat : (2080448633 : ℕ)^2137*100000000000000^1625 ≤ 31564695386317^1625*5000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080448633 5000000000 31564695386317 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4513899409/10000000000 : ℝ)^2137 ≤ (8783126820521/25000000000000 : ℝ)^1625 := by
    have hnat : (4513899409 : ℕ)^2137*25000000000000^1625 ≤ 8783126820521^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4513899409 10000000000 8783126820521 25000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(173359919/400000000 : ℝ), (2080448633/5000000000 : ℝ), (4513899409/10000000000 : ℝ)] ![(1040712416089/3125000000000 : ℝ), (31564695386317/100000000000000 : ℝ), (8783126820521/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(173359919/400000000 : ℝ)|^2137 ≤ (1040712416089/3125000000000 : ℝ)^1625
        have hw : |(173359919/400000000 : ℝ)|=(173359919/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2080448633/5000000000 : ℝ)|^2137 ≤ (31564695386317/100000000000000 : ℝ)^1625
        have hw : |(2080448633/5000000000 : ℝ)|=(2080448633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4513899409/10000000000 : ℝ)|^2137 ≤ (8783126820521/25000000000000 : ℝ)^1625
        have hw : |(4513899409/10000000000 : ℝ)|=(4513899409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s7_4 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2068426699/10000000000 : ℝ)*x 0 + (327773317/625000000 : ℝ)*x 1 + (270673927/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2068426699/10000000000 : ℝ)^2137 ≤ (2517932770043/20000000000000 : ℝ)^1625 := by
    have hnat : (2068426699 : ℕ)^2137*20000000000000^1625 ≤ 2517932770043^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068426699 10000000000 2517932770043 20000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327773317/625000000 : ℝ)^2137 ≤ (42793271988037/100000000000000 : ℝ)^1625 := by
    have hnat : (327773317 : ℕ)^2137*100000000000000^1625 ≤ 42793271988037^1625*625000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327773317 625000000 42793271988037 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270673927/500000000 : ℝ)^2137 ≤ (2230853207363/5000000000000 : ℝ)^1625 := by
    have hnat : (270673927 : ℕ)^2137*5000000000000^1625 ≤ 2230853207363^1625*500000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270673927 500000000 2230853207363 5000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2068426699/10000000000 : ℝ), (327773317/625000000 : ℝ), (270673927/500000000 : ℝ)] ![(2517932770043/20000000000000 : ℝ), (42793271988037/100000000000000 : ℝ), (2230853207363/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2068426699/10000000000 : ℝ)|^2137 ≤ (2517932770043/20000000000000 : ℝ)^1625
        have hw : |(-2068426699/10000000000 : ℝ)|=(2068426699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327773317/625000000 : ℝ)|^2137 ≤ (42793271988037/100000000000000 : ℝ)^1625
        have hw : |(327773317/625000000 : ℝ)|=(327773317/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270673927/500000000 : ℝ)|^2137 ≤ (2230853207363/5000000000000 : ℝ)^1625
        have hw : |(270673927/500000000 : ℝ)|=(270673927/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s7_5 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1061143903/2000000000 : ℝ)*x 0 + (-496376067/2500000000 : ℝ)*x 1 + (270673927/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061143903/2000000000 : ℝ)^2137 ≤ (43452779770353/100000000000000 : ℝ)^1625 := by
    have hnat : (1061143903 : ℕ)^2137*100000000000000^1625 ≤ 43452779770353^1625*2000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061143903 2000000000 43452779770353 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (496376067/2500000000 : ℝ)^2137 ≤ (11930156062799/100000000000000 : ℝ)^1625 := by
    have hnat : (496376067 : ℕ)^2137*100000000000000^1625 ≤ 11930156062799^1625*2500000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      496376067 2500000000 11930156062799 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270673927/500000000 : ℝ)^2137 ≤ (2230853207363/5000000000000 : ℝ)^1625 := by
    have hnat : (270673927 : ℕ)^2137*5000000000000^1625 ≤ 2230853207363^1625*500000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270673927 500000000 2230853207363 5000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061143903/2000000000 : ℝ), (-496376067/2500000000 : ℝ), (270673927/500000000 : ℝ)] ![(43452779770353/100000000000000 : ℝ), (11930156062799/100000000000000 : ℝ), (2230853207363/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061143903/2000000000 : ℝ)|^2137 ≤ (43452779770353/100000000000000 : ℝ)^1625
        have hw : |(1061143903/2000000000 : ℝ)|=(1061143903/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-496376067/2500000000 : ℝ)|^2137 ≤ (11930156062799/100000000000000 : ℝ)^1625
        have hw : |(-496376067/2500000000 : ℝ)|=(496376067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270673927/500000000 : ℝ)|^2137 ≤ (2230853207363/5000000000000 : ℝ)^1625
        have hw : |(270673927/500000000 : ℝ)|=(270673927/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s7_6 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1326429879/2500000000 : ℝ)*x 0 + (5413478539/10000000000 : ℝ)*x 1 + (-496376067/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326429879/2500000000 : ℝ)^2137 ≤ (43452779781123/100000000000000 : ℝ)^1625 := by
    have hnat : (1326429879 : ℕ)^2137*100000000000000^1625 ≤ 43452779781123^1625*2500000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326429879 2500000000 43452779781123 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413478539/10000000000 : ℝ)^2137 ≤ (44617064136421/100000000000000 : ℝ)^1625 := by
    have hnat : (5413478539 : ℕ)^2137*100000000000000^1625 ≤ 44617064136421^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413478539 10000000000 44617064136421 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (496376067/2500000000 : ℝ)^2137 ≤ (11930156062799/100000000000000 : ℝ)^1625 := by
    have hnat : (496376067 : ℕ)^2137*100000000000000^1625 ≤ 11930156062799^1625*2500000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      496376067 2500000000 11930156062799 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326429879/2500000000 : ℝ), (5413478539/10000000000 : ℝ), (-496376067/2500000000 : ℝ)] ![(43452779781123/100000000000000 : ℝ), (44617064136421/100000000000000 : ℝ), (11930156062799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326429879/2500000000 : ℝ)|^2137 ≤ (43452779781123/100000000000000 : ℝ)^1625
        have hw : |(1326429879/2500000000 : ℝ)|=(1326429879/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413478539/10000000000 : ℝ)|^2137 ≤ (44617064136421/100000000000000 : ℝ)^1625
        have hw : |(5413478539/10000000000 : ℝ)|=(5413478539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-496376067/2500000000 : ℝ)|^2137 ≤ (11930156062799/100000000000000 : ℝ)^1625
        have hw : |(-496376067/2500000000 : ℝ)|=(496376067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s7_7 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4334023083/10000000000 : ℝ)*x 0 + (2256319907/5000000000 : ℝ)*x 1 + (2081082023/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4334023083/10000000000 : ℝ)^2137 ≤ (33303051035421/100000000000000 : ℝ)^1625 := by
    have hnat : (4334023083 : ℕ)^2137*100000000000000^1625 ≤ 33303051035421^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4334023083 10000000000 33303051035421 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2256319907/5000000000 : ℝ)^2137 ≤ (4389951910399/12500000000000 : ℝ)^1625 := by
    have hnat : (2256319907 : ℕ)^2137*12500000000000^1625 ≤ 4389951910399^1625*5000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2256319907 5000000000 4389951910399 12500000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2081082023/5000000000 : ℝ)^2137 ≤ (31577333661061/100000000000000 : ℝ)^1625 := by
    have hnat : (2081082023 : ℕ)^2137*100000000000000^1625 ≤ 31577333661061^1625*5000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081082023 5000000000 31577333661061 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4334023083/10000000000 : ℝ), (2256319907/5000000000 : ℝ), (2081082023/5000000000 : ℝ)] ![(33303051035421/100000000000000 : ℝ), (4389951910399/12500000000000 : ℝ), (31577333661061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4334023083/10000000000 : ℝ)|^2137 ≤ (33303051035421/100000000000000 : ℝ)^1625
        have hw : |(4334023083/10000000000 : ℝ)|=(4334023083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2256319907/5000000000 : ℝ)|^2137 ≤ (4389951910399/12500000000000 : ℝ)^1625
        have hw : |(2256319907/5000000000 : ℝ)|=(2256319907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2081082023/5000000000 : ℝ)|^2137 ≤ (31577333661061/100000000000000 : ℝ)^1625
        have hw : |(2081082023/5000000000 : ℝ)|=(2081082023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1314_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76813193/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14689/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11081/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11083/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (459/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14689/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11081/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14689/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11081/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14689/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11081/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14689/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11081/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14689/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11081/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14689/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11081/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11081/100000 : ℝ) ^ (4273/1024 : ℝ) ≤ (10307890561426417/100000000000000000000 : ℝ) := by
    have hpowers : (11081/100000 : ℝ)^4273 ≤ (10307890561426417/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11081 : ℕ)^4273*100000000000000000000^1024 ≤ 10307890561426417^1024*100000^4273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11081 100000 10307890561426417 100000000000000000000 4273 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11081/100000 : ℝ)) (X := (10307890561426417/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14689/100000 : ℝ) ^ (4273/1024 : ℝ) ≤ (83545341294879/250000000000000000 : ℝ) := by
    have hpowers : (14689/100000 : ℝ)^4273 ≤ (83545341294879/250000000000000000 : ℝ)^1024 := by
      have hnat : (14689 : ℕ)^4273*250000000000000000^1024 ≤ 83545341294879^1024*100000^4273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14689 100000 83545341294879 250000000000000000 4273 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14689/100000 : ℝ)) (X := (83545341294879/250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010307890561426417/50000000000000000000 : ℝ) ≤ (5000247003340689/5000000000000000 : ℝ) ^ (4273/1024 : ℝ) := by
    have hpowers : (50010307890561426417/50000000000000000000 : ℝ)^1024 ≤ (5000247003340689/5000000000000000 : ℝ)^4273 := by
      have hnat : (50010307890561426417 : ℕ)^1024*5000000000000000^4273 ≤ 5000247003340689^4273*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010307890561426417 50000000000000000000 5000247003340689 5000000000000000 1024 4273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000247003340689/5000000000000000 : ℝ)) (X := (50010307890561426417/50000000000000000000 : ℝ)) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100043726027079378017/100000000000000000000 : ℝ) ≤ (500052384753471/500000000000000 : ℝ) ^ (4273/1024 : ℝ) := by
    have hpowers : (100043726027079378017/100000000000000000000 : ℝ)^1024 ≤ (500052384753471/500000000000000 : ℝ)^4273 := by
      have hnat : (100043726027079378017 : ℕ)^1024*500000000000000^4273 ≤ 500052384753471^4273*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100043726027079378017 100000000000000000000 500052384753471 500000000000000 1024 4273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500052384753471/500000000000000 : ℝ)) (X := (100043726027079378017/100000000000000000000 : ℝ)) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (125083545341294879/125000000000000000 : ℝ) ≤ (5000800691728731/5000000000000000 : ℝ) ^ (4273/1024 : ℝ) := by
    have hpowers : (125083545341294879/125000000000000000 : ℝ)^1024 ≤ (5000800691728731/5000000000000000 : ℝ)^4273 := by
      have hnat : (125083545341294879 : ℕ)^1024*5000000000000000^4273 ≤ 5000800691728731^4273*125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        125083545341294879 125000000000000000 5000800691728731 5000000000000000 1024 4273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000800691728731/5000000000000000 : ℝ)) (X := (125083545341294879/125000000000000000 : ℝ)) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10307890561426417/100000000000000000000 : ℝ) ≤ ((1803475576702531251/1804000000000000000 : ℝ)+2*(276844194021/180400000000000 : ℝ)*(11081/100000 : ℝ))^(4273/1024 : ℝ) := by
    rw [show (1803475576702531251/1804000000000000000 : ℝ)+2*(276844194021/180400000000000 : ℝ)*(11081/100000 : ℝ)=(5000247003340689/5000000000000000 : ℝ) by norm_num, show 1+2*(10307890561426417/100000000000000000000 : ℝ)=(50010307890561426417/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(83545341294879/250000000000000000 : ℝ)+(10307890561426417/100000000000000000000 : ℝ) ≤ ((1803475576702531251/1804000000000000000 : ℝ)+(276844194021/180400000000000 : ℝ)*((14689/100000 : ℝ)+(11081/100000 : ℝ)))^(4273/1024 : ℝ) := by
    rw [show (1803475576702531251/1804000000000000000 : ℝ)+(276844194021/180400000000000 : ℝ)*((14689/100000 : ℝ)+(11081/100000 : ℝ))=(500052384753471/500000000000000 : ℝ) by norm_num, show 1+(83545341294879/250000000000000000 : ℝ)+(10307890561426417/100000000000000000000 : ℝ)=(100043726027079378017/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(83545341294879/250000000000000000 : ℝ) ≤ ((1803475576702531251/1804000000000000000 : ℝ)+2*(276844194021/180400000000000 : ℝ)*(14689/100000 : ℝ))^(4273/1024 : ℝ) := by
    rw [show (1803475576702531251/1804000000000000000 : ℝ)+2*(276844194021/180400000000000 : ℝ)*(14689/100000 : ℝ)=(5000800691728731/5000000000000000 : ℝ) by norm_num, show 1+2*(83545341294879/250000000000000000 : ℝ)=(125083545341294879/125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1803475576702531251/1804000000000000000 : ℝ)*(X 1 0+X 2 0)+(276844194021/180400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4273/1024 : ℝ)) (lo := (11081/100000 : ℝ)) (hi := (14689/100000 : ℝ)) (c := (1803475576702531251/1804000000000000000 : ℝ)) (alpha := (276844194021/180400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1803475576702531251/1804000000000000000 : ℝ)*(X 0 1+X 2 1)+(276844194021/180400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4273/1024 : ℝ)) (lo := (11081/100000 : ℝ)) (hi := (14689/100000 : ℝ)) (c := (1803475576702531251/1804000000000000000 : ℝ)) (alpha := (276844194021/180400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1803475576702531251/1804000000000000000 : ℝ)*(X 0 2+X 1 2)+(276844194021/180400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4273/1024 : ℝ)) (lo := (11081/100000 : ℝ)) (hi := (14689/100000 : ℝ)) (c := (1803475576702531251/1804000000000000000 : ℝ)) (alpha := (276844194021/180400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2068413989/10000000000 : ℝ)*X 0 0+(5414089907/10000000000 : ℝ)*X 0 1+(262188251/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267472347/500000000 : ℝ)*X 1 0+(-2155217473/10000000000 : ℝ)*X 1 1+(5243764441/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349446149/10000000000 : ℝ)*X 2 0+(5243765027/10000000000 : ℝ)*X 2 1+(-2155217749/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((173359919/400000000 : ℝ)*X 0 0+(2080448633/5000000000 : ℝ)*X 0 1+(4513899409/10000000000 : ℝ)*X 0 2+(173359919/400000000 : ℝ)*X 1 0+(2080448633/5000000000 : ℝ)*X 1 1+(4513899409/10000000000 : ℝ)*X 1 2+(173359919/400000000 : ℝ)*X 2 0+(2080448633/5000000000 : ℝ)*X 2 1+(4513899409/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2068426699/10000000000 : ℝ)*X 0 0+(327773317/625000000 : ℝ)*X 0 1+(270673927/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061143903/2000000000 : ℝ)*X 1 0+(-496376067/2500000000 : ℝ)*X 1 1+(270673927/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326429879/2500000000 : ℝ)*X 2 0+(5413478539/10000000000 : ℝ)*X 2 1+(-496376067/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4334023083/10000000000 : ℝ)*X 0 0+(2256319907/5000000000 : ℝ)*X 0 1+(2081082023/5000000000 : ℝ)*X 0 2+(4334023083/10000000000 : ℝ)*X 1 0+(2256319907/5000000000 : ℝ)*X 1 1+(2081082023/5000000000 : ℝ)*X 1 2+(4334023083/10000000000 : ℝ)*X 2 0+(2256319907/5000000000 : ℝ)*X 2 1+(2081082023/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9105392515559483616453/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (643570929/50000000000000 : ℝ)*(base19) + (494692773/50000000000000 : ℝ)*(base23) + (5749013/25000000000000 : ℝ)*(lower2) + (6751489/10000000000000 : ℝ)*(upper3) + (164061279/50000000000000 : ℝ)*(lower4) + (2176007120396351/50000000000000 : ℝ)*(major0) + (2176007120396351/50000000000000 : ℝ)*(major1) + (2176007120396351/50000000000000 : ℝ)*(major2) + (5871160445935959/100000000000000 : ℝ)*(sp0) + (46969369780853/800000000000 : ℝ)*(sp1) + (2935585760181469/50000000000000 : ℝ)*(sp2) + (1416426106703651/50000000000000 : ℝ)*(sp3) + (482552501/4000000000000 : ℝ)*(sp4) + (3752359349/100000000000000 : ℝ)*(sp7) + (56657119315333/2000000000000 : ℝ)*(f.failure) + (1467793127437121/25000000000000 : ℝ)*(f.sum) + (28089206989/10000000000000000000000000 : ℝ)*base66 + (727223584342849/200000000000000000000000000000 : ℝ)*base68 + (843857228542849/200000000000000000000000000000 : ℝ)*base70 + (1107122361542849/200000000000000000000000000000 : ℝ)*base72 + (34113885009/10000000000000000000000000 : ℝ)*base74 + (418048017542849/200000000000000000000000000000 : ℝ)*base76 + (1925587986057151/200000000000000000000000000000 : ℝ)*base77 + (1942178926942849/200000000000000000000000000000 : ℝ)*base80 + (16026537179/10000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (411731/100000000000000000000 : ℝ)*base90 + (411731/100000000000000000000 : ℝ)*base92 + (411731/100000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (843813069506807711055399687/90200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1646934781/100000000000000 : ℝ)*(base19) + (89545127/5000000000000 : ℝ)*(base23) + (113068137/20000000000000 : ℝ)*(lower1) + (47507369/25000000000000 : ℝ)*(upper3) + (64845743/100000000000000 : ℝ)*(lower4) + (24025349/12500000000000 : ℝ)*(upper5) + (4383341355084479/100000000000000 : ℝ)*(major0) + (4383341355084479/100000000000000 : ℝ)*(major1) + (4383341355084479/100000000000000 : ℝ)*(major2) + (1251889459/50000000000000 : ℝ)*(sp2) + (5913434678845541/100000000000000 : ℝ)*(sp4) + (147835825797769/2500000000000 : ℝ)*(sp5) + (1478357596041021/25000000000000 : ℝ)*(sp6) + (1426623859746489/50000000000000 : ℝ)*(sp7) + (1426623859746489/50000000000000 : ℝ)*(f.failure) + (5913434678845541/100000000000000 : ℝ)*(f.sum) + (23932775324759/9020000000000000000000000000 : ℝ)*base65 + (12809819008105543229/180400000000000000000000000000000 : ℝ)*base67 + (1409536491448056771/180400000000000000000000000000000 : ℝ)*base70 + (24817262034893543229/180400000000000000000000000000000 : ℝ)*base71 + (12455622056181/9020000000000000000000000000 : ℝ)*base74 + (20581889298352056771/180400000000000000000000000000000 : ℝ)*base76 + (726849163276856771/180400000000000000000000000000000 : ℝ)*base78 + (985228660538456771/180400000000000000000000000000000 : ℝ)*base80 + (31397987203821/9020000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (15629377/2500000000000000000000 : ℝ)*base89 + (15629377/2500000000000000000000 : ℝ)*base91 + (15629377/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1314_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76813193/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14689/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11081/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11083/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (459/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1314_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1314_s8_0 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1337360951/2500000000 : ℝ)*x 0 + (-1077601899/5000000000 : ℝ)*x 1 + (5243777931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337360951/2500000000 : ℝ)^2137 ≤ (43924310064769/100000000000000 : ℝ)^1625 := by
    have hnat : (1337360951 : ℕ)^2137*100000000000000^1625 ≤ 43924310064769^1625*2500000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337360951 2500000000 43924310064769 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1077601899/5000000000 : ℝ)^2137 ≤ (2657760836151/20000000000000 : ℝ)^1625 := by
    have hnat : (1077601899 : ℕ)^2137*20000000000000^1625 ≤ 2657760836151^1625*5000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077601899 5000000000 2657760836151 20000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243777931/10000000000 : ℝ)^2137 ≤ (10696721437221/25000000000000 : ℝ)^1625 := by
    have hnat : (5243777931 : ℕ)^2137*25000000000000^1625 ≤ 10696721437221^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243777931 10000000000 10696721437221 25000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337360951/2500000000 : ℝ), (-1077601899/5000000000 : ℝ), (5243777931/10000000000 : ℝ)] ![(43924310064769/100000000000000 : ℝ), (2657760836151/20000000000000 : ℝ), (10696721437221/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337360951/2500000000 : ℝ)|^2137 ≤ (43924310064769/100000000000000 : ℝ)^1625
        have hw : |(1337360951/2500000000 : ℝ)|=(1337360951/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1077601899/5000000000 : ℝ)|^2137 ≤ (2657760836151/20000000000000 : ℝ)^1625
        have hw : |(-1077601899/5000000000 : ℝ)|=(1077601899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243777931/10000000000 : ℝ)|^2137 ≤ (10696721437221/25000000000000 : ℝ)^1625
        have hw : |(5243777931/10000000000 : ℝ)|=(5243777931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s8_1 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2068425207/10000000000 : ℝ)*x 0 + (5244385653/10000000000 : ℝ)*x 1 + (2706733593/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2068425207/10000000000 : ℝ)^2137 ≤ (12589651907751/100000000000000 : ℝ)^1625 := by
    have hnat : (2068425207 : ℕ)^2137*100000000000000^1625 ≤ 12589651907751^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068425207 10000000000 12589651907751 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244385653/10000000000 : ℝ)^2137 ≤ (8558681398517/20000000000000 : ℝ)^1625 := by
    have hnat : (5244385653 : ℕ)^2137*20000000000000^1625 ≤ 8558681398517^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244385653 10000000000 8558681398517 20000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706733593/5000000000 : ℝ)^2137 ≤ (44616941085117/100000000000000 : ℝ)^1625 := by
    have hnat : (2706733593 : ℕ)^2137*100000000000000^1625 ≤ 44616941085117^1625*5000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706733593 5000000000 44616941085117 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2068425207/10000000000 : ℝ), (5244385653/10000000000 : ℝ), (2706733593/5000000000 : ℝ)] ![(12589651907751/100000000000000 : ℝ), (8558681398517/20000000000000 : ℝ), (44616941085117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2068425207/10000000000 : ℝ)|^2137 ≤ (12589651907751/100000000000000 : ℝ)^1625
        have hw : |(-2068425207/10000000000 : ℝ)|=(2068425207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244385653/10000000000 : ℝ)|^2137 ≤ (8558681398517/20000000000000 : ℝ)^1625
        have hw : |(5244385653/10000000000 : ℝ)|=(5244385653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706733593/5000000000 : ℝ)|^2137 ≤ (44616941085117/100000000000000 : ℝ)^1625
        have hw : |(2706733593/5000000000 : ℝ)|=(2706733593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s8_2 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1326430903/2500000000 : ℝ)*x 0 + (-992757087/5000000000 : ℝ)*x 1 + (5413467247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326430903/2500000000 : ℝ)^2137 ≤ (8690564779187/20000000000000 : ℝ)^1625 := by
    have hnat : (1326430903 : ℕ)^2137*20000000000000^1625 ≤ 8690564779187^1625*2500000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326430903 2500000000 8690564779187 20000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (992757087/5000000000 : ℝ)^2137 ≤ (1491279292271/12500000000000 : ℝ)^1625 := by
    have hnat : (992757087 : ℕ)^2137*12500000000000^1625 ≤ 1491279292271^1625*5000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      992757087 5000000000 1491279292271 12500000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413467247/10000000000 : ℝ)^2137 ≤ (1784677669851/4000000000000 : ℝ)^1625 := by
    have hnat : (5413467247 : ℕ)^2137*4000000000000^1625 ≤ 1784677669851^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413467247 10000000000 1784677669851 4000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326430903/2500000000 : ℝ), (-992757087/5000000000 : ℝ), (5413467247/10000000000 : ℝ)] ![(8690564779187/20000000000000 : ℝ), (1491279292271/12500000000000 : ℝ), (1784677669851/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326430903/2500000000 : ℝ)|^2137 ≤ (8690564779187/20000000000000 : ℝ)^1625
        have hw : |(1326430903/2500000000 : ℝ)|=(1326430903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-992757087/5000000000 : ℝ)|^2137 ≤ (1491279292271/12500000000000 : ℝ)^1625
        have hw : |(-992757087/5000000000 : ℝ)|=(992757087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413467247/10000000000 : ℝ)|^2137 ≤ (1784677669851/4000000000000 : ℝ)^1625
        have hw : |(5413467247/10000000000 : ℝ)|=(5413467247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s8_3 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305723553/10000000000 : ℝ)*x 0 + (338341703/625000000 : ℝ)*x 1 + (-992757127/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305723553/10000000000 : ℝ)^2137 ≤ (10863205815123/25000000000000 : ℝ)^1625 := by
    have hnat : (5305723553 : ℕ)^2137*25000000000000^1625 ≤ 10863205815123^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305723553 10000000000 10863205815123 25000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338341703/625000000 : ℝ)^2137 ≤ (44616941757113/100000000000000 : ℝ)^1625 := by
    have hnat : (338341703 : ℕ)^2137*100000000000000^1625 ≤ 44616941757113^1625*625000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338341703 625000000 44616941757113 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (992757127/5000000000 : ℝ)^2137 ≤ (5965117485157/50000000000000 : ℝ)^1625 := by
    have hnat : (992757127 : ℕ)^2137*50000000000000^1625 ≤ 5965117485157^1625*5000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      992757127 5000000000 5965117485157 50000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305723553/10000000000 : ℝ), (338341703/625000000 : ℝ), (-992757127/5000000000 : ℝ)] ![(10863205815123/25000000000000 : ℝ), (44616941757113/100000000000000 : ℝ), (5965117485157/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305723553/10000000000 : ℝ)|^2137 ≤ (10863205815123/25000000000000 : ℝ)^1625
        have hw : |(5305723553/10000000000 : ℝ)|=(5305723553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338341703/625000000 : ℝ)|^2137 ≤ (44616941757113/100000000000000 : ℝ)^1625
        have hw : |(338341703/625000000 : ℝ)|=(338341703/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-992757127/5000000000 : ℝ)|^2137 ≤ (5965117485157/50000000000000 : ℝ)^1625
        have hw : |(-992757127/5000000000 : ℝ)|=(992757127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s8_4 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (270876499/625000000 : ℝ)*x 0 + (2256307431/5000000000 : ℝ)*x 1 + (416218873/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270876499/625000000 : ℝ)^2137 ≤ (33303060140187/100000000000000 : ℝ)^1625 := by
    have hnat : (270876499 : ℕ)^2137*100000000000000^1625 ≤ 33303060140187^1625*625000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270876499 625000000 33303060140187 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2256307431/5000000000 : ℝ)^2137 ≤ (702387198201/2000000000000 : ℝ)^1625 := by
    have hnat : (2256307431 : ℕ)^2137*2000000000000^1625 ≤ 702387198201^1625*5000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2256307431 5000000000 702387198201 2000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (416218873/1000000000 : ℝ)^2137 ≤ (15788789968891/50000000000000 : ℝ)^1625 := by
    have hnat : (416218873 : ℕ)^2137*50000000000000^1625 ≤ 15788789968891^1625*1000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416218873 1000000000 15788789968891 50000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(270876499/625000000 : ℝ), (2256307431/5000000000 : ℝ), (416218873/1000000000 : ℝ)] ![(33303060140187/100000000000000 : ℝ), (702387198201/2000000000000 : ℝ), (15788789968891/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(270876499/625000000 : ℝ)|^2137 ≤ (33303060140187/100000000000000 : ℝ)^1625
        have hw : |(270876499/625000000 : ℝ)|=(270876499/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2256307431/5000000000 : ℝ)|^2137 ≤ (702387198201/2000000000000 : ℝ)^1625
        have hw : |(2256307431/5000000000 : ℝ)|=(2256307431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(416218873/1000000000 : ℝ)|^2137 ≤ (15788789968891/50000000000000 : ℝ)^1625
        have hw : |(416218873/1000000000 : ℝ)|=(416218873/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1314_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76813193/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (459/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11083/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11083/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14687/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (459/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11083/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (459/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11083/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (459/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11083/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (459/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11083/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (459/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11083/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (459/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11083/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11083/100000 : ℝ) ^ (4273/1024 : ℝ) ≤ (2063131243409/20000000000000000 : ℝ) := by
    have hpowers : (11083/100000 : ℝ)^4273 ≤ (2063131243409/20000000000000000 : ℝ)^1024 := by
      have hnat : (11083 : ℕ)^4273*20000000000000000^1024 ≤ 2063131243409^1024*100000^4273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11083 100000 2063131243409 20000000000000000 4273 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11083/100000 : ℝ)) (X := (2063131243409/20000000000000000 : ℝ)) (by norm_num) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (459/3125 : ℝ) ^ (4273/1024 : ℝ) ≤ (668172882359423/2000000000000000000 : ℝ) := by
    have hpowers : (459/3125 : ℝ)^4273 ≤ (668172882359423/2000000000000000000 : ℝ)^1024 := by
      have hnat : (459 : ℕ)^4273*2000000000000000000^1024 ≤ 668172882359423^1024*3125^4273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        459 3125 668172882359423 2000000000000000000 4273 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (459/3125 : ℝ)) (X := (668172882359423/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002063131243409/10000000000000000 : ℝ) ≤ (1000049437882201/1000000000000000 : ℝ) ^ (4273/1024 : ℝ) := by
    have hpowers : (10002063131243409/10000000000000000 : ℝ)^1024 ≤ (1000049437882201/1000000000000000 : ℝ)^4273 := by
      have hnat : (10002063131243409 : ℕ)^1024*1000000000000000^4273 ≤ 1000049437882201^4273*10000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002063131243409 10000000000000000 1000049437882201 1000000000000000 1024 4273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000049437882201/1000000000000000 : ℝ)) (X := (10002063131243409/10000000000000000 : ℝ)) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2000874486006700323/2000000000000000000 : ℝ) ≤ (2500261913425683/2500000000000000 : ℝ) ^ (4273/1024 : ℝ) := by
    have hpowers : (2000874486006700323/2000000000000000000 : ℝ)^1024 ≤ (2500261913425683/2500000000000000 : ℝ)^4273 := by
      have hnat : (2000874486006700323 : ℕ)^1024*2500000000000000^4273 ≤ 2500261913425683^4273*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000874486006700323 2000000000000000000 2500261913425683 2500000000000000 1024 4273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500261913425683/2500000000000000 : ℝ)) (X := (2000874486006700323/2000000000000000000 : ℝ)) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1000668172882359423/1000000000000000000 : ℝ) ≤ (5000800464291727/5000000000000000 : ℝ) ^ (4273/1024 : ℝ) := by
    have hpowers : (1000668172882359423/1000000000000000000 : ℝ)^1024 ≤ (5000800464291727/5000000000000000 : ℝ)^4273 := by
      have hnat : (1000668172882359423 : ℕ)^1024*5000000000000000^4273 ≤ 5000800464291727^4273*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000668172882359423 1000000000000000000 5000800464291727 5000000000000000 1024 4273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000800464291727/5000000000000000 : ℝ)) (X := (1000668172882359423/1000000000000000000 : ℝ)) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2063131243409/20000000000000000 : ℝ) ≤ ((18019759172323631099/18025000000000000000 : ℝ)+2*(276637440361/180250000000000 : ℝ)*(11083/100000 : ℝ))^(4273/1024 : ℝ) := by
    rw [show (18019759172323631099/18025000000000000000 : ℝ)+2*(276637440361/180250000000000 : ℝ)*(11083/100000 : ℝ)=(1000049437882201/1000000000000000 : ℝ) by norm_num, show 1+2*(2063131243409/20000000000000000 : ℝ)=(10002063131243409/10000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(668172882359423/2000000000000000000 : ℝ)+(2063131243409/20000000000000000 : ℝ) ≤ ((18019759172323631099/18025000000000000000 : ℝ)+(276637440361/180250000000000 : ℝ)*((459/3125 : ℝ)+(11083/100000 : ℝ)))^(4273/1024 : ℝ) := by
    rw [show (18019759172323631099/18025000000000000000 : ℝ)+(276637440361/180250000000000 : ℝ)*((459/3125 : ℝ)+(11083/100000 : ℝ))=(2500261913425683/2500000000000000 : ℝ) by norm_num, show 1+(668172882359423/2000000000000000000 : ℝ)+(2063131243409/20000000000000000 : ℝ)=(2000874486006700323/2000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(668172882359423/2000000000000000000 : ℝ) ≤ ((18019759172323631099/18025000000000000000 : ℝ)+2*(276637440361/180250000000000 : ℝ)*(459/3125 : ℝ))^(4273/1024 : ℝ) := by
    rw [show (18019759172323631099/18025000000000000000 : ℝ)+2*(276637440361/180250000000000 : ℝ)*(459/3125 : ℝ)=(5000800464291727/5000000000000000 : ℝ) by norm_num, show 1+2*(668172882359423/2000000000000000000 : ℝ)=(1000668172882359423/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18019759172323631099/18025000000000000000 : ℝ)*(X 1 0+X 2 0)+(276637440361/180250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4273/1024 : ℝ)) (lo := (11083/100000 : ℝ)) (hi := (459/3125 : ℝ)) (c := (18019759172323631099/18025000000000000000 : ℝ)) (alpha := (276637440361/180250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18019759172323631099/18025000000000000000 : ℝ)*(X 0 1+X 2 1)+(276637440361/180250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4273/1024 : ℝ)) (lo := (11083/100000 : ℝ)) (hi := (459/3125 : ℝ)) (c := (18019759172323631099/18025000000000000000 : ℝ)) (alpha := (276637440361/180250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18019759172323631099/18025000000000000000 : ℝ)*(X 0 2+X 1 2)+(276637440361/180250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4273/1024 : ℝ)) (lo := (11083/100000 : ℝ)) (hi := (459/3125 : ℝ)) (c := (18019759172323631099/18025000000000000000 : ℝ)) (alpha := (276637440361/180250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((1337360951/2500000000 : ℝ)*X 1 0+(-1077601899/5000000000 : ℝ)*X 1 1+(5243777931/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s8_0 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-2068425207/10000000000 : ℝ)*X 0 0+(5244385653/10000000000 : ℝ)*X 0 1+(2706733593/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s8_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1326430903/2500000000 : ℝ)*X 1 0+(-992757087/5000000000 : ℝ)*X 1 1+(5413467247/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s8_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5305723553/10000000000 : ℝ)*X 2 0+(338341703/625000000 : ℝ)*X 2 1+(-992757127/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s8_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((270876499/625000000 : ℝ)*X 0 0+(2256307431/5000000000 : ℝ)*X 0 1+(416218873/1000000000 : ℝ)*X 0 2+(270876499/625000000 : ℝ)*X 1 0+(2256307431/5000000000 : ℝ)*X 1 1+(416218873/1000000000 : ℝ)*X 1 2+(270876499/625000000 : ℝ)*X 2 0+(2256307431/5000000000 : ℝ)*X 2 1+(416218873/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s8_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (828015225235726008348391149/450625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (418857497/100000000000000 : ℝ)*(base19) + (352533083/100000000000000 : ℝ)*(base23) + (129561399/100000000000000 : ℝ)*(lower1) + (6156201/12500000000000 : ℝ)*(upper3) + (6213127/50000000000000 : ℝ)*(lower4) + (57530233/100000000000000 : ℝ)*(upper5) + (2191990595834439/50000000000000 : ℝ)*(major0) + (2191990595834439/50000000000000 : ℝ)*(major1) + (2191990595834439/50000000000000 : ℝ)*(major2) + (181863889/6250000000000 : ℝ)*(sp0) + (1182859622773023/20000000000000 : ℝ)*(sp1) + (2957147392592697/50000000000000 : ℝ)*(sp2) + (5914297761332033/100000000000000 : ℝ)*(sp3) + (71341605205581/2500000000000 : ℝ)*(sp4) + (71341605205581/2500000000000 : ℝ)*(f.failure) + (1182859622773023/20000000000000 : ℝ)*(f.sum) + (73107704678959/18025000000000000000000000000 : ℝ)*base66 + (8548251100905231539/901250000000000000000000000000000 : ℝ)*base68 + (3971625746423981539/901250000000000000000000000000000 : ℝ)*base70 + (8249868323266481539/901250000000000000000000000000000 : ℝ)*base72 + (8329990501923/2253125000000000000000000000 : ℝ)*base74 + (4786096611813981539/901250000000000000000000000000000 : ℝ)*base76 + (8682333158297731539/901250000000000000000000000000000 : ℝ)*base78 + (19377274631116481539/901250000000000000000000000000000 : ℝ)*base80 + (29177593912267/9012500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (530133/125000000000000000000 : ℝ)*base89 + (530133/125000000000000000000 : ℝ)*base91 + (530133/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1314_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76813193/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (459/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11083/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11083/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14687/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1314_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1314_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76813193/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14699/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (346/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11083/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14687/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1314_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1314_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1314_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76813193/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14699/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (346/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11083/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14687/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1314_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
