-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1571_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:27:51.154851+00:00
-- url     : https://prove2.me/submissions/705af59e-fa94-4928-a93c-8cc96a646732

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
theorem support_rectangle_w1571_s6_0 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1784249827/10000000000 : ℝ)*x 0 + (1356414769/2500000000 : ℝ)*x 1 + (5220100021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1784249827/10000000000 : ℝ)^4639 ≤ (5475072471543/50000000000000 : ℝ)^3615 := by
    have hnat : (1784249827 : ℕ)^4639*50000000000000^3615 ≤ 5475072471543^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1784249827 10000000000 5475072471543 50000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356414769/2500000000 : ℝ)^4639 ≤ (45628102391391/100000000000000 : ℝ)^3615 := by
    have hnat : (1356414769 : ℕ)^4639*100000000000000^3615 ≤ 45628102391391^3615*2500000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356414769 2500000000 45628102391391 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5220100021/10000000000 : ℝ)^4639 ≤ (21710876323321/50000000000000 : ℝ)^3615 := by
    have hnat : (5220100021 : ℕ)^4639*50000000000000^3615 ≤ 21710876323321^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220100021 10000000000 21710876323321 50000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1784249827/10000000000 : ℝ), (1356414769/2500000000 : ℝ), (5220100021/10000000000 : ℝ)] ![(5475072471543/50000000000000 : ℝ), (45628102391391/100000000000000 : ℝ), (21710876323321/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1784249827/10000000000 : ℝ)|^4639 ≤ (5475072471543/50000000000000 : ℝ)^3615
        have hw : |(-1784249827/10000000000 : ℝ)|=(1784249827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356414769/2500000000 : ℝ)|^4639 ≤ (45628102391391/100000000000000 : ℝ)^3615
        have hw : |(1356414769/2500000000 : ℝ)|=(1356414769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5220100021/10000000000 : ℝ)|^4639 ≤ (21710876323321/50000000000000 : ℝ)^3615
        have hw : |(5220100021/10000000000 : ℝ)|=(5220100021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s6_1 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337032053/2500000000 : ℝ)*x 0 + (-944704421/5000000000 : ℝ)*x 1 + (1044020009/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337032053/2500000000 : ℝ)^4639 ≤ (11198274996331/25000000000000 : ℝ)^3615 := by
    have hnat : (1337032053 : ℕ)^4639*25000000000000^3615 ≤ 11198274996331^3615*2500000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337032053 2500000000 11198274996331 25000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (944704421/5000000000 : ℝ)^4639 ≤ (11785147090923/100000000000000 : ℝ)^3615 := by
    have hnat : (944704421 : ℕ)^4639*100000000000000^3615 ≤ 11785147090923^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      944704421 5000000000 11785147090923 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1044020009/2000000000 : ℝ)^4639 ≤ (10855438225707/25000000000000 : ℝ)^3615 := by
    have hnat : (1044020009 : ℕ)^4639*25000000000000^3615 ≤ 10855438225707^3615*2000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044020009 2000000000 10855438225707 25000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337032053/2500000000 : ℝ), (-944704421/5000000000 : ℝ), (1044020009/2000000000 : ℝ)] ![(11198274996331/25000000000000 : ℝ), (11785147090923/100000000000000 : ℝ), (10855438225707/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337032053/2500000000 : ℝ)|^4639 ≤ (11198274996331/25000000000000 : ℝ)^3615
        have hw : |(1337032053/2500000000 : ℝ)|=(1337032053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-944704421/5000000000 : ℝ)|^4639 ≤ (11785147090923/100000000000000 : ℝ)^3615
        have hw : |(-944704421/5000000000 : ℝ)|=(944704421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1044020009/2000000000 : ℝ)|^4639 ≤ (10855438225707/25000000000000 : ℝ)^3615
        have hw : |(1044020009/2000000000 : ℝ)|=(1044020009/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s6_2 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348128217/10000000000 : ℝ)*x 0 + (5220100041/10000000000 : ℝ)*x 1 + (-47235221/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348128217/10000000000 : ℝ)^4639 ≤ (5599137504883/12500000000000 : ℝ)^3615 := by
    have hnat : (5348128217 : ℕ)^4639*12500000000000^3615 ≤ 5599137504883^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348128217 10000000000 5599137504883 12500000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5220100041/10000000000 : ℝ)^4639 ≤ (4342175286013/10000000000000 : ℝ)^3615 := by
    have hnat : (5220100041 : ℕ)^4639*10000000000000^3615 ≤ 4342175286013^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220100041 10000000000 4342175286013 10000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (47235221/250000000 : ℝ)^4639 ≤ (5892573537457/50000000000000 : ℝ)^3615 := by
    have hnat : (47235221 : ℕ)^4639*50000000000000^3615 ≤ 5892573537457^3615*250000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47235221 250000000 5892573537457 50000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348128217/10000000000 : ℝ), (5220100041/10000000000 : ℝ), (-47235221/250000000 : ℝ)] ![(5599137504883/12500000000000 : ℝ), (4342175286013/10000000000000 : ℝ), (5892573537457/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348128217/10000000000 : ℝ)|^4639 ≤ (5599137504883/12500000000000 : ℝ)^3615
        have hw : |(5348128217/10000000000 : ℝ)|=(5348128217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5220100041/10000000000 : ℝ)|^4639 ≤ (4342175286013/10000000000000 : ℝ)^3615
        have hw : |(5220100041/10000000000 : ℝ)|=(5220100041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-47235221/250000000 : ℝ)|^4639 ≤ (5892573537457/50000000000000 : ℝ)^3615
        have hw : |(-47235221/250000000 : ℝ)|=(47235221/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s6_3 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4243065871/10000000000 : ℝ)*x 0 + (4005904099/10000000000 : ℝ)*x 1 + (898293877/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4243065871/10000000000 : ℝ)^4639 ≤ (4160301492013/12500000000000 : ℝ)^3615 := by
    have hnat : (4243065871 : ℕ)^4639*12500000000000^3615 ≤ 4160301492013^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4243065871 10000000000 4160301492013 12500000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4005904099/10000000000 : ℝ)^4639 ≤ (3091433051753/10000000000000 : ℝ)^3615 := by
    have hnat : (4005904099 : ℕ)^4639*10000000000000^3615 ≤ 3091433051753^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4005904099 10000000000 3091433051753 10000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (898293877/2000000000 : ℝ)^4639 ≤ (35803257529199/100000000000000 : ℝ)^3615 := by
    have hnat : (898293877 : ℕ)^4639*100000000000000^3615 ≤ 35803257529199^3615*2000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898293877 2000000000 35803257529199 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4243065871/10000000000 : ℝ), (4005904099/10000000000 : ℝ), (898293877/2000000000 : ℝ)] ![(4160301492013/12500000000000 : ℝ), (3091433051753/10000000000000 : ℝ), (35803257529199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4243065871/10000000000 : ℝ)|^4639 ≤ (4160301492013/12500000000000 : ℝ)^3615
        have hw : |(4243065871/10000000000 : ℝ)|=(4243065871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4005904099/10000000000 : ℝ)|^4639 ≤ (3091433051753/10000000000000 : ℝ)^3615
        have hw : |(4005904099/10000000000 : ℝ)|=(4005904099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(898293877/2000000000 : ℝ)|^4639 ≤ (35803257529199/100000000000000 : ℝ)^3615
        have hw : |(898293877/2000000000 : ℝ)|=(898293877/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s6_4 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-892138279/5000000000 : ℝ)*x 0 + (5221171013/10000000000 : ℝ)*x 1 + (5424580169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (892138279/5000000000 : ℝ)^4639 ≤ (10950355464561/100000000000000 : ℝ)^3615 := by
    have hnat : (892138279 : ℕ)^4639*100000000000000^3615 ≤ 10950355464561^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      892138279 5000000000 10950355464561 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5221171013/10000000000 : ℝ)^4639 ≤ (43433185205377/100000000000000 : ℝ)^3615 := by
    have hnat : (5221171013 : ℕ)^4639*100000000000000^3615 ≤ 43433185205377^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221171013 10000000000 43433185205377 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5424580169/10000000000 : ℝ)^4639 ≤ (45616459314761/100000000000000 : ℝ)^3615 := by
    have hnat : (5424580169 : ℕ)^4639*100000000000000^3615 ≤ 45616459314761^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424580169 10000000000 45616459314761 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-892138279/5000000000 : ℝ), (5221171013/10000000000 : ℝ), (5424580169/10000000000 : ℝ)] ![(10950355464561/100000000000000 : ℝ), (43433185205377/100000000000000 : ℝ), (45616459314761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-892138279/5000000000 : ℝ)|^4639 ≤ (10950355464561/100000000000000 : ℝ)^3615
        have hw : |(-892138279/5000000000 : ℝ)|=(892138279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5221171013/10000000000 : ℝ)|^4639 ≤ (43433185205377/100000000000000 : ℝ)^3615
        have hw : |(5221171013/10000000000 : ℝ)|=(5221171013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5424580169/10000000000 : ℝ)|^4639 ≤ (45616459314761/100000000000000 : ℝ)^3615
        have hw : |(5424580169/10000000000 : ℝ)|=(5424580169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s6_5 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323434269/2500000000 : ℝ)*x 0 + (-421232183/2500000000 : ℝ)*x 1 + (542458023/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323434269/2500000000 : ℝ)^4639 ≤ (22104675616591/50000000000000 : ℝ)^3615 := by
    have hnat : (1323434269 : ℕ)^4639*50000000000000^3615 ≤ 22104675616591^3615*2500000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323434269 2500000000 22104675616591 50000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (421232183/2500000000 : ℝ)^4639 ≤ (1271773596897/12500000000000 : ℝ)^3615 := by
    have hnat : (421232183 : ℕ)^4639*12500000000000^3615 ≤ 1271773596897^3615*2500000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421232183 2500000000 1271773596897 12500000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542458023/1000000000 : ℝ)^4639 ≤ (45616459973027/100000000000000 : ℝ)^3615 := by
    have hnat : (542458023 : ℕ)^4639*100000000000000^3615 ≤ 45616459973027^3615*1000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542458023 1000000000 45616459973027 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323434269/2500000000 : ℝ), (-421232183/2500000000 : ℝ), (542458023/1000000000 : ℝ)] ![(22104675616591/50000000000000 : ℝ), (1271773596897/12500000000000 : ℝ), (45616459973027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323434269/2500000000 : ℝ)|^4639 ≤ (22104675616591/50000000000000 : ℝ)^3615
        have hw : |(1323434269/2500000000 : ℝ)|=(1323434269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-421232183/2500000000 : ℝ)|^4639 ≤ (1271773596897/12500000000000 : ℝ)^3615
        have hw : |(-421232183/2500000000 : ℝ)|=(421232183/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(542458023/1000000000 : ℝ)|^4639 ≤ (45616459973027/100000000000000 : ℝ)^3615
        have hw : |(542458023/1000000000 : ℝ)|=(542458023/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s6_6 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (330858569/625000000 : ℝ)*x 0 + (5424580337/10000000000 : ℝ)*x 1 + (-336985709/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330858569/625000000 : ℝ)^4639 ≤ (22104675766627/50000000000000 : ℝ)^3615 := by
    have hnat : (330858569 : ℕ)^4639*50000000000000^3615 ≤ 22104675766627^3615*625000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330858569 625000000 22104675766627 50000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5424580337/10000000000 : ℝ)^4639 ≤ (4561646112769/10000000000000 : ℝ)^3615 := by
    have hnat : (5424580337 : ℕ)^4639*10000000000000^3615 ≤ 4561646112769^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424580337 10000000000 4561646112769 10000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336985709/2000000000 : ℝ)^4639 ≤ (10174187326151/100000000000000 : ℝ)^3615 := by
    have hnat : (336985709 : ℕ)^4639*100000000000000^3615 ≤ 10174187326151^3615*2000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336985709 2000000000 10174187326151 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330858569/625000000 : ℝ), (5424580337/10000000000 : ℝ), (-336985709/2000000000 : ℝ)] ![(22104675766627/50000000000000 : ℝ), (4561646112769/10000000000000 : ℝ), (10174187326151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330858569/625000000 : ℝ)|^4639 ≤ (22104675766627/50000000000000 : ℝ)^3615
        have hw : |(330858569/625000000 : ℝ)|=(330858569/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5424580337/10000000000 : ℝ)|^4639 ≤ (4561646112769/10000000000000 : ℝ)^3615
        have hw : |(5424580337/10000000000 : ℝ)|=(5424580337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-336985709/2000000000 : ℝ)|^4639 ≤ (10174187326151/100000000000000 : ℝ)^3615
        have hw : |(-336985709/2000000000 : ℝ)|=(336985709/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_s6_7 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (848625831/2000000000 : ℝ)*x 0 + (4488939711/10000000000 : ℝ)*x 1 + (4008452337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (848625831/2000000000 : ℝ)^4639 ≤ (33283048945631/100000000000000 : ℝ)^3615 := by
    have hnat : (848625831 : ℕ)^4639*100000000000000^3615 ≤ 33283048945631^3615*2000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848625831 2000000000 33283048945631 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4488939711/10000000000 : ℝ)^4639 ≤ (2236086409123/6250000000000 : ℝ)^3615 := by
    have hnat : (4488939711 : ℕ)^4639*6250000000000^3615 ≤ 2236086409123^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488939711 10000000000 2236086409123 6250000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4008452337/10000000000 : ℝ)^4639 ≤ (30939568490823/100000000000000 : ℝ)^3615 := by
    have hnat : (4008452337 : ℕ)^4639*100000000000000^3615 ≤ 30939568490823^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4008452337 10000000000 30939568490823 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(848625831/2000000000 : ℝ), (4488939711/10000000000 : ℝ), (4008452337/10000000000 : ℝ)] ![(33283048945631/100000000000000 : ℝ), (2236086409123/6250000000000 : ℝ), (30939568490823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(848625831/2000000000 : ℝ)|^4639 ≤ (33283048945631/100000000000000 : ℝ)^3615
        have hw : |(848625831/2000000000 : ℝ)|=(848625831/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4488939711/10000000000 : ℝ)|^4639 ≤ (2236086409123/6250000000000 : ℝ)^3615
        have hw : |(4488939711/10000000000 : ℝ)|=(4488939711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4008452337/10000000000 : ℝ)|^4639 ≤ (30939568490823/100000000000000 : ℝ)^3615
        have hw : |(4008452337/10000000000 : ℝ)|=(4008452337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1571_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168108509/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2781/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (89/800 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3871/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2781/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2781/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2781/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2781/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2781/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2781/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2781/25000 : ℝ) ^ (4637/1024 : ℝ) ≤ (479914888975333/10000000000000000000 : ℝ) := by
    have hpowers : (2781/25000 : ℝ)^4637 ≤ (479914888975333/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2781 : ℕ)^4637*10000000000000000000^1024 ≤ 479914888975333^1024*25000^4637 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2781 25000 479914888975333 10000000000000000000 4637 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2781/25000 : ℝ)) (X := (479914888975333/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4637 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3097/20000 : ℝ) ^ (4637/1024 : ℝ) ≤ (21461421094296539/100000000000000000000 : ℝ) := by
    have hpowers : (3097/20000 : ℝ)^4637 ≤ (21461421094296539/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3097 : ℕ)^4637*100000000000000000000^1024 ≤ 21461421094296539^1024*20000^4637 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3097 20000 21461421094296539 100000000000000000000 4637 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3097/20000 : ℝ)) (X := (21461421094296539/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4637 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000479914888975333/5000000000000000000 : ℝ) ≤ (1000021195362131/1000000000000000 : ℝ) ^ (4637/1024 : ℝ) := by
    have hpowers : (5000479914888975333/5000000000000000000 : ℝ)^1024 ≤ (1000021195362131/1000000000000000 : ℝ)^4637 := by
      have hnat : (5000479914888975333 : ℕ)^1024*1000000000000000^4637 ≤ 1000021195362131^4637*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000479914888975333 5000000000000000000 1000021195362131 1000000000000000 1024 4637 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000021195362131/1000000000000000 : ℝ)) (X := (5000479914888975333/5000000000000000000 : ℝ)) (by norm_num) 4637 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100026260569984049869/100000000000000000000 : ℝ) ≤ (5000289929620171/5000000000000000 : ℝ) ^ (4637/1024 : ℝ) := by
    have hpowers : (100026260569984049869/100000000000000000000 : ℝ)^1024 ≤ (5000289929620171/5000000000000000 : ℝ)^4637 := by
      have hnat : (100026260569984049869 : ℕ)^1024*5000000000000000^4637 ≤ 5000289929620171^4637*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100026260569984049869 100000000000000000000 5000289929620171 5000000000000000 1024 4637 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000289929620171/5000000000000000 : ℝ)) (X := (100026260569984049869/100000000000000000000 : ℝ)) (by norm_num) 4637 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50021461421094296539/50000000000000000000 : ℝ) ≤ (5000473882429687/5000000000000000 : ℝ) ^ (4637/1024 : ℝ) := by
    have hpowers : (50021461421094296539/50000000000000000000 : ℝ)^1024 ≤ (5000473882429687/5000000000000000 : ℝ)^4637 := by
      have hnat : (50021461421094296539 : ℕ)^1024*5000000000000000^4637 ≤ 5000473882429687^4637*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021461421094296539 50000000000000000000 5000473882429687 5000000000000000 1024 4637 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000473882429687/5000000000000000 : ℝ)) (X := (50021461421094296539/50000000000000000000 : ℝ)) (by norm_num) 4637 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(479914888975333/10000000000000000000 : ℝ) ≤ ((3114481368966450641/3115000000000000000 : ℝ)+2*(6569743197/7787500000000 : ℝ)*(2781/25000 : ℝ))^(4637/1024 : ℝ) := by
    rw [show (3114481368966450641/3115000000000000000 : ℝ)+2*(6569743197/7787500000000 : ℝ)*(2781/25000 : ℝ)=(1000021195362131/1000000000000000 : ℝ) by norm_num, show 1+2*(479914888975333/10000000000000000000 : ℝ)=(5000479914888975333/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21461421094296539/100000000000000000000 : ℝ)+(479914888975333/10000000000000000000 : ℝ) ≤ ((3114481368966450641/3115000000000000000 : ℝ)+(6569743197/7787500000000 : ℝ)*((3097/20000 : ℝ)+(2781/25000 : ℝ)))^(4637/1024 : ℝ) := by
    rw [show (3114481368966450641/3115000000000000000 : ℝ)+(6569743197/7787500000000 : ℝ)*((3097/20000 : ℝ)+(2781/25000 : ℝ))=(5000289929620171/5000000000000000 : ℝ) by norm_num, show 1+(21461421094296539/100000000000000000000 : ℝ)+(479914888975333/10000000000000000000 : ℝ)=(100026260569984049869/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21461421094296539/100000000000000000000 : ℝ) ≤ ((3114481368966450641/3115000000000000000 : ℝ)+2*(6569743197/7787500000000 : ℝ)*(3097/20000 : ℝ))^(4637/1024 : ℝ) := by
    rw [show (3114481368966450641/3115000000000000000 : ℝ)+2*(6569743197/7787500000000 : ℝ)*(3097/20000 : ℝ)=(5000473882429687/5000000000000000 : ℝ) by norm_num, show 1+2*(21461421094296539/100000000000000000000 : ℝ)=(50021461421094296539/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3114481368966450641/3115000000000000000 : ℝ)*(X 1 0+X 2 0)+(6569743197/7787500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4637/1024 : ℝ)) (lo := (2781/25000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (3114481368966450641/3115000000000000000 : ℝ)) (alpha := (6569743197/7787500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3114481368966450641/3115000000000000000 : ℝ)*(X 0 1+X 2 1)+(6569743197/7787500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4637/1024 : ℝ)) (lo := (2781/25000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (3114481368966450641/3115000000000000000 : ℝ)) (alpha := (6569743197/7787500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3114481368966450641/3115000000000000000 : ℝ)*(X 0 2+X 1 2)+(6569743197/7787500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4637/1024 : ℝ)) (lo := (2781/25000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (3114481368966450641/3115000000000000000 : ℝ)) (alpha := (6569743197/7787500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1784249827/10000000000 : ℝ)*X 0 0+(1356414769/2500000000 : ℝ)*X 0 1+(5220100021/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337032053/2500000000 : ℝ)*X 1 0+(-944704421/5000000000 : ℝ)*X 1 1+(1044020009/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348128217/10000000000 : ℝ)*X 2 0+(5220100041/10000000000 : ℝ)*X 2 1+(-47235221/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4243065871/10000000000 : ℝ)*X 0 0+(4005904099/10000000000 : ℝ)*X 0 1+(898293877/2000000000 : ℝ)*X 0 2+(4243065871/10000000000 : ℝ)*X 1 0+(4005904099/10000000000 : ℝ)*X 1 1+(898293877/2000000000 : ℝ)*X 1 2+(4243065871/10000000000 : ℝ)*X 2 0+(4005904099/10000000000 : ℝ)*X 2 1+(898293877/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-892138279/5000000000 : ℝ)*X 0 0+(5221171013/10000000000 : ℝ)*X 0 1+(5424580169/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323434269/2500000000 : ℝ)*X 1 0+(-421232183/2500000000 : ℝ)*X 1 1+(542458023/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((330858569/625000000 : ℝ)*X 2 0+(5424580337/10000000000 : ℝ)*X 2 1+(-336985709/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((848625831/2000000000 : ℝ)*X 0 0+(4488939711/10000000000 : ℝ)*X 0 1+(4008452337/10000000000 : ℝ)*X 0 2+(848625831/2000000000 : ℝ)*X 1 0+(4488939711/10000000000 : ℝ)*X 1 1+(4008452337/10000000000 : ℝ)*X 1 2+(848625831/2000000000 : ℝ)*X 2 0+(4488939711/10000000000 : ℝ)*X 2 1+(4008452337/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (501592859209899729252771/139062500000000000000000000000 : ℝ) := by norm_num
    linear_combination (958897/160000000000 : ℝ)*(base19) + (575499979/100000000000000 : ℝ)*(base23) + (15166641/100000000000000 : ℝ)*(lower2) + (4960737/6250000000000 : ℝ)*(upper3) + (61427191/100000000000000 : ℝ)*(upper5) + (43276670930851/1250000000000 : ℝ)*(major0) + (43276670930851/1250000000000 : ℝ)*(major1) + (43276670930851/1250000000000 : ℝ)*(major2) + (2432396428360227/50000000000000 : ℝ)*(sp0) + (608100369520107/12500000000000 : ℝ)*(sp1) + (2432401489985751/50000000000000 : ℝ)*(sp2) + (128716207096593/6250000000000 : ℝ)*(sp3) + (10698751027/100000000000000 : ℝ)*(sp4) + (4359687187/100000000000000 : ℝ)*(sp7) + (1029731836616337/50000000000000 : ℝ)*(f.failure) + (4864803555471481/100000000000000 : ℝ)*(f.sum) + (327520455709/623000000000000000000000000 : ℝ)*base65 + (59171795689649509/3893750000000000000000000000000 : ℝ)*base68 + (34035867284999509/3893750000000000000000000000000 : ℝ)*base70 + (41436104679418259/3893750000000000000000000000000 : ℝ)*base72 + (71043032251/24920000000000000000000000 : ℝ)*base74 + (39423748150805759/3893750000000000000000000000000 : ℝ)*base76 + (12304634265830759/3893750000000000000000000000000 : ℝ)*base78 + (72615788082905759/3893750000000000000000000000000 : ℝ)*base80 + (2701519692621/623000000000000000000000000 : ℝ)*base82 + (18111533/5000000000000000000000 : ℝ)*base89 + (18111533/5000000000000000000000 : ℝ)*base91 + (18111533/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (456775850297118756261/124600000000000000000000000 : ℝ) := by norm_num
    linear_combination (122651399/25000000000000 : ℝ)*(base19) + (677907487/100000000000000 : ℝ)*(base23) + (139715371/100000000000000 : ℝ)*(lower1) + (57373027/50000000000000 : ℝ)*(upper3) + (5595241/12500000000000 : ℝ)*(lower4) + (7148699/12500000000000 : ℝ)*(upper5) + (174935212484509/5000000000000 : ℝ)*(major0) + (174935212484509/5000000000000 : ℝ)*(major1) + (174935212484509/5000000000000 : ℝ)*(major2) + (7469130703/100000000000000 : ℝ)*(sp2) + (2458095277566311/50000000000000 : ℝ)*(sp4) + (2458095032263513/50000000000000 : ℝ)*(sp5) + (153630700252951/3125000000000 : ℝ)*(sp6) + (2081217822049793/100000000000000 : ℝ)*(sp7) + (2081217822049793/100000000000000 : ℝ)*(f.failure) + (2458095277566311/50000000000000 : ℝ)*(f.sum) + (3489603390961/623000000000000000000000000 : ℝ)*base66 + (513970239247854731/15575000000000000000000000000000 : ℝ)*base68 + (48482361768395269/15575000000000000000000000000000 : ℝ)*base69 + (517482635092504731/15575000000000000000000000000000 : ℝ)*base72 + (1123849321943/623000000000000000000000000 : ℝ)*base73 + (1340052898192745269/15575000000000000000000000000000 : ℝ)*base75 + (45563964448270269/15575000000000000000000000000000 : ℝ)*base77 + (203622108947429731/15575000000000000000000000000000 : ℝ)*base80 + (584255633673/623000000000000000000000000 : ℝ)*base81 + (24988637/10000000000000000000000 : ℝ)*base89 + (24988637/10000000000000000000000 : ℝ)*base91 + (24988637/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1571_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168108509/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2781/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (89/800 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1571_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1571_box_0 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-197576103/1250000000 : ℝ)*x 0 + (337280219/625000000 : ℝ)*x 1 + (5396483583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (197576103/1250000000 : ℝ)^4639 ≤ (9373031050389/100000000000000 : ℝ)^3615 := by
    have hnat : (197576103 : ℕ)^4639*100000000000000^3615 ≤ 9373031050389^3615*1250000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197576103 1250000000 9373031050389 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337280219/625000000 : ℝ)^4639 ≤ (45313484044827/100000000000000 : ℝ)^3615 := by
    have hnat : (337280219 : ℕ)^4639*100000000000000^3615 ≤ 45313484044827^3615*625000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337280219 625000000 45313484044827 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396483583/10000000000 : ℝ)^4639 ≤ (22656742448041/50000000000000 : ℝ)^3615 := by
    have hnat : (5396483583 : ℕ)^4639*50000000000000^3615 ≤ 22656742448041^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396483583 10000000000 22656742448041 50000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-197576103/1250000000 : ℝ), (337280219/625000000 : ℝ), (5396483583/10000000000 : ℝ)] ![(9373031050389/100000000000000 : ℝ), (45313484044827/100000000000000 : ℝ), (22656742448041/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-197576103/1250000000 : ℝ)|^4639 ≤ (9373031050389/100000000000000 : ℝ)^3615
        have hw : |(-197576103/1250000000 : ℝ)|=(197576103/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337280219/625000000 : ℝ)|^4639 ≤ (45313484044827/100000000000000 : ℝ)^3615
        have hw : |(337280219/625000000 : ℝ)|=(337280219/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396483583/10000000000 : ℝ)|^4639 ≤ (22656742448041/50000000000000 : ℝ)^3615
        have hw : |(5396483583/10000000000 : ℝ)|=(5396483583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_box_1 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2635571963/5000000000 : ℝ)*x 0 + (-109678039/625000000 : ℝ)*x 1 + (2698242161/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2635571963/5000000000 : ℝ)^4639 ≤ (10991842489027/25000000000000 : ℝ)^3615 := by
    have hnat : (2635571963 : ℕ)^4639*25000000000000^3615 ≤ 10991842489027^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635571963 5000000000 10991842489027 25000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (109678039/625000000 : ℝ)^4639 ≤ (5359568586099/50000000000000 : ℝ)^3615 := by
    have hnat : (109678039 : ℕ)^4639*50000000000000^3615 ≤ 5359568586099^3615*625000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109678039 625000000 5359568586099 50000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698242161/5000000000 : ℝ)^4639 ≤ (45313492859089/100000000000000 : ℝ)^3615 := by
    have hnat : (2698242161 : ℕ)^4639*100000000000000^3615 ≤ 45313492859089^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698242161 5000000000 45313492859089 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2635571963/5000000000 : ℝ), (-109678039/625000000 : ℝ), (2698242161/5000000000 : ℝ)] ![(10991842489027/25000000000000 : ℝ), (5359568586099/50000000000000 : ℝ), (45313492859089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2635571963/5000000000 : ℝ)|^4639 ≤ (10991842489027/25000000000000 : ℝ)^3615
        have hw : |(2635571963/5000000000 : ℝ)|=(2635571963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-109678039/625000000 : ℝ)|^4639 ≤ (5359568586099/50000000000000 : ℝ)^3615
        have hw : |(-109678039/625000000 : ℝ)|=(109678039/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698242161/5000000000 : ℝ)|^4639 ≤ (45313492859089/100000000000000 : ℝ)^3615
        have hw : |(2698242161/5000000000 : ℝ)|=(2698242161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_box_2 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5271144291/10000000000 : ℝ)*x 0 + (5396484307/10000000000 : ℝ)*x 1 + (-877424073/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5271144291/10000000000 : ℝ)^4639 ≤ (10991843465757/25000000000000 : ℝ)^3615 := by
    have hnat : (5271144291 : ℕ)^4639*25000000000000^3615 ≤ 10991843465757^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271144291 10000000000 10991843465757 25000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396484307/10000000000 : ℝ)^4639 ≤ (45313492697459/100000000000000 : ℝ)^3615 := by
    have hnat : (5396484307 : ℕ)^4639*100000000000000^3615 ≤ 45313492697459^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396484307 10000000000 45313492697459 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (877424073/5000000000 : ℝ)^4639 ≤ (10719133425367/100000000000000 : ℝ)^3615 := by
    have hnat : (877424073 : ℕ)^4639*100000000000000^3615 ≤ 10719133425367^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      877424073 5000000000 10719133425367 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5271144291/10000000000 : ℝ), (5396484307/10000000000 : ℝ), (-877424073/5000000000 : ℝ)] ![(10991843465757/25000000000000 : ℝ), (45313492697459/100000000000000 : ℝ), (10719133425367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5271144291/10000000000 : ℝ)|^4639 ≤ (10991843465757/25000000000000 : ℝ)^3615
        have hw : |(5271144291/10000000000 : ℝ)|=(5271144291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396484307/10000000000 : ℝ)|^4639 ≤ (45313492697459/100000000000000 : ℝ)^3615
        have hw : |(5396484307/10000000000 : ℝ)|=(5396484307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-877424073/5000000000 : ℝ)|^4639 ≤ (10719133425367/100000000000000 : ℝ)^3615
        have hw : |(-877424073/5000000000 : ℝ)|=(877424073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_box_3 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2221855157/5000000000 : ℝ)*x 0 + (4149372397/10000000000 : ℝ)*x 1 + (4149373277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2221855157/5000000000 : ℝ)^4639 ≤ (282523588119/800000000000 : ℝ)^3615 := by
    have hnat : (2221855157 : ℕ)^4639*800000000000^3615 ≤ 282523588119^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2221855157 5000000000 282523588119 800000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4149372397/10000000000 : ℝ)^4639 ≤ (32342271335439/100000000000000 : ℝ)^3615 := by
    have hnat : (4149372397 : ℕ)^4639*100000000000000^3615 ≤ 32342271335439^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4149372397 10000000000 32342271335439 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4149373277/10000000000 : ℝ)^4639 ≤ (646845602751/2000000000000 : ℝ)^3615 := by
    have hnat : (4149373277 : ℕ)^4639*2000000000000^3615 ≤ 646845602751^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4149373277 10000000000 646845602751 2000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2221855157/5000000000 : ℝ), (4149372397/10000000000 : ℝ), (4149373277/10000000000 : ℝ)] ![(282523588119/800000000000 : ℝ), (32342271335439/100000000000000 : ℝ), (646845602751/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2221855157/5000000000 : ℝ)|^4639 ≤ (282523588119/800000000000 : ℝ)^3615
        have hw : |(2221855157/5000000000 : ℝ)|=(2221855157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4149372397/10000000000 : ℝ)|^4639 ≤ (32342271335439/100000000000000 : ℝ)^3615
        have hw : |(4149372397/10000000000 : ℝ)|=(4149372397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4149373277/10000000000 : ℝ)|^4639 ≤ (646845602751/2000000000000 : ℝ)^3615
        have hw : |(4149373277/10000000000 : ℝ)|=(4149373277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_box_4 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1993281263/10000000000 : ℝ)*x 0 + (5245074053/10000000000 : ℝ)*x 1 + (5245074013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1993281263/10000000000 : ℝ)^4639 ≤ (6311483630907/50000000000000 : ℝ)^3615 := by
    have hnat : (1993281263 : ℕ)^4639*50000000000000^3615 ≤ 6311483630907^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1993281263 10000000000 6311483630907 50000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245074053/10000000000 : ℝ)^4639 ≤ (21844258286473/50000000000000 : ℝ)^3615 := by
    have hnat : (5245074053 : ℕ)^4639*50000000000000^3615 ≤ 21844258286473^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245074053 10000000000 21844258286473 50000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245074013/10000000000 : ℝ)^4639 ≤ (43688516145391/100000000000000 : ℝ)^3615 := by
    have hnat : (5245074013 : ℕ)^4639*100000000000000^3615 ≤ 43688516145391^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245074013 10000000000 43688516145391 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1993281263/10000000000 : ℝ), (5245074053/10000000000 : ℝ), (5245074013/10000000000 : ℝ)] ![(6311483630907/50000000000000 : ℝ), (21844258286473/50000000000000 : ℝ), (43688516145391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1993281263/10000000000 : ℝ)|^4639 ≤ (6311483630907/50000000000000 : ℝ)^3615
        have hw : |(-1993281263/10000000000 : ℝ)|=(1993281263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245074053/10000000000 : ℝ)|^4639 ≤ (21844258286473/50000000000000 : ℝ)^3615
        have hw : |(5245074053/10000000000 : ℝ)|=(5245074053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245074013/10000000000 : ℝ)|^4639 ≤ (43688516145391/100000000000000 : ℝ)^3615
        have hw : |(5245074013/10000000000 : ℝ)|=(5245074013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_box_5 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5376090229/10000000000 : ℝ)*x 0 + (-1818122823/10000000000 : ℝ)*x 1 + (5245074041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376090229/10000000000 : ℝ)^4639 ≤ (22546928218957/50000000000000 : ℝ)^3615 := by
    have hnat : (5376090229 : ℕ)^4639*50000000000000^3615 ≤ 22546928218957^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376090229 10000000000 22546928218957 50000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1818122823/10000000000 : ℝ)^4639 ≤ (11217627098087/100000000000000 : ℝ)^3615 := by
    have hnat : (1818122823 : ℕ)^4639*100000000000000^3615 ≤ 11217627098087^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1818122823 10000000000 11217627098087 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245074041/10000000000 : ℝ)^4639 ≤ (43688516444679/100000000000000 : ℝ)^3615 := by
    have hnat : (5245074041 : ℕ)^4639*100000000000000^3615 ≤ 43688516444679^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245074041 10000000000 43688516444679 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376090229/10000000000 : ℝ), (-1818122823/10000000000 : ℝ), (5245074041/10000000000 : ℝ)] ![(22546928218957/50000000000000 : ℝ), (11217627098087/100000000000000 : ℝ), (43688516444679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376090229/10000000000 : ℝ)|^4639 ≤ (22546928218957/50000000000000 : ℝ)^3615
        have hw : |(5376090229/10000000000 : ℝ)|=(5376090229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1818122823/10000000000 : ℝ)|^4639 ≤ (11217627098087/100000000000000 : ℝ)^3615
        have hw : |(-1818122823/10000000000 : ℝ)|=(1818122823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245074041/10000000000 : ℝ)|^4639 ≤ (43688516444679/100000000000000 : ℝ)^3615
        have hw : |(5245074041/10000000000 : ℝ)|=(5245074041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_box_6 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2688045199/5000000000 : ℝ)*x 0 + (52450741/100000000 : ℝ)*x 1 + (-909061257/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688045199/5000000000 : ℝ)^4639 ≤ (45093858257001/100000000000000 : ℝ)^3615 := by
    have hnat : (2688045199 : ℕ)^4639*100000000000000^3615 ≤ 45093858257001^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688045199 5000000000 45093858257001 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52450741/100000000 : ℝ)^4639 ≤ (43688517075323/100000000000000 : ℝ)^3615 := by
    have hnat : (52450741 : ℕ)^4639*100000000000000^3615 ≤ 43688517075323^3615*100000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52450741 100000000 43688517075323 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (909061257/5000000000 : ℝ)^4639 ≤ (11217624651547/100000000000000 : ℝ)^3615 := by
    have hnat : (909061257 : ℕ)^4639*100000000000000^3615 ≤ 11217624651547^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      909061257 5000000000 11217624651547 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688045199/5000000000 : ℝ), (52450741/100000000 : ℝ), (-909061257/5000000000 : ℝ)] ![(45093858257001/100000000000000 : ℝ), (43688517075323/100000000000000 : ℝ), (11217624651547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688045199/5000000000 : ℝ)|^4639 ≤ (45093858257001/100000000000000 : ℝ)^3615
        have hw : |(2688045199/5000000000 : ℝ)|=(2688045199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(52450741/100000000 : ℝ)|^4639 ≤ (43688517075323/100000000000000 : ℝ)^3615
        have hw : |(52450741/100000000 : ℝ)|=(52450741/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-909061257/5000000000 : ℝ)|^4639 ≤ (11217624651547/100000000000000 : ℝ)^3615
        have hw : |(-909061257/5000000000 : ℝ)|=(909061257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_box_7 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (100993129/250000000 : ℝ)*x 0 + (174049507/400000000 : ℝ)*x 1 + (2175619239/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (100993129/250000000 : ℝ)^4639 ≤ (31249666811803/100000000000000 : ℝ)^3615 := by
    have hnat : (100993129 : ℕ)^4639*100000000000000^3615 ≤ 31249666811803^3615*250000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100993129 250000000 31249666811803 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (174049507/400000000 : ℝ)^4639 ≤ (34375162517447/100000000000000 : ℝ)^3615 := by
    have hnat : (174049507 : ℕ)^4639*100000000000000^3615 ≤ 34375162517447^3615*400000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174049507 400000000 34375162517447 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2175619239/5000000000 : ℝ)^4639 ≤ (34375170658181/100000000000000 : ℝ)^3615 := by
    have hnat : (2175619239 : ℕ)^4639*100000000000000^3615 ≤ 34375170658181^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175619239 5000000000 34375170658181 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(100993129/250000000 : ℝ), (174049507/400000000 : ℝ), (2175619239/5000000000 : ℝ)] ![(31249666811803/100000000000000 : ℝ), (34375162517447/100000000000000 : ℝ), (34375170658181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(100993129/250000000 : ℝ)|^4639 ≤ (31249666811803/100000000000000 : ℝ)^3615
        have hw : |(100993129/250000000 : ℝ)|=(100993129/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(174049507/400000000 : ℝ)|^4639 ≤ (34375162517447/100000000000000 : ℝ)^3615
        have hw : |(174049507/400000000 : ℝ)|=(174049507/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2175619239/5000000000 : ℝ)|^4639 ≤ (34375170658181/100000000000000 : ℝ)^3615
        have hw : |(2175619239/5000000000 : ℝ)|=(2175619239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_box_8 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-381160871/2000000000 : ℝ)*x 0 + (5138388841/10000000000 : ℝ)*x 1 + (2708375181/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (381160871/2000000000 : ℝ)^4639 ≤ (5958271595401/50000000000000 : ℝ)^3615 := by
    have hnat : (381160871 : ℕ)^4639*50000000000000^3615 ≤ 5958271595401^3615*2000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      381160871 2000000000 5958271595401 50000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5138388841/10000000000 : ℝ)^4639 ≤ (42551473558929/100000000000000 : ℝ)^3615 := by
    have hnat : (5138388841 : ℕ)^4639*100000000000000^3615 ≤ 42551473558929^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138388841 10000000000 42551473558929 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2708375181/5000000000 : ℝ)^4639 ≤ (45531983236081/100000000000000 : ℝ)^3615 := by
    have hnat : (2708375181 : ℕ)^4639*100000000000000^3615 ≤ 45531983236081^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708375181 5000000000 45531983236081 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-381160871/2000000000 : ℝ), (5138388841/10000000000 : ℝ), (2708375181/5000000000 : ℝ)] ![(5958271595401/50000000000000 : ℝ), (42551473558929/100000000000000 : ℝ), (45531983236081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-381160871/2000000000 : ℝ)|^4639 ≤ (5958271595401/50000000000000 : ℝ)^3615
        have hw : |(-381160871/2000000000 : ℝ)|=(381160871/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5138388841/10000000000 : ℝ)|^4639 ≤ (42551473558929/100000000000000 : ℝ)^3615
        have hw : |(5138388841/10000000000 : ℝ)|=(5138388841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2708375181/5000000000 : ℝ)|^4639 ≤ (45531983236081/100000000000000 : ℝ)^3615
        have hw : |(2708375181/5000000000 : ℝ)|=(2708375181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_box_9 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257093803/10000000000 : ℝ)*x 0 + (-436536893/2500000000 : ℝ)*x 1 + (5416750321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257093803/10000000000 : ℝ)^4639 ≤ (8763407156053/20000000000000 : ℝ)^3615 := by
    have hnat : (5257093803 : ℕ)^4639*20000000000000^3615 ≤ 8763407156053^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257093803 10000000000 8763407156053 20000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (436536893/2500000000 : ℝ)^4639 ≤ (213019628291/2000000000000 : ℝ)^3615 := by
    have hnat : (436536893 : ℕ)^4639*2000000000000^3615 ≤ 213019628291^3615*2500000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436536893 2500000000 213019628291 2000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416750321/10000000000 : ℝ)^4639 ≤ (45531982793821/100000000000000 : ℝ)^3615 := by
    have hnat : (5416750321 : ℕ)^4639*100000000000000^3615 ≤ 45531982793821^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416750321 10000000000 45531982793821 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257093803/10000000000 : ℝ), (-436536893/2500000000 : ℝ), (5416750321/10000000000 : ℝ)] ![(8763407156053/20000000000000 : ℝ), (213019628291/2000000000000 : ℝ), (45531982793821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257093803/10000000000 : ℝ)|^4639 ≤ (8763407156053/20000000000000 : ℝ)^3615
        have hw : |(5257093803/10000000000 : ℝ)|=(5257093803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-436536893/2500000000 : ℝ)|^4639 ≤ (213019628291/2000000000000 : ℝ)^3615
        have hw : |(-436536893/2500000000 : ℝ)|=(436536893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416750321/10000000000 : ℝ)|^4639 ≤ (45531982793821/100000000000000 : ℝ)^3615
        have hw : |(5416750321/10000000000 : ℝ)|=(5416750321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_box_10 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257093739/10000000000 : ℝ)*x 0 + (677093797/1250000000 : ℝ)*x 1 + (-873073791/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257093739/10000000000 : ℝ)^4639 ≤ (21908517547867/50000000000000 : ℝ)^3615 := by
    have hnat : (5257093739 : ℕ)^4639*50000000000000^3615 ≤ 21908517547867^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257093739 10000000000 21908517547867 50000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (677093797/1250000000 : ℝ)^4639 ≤ (45531983387097/100000000000000 : ℝ)^3615 := by
    have hnat : (677093797 : ℕ)^4639*100000000000000^3615 ≤ 45531983387097^3615*1250000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677093797 1250000000 45531983387097 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (873073791/5000000000 : ℝ)^4639 ≤ (426039259713/4000000000000 : ℝ)^3615 := by
    have hnat : (873073791 : ℕ)^4639*4000000000000^3615 ≤ 426039259713^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873073791 5000000000 426039259713 4000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257093739/10000000000 : ℝ), (677093797/1250000000 : ℝ), (-873073791/5000000000 : ℝ)] ![(21908517547867/50000000000000 : ℝ), (45531983387097/100000000000000 : ℝ), (426039259713/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257093739/10000000000 : ℝ)|^4639 ≤ (21908517547867/50000000000000 : ℝ)^3615
        have hw : |(5257093739/10000000000 : ℝ)|=(5257093739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(677093797/1250000000 : ℝ)|^4639 ≤ (45531983387097/100000000000000 : ℝ)^3615
        have hw : |(677093797/1250000000 : ℝ)|=(677093797/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-873073791/5000000000 : ℝ)|^4639 ≤ (426039259713/4000000000000 : ℝ)^3615
        have hw : |(-873073791/5000000000 : ℝ)|=(873073791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_box_11 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4496642563/10000000000 : ℝ)*x 0 + (824463491/2000000000 : ℝ)*x 1 + (164892701/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4496642563/10000000000 : ℝ)^4639 ≤ (17928092333703/50000000000000 : ℝ)^3615 := by
    have hnat : (4496642563 : ℕ)^4639*50000000000000^3615 ≤ 17928092333703^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496642563 10000000000 17928092333703 50000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (824463491/2000000000 : ℝ)^4639 ≤ (32071907307681/100000000000000 : ℝ)^3615 := by
    have hnat : (824463491 : ℕ)^4639*100000000000000^3615 ≤ 32071907307681^3615*2000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      824463491 2000000000 32071907307681 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164892701/400000000 : ℝ)^4639 ≤ (32071908006553/100000000000000 : ℝ)^3615 := by
    have hnat : (164892701 : ℕ)^4639*100000000000000^3615 ≤ 32071908006553^3615*400000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164892701 400000000 32071908006553 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4496642563/10000000000 : ℝ), (824463491/2000000000 : ℝ), (164892701/400000000 : ℝ)] ![(17928092333703/50000000000000 : ℝ), (32071907307681/100000000000000 : ℝ), (32071908006553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4496642563/10000000000 : ℝ)|^4639 ≤ (17928092333703/50000000000000 : ℝ)^3615
        have hw : |(4496642563/10000000000 : ℝ)|=(4496642563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(824463491/2000000000 : ℝ)|^4639 ≤ (32071907307681/100000000000000 : ℝ)^3615
        have hw : |(824463491/2000000000 : ℝ)|=(824463491/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164892701/400000000 : ℝ)|^4639 ≤ (32071908006553/100000000000000 : ℝ)^3615
        have hw : |(164892701/400000000 : ℝ)|=(164892701/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_box_12 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-833871697/5000000000 : ℝ)*x 0 + (1099984109/2000000000 : ℝ)*x 1 + (5230024041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (833871697/5000000000 : ℝ)^4639 ≤ (2008243180879/20000000000000 : ℝ)^3615 := by
    have hnat : (833871697 : ℕ)^4639*20000000000000^3615 ≤ 2008243180879^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833871697 5000000000 2008243180879 20000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1099984109/2000000000 : ℝ)^4639 ≤ (2901941855741/6250000000000 : ℝ)^3615 := by
    have hnat : (1099984109 : ℕ)^4639*6250000000000^3615 ≤ 2901941855741^3615*2000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099984109 2000000000 2901941855741 6250000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5230024041/10000000000 : ℝ)^4639 ≤ (2176385719503/5000000000000 : ℝ)^3615 := by
    have hnat : (5230024041 : ℕ)^4639*5000000000000^3615 ≤ 2176385719503^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230024041 10000000000 2176385719503 5000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-833871697/5000000000 : ℝ), (1099984109/2000000000 : ℝ), (5230024041/10000000000 : ℝ)] ![(2008243180879/20000000000000 : ℝ), (2901941855741/6250000000000 : ℝ), (2176385719503/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-833871697/5000000000 : ℝ)|^4639 ≤ (2008243180879/20000000000000 : ℝ)^3615
        have hw : |(-833871697/5000000000 : ℝ)|=(833871697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1099984109/2000000000 : ℝ)|^4639 ≤ (2901941855741/6250000000000 : ℝ)^3615
        have hw : |(1099984109/2000000000 : ℝ)|=(1099984109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5230024041/10000000000 : ℝ)|^4639 ≤ (2176385719503/5000000000000 : ℝ)^3615
        have hw : |(5230024041/10000000000 : ℝ)|=(5230024041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_box_13 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42082211/78125000 : ℝ)*x 0 + (-912120817/5000000000 : ℝ)*x 1 + (5230024521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42082211/78125000 : ℝ)^4639 ≤ (45206183965909/100000000000000 : ℝ)^3615 := by
    have hnat : (42082211 : ℕ)^4639*100000000000000^3615 ≤ 45206183965909^3615*78125000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42082211 78125000 45206183965909 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (912120817/5000000000 : ℝ)^4639 ≤ (5633048251283/50000000000000 : ℝ)^3615 := by
    have hnat : (912120817 : ℕ)^4639*50000000000000^3615 ≤ 5633048251283^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      912120817 5000000000 5633048251283 50000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5230024521/10000000000 : ℝ)^4639 ≤ (21763859758271/50000000000000 : ℝ)^3615 := by
    have hnat : (5230024521 : ℕ)^4639*50000000000000^3615 ≤ 21763859758271^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230024521 10000000000 21763859758271 50000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42082211/78125000 : ℝ), (-912120817/5000000000 : ℝ), (5230024521/10000000000 : ℝ)] ![(45206183965909/100000000000000 : ℝ), (5633048251283/50000000000000 : ℝ), (21763859758271/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42082211/78125000 : ℝ)|^4639 ≤ (45206183965909/100000000000000 : ℝ)^3615
        have hw : |(42082211/78125000 : ℝ)|=(42082211/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-912120817/5000000000 : ℝ)|^4639 ≤ (5633048251283/50000000000000 : ℝ)^3615
        have hw : |(-912120817/5000000000 : ℝ)|=(912120817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5230024521/10000000000 : ℝ)|^4639 ≤ (21763859758271/50000000000000 : ℝ)^3615
        have hw : |(5230024521/10000000000 : ℝ)|=(5230024521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_box_14 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5386522379/10000000000 : ℝ)*x 0 + (5230025093/10000000000 : ℝ)*x 1 + (-1824241717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5386522379/10000000000 : ℝ)^4639 ≤ (2260308859587/5000000000000 : ℝ)^3615 := by
    have hnat : (5386522379 : ℕ)^4639*5000000000000^3615 ≤ 2260308859587^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386522379 10000000000 2260308859587 5000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5230025093/10000000000 : ℝ)^4639 ≤ (43527725625601/100000000000000 : ℝ)^3615 := by
    have hnat : (5230025093 : ℕ)^4639*100000000000000^3615 ≤ 43527725625601^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230025093 10000000000 43527725625601 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1824241717/10000000000 : ℝ)^4639 ≤ (11266097160353/100000000000000 : ℝ)^3615 := by
    have hnat : (1824241717 : ℕ)^4639*100000000000000^3615 ≤ 11266097160353^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1824241717 10000000000 11266097160353 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5386522379/10000000000 : ℝ), (5230025093/10000000000 : ℝ), (-1824241717/10000000000 : ℝ)] ![(2260308859587/5000000000000 : ℝ), (43527725625601/100000000000000 : ℝ), (11266097160353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5386522379/10000000000 : ℝ)|^4639 ≤ (2260308859587/5000000000000 : ℝ)^3615
        have hw : |(5386522379/10000000000 : ℝ)|=(5386522379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5230025093/10000000000 : ℝ)|^4639 ≤ (43527725625601/100000000000000 : ℝ)^3615
        have hw : |(5230025093/10000000000 : ℝ)|=(5230025093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1824241717/10000000000 : ℝ)|^4639 ≤ (11266097160353/100000000000000 : ℝ)^3615
        have hw : |(-1824241717/10000000000 : ℝ)|=(1824241717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1571_box_15 (p : ℝ) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (499838453/1250000000 : ℝ)*x 0 + (4371278179/10000000000 : ℝ)*x 1 + (2185638713/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (499838453/1250000000 : ℝ)^4639 ≤ (30843080557123/100000000000000 : ℝ)^3615 := by
    have hnat : (499838453 : ℕ)^4639*100000000000000^3615 ≤ 30843080557123^3615*1250000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499838453 1250000000 30843080557123 100000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4371278179/10000000000 : ℝ)^4639 ≤ (17289231768793/50000000000000 : ℝ)^3615 := by
    have hnat : (4371278179 : ℕ)^4639*50000000000000^3615 ≤ 17289231768793^3615*10000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4371278179 10000000000 17289231768793 50000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2185638713/5000000000 : ℝ)^4639 ≤ (8644613973451/25000000000000 : ℝ)^3615 := by
    have hnat : (2185638713 : ℕ)^4639*25000000000000^3615 ≤ 8644613973451^3615*5000000000^4639 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185638713 5000000000 8644613973451 25000000000000 4639 3615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4639/1024 : ℝ)) 4639 3615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(499838453/1250000000 : ℝ), (4371278179/10000000000 : ℝ), (2185638713/5000000000 : ℝ)] ![(30843080557123/100000000000000 : ℝ), (17289231768793/50000000000000 : ℝ), (8644613973451/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(499838453/1250000000 : ℝ)|^4639 ≤ (30843080557123/100000000000000 : ℝ)^3615
        have hw : |(499838453/1250000000 : ℝ)|=(499838453/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4371278179/10000000000 : ℝ)|^4639 ≤ (17289231768793/50000000000000 : ℝ)^3615
        have hw : |(4371278179/10000000000 : ℝ)|=(4371278179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2185638713/5000000000 : ℝ)|^4639 ≤ (8644613973451/25000000000000 : ℝ)^3615
        have hw : |(2185638713/5000000000 : ℝ)|=(2185638713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1571_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168108509/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (89/800 : ℝ)*pair X i i ≤ pair X i h) :
    -(6383/10000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58907/100000 : ℝ) ∧ (8093/10000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (21593/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (89/800 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (89/800 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (89/800 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (89/800 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (89/800 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (89/800 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (89/800 : ℝ) ^ (4637/1024 : ℝ) ≤ (4801102820907787/100000000000000000000 : ℝ) := by
    have hpowers : (89/800 : ℝ)^4637 ≤ (4801102820907787/100000000000000000000 : ℝ)^1024 := by
      have hnat : (89 : ℕ)^4637*100000000000000000000^1024 ≤ 4801102820907787^1024*800^4637 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        89 800 4801102820907787 100000000000000000000 4637 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (89/800 : ℝ)) (X := (4801102820907787/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4637 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3871/25000 : ℝ) ^ (4637/1024 : ℝ) ≤ (2681893223501853/12500000000000000000 : ℝ) := by
    have hpowers : (3871/25000 : ℝ)^4637 ≤ (2681893223501853/12500000000000000000 : ℝ)^1024 := by
      have hnat : (3871 : ℕ)^4637*12500000000000000000^1024 ≤ 2681893223501853^1024*25000^4637 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3871 25000 2681893223501853 12500000000000000000 4637 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3871/25000 : ℝ)) (X := (2681893223501853/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4637 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004801102820907787/50000000000000000000 : ℝ) ≤ (1000021203991313/1000000000000000 : ℝ) ^ (4637/1024 : ℝ) := by
    have hpowers : (50004801102820907787/50000000000000000000 : ℝ)^1024 ≤ (1000021203991313/1000000000000000 : ℝ)^4637 := by
      have hnat : (50004801102820907787 : ℕ)^1024*1000000000000000^4637 ≤ 1000021203991313^4637*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004801102820907787 50000000000000000000 1000021203991313 1000000000000000 1024 4637 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000021203991313/1000000000000000 : ℝ)) (X := (50004801102820907787/50000000000000000000 : ℝ)) (by norm_num) 4637 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100026256248608922611/100000000000000000000 : ℝ) ≤ (10000579763829883/10000000000000000 : ℝ) ^ (4637/1024 : ℝ) := by
    have hpowers : (100026256248608922611/100000000000000000000 : ℝ)^1024 ≤ (10000579763829883/10000000000000000 : ℝ)^4637 := by
      have hnat : (100026256248608922611 : ℕ)^1024*10000000000000000^4637 ≤ 10000579763829883^4637*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100026256248608922611 100000000000000000000 10000579763829883 10000000000000000 1024 4637 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000579763829883/10000000000000000 : ℝ)) (X := (100026256248608922611/100000000000000000000 : ℝ)) (by norm_num) 4637 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6252681893223501853/6250000000000000000 : ℝ) ≤ (2500236871936659/2500000000000000 : ℝ) ^ (4637/1024 : ℝ) := by
    have hpowers : (6252681893223501853/6250000000000000000 : ℝ)^1024 ≤ (2500236871936659/2500000000000000 : ℝ)^4637 := by
      have hnat : (6252681893223501853 : ℕ)^1024*2500000000000000^4637 ≤ 2500236871936659^4637*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252681893223501853 6250000000000000000 2500236871936659 2500000000000000 1024 4637 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500236871936659/2500000000000000 : ℝ)) (X := (6252681893223501853/6250000000000000000 : ℝ)) (by norm_num) 4637 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4801102820907787/100000000000000000000 : ℝ) ≤ ((2179137121241678971/2179500000000000000 : ℝ)+2*(367723916753/435900000000000 : ℝ)*(89/800 : ℝ))^(4637/1024 : ℝ) := by
    rw [show (2179137121241678971/2179500000000000000 : ℝ)+2*(367723916753/435900000000000 : ℝ)*(89/800 : ℝ)=(1000021203991313/1000000000000000 : ℝ) by norm_num, show 1+2*(4801102820907787/100000000000000000000 : ℝ)=(50004801102820907787/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2681893223501853/12500000000000000000 : ℝ)+(4801102820907787/100000000000000000000 : ℝ) ≤ ((2179137121241678971/2179500000000000000 : ℝ)+(367723916753/435900000000000 : ℝ)*((3871/25000 : ℝ)+(89/800 : ℝ)))^(4637/1024 : ℝ) := by
    rw [show (2179137121241678971/2179500000000000000 : ℝ)+(367723916753/435900000000000 : ℝ)*((3871/25000 : ℝ)+(89/800 : ℝ))=(10000579763829883/10000000000000000 : ℝ) by norm_num, show 1+(2681893223501853/12500000000000000000 : ℝ)+(4801102820907787/100000000000000000000 : ℝ)=(100026256248608922611/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2681893223501853/12500000000000000000 : ℝ) ≤ ((2179137121241678971/2179500000000000000 : ℝ)+2*(367723916753/435900000000000 : ℝ)*(3871/25000 : ℝ))^(4637/1024 : ℝ) := by
    rw [show (2179137121241678971/2179500000000000000 : ℝ)+2*(367723916753/435900000000000 : ℝ)*(3871/25000 : ℝ)=(2500236871936659/2500000000000000 : ℝ) by norm_num, show 1+2*(2681893223501853/12500000000000000000 : ℝ)=(6252681893223501853/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2179137121241678971/2179500000000000000 : ℝ)*(X 1 0+X 2 0)+(367723916753/435900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4637/1024 : ℝ)) (lo := (89/800 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (2179137121241678971/2179500000000000000 : ℝ)) (alpha := (367723916753/435900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2179137121241678971/2179500000000000000 : ℝ)*(X 0 1+X 2 1)+(367723916753/435900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4637/1024 : ℝ)) (lo := (89/800 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (2179137121241678971/2179500000000000000 : ℝ)) (alpha := (367723916753/435900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2179137121241678971/2179500000000000000 : ℝ)*(X 0 2+X 1 2)+(367723916753/435900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4637/1024 : ℝ)) (lo := (89/800 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (2179137121241678971/2179500000000000000 : ℝ)) (alpha := (367723916753/435900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-197576103/1250000000 : ℝ)*X 0 0+(337280219/625000000 : ℝ)*X 0 1+(5396483583/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2635571963/5000000000 : ℝ)*X 1 0+(-109678039/625000000 : ℝ)*X 1 1+(2698242161/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5271144291/10000000000 : ℝ)*X 2 0+(5396484307/10000000000 : ℝ)*X 2 1+(-877424073/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2221855157/5000000000 : ℝ)*X 0 0+(4149372397/10000000000 : ℝ)*X 0 1+(4149373277/10000000000 : ℝ)*X 0 2+(2221855157/5000000000 : ℝ)*X 1 0+(4149372397/10000000000 : ℝ)*X 1 1+(4149373277/10000000000 : ℝ)*X 1 2+(2221855157/5000000000 : ℝ)*X 2 0+(4149372397/10000000000 : ℝ)*X 2 1+(4149373277/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1993281263/10000000000 : ℝ)*X 0 0+(5245074053/10000000000 : ℝ)*X 0 1+(5245074013/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5376090229/10000000000 : ℝ)*X 1 0+(-1818122823/10000000000 : ℝ)*X 1 1+(5245074041/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2688045199/5000000000 : ℝ)*X 2 0+(52450741/100000000 : ℝ)*X 2 1+(-909061257/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((100993129/250000000 : ℝ)*X 0 0+(174049507/400000000 : ℝ)*X 0 1+(2175619239/5000000000 : ℝ)*X 0 2+(100993129/250000000 : ℝ)*X 1 0+(174049507/400000000 : ℝ)*X 1 1+(2175619239/5000000000 : ℝ)*X 1 2+(100993129/250000000 : ℝ)*X 2 0+(174049507/400000000 : ℝ)*X 2 1+(2175619239/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-381160871/2000000000 : ℝ)*X 0 0+(5138388841/10000000000 : ℝ)*X 0 1+(2708375181/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5257093803/10000000000 : ℝ)*X 1 0+(-436536893/2500000000 : ℝ)*X 1 1+(5416750321/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5257093739/10000000000 : ℝ)*X 2 0+(677093797/1250000000 : ℝ)*X 2 1+(-873073791/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4496642563/10000000000 : ℝ)*X 0 0+(824463491/2000000000 : ℝ)*X 0 1+(164892701/400000000 : ℝ)*X 0 2+(4496642563/10000000000 : ℝ)*X 1 0+(824463491/2000000000 : ℝ)*X 1 1+(164892701/400000000 : ℝ)*X 1 2+(4496642563/10000000000 : ℝ)*X 2 0+(824463491/2000000000 : ℝ)*X 2 1+(164892701/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-833871697/5000000000 : ℝ)*X 0 0+(1099984109/2000000000 : ℝ)*X 0 1+(5230024041/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((42082211/78125000 : ℝ)*X 1 0+(-912120817/5000000000 : ℝ)*X 1 1+(5230024521/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5386522379/10000000000 : ℝ)*X 2 0+(5230025093/10000000000 : ℝ)*X 2 1+(-1824241717/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((499838453/1250000000 : ℝ)*X 0 0+(4371278179/10000000000 : ℝ)*X 0 1+(2185638713/5000000000 : ℝ)*X 0 2+(499838453/1250000000 : ℝ)*X 1 0+(4371278179/10000000000 : ℝ)*X 1 1+(2185638713/5000000000 : ℝ)*X 1 2+(499838453/1250000000 : ℝ)*X 2 0+(4371278179/10000000000 : ℝ)*X 2 1+(2185638713/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1571_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-6383/10000 : ℝ) ≤ (-5796368894884158883106347730199/9081250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18057799/20000000000000 : ℝ)*(upper0) + (72138377/100000000000000 : ℝ)*(lower2) + (11083429/10000000000000 : ℝ)*(upper5) + (577311774188827/25000000000000 : ℝ)*(major0) + (577311774188827/25000000000000 : ℝ)*(major1) + (577311774188827/25000000000000 : ℝ)*(major2) + (975645249/100000000000000 : ℝ)*(sp1) + (1932548193/50000000000000 : ℝ)*(sp3) + (326610414734201/10000000000000 : ℝ)*(sp4) + (408263070607863/12500000000000 : ℝ)*(sp5) + (816524778970671/25000000000000 : ℝ)*(sp6) + (686830373113179/50000000000000 : ℝ)*(sp7) + (696583071/50000000000000 : ℝ)*(sp8) + (6424625469/100000000000000 : ℝ)*(sp14) + (1373664611322743/100000000000000 : ℝ)*(f.failure) + (408263192563519/12500000000000 : ℝ)*(f.sum) + (114873272477/170273437500000000000000000 : ℝ)*base66 + (304661345799737983/54487500000000000000000000000000 : ℝ)*base68 + (405748012577537983/54487500000000000000000000000000 : ℝ)*base70 + (592654058806862983/54487500000000000000000000000000 : ℝ)*base72 + (25956079718791/1362187500000000000000000000 : ℝ)*base74 + (671523419017187983/54487500000000000000000000000000 : ℝ)*base76 + (543215718895450483/54487500000000000000000000000000 : ℝ)*base78 + (697194203216425483/54487500000000000000000000000000 : ℝ)*base80 + (54354479808691/21795000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (43520187/10000000000000000000000 : ℝ)*base89 + (43520187/10000000000000000000000 : ℝ)*base91 + (43520187/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (58907/100000 : ℝ) ≤ (21398993575467840081960724024957/36325000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (148661203/100000000000000 : ℝ)*(lower1) + (57246057/100000000000000 : ℝ)*(lower3) + (162377819/100000000000000 : ℝ)*(upper4) + (5428907/10000000000000 : ℝ)*(upper5) + (2389539291053011/100000000000000 : ℝ)*(major0) + (2389539291053011/100000000000000 : ℝ)*(major1) + (2389539291053011/100000000000000 : ℝ)*(major2) + (1669007619455259/50000000000000 : ℝ)*(sp0) + (417250623047123/12500000000000 : ℝ)*(sp1) + (1669000560698843/50000000000000 : ℝ)*(sp2) + (177673062558209/12500000000000 : ℝ)*(sp3) + (5127266767/50000000000000 : ℝ)*(sp5) + (110293069/781250000000 : ℝ)*(sp6) + (21117361487/50000000000000 : ℝ)*(sp11) + (710713367594323/50000000000000 : ℝ)*(f.failure) + (1669007619455259/50000000000000 : ℝ)*(f.sum) + (23973954972427/21795000000000000000000000000 : ℝ)*base66 + (1514052348604646681/217950000000000000000000000000000 : ℝ)*base67 + (1214538819411746681/217950000000000000000000000000000 : ℝ)*base69 + (1553052362143346681/217950000000000000000000000000000 : ℝ)*base71 + (102962912695237/21795000000000000000000000000 : ℝ)*base74 + (1727155094835146681/217950000000000000000000000000000 : ℝ)*base75 + (1321925259451946681/217950000000000000000000000000000 : ℝ)*base77 + (2249226090951146681/217950000000000000000000000000000 : ℝ)*base79 + (20278522534733/21795000000000000000000000000 : ℝ)*base81 + (6394407/5000000000000000000000 : ℝ)*base89 + (6394407/5000000000000000000000 : ℝ)*base91 + (6394407/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (8093/10000 : ℝ) ≤ (7349691991799589021808623925617/9081250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1310177/12500000000000 : ℝ)*(lower1) + (2300911/20000000000000 : ℝ)*(upper2) + (4439771/20000000000000 : ℝ)*(lower3) + (32659861/100000000000000 : ℝ)*(lower5) + (643959491542073/25000000000000 : ℝ)*(major0) + (643959491542073/25000000000000 : ℝ)*(major1) + (643959491542073/25000000000000 : ℝ)*(major2) + (1485983899/100000000000000 : ℝ)*(sp0) + (8175573429/100000000000000 : ℝ)*(sp2) + (2101131669/50000000000000 : ℝ)*(sp3) + (1796224842940101/50000000000000 : ℝ)*(sp8) + (35924511718641/1000000000000 : ℝ)*(sp9) + (224527687268167/6250000000000 : ℝ)*(sp10) + (1532243023942381/100000000000000 : ℝ)*(sp11) + (1532247226205719/100000000000000 : ℝ)*(f.failure) + (35924511718641/1000000000000 : ℝ)*(f.sum) + (56031634278421/21795000000000000000000000000 : ℝ)*base65 + (119588375765820617/54487500000000000000000000000000 : ℝ)*base68 + (182820552647841883/54487500000000000000000000000000 : ℝ)*base69 + (277847077229879383/54487500000000000000000000000000 : ℝ)*base71 + (57002688656219/21795000000000000000000000000 : ℝ)*base74 + (519803244493079383/54487500000000000000000000000000 : ℝ)*base75 + (285923533395216883/54487500000000000000000000000000 : ℝ)*base77 + (179701350359858117/54487500000000000000000000000000 : ℝ)*base80 + (22610053082041/21795000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (51637029/10000000000000000000000 : ℝ)*base90 + (51637029/10000000000000000000000 : ℝ)*base92 + (51637029/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-21593/25000 : ℝ) ≤ (-125495455621394483698684857/145300000000000000000000000 : ℝ) := by norm_num
    linear_combination (1401911/3125000000000 : ℝ)*(lower0) + (203036321/100000000000000 : ℝ)*(upper3) + (62620251/100000000000000 : ℝ)*(lower4) + (10465414580177/400000000000 : ℝ)*(major0) + (10465414580177/400000000000 : ℝ)*(major1) + (10465414580177/400000000000 : ℝ)*(major2) + (1059498801/25000000000000 : ℝ)*(sp0) + (16336359541/10000000000000 : ℝ)*(sp5) + (23700528631/50000000000000 : ℝ)*(sp7) + (8039559247/100000000000000 : ℝ)*(sp8) + (1852568420926207/50000000000000 : ℝ)*(sp12) + (28945201217277/781250000000 : ℝ)*(sp13) + (1852574559703433/50000000000000 : ℝ)*(sp14) + (778150367104153/50000000000000 : ℝ)*(sp15) + (48635879227049/3125000000000 : ℝ)*(f.failure) + (1852574559703433/50000000000000 : ℝ)*(f.sum) + (7886038310897/4359000000000000000000000000 : ℝ)*base65 + (2187202134538267/871800000000000000000000000000 : ℝ)*base67 + (5319037174681267/871800000000000000000000000000 : ℝ)*base69 + (681392903299267/871800000000000000000000000000 : ℝ)*base71 + (1147337446537/217950000000000000000000000 : ℝ)*base73 + (1332924165657533/871800000000000000000000000000 : ℝ)*base76 + (583611281037533/871800000000000000000000000000 : ℝ)*base78 + (2241337310668733/871800000000000000000000000000 : ℝ)*base80 + (358479998269/54487500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1390059/312500000000000000000 : ℝ)*base90 + (1390059/312500000000000000000 : ℝ)*base92 + (1390059/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1571_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168108509/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (89/800 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6383/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(58907/100000 : ℝ) else (8093/10000 : ℝ) ≤ X j i ∧ X j i ≤ (21593/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1571_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1571_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168108509/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2781/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6383/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(58907/100000 : ℝ) else (8093/10000 : ℝ) ≤ X j i ∧ X j i ≤ (21593/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1571_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1571_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4637/1024 : ℝ) ≤ p) (hpb : p ≤ (4639/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168108509/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2781/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6383/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(58907/100000 : ℝ) else (8093/10000 : ℝ) ≤ X j i ∧ X j i ≤ (21593/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1571_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
