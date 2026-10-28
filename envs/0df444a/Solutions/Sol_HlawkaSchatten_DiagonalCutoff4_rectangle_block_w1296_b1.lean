-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1296_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:27:41.753862+00:00
-- url     : https://prove2.me/submissions/a6154e4e-c364-4e22-8a69-3f7f0c8cbc31

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
theorem support_rectangle_w1296_s3_0 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-16266317/78125000 : ℝ)*x 0 + (5433484267/10000000000 : ℝ)*x 1 + (1045237/2000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16266317/78125000 : ℝ)^133 ≤ (316605288407/2500000000000 : ℝ)^101 := by
    have hnat : (16266317 : ℕ)^133*2500000000000^101 ≤ 316605288407^101*78125000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16266317 78125000 316605288407 2500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5433484267/10000000000 : ℝ)^133 ≤ (2799128777341/6250000000000 : ℝ)^101 := by
    have hnat : (5433484267 : ℕ)^133*6250000000000^101 ≤ 2799128777341^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433484267 10000000000 2799128777341 6250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1045237/2000000 : ℝ)^133 ≤ (1701989120551/4000000000000 : ℝ)^101 := by
    have hnat : (1045237 : ℕ)^133*4000000000000^101 ≤ 1701989120551^101*2000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045237 2000000 1701989120551 4000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-16266317/78125000 : ℝ), (5433484267/10000000000 : ℝ), (1045237/2000000 : ℝ)] ![(316605288407/2500000000000 : ℝ), (2799128777341/6250000000000 : ℝ), (1701989120551/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-16266317/78125000 : ℝ)|^133 ≤ (316605288407/2500000000000 : ℝ)^101
        have hw : |(-16266317/78125000 : ℝ)|=(16266317/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5433484267/10000000000 : ℝ)|^133 ≤ (2799128777341/6250000000000 : ℝ)^101
        have hw : |(5433484267/10000000000 : ℝ)|=(5433484267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1045237/2000000 : ℝ)|^133 ≤ (1701989120551/4000000000000 : ℝ)^101
        have hw : |(1045237/2000000 : ℝ)|=(1045237/2000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s3_1 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1070879389/2000000000 : ℝ)*x 0 + (-2735211/12500000 : ℝ)*x 1 + (653273133/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070879389/2000000000 : ℝ)^133 ≤ (21964811471183/50000000000000 : ℝ)^101 := by
    have hnat : (1070879389 : ℕ)^133*50000000000000^101 ≤ 21964811471183^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070879389 2000000000 21964811471183 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2735211/12500000 : ℝ)^133 ≤ (845040521063/6250000000000 : ℝ)^101 := by
    have hnat : (2735211 : ℕ)^133*6250000000000^101 ≤ 845040521063^101*12500000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2735211 12500000 845040521063 6250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (653273133/1250000000 : ℝ)^133 ≤ (4254972869993/10000000000000 : ℝ)^101 := by
    have hnat : (653273133 : ℕ)^133*10000000000000^101 ≤ 4254972869993^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653273133 1250000000 4254972869993 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070879389/2000000000 : ℝ), (-2735211/12500000 : ℝ), (653273133/1250000000 : ℝ)] ![(21964811471183/50000000000000 : ℝ), (845040521063/6250000000000 : ℝ), (4254972869993/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070879389/2000000000 : ℝ)|^133 ≤ (21964811471183/50000000000000 : ℝ)^101
        have hw : |(1070879389/2000000000 : ℝ)|=(1070879389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2735211/12500000 : ℝ)|^133 ≤ (845040521063/6250000000000 : ℝ)^101
        have hw : |(-2735211/12500000 : ℝ)|=(2735211/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(653273133/1250000000 : ℝ)|^133 ≤ (4254972869993/10000000000000 : ℝ)^101
        have hw : |(653273133/1250000000 : ℝ)|=(653273133/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s3_2 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1338599241/2500000000 : ℝ)*x 0 + (5226184923/10000000000 : ℝ)*x 1 + (-2188168961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338599241/2500000000 : ℝ)^133 ≤ (21964811573819/50000000000000 : ℝ)^101 := by
    have hnat : (1338599241 : ℕ)^133*50000000000000^101 ≤ 21964811573819^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338599241 2500000000 21964811573819 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5226184923/10000000000 : ℝ)^133 ≤ (10637431797061/25000000000000 : ℝ)^101 := by
    have hnat : (5226184923 : ℕ)^133*25000000000000^101 ≤ 10637431797061^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226184923 10000000000 10637431797061 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2188168961/10000000000 : ℝ)^133 ≤ (3380162411753/25000000000000 : ℝ)^101 := by
    have hnat : (2188168961 : ℕ)^133*25000000000000^101 ≤ 3380162411753^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188168961 10000000000 3380162411753 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338599241/2500000000 : ℝ), (5226184923/10000000000 : ℝ), (-2188168961/10000000000 : ℝ)] ![(21964811573819/50000000000000 : ℝ), (10637431797061/25000000000000 : ℝ), (3380162411753/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338599241/2500000000 : ℝ)|^133 ≤ (21964811573819/50000000000000 : ℝ)^101
        have hw : |(1338599241/2500000000 : ℝ)|=(1338599241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5226184923/10000000000 : ℝ)|^133 ≤ (10637431797061/25000000000000 : ℝ)^101
        have hw : |(5226184923/10000000000 : ℝ)|=(5226184923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2188168961/10000000000 : ℝ)|^133 ≤ (3380162411753/25000000000000 : ℝ)^101
        have hw : |(-2188168961/10000000000 : ℝ)|=(2188168961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s3_3 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (867481461/2000000000 : ℝ)*x 0 + (2064529989/5000000000 : ℝ)*x 1 + (4555760581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (867481461/2000000000 : ℝ)^133 ≤ (6657684919699/20000000000000 : ℝ)^101 := by
    have hnat : (867481461 : ℕ)^133*20000000000000^101 ≤ 6657684919699^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      867481461 2000000000 6657684919699 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2064529989/5000000000 : ℝ)^133 ≤ (3119900026519/10000000000000 : ℝ)^101 := by
    have hnat : (2064529989 : ℕ)^133*10000000000000^101 ≤ 3119900026519^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064529989 5000000000 3119900026519 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4555760581/10000000000 : ℝ)^133 ≤ (1775628755987/5000000000000 : ℝ)^101 := by
    have hnat : (4555760581 : ℕ)^133*5000000000000^101 ≤ 1775628755987^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4555760581 10000000000 1775628755987 5000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(867481461/2000000000 : ℝ), (2064529989/5000000000 : ℝ), (4555760581/10000000000 : ℝ)] ![(6657684919699/20000000000000 : ℝ), (3119900026519/10000000000000 : ℝ), (1775628755987/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(867481461/2000000000 : ℝ)|^133 ≤ (6657684919699/20000000000000 : ℝ)^101
        have hw : |(867481461/2000000000 : ℝ)|=(867481461/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2064529989/5000000000 : ℝ)|^133 ≤ (3119900026519/10000000000000 : ℝ)^101
        have hw : |(2064529989/5000000000 : ℝ)|=(2064529989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4555760581/10000000000 : ℝ)|^133 ≤ (1775628755987/5000000000000 : ℝ)^101
        have hw : |(4555760581/10000000000 : ℝ)|=(4555760581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s3_4 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1041055429/5000000000 : ℝ)*x 0 + (2613537559/5000000000 : ℝ)*x 1 + (2716294281/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1041055429/5000000000 : ℝ)^133 ≤ (1266439000583/10000000000000 : ℝ)^101 := by
    have hnat : (1041055429 : ℕ)^133*10000000000000^101 ≤ 1266439000583^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041055429 5000000000 1266439000583 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2613537559/5000000000 : ℝ)^133 ≤ (166247153827/390625000000 : ℝ)^101 := by
    have hnat : (2613537559 : ℕ)^133*390625000000^101 ≤ 166247153827^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613537559 5000000000 166247153827 390625000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2716294281/5000000000 : ℝ)^133 ≤ (22388169299821/50000000000000 : ℝ)^101 := by
    have hnat : (2716294281 : ℕ)^133*50000000000000^101 ≤ 22388169299821^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716294281 5000000000 22388169299821 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1041055429/5000000000 : ℝ), (2613537559/5000000000 : ℝ), (2716294281/5000000000 : ℝ)] ![(1266439000583/10000000000000 : ℝ), (166247153827/390625000000 : ℝ), (22388169299821/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1041055429/5000000000 : ℝ)|^133 ≤ (1266439000583/10000000000000 : ℝ)^101
        have hw : |(-1041055429/5000000000 : ℝ)|=(1041055429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2613537559/5000000000 : ℝ)|^133 ≤ (166247153827/390625000000 : ℝ)^101
        have hw : |(2613537559/5000000000 : ℝ)|=(2613537559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2716294281/5000000000 : ℝ)|^133 ≤ (22388169299821/50000000000000 : ℝ)^101
        have hw : |(2716294281/5000000000 : ℝ)|=(2716294281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s3_5 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2650646231/5000000000 : ℝ)*x 0 + (-990882589/5000000000 : ℝ)*x 1 + (5432588521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2650646231/5000000000 : ℝ)^133 ≤ (10839198836293/25000000000000 : ℝ)^101 := by
    have hnat : (2650646231 : ℕ)^133*25000000000000^101 ≤ 10839198836293^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2650646231 5000000000 10839198836293 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (990882589/5000000000 : ℝ)^133 ≤ (5933433243889/50000000000000 : ℝ)^101 := by
    have hnat : (990882589 : ℕ)^133*50000000000000^101 ≤ 5933433243889^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      990882589 5000000000 5933433243889 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5432588521/10000000000 : ℝ)^133 ≤ (22388169077323/50000000000000 : ℝ)^101 := by
    have hnat : (5432588521 : ℕ)^133*50000000000000^101 ≤ 22388169077323^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432588521 10000000000 22388169077323 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2650646231/5000000000 : ℝ), (-990882589/5000000000 : ℝ), (5432588521/10000000000 : ℝ)] ![(10839198836293/25000000000000 : ℝ), (5933433243889/50000000000000 : ℝ), (22388169077323/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2650646231/5000000000 : ℝ)|^133 ≤ (10839198836293/25000000000000 : ℝ)^101
        have hw : |(2650646231/5000000000 : ℝ)|=(2650646231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-990882589/5000000000 : ℝ)|^133 ≤ (5933433243889/50000000000000 : ℝ)^101
        have hw : |(-990882589/5000000000 : ℝ)|=(990882589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5432588521/10000000000 : ℝ)|^133 ≤ (22388169077323/50000000000000 : ℝ)^101
        have hw : |(5432588521/10000000000 : ℝ)|=(5432588521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s3_6 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2650646261/5000000000 : ℝ)*x 0 + (5432588443/10000000000 : ℝ)*x 1 + (-495441301/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2650646261/5000000000 : ℝ)^133 ≤ (43356795991357/100000000000000 : ℝ)^101 := by
    have hnat : (2650646261 : ℕ)^133*100000000000000^101 ≤ 43356795991357^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2650646261 5000000000 43356795991357 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5432588443/10000000000 : ℝ)^133 ≤ (44776337308069/100000000000000 : ℝ)^101 := by
    have hnat : (5432588443 : ℕ)^133*100000000000000^101 ≤ 44776337308069^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432588443 10000000000 44776337308069 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (495441301/2500000000 : ℝ)^133 ≤ (11866866692793/100000000000000 : ℝ)^101 := by
    have hnat : (495441301 : ℕ)^133*100000000000000^101 ≤ 11866866692793^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      495441301 2500000000 11866866692793 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2650646261/5000000000 : ℝ), (5432588443/10000000000 : ℝ), (-495441301/2500000000 : ℝ)] ![(43356795991357/100000000000000 : ℝ), (44776337308069/100000000000000 : ℝ), (11866866692793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2650646261/5000000000 : ℝ)|^133 ≤ (43356795991357/100000000000000 : ℝ)^101
        have hw : |(2650646261/5000000000 : ℝ)|=(2650646261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5432588443/10000000000 : ℝ)|^133 ≤ (44776337308069/100000000000000 : ℝ)^101
        have hw : |(5432588443/10000000000 : ℝ)|=(5432588443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-495441301/2500000000 : ℝ)|^133 ≤ (11866866692793/100000000000000 : ℝ)^101
        have hw : |(-495441301/2500000000 : ℝ)|=(495441301/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s3_7 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4337452967/10000000000 : ℝ)*x 0 + (8894391/19531250 : ℝ)*x 1 + (258181483/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4337452967/10000000000 : ℝ)^133 ≤ (16644443037161/50000000000000 : ℝ)^101 := by
    have hnat : (4337452967 : ℕ)^133*50000000000000^101 ≤ 16644443037161^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4337452967 10000000000 16644443037161 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8894391/19531250 : ℝ)^133 ≤ (35493767166313/100000000000000 : ℝ)^101 := by
    have hnat : (8894391 : ℕ)^133*100000000000000^101 ≤ 35493767166313^101*19531250^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8894391 19531250 35493767166313 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258181483/625000000 : ℝ)^133 ≤ (1951084170919/6250000000000 : ℝ)^101 := by
    have hnat : (258181483 : ℕ)^133*6250000000000^101 ≤ 1951084170919^101*625000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258181483 625000000 1951084170919 6250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4337452967/10000000000 : ℝ), (8894391/19531250 : ℝ), (258181483/625000000 : ℝ)] ![(16644443037161/50000000000000 : ℝ), (35493767166313/100000000000000 : ℝ), (1951084170919/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4337452967/10000000000 : ℝ)|^133 ≤ (16644443037161/50000000000000 : ℝ)^101
        have hw : |(4337452967/10000000000 : ℝ)|=(4337452967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8894391/19531250 : ℝ)|^133 ≤ (35493767166313/100000000000000 : ℝ)^101
        have hw : |(8894391/19531250 : ℝ)|=(8894391/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(258181483/625000000 : ℝ)|^133 ≤ (1951084170919/6250000000000 : ℝ)^101
        have hw : |(258181483/625000000 : ℝ)|=(258181483/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1296_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30583789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16299/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4767/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2669/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15061/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16299/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4767/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16299/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4767/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16299/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4767/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16299/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4767/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16299/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4767/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16299/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4767/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4767/50000 : ℝ) ^ (4255/1024 : ℝ) ≤ (5735999882836811/100000000000000000000 : ℝ) := by
    have hpowers : (4767/50000 : ℝ)^4255 ≤ (5735999882836811/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4767 : ℕ)^4255*100000000000000000000^1024 ≤ 5735999882836811^1024*50000^4255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4767 50000 5735999882836811 100000000000000000000 4255 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4767/50000 : ℝ)) (X := (5735999882836811/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16299/100000 : ℝ) ^ (4255/1024 : ℝ) ≤ (5324923379006887/10000000000000000000 : ℝ) := by
    have hpowers : (16299/100000 : ℝ)^4255 ≤ (5324923379006887/10000000000000000000 : ℝ)^1024 := by
      have hnat : (16299 : ℕ)^4255*10000000000000000000^1024 ≤ 5324923379006887^1024*100000^4255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16299 100000 5324923379006887 10000000000000000000 4255 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16299/100000 : ℝ)) (X := (5324923379006887/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005735999882836811/50000000000000000000 : ℝ) ≤ (5000138035442181/5000000000000000 : ℝ) ^ (4255/1024 : ℝ) := by
    have hpowers : (50005735999882836811/50000000000000000000 : ℝ)^1024 ≤ (5000138035442181/5000000000000000 : ℝ)^4255 := by
      have hnat : (50005735999882836811 : ℕ)^1024*5000000000000000^4255 ≤ 5000138035442181^4255*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005735999882836811 50000000000000000000 5000138035442181 5000000000000000 1024 4255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000138035442181/5000000000000000 : ℝ)) (X := (50005735999882836811/50000000000000000000 : ℝ)) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100058985233672905681/100000000000000000000 : ℝ) ≤ (1000141920933473/1000000000000000 : ℝ) ^ (4255/1024 : ℝ) := by
    have hpowers : (100058985233672905681/100000000000000000000 : ℝ)^1024 ≤ (1000141920933473/1000000000000000 : ℝ)^4255 := by
      have hnat : (100058985233672905681 : ℕ)^1024*1000000000000000^4255 ≤ 1000141920933473^4255*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100058985233672905681 100000000000000000000 1000141920933473 1000000000000000 1024 4255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000141920933473/1000000000000000 : ℝ)) (X := (100058985233672905681/100000000000000000000 : ℝ)) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5005324923379006887/5000000000000000000 : ℝ) ≤ (5001281173892549/5000000000000000 : ℝ) ^ (4255/1024 : ℝ) := by
    have hpowers : (5005324923379006887/5000000000000000000 : ℝ)^1024 ≤ (5001281173892549/5000000000000000 : ℝ)^4255 := by
      have hnat : (5005324923379006887 : ℕ)^1024*5000000000000000^4255 ≤ 5001281173892549^4255*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5005324923379006887 5000000000000000000 5001281173892549 5000000000000000 1024 4255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001281173892549/5000000000000000 : ℝ)) (X := (5005324923379006887/5000000000000000000 : ℝ)) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5735999882836811/100000000000000000000 : ℝ) ≤ ((11271678375926848651/11275000000000000000 : ℝ)+2*(17861538287/10570312500000 : ℝ)*(4767/50000 : ℝ))^(4255/1024 : ℝ) := by
    rw [show (11271678375926848651/11275000000000000000 : ℝ)+2*(17861538287/10570312500000 : ℝ)*(4767/50000 : ℝ)=(5000138035442181/5000000000000000 : ℝ) by norm_num, show 1+2*(5735999882836811/100000000000000000000 : ℝ)=(50005735999882836811/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5324923379006887/10000000000000000000 : ℝ)+(5735999882836811/100000000000000000000 : ℝ) ≤ ((11271678375926848651/11275000000000000000 : ℝ)+(17861538287/10570312500000 : ℝ)*((16299/100000 : ℝ)+(4767/50000 : ℝ)))^(4255/1024 : ℝ) := by
    rw [show (11271678375926848651/11275000000000000000 : ℝ)+(17861538287/10570312500000 : ℝ)*((16299/100000 : ℝ)+(4767/50000 : ℝ))=(1000141920933473/1000000000000000 : ℝ) by norm_num, show 1+(5324923379006887/10000000000000000000 : ℝ)+(5735999882836811/100000000000000000000 : ℝ)=(100058985233672905681/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5324923379006887/10000000000000000000 : ℝ) ≤ ((11271678375926848651/11275000000000000000 : ℝ)+2*(17861538287/10570312500000 : ℝ)*(16299/100000 : ℝ))^(4255/1024 : ℝ) := by
    rw [show (11271678375926848651/11275000000000000000 : ℝ)+2*(17861538287/10570312500000 : ℝ)*(16299/100000 : ℝ)=(5001281173892549/5000000000000000 : ℝ) by norm_num, show 1+2*(5324923379006887/10000000000000000000 : ℝ)=(5005324923379006887/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11271678375926848651/11275000000000000000 : ℝ)*(X 1 0+X 2 0)+(17861538287/10570312500000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4255/1024 : ℝ)) (lo := (4767/50000 : ℝ)) (hi := (16299/100000 : ℝ)) (c := (11271678375926848651/11275000000000000000 : ℝ)) (alpha := (17861538287/10570312500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11271678375926848651/11275000000000000000 : ℝ)*(X 0 1+X 2 1)+(17861538287/10570312500000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4255/1024 : ℝ)) (lo := (4767/50000 : ℝ)) (hi := (16299/100000 : ℝ)) (c := (11271678375926848651/11275000000000000000 : ℝ)) (alpha := (17861538287/10570312500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11271678375926848651/11275000000000000000 : ℝ)*(X 0 2+X 1 2)+(17861538287/10570312500000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4255/1024 : ℝ)) (lo := (4767/50000 : ℝ)) (hi := (16299/100000 : ℝ)) (c := (11271678375926848651/11275000000000000000 : ℝ)) (alpha := (17861538287/10570312500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-16266317/78125000 : ℝ)*X 0 0+(5433484267/10000000000 : ℝ)*X 0 1+(1045237/2000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070879389/2000000000 : ℝ)*X 1 0+(-2735211/12500000 : ℝ)*X 1 1+(653273133/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338599241/2500000000 : ℝ)*X 2 0+(5226184923/10000000000 : ℝ)*X 2 1+(-2188168961/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((867481461/2000000000 : ℝ)*X 0 0+(2064529989/5000000000 : ℝ)*X 0 1+(4555760581/10000000000 : ℝ)*X 0 2+(867481461/2000000000 : ℝ)*X 1 0+(2064529989/5000000000 : ℝ)*X 1 1+(4555760581/10000000000 : ℝ)*X 1 2+(867481461/2000000000 : ℝ)*X 2 0+(2064529989/5000000000 : ℝ)*X 2 1+(4555760581/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1041055429/5000000000 : ℝ)*X 0 0+(2613537559/5000000000 : ℝ)*X 0 1+(2716294281/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2650646231/5000000000 : ℝ)*X 1 0+(-990882589/5000000000 : ℝ)*X 1 1+(5432588521/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2650646261/5000000000 : ℝ)*X 2 0+(5432588443/10000000000 : ℝ)*X 2 1+(-495441301/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4337452967/10000000000 : ℝ)*X 0 0+(8894391/19531250 : ℝ)*X 0 1+(258181483/625000000 : ℝ)*X 0 2+(4337452967/10000000000 : ℝ)*X 1 0+(8894391/19531250 : ℝ)*X 1 1+(258181483/625000000 : ℝ)*X 1 2+(4337452967/10000000000 : ℝ)*X 2 0+(8894391/19531250 : ℝ)*X 2 1+(258181483/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (566339180772962067704851251/281875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (33412061/10000000000000 : ℝ)*(base19) + (414657951/100000000000000 : ℝ)*(base23) + (2859461/50000000000000 : ℝ)*(lower2) + (11093173/10000000000000 : ℝ)*(upper3) + (39676297/100000000000000 : ℝ)*(lower4) + (1791881390204133/50000000000000 : ℝ)*(major0) + (1791881390204133/50000000000000 : ℝ)*(major1) + (1791881390204133/50000000000000 : ℝ)*(major2) + (2411975737062707/50000000000000 : ℝ)*(sp0) + (4823954988997473/100000000000000 : ℝ)*(sp1) + (1205988727115033/25000000000000 : ℝ)*(sp2) + (2343566270744981/100000000000000 : ℝ)*(sp3) + (3848992669/100000000000000 : ℝ)*(sp4) + (1949990303/50000000000000 : ℝ)*(sp7) + (1171785085362793/50000000000000 : ℝ)*(f.failure) + (4823955323118083/100000000000000 : ℝ)*(f.sum) + (108686973782479/11275000000000000000000000000 : ℝ)*base66 + (3350779773030574583/563750000000000000000000000000000 : ℝ)*base67 + (4033453479896824583/563750000000000000000000000000000 : ℝ)*base69 + (256362166771925417/563750000000000000000000000000000 : ℝ)*base72 + (14655479162227/5637500000000000000000000000 : ℝ)*base74 + (2832947125404324583/563750000000000000000000000000000 : ℝ)*base75 + (623881651288175417/563750000000000000000000000000000 : ℝ)*base78 + (7321373424835574583/563750000000000000000000000000000 : ℝ)*base79 + (18749203774121/11275000000000000000000000000 : ℝ)*base81 + (10437323/1000000000000000000000 : ℝ)*base90 + (10437323/1000000000000000000000 : ℝ)*base92 + (10437323/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (373910890269089807551005683/56375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (167446941/10000000000000 : ℝ)*(base19) + (894078431/50000000000000 : ℝ)*(base23) + (83804037/50000000000000 : ℝ)*(upper3) + (29807077/100000000000000 : ℝ)*(lower4) + (2827211/1562500000000 : ℝ)*(upper5) + (361489571408863/10000000000000 : ℝ)*(major0) + (361489571408863/10000000000000 : ℝ)*(major1) + (361489571408863/10000000000000 : ℝ)*(major2) + (27966632963/100000000000000 : ℝ)*(sp1) + (28205204359/100000000000000 : ℝ)*(sp2) + (4865861928029131/100000000000000 : ℝ)*(sp4) + (2432916143463379/50000000000000 : ℝ)*(sp5) + (486583193466791/10000000000000 : ℝ)*(sp6) + (2363929279062597/100000000000000 : ℝ)*(sp7) + (2363929279062597/100000000000000 : ℝ)*(f.failure) + (4865861928029131/100000000000000 : ℝ)*(f.sum) + (8106946522097/6765000000000000000000000000 : ℝ)*base66 + (960644996115681439/338250000000000000000000000000000 : ℝ)*base67 + (2658469170348681439/338250000000000000000000000000000 : ℝ)*base69 + (3915707114079681439/338250000000000000000000000000000 : ℝ)*base71 + (2470167909667/1691250000000000000000000000 : ℝ)*base73 + (2250603962202681439/338250000000000000000000000000000 : ℝ)*base75 + (3810667342993431439/338250000000000000000000000000000 : ℝ)*base77 + (3457139363056431439/338250000000000000000000000000000 : ℝ)*base79 + (6826208673763/6765000000000000000000000000 : ℝ)*base81 + (15559967/2000000000000000000000 : ℝ)*base90 + (15559967/2000000000000000000000 : ℝ)*base92 + (15559967/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1296_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30583789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16299/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4767/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2669/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15061/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1296_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1296_s4_0 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2083967047/10000000000 : ℝ)*x 0 + (1354655541/2500000000 : ℝ)*x 1 + (5239815683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2083967047/10000000000 : ℝ)^133 ≤ (6339629715959/50000000000000 : ℝ)^101 := by
    have hnat : (2083967047 : ℕ)^133*50000000000000^101 ≤ 6339629715959^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083967047 10000000000 6339629715959 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1354655541/2500000000 : ℝ)^133 ≤ (44624815295531/100000000000000 : ℝ)^101 := by
    have hnat : (1354655541 : ℕ)^133*100000000000000^101 ≤ 44624815295531^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354655541 2500000000 44624815295531 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5239815683/10000000000 : ℝ)^133 ≤ (21347962629491/50000000000000 : ℝ)^101 := by
    have hnat : (5239815683 : ℕ)^133*50000000000000^101 ≤ 21347962629491^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239815683 10000000000 21347962629491 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2083967047/10000000000 : ℝ), (1354655541/2500000000 : ℝ), (5239815683/10000000000 : ℝ)] ![(6339629715959/50000000000000 : ℝ), (44624815295531/100000000000000 : ℝ), (21347962629491/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2083967047/10000000000 : ℝ)|^133 ≤ (6339629715959/50000000000000 : ℝ)^101
        have hw : |(-2083967047/10000000000 : ℝ)|=(2083967047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1354655541/2500000000 : ℝ)|^133 ≤ (44624815295531/100000000000000 : ℝ)^101
        have hw : |(1354655541/2500000000 : ℝ)|=(1354655541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5239815683/10000000000 : ℝ)|^133 ≤ (21347962629491/50000000000000 : ℝ)^101
        have hw : |(5239815683/10000000000 : ℝ)|=(5239815683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s4_1 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (133765963/250000000 : ℝ)*x 0 + (-543794727/2500000000 : ℝ)*x 1 + (2619907807/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133765963/250000000 : ℝ)^133 ≤ (5486127765773/12500000000000 : ℝ)^101 := by
    have hnat : (133765963 : ℕ)^133*12500000000000^101 ≤ 5486127765773^101*250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133765963 250000000 5486127765773 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543794727/2500000000 : ℝ)^133 ≤ (209610208459/1562500000000 : ℝ)^101 := by
    have hnat : (543794727 : ℕ)^133*1562500000000^101 ≤ 209610208459^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543794727 2500000000 209610208459 1562500000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2619907807/5000000000 : ℝ)^133 ≤ (42695924518611/100000000000000 : ℝ)^101 := by
    have hnat : (2619907807 : ℕ)^133*100000000000000^101 ≤ 42695924518611^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619907807 5000000000 42695924518611 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133765963/250000000 : ℝ), (-543794727/2500000000 : ℝ), (2619907807/5000000000 : ℝ)] ![(5486127765773/12500000000000 : ℝ), (209610208459/1562500000000 : ℝ), (42695924518611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133765963/250000000 : ℝ)|^133 ≤ (5486127765773/12500000000000 : ℝ)^101
        have hw : |(133765963/250000000 : ℝ)|=(133765963/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-543794727/2500000000 : ℝ)|^133 ≤ (209610208459/1562500000000 : ℝ)^101
        have hw : |(-543794727/2500000000 : ℝ)|=(543794727/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2619907807/5000000000 : ℝ)|^133 ≤ (42695924518611/100000000000000 : ℝ)^101
        have hw : |(2619907807/5000000000 : ℝ)|=(2619907807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s4_2 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2675319403/5000000000 : ℝ)*x 0 + (5239815061/10000000000 : ℝ)*x 1 + (-2175179259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675319403/5000000000 : ℝ)^133 ≤ (10972256303847/25000000000000 : ℝ)^101 := by
    have hnat : (2675319403 : ℕ)^133*25000000000000^101 ≤ 10972256303847^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675319403 5000000000 10972256303847 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5239815061/10000000000 : ℝ)^133 ≤ (10673979646227/25000000000000 : ℝ)^101 := by
    have hnat : (5239815061 : ℕ)^133*25000000000000^101 ≤ 10673979646227^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239815061 10000000000 10673979646227 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2175179259/10000000000 : ℝ)^133 ≤ (6707528095983/50000000000000 : ℝ)^101 := by
    have hnat : (2175179259 : ℕ)^133*50000000000000^101 ≤ 6707528095983^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175179259 10000000000 6707528095983 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675319403/5000000000 : ℝ), (5239815061/10000000000 : ℝ), (-2175179259/10000000000 : ℝ)] ![(10972256303847/25000000000000 : ℝ), (10673979646227/25000000000000 : ℝ), (6707528095983/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675319403/5000000000 : ℝ)|^133 ≤ (10972256303847/25000000000000 : ℝ)^101
        have hw : |(2675319403/5000000000 : ℝ)|=(2675319403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5239815061/10000000000 : ℝ)|^133 ≤ (10673979646227/25000000000000 : ℝ)^101
        have hw : |(5239815061/10000000000 : ℝ)|=(5239815061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2175179259/10000000000 : ℝ)|^133 ≤ (6707528095983/50000000000000 : ℝ)^101
        have hw : |(-2175179259/10000000000 : ℝ)|=(2175179259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s4_3 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (867708767/2000000000 : ℝ)*x 0 + (4158241203/10000000000 : ℝ)*x 1 + (2263146843/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (867708767/2000000000 : ℝ)^133 ≤ (16649955608967/50000000000000 : ℝ)^101 := by
    have hnat : (867708767 : ℕ)^133*50000000000000^101 ≤ 16649955608967^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      867708767 2000000000 16649955608967 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4158241203/10000000000 : ℝ)^133 ≤ (31489675775907/100000000000000 : ℝ)^101 := by
    have hnat : (4158241203 : ℕ)^133*100000000000000^101 ≤ 31489675775907^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4158241203 10000000000 31489675775907 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2263146843/5000000000 : ℝ)^133 ≤ (17605206494861/50000000000000 : ℝ)^101 := by
    have hnat : (2263146843 : ℕ)^133*50000000000000^101 ≤ 17605206494861^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2263146843 5000000000 17605206494861 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(867708767/2000000000 : ℝ), (4158241203/10000000000 : ℝ), (2263146843/5000000000 : ℝ)] ![(16649955608967/50000000000000 : ℝ), (31489675775907/100000000000000 : ℝ), (17605206494861/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(867708767/2000000000 : ℝ)|^133 ≤ (16649955608967/50000000000000 : ℝ)^101
        have hw : |(867708767/2000000000 : ℝ)|=(867708767/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4158241203/10000000000 : ℝ)|^133 ≤ (31489675775907/100000000000000 : ℝ)^101
        have hw : |(4158241203/10000000000 : ℝ)|=(4158241203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2263146843/5000000000 : ℝ)|^133 ≤ (17605206494861/50000000000000 : ℝ)^101
        have hw : |(2263146843/5000000000 : ℝ)|=(2263146843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s4_4 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-208398083/1000000000 : ℝ)*x 0 + (5240478679/10000000000 : ℝ)*x 1 + (541795597/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (208398083/1000000000 : ℝ)^133 ≤ (12679369859489/100000000000000 : ℝ)^101 := by
    have hnat : (208398083 : ℕ)^133*100000000000000^101 ≤ 12679369859489^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208398083 1000000000 12679369859489 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5240478679/10000000000 : ℝ)^133 ≤ (854060787289/2000000000000 : ℝ)^101 := by
    have hnat : (5240478679 : ℕ)^133*2000000000000^101 ≤ 854060787289^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240478679 10000000000 854060787289 2000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541795597/1000000000 : ℝ)^133 ≤ (44617590757397/100000000000000 : ℝ)^101 := by
    have hnat : (541795597 : ℕ)^133*100000000000000^101 ≤ 44617590757397^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541795597 1000000000 44617590757397 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-208398083/1000000000 : ℝ), (5240478679/10000000000 : ℝ), (541795597/1000000000 : ℝ)] ![(12679369859489/100000000000000 : ℝ), (854060787289/2000000000000 : ℝ), (44617590757397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-208398083/1000000000 : ℝ)|^133 ≤ (12679369859489/100000000000000 : ℝ)^101
        have hw : |(-208398083/1000000000 : ℝ)|=(208398083/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5240478679/10000000000 : ℝ)|^133 ≤ (854060787289/2000000000000 : ℝ)^101
        have hw : |(5240478679/10000000000 : ℝ)|=(5240478679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541795597/1000000000 : ℝ)|^133 ≤ (44617590757397/100000000000000 : ℝ)^101
        have hw : |(541795597/1000000000 : ℝ)|=(541795597/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s4_5 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (16577613/31250000 : ℝ)*x 0 + (-15601863/78125000 : ℝ)*x 1 + (2708977917/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16577613/31250000 : ℝ)^133 ≤ (43394964132409/100000000000000 : ℝ)^101 := by
    have hnat : (16577613 : ℕ)^133*100000000000000^101 ≤ 43394964132409^101*31250000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16577613 31250000 43394964132409 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (15601863/78125000 : ℝ)^133 ≤ (2996861643729/25000000000000 : ℝ)^101 := by
    have hnat : (15601863 : ℕ)^133*25000000000000^101 ≤ 2996861643729^101*78125000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15601863 78125000 2996861643729 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2708977917/5000000000 : ℝ)^133 ≤ (1784703571303/4000000000000 : ℝ)^101 := by
    have hnat : (2708977917 : ℕ)^133*4000000000000^101 ≤ 1784703571303^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708977917 5000000000 1784703571303 4000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16577613/31250000 : ℝ), (-15601863/78125000 : ℝ), (2708977917/5000000000 : ℝ)] ![(43394964132409/100000000000000 : ℝ), (2996861643729/25000000000000 : ℝ), (1784703571303/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16577613/31250000 : ℝ)|^133 ≤ (43394964132409/100000000000000 : ℝ)^101
        have hw : |(16577613/31250000 : ℝ)|=(16577613/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-15601863/78125000 : ℝ)|^133 ≤ (2996861643729/25000000000000 : ℝ)^101
        have hw : |(-15601863/78125000 : ℝ)|=(15601863/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2708977917/5000000000 : ℝ)|^133 ≤ (1784703571303/4000000000000 : ℝ)^101
        have hw : |(2708977917/5000000000 : ℝ)|=(2708977917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s4_6 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5304835801/10000000000 : ℝ)*x 0 + (2708978113/5000000000 : ℝ)*x 1 + (-998519207/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304835801/10000000000 : ℝ)^133 ≤ (173579841061/400000000000 : ℝ)^101 := by
    have hnat : (5304835801 : ℕ)^133*400000000000^101 ≤ 173579841061^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304835801 10000000000 173579841061 400000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2708978113/5000000000 : ℝ)^133 ≤ (22308796766767/50000000000000 : ℝ)^101 := by
    have hnat : (2708978113 : ℕ)^133*50000000000000^101 ≤ 22308796766767^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708978113 5000000000 22308796766767 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (998519207/5000000000 : ℝ)^133 ≤ (5993723089847/50000000000000 : ℝ)^101 := by
    have hnat : (998519207 : ℕ)^133*50000000000000^101 ≤ 5993723089847^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998519207 5000000000 5993723089847 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304835801/10000000000 : ℝ), (2708978113/5000000000 : ℝ), (-998519207/5000000000 : ℝ)] ![(173579841061/400000000000 : ℝ), (22308796766767/50000000000000 : ℝ), (5993723089847/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304835801/10000000000 : ℝ)|^133 ≤ (173579841061/400000000000 : ℝ)^101
        have hw : |(5304835801/10000000000 : ℝ)|=(5304835801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2708978113/5000000000 : ℝ)|^133 ≤ (22308796766767/50000000000000 : ℝ)^101
        have hw : |(2708978113/5000000000 : ℝ)|=(2708978113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-998519207/5000000000 : ℝ)|^133 ≤ (5993723089847/50000000000000 : ℝ)^101
        have hw : |(-998519207/5000000000 : ℝ)|=(998519207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s4_7 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4338573191/10000000000 : ℝ)*x 0 + (4524929111/10000000000 : ℝ)*x 1 + (83192261/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4338573191/10000000000 : ℝ)^133 ≤ (16650103962093/50000000000000 : ℝ)^101 := by
    have hnat : (4338573191 : ℕ)^133*50000000000000^101 ≤ 16650103962093^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4338573191 10000000000 16650103962093 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4524929111/10000000000 : ℝ)^133 ≤ (17598217651157/50000000000000 : ℝ)^101 := by
    have hnat : (4524929111 : ℕ)^133*50000000000000^101 ≤ 17598217651157^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4524929111 10000000000 17598217651157 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (83192261/200000000 : ℝ)^133 ≤ (31503356754141/100000000000000 : ℝ)^101 := by
    have hnat : (83192261 : ℕ)^133*100000000000000^101 ≤ 31503356754141^101*200000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83192261 200000000 31503356754141 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4338573191/10000000000 : ℝ), (4524929111/10000000000 : ℝ), (83192261/200000000 : ℝ)] ![(16650103962093/50000000000000 : ℝ), (17598217651157/50000000000000 : ℝ), (31503356754141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4338573191/10000000000 : ℝ)|^133 ≤ (16650103962093/50000000000000 : ℝ)^101
        have hw : |(4338573191/10000000000 : ℝ)|=(4338573191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4524929111/10000000000 : ℝ)|^133 ≤ (17598217651157/50000000000000 : ℝ)^101
        have hw : |(4524929111/10000000000 : ℝ)|=(4524929111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(83192261/200000000 : ℝ)|^133 ≤ (31503356754141/100000000000000 : ℝ)^101
        have hw : |(83192261/200000000 : ℝ)|=(83192261/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1296_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30583789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15061/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2669/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10967/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14751/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15061/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2669/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15061/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2669/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15061/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2669/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15061/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2669/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15061/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2669/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15061/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2669/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2669/25000 : ℝ) ^ (4255/1024 : ℝ) ≤ (9178504359357247/100000000000000000000 : ℝ) := by
    have hpowers : (2669/25000 : ℝ)^4255 ≤ (9178504359357247/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2669 : ℕ)^4255*100000000000000000000^1024 ≤ 9178504359357247^1024*25000^4255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2669 25000 9178504359357247 100000000000000000000 4255 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2669/25000 : ℝ)) (X := (9178504359357247/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15061/100000 : ℝ) ^ (4255/1024 : ℝ) ≤ (2396833058803841/6250000000000000000 : ℝ) := by
    have hpowers : (15061/100000 : ℝ)^4255 ≤ (2396833058803841/6250000000000000000 : ℝ)^1024 := by
      have hnat : (15061 : ℕ)^4255*6250000000000000000^1024 ≤ 2396833058803841^1024*100000^4255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15061 100000 2396833058803841 6250000000000000000 4255 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15061/100000 : ℝ)) (X := (2396833058803841/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009178504359357247/50000000000000000000 : ℝ) ≤ (10000441745404199/10000000000000000 : ℝ) ^ (4255/1024 : ℝ) := by
    have hpowers : (50009178504359357247/50000000000000000000 : ℝ)^1024 ≤ (10000441745404199/10000000000000000 : ℝ)^4255 := by
      have hnat : (50009178504359357247 : ℕ)^1024*10000000000000000^4255 ≤ 10000441745404199^4255*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009178504359357247 50000000000000000000 10000441745404199 10000000000000000 1024 4255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000441745404199/10000000000000000 : ℝ)) (X := (50009178504359357247/50000000000000000000 : ℝ)) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047527833300218703/100000000000000000000 : ℝ) ≤ (312535737163297/312500000000000 : ℝ) ^ (4255/1024 : ℝ) := by
    have hpowers : (100047527833300218703/100000000000000000000 : ℝ)^1024 ≤ (312535737163297/312500000000000 : ℝ)^4255 := by
      have hnat : (100047527833300218703 : ℕ)^1024*312500000000000^4255 ≤ 312535737163297^4255*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047527833300218703 100000000000000000000 312535737163297 312500000000000 1024 4255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312535737163297/312500000000000 : ℝ)) (X := (100047527833300218703/100000000000000000000 : ℝ)) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3127396833058803841/3125000000000000000 : ℝ) ≤ (10001845433046809/10000000000000000 : ℝ) ^ (4255/1024 : ℝ) := by
    have hpowers : (3127396833058803841/3125000000000000000 : ℝ)^1024 ≤ (10001845433046809/10000000000000000 : ℝ)^4255 := by
      have hnat : (3127396833058803841 : ℕ)^1024*10000000000000000^4255 ≤ 10001845433046809^4255*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127396833058803841 3125000000000000000 10001845433046809 10000000000000000 1024 4255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001845433046809/10000000000000000 : ℝ)) (X := (3127396833058803841/3125000000000000000 : ℝ)) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9178504359357247/100000000000000000000 : ℝ) ≤ ((8767390256864981651/8770000000000000000 : ℝ)+2*(140368764261/87700000000000 : ℝ)*(2669/25000 : ℝ))^(4255/1024 : ℝ) := by
    rw [show (8767390256864981651/8770000000000000000 : ℝ)+2*(140368764261/87700000000000 : ℝ)*(2669/25000 : ℝ)=(10000441745404199/10000000000000000 : ℝ) by norm_num, show 1+2*(9178504359357247/100000000000000000000 : ℝ)=(50009178504359357247/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2396833058803841/6250000000000000000 : ℝ)+(9178504359357247/100000000000000000000 : ℝ) ≤ ((8767390256864981651/8770000000000000000 : ℝ)+(140368764261/87700000000000 : ℝ)*((15061/100000 : ℝ)+(2669/25000 : ℝ)))^(4255/1024 : ℝ) := by
    rw [show (8767390256864981651/8770000000000000000 : ℝ)+(140368764261/87700000000000 : ℝ)*((15061/100000 : ℝ)+(2669/25000 : ℝ))=(312535737163297/312500000000000 : ℝ) by norm_num, show 1+(2396833058803841/6250000000000000000 : ℝ)+(9178504359357247/100000000000000000000 : ℝ)=(100047527833300218703/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2396833058803841/6250000000000000000 : ℝ) ≤ ((8767390256864981651/8770000000000000000 : ℝ)+2*(140368764261/87700000000000 : ℝ)*(15061/100000 : ℝ))^(4255/1024 : ℝ) := by
    rw [show (8767390256864981651/8770000000000000000 : ℝ)+2*(140368764261/87700000000000 : ℝ)*(15061/100000 : ℝ)=(10001845433046809/10000000000000000 : ℝ) by norm_num, show 1+2*(2396833058803841/6250000000000000000 : ℝ)=(3127396833058803841/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8767390256864981651/8770000000000000000 : ℝ)*(X 1 0+X 2 0)+(140368764261/87700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4255/1024 : ℝ)) (lo := (2669/25000 : ℝ)) (hi := (15061/100000 : ℝ)) (c := (8767390256864981651/8770000000000000000 : ℝ)) (alpha := (140368764261/87700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8767390256864981651/8770000000000000000 : ℝ)*(X 0 1+X 2 1)+(140368764261/87700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4255/1024 : ℝ)) (lo := (2669/25000 : ℝ)) (hi := (15061/100000 : ℝ)) (c := (8767390256864981651/8770000000000000000 : ℝ)) (alpha := (140368764261/87700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8767390256864981651/8770000000000000000 : ℝ)*(X 0 2+X 1 2)+(140368764261/87700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4255/1024 : ℝ)) (lo := (2669/25000 : ℝ)) (hi := (15061/100000 : ℝ)) (c := (8767390256864981651/8770000000000000000 : ℝ)) (alpha := (140368764261/87700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2083967047/10000000000 : ℝ)*X 0 0+(1354655541/2500000000 : ℝ)*X 0 1+(5239815683/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((133765963/250000000 : ℝ)*X 1 0+(-543794727/2500000000 : ℝ)*X 1 1+(2619907807/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675319403/5000000000 : ℝ)*X 2 0+(5239815061/10000000000 : ℝ)*X 2 1+(-2175179259/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((867708767/2000000000 : ℝ)*X 0 0+(4158241203/10000000000 : ℝ)*X 0 1+(2263146843/5000000000 : ℝ)*X 0 2+(867708767/2000000000 : ℝ)*X 1 0+(4158241203/10000000000 : ℝ)*X 1 1+(2263146843/5000000000 : ℝ)*X 1 2+(867708767/2000000000 : ℝ)*X 2 0+(4158241203/10000000000 : ℝ)*X 2 1+(2263146843/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-208398083/1000000000 : ℝ)*X 0 0+(5240478679/10000000000 : ℝ)*X 0 1+(541795597/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((16577613/31250000 : ℝ)*X 1 0+(-15601863/78125000 : ℝ)*X 1 1+(2708977917/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5304835801/10000000000 : ℝ)*X 2 0+(2708978113/5000000000 : ℝ)*X 2 1+(-998519207/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4338573191/10000000000 : ℝ)*X 0 0+(4524929111/10000000000 : ℝ)*X 0 1+(83192261/200000000 : ℝ)*X 0 2+(4338573191/10000000000 : ℝ)*X 1 0+(4524929111/10000000000 : ℝ)*X 1 1+(83192261/200000000 : ℝ)*X 1 2+(4338573191/10000000000 : ℝ)*X 2 0+(4524929111/10000000000 : ℝ)*X 2 1+(83192261/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (61398379308948904678698387/54812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (527542723/50000000000000 : ℝ)*(base19) + (1442558901/100000000000000 : ℝ)*(base23) + (159831657/100000000000000 : ℝ)*(upper2) + (287247187/100000000000000 : ℝ)*(upper3) + (112458859/100000000000000 : ℝ)*(upper4) + (519355779771407/12500000000000 : ℝ)*(major0) + (519355779771407/12500000000000 : ℝ)*(major1) + (519355779771407/12500000000000 : ℝ)*(major2) + (5592657358112197/100000000000000 : ℝ)*(sp0) + (2796333102766633/50000000000000 : ℝ)*(sp1) + (559266581805981/10000000000000 : ℝ)*(sp2) + (27170120669033/1000000000000 : ℝ)*(sp3) + (4951253257/50000000000000 : ℝ)*(sp4) + (1638935257/12500000000000 : ℝ)*(sp7) + (679256294596339/25000000000000 : ℝ)*(f.failure) + (5592667260618711/100000000000000 : ℝ)*(f.sum) + (25287460346771/4385000000000000000000000000 : ℝ)*base65 + (1432935484038402957/109625000000000000000000000000000 : ℝ)*base67 + (995518874916277957/109625000000000000000000000000000 : ℝ)*base69 + (1435021528735652957/109625000000000000000000000000000 : ℝ)*base71 + (2224925305859/1096250000000000000000000000 : ℝ)*base73 + (142763409133652957/109625000000000000000000000000000 : ℝ)*base75 + (907288912038152957/109625000000000000000000000000000 : ℝ)*base77 + (1751039926889402957/109625000000000000000000000000000 : ℝ)*base79 + (4717631112483/2192500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (7851529/500000000000000000000 : ℝ)*base90 + (7851529/500000000000000000000 : ℝ)*base92 + (7851529/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (101424645138737469195478191/10962500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (524086349/25000000000000 : ℝ)*(base19) + (93056537/5000000000000 : ℝ)*(base23) + (241341453/100000000000000 : ℝ)*(upper3) + (51806357/100000000000000 : ℝ)*(lower4) + (110549383/100000000000000 : ℝ)*(upper5) + (104648398860653/2500000000000 : ℝ)*(major0) + (104648398860653/2500000000000 : ℝ)*(major1) + (104648398860653/2500000000000 : ℝ)*(major2) + (18035900421/50000000000000 : ℝ)*(sp1) + (20840611427/50000000000000 : ℝ)*(sp2) + (5634515575386641/100000000000000 : ℝ)*(sp4) + (1408619351810101/25000000000000 : ℝ)*(sp5) + (704309004129131/12500000000000 : ℝ)*(sp6) + (1368678012533411/50000000000000 : ℝ)*(sp7) + (1368678012533411/50000000000000 : ℝ)*(f.failure) + (5634515575386641/100000000000000 : ℝ)*(f.sum) + (81863023751/43850000000000000000000000 : ℝ)*base65 + (137963200998253103/21925000000000000000000000000000 : ℝ)*base67 + (93945663544428103/21925000000000000000000000000000 : ℝ)*base69 + (263551157651328103/21925000000000000000000000000000 : ℝ)*base71 + (1978753447393/438500000000000000000000000 : ℝ)*base74 + (148063958807021897/21925000000000000000000000000000 : ℝ)*base76 + (47213207824228103/21925000000000000000000000000000 : ℝ)*base77 + (125576037940021897/21925000000000000000000000000000 : ℝ)*base80 + (372775112937/87700000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2525721/1000000000000000000000 : ℝ)*base90 + (2525721/1000000000000000000000 : ℝ)*base92 + (2525721/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1296_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30583789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15061/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2669/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10967/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14751/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1296_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1296_s5_0 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-260539337/1250000000 : ℝ)*x 0 + (5415663289/10000000000 : ℝ)*x 1 + (524254611/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (260539337/1250000000 : ℝ)^133 ≤ (12682044820359/100000000000000 : ℝ)^101 := by
    have hnat : (260539337 : ℕ)^133*100000000000000^101 ≤ 12682044820359^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260539337 1250000000 12682044820359 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415663289/10000000000 : ℝ)^133 ≤ (445927299387/1000000000000 : ℝ)^101 := by
    have hnat : (5415663289 : ℕ)^133*1000000000000^101 ≤ 445927299387^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415663289 10000000000 445927299387 1000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524254611/1000000000 : ℝ)^133 ≤ (2670326576497/6250000000000 : ℝ)^101 := by
    have hnat : (524254611 : ℕ)^133*6250000000000^101 ≤ 2670326576497^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524254611 1000000000 2670326576497 6250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-260539337/1250000000 : ℝ), (5415663289/10000000000 : ℝ), (524254611/1000000000 : ℝ)] ![(12682044820359/100000000000000 : ℝ), (445927299387/1000000000000 : ℝ), (2670326576497/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-260539337/1250000000 : ℝ)|^133 ≤ (12682044820359/100000000000000 : ℝ)^101
        have hw : |(-260539337/1250000000 : ℝ)|=(260539337/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415663289/10000000000 : ℝ)|^133 ≤ (445927299387/1000000000000 : ℝ)^101
        have hw : |(5415663289/10000000000 : ℝ)|=(5415663289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524254611/1000000000 : ℝ)|^133 ≤ (2670326576497/6250000000000 : ℝ)^101
        have hw : |(524254611/1000000000 : ℝ)|=(524254611/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s5_1 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2674943877/5000000000 : ℝ)*x 0 + (-2172569041/10000000000 : ℝ)*x 1 + (5242546113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674943877/5000000000 : ℝ)^133 ≤ (43880912973033/100000000000000 : ℝ)^101 := by
    have hnat : (2674943877 : ℕ)^133*100000000000000^101 ≤ 43880912973033^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674943877 5000000000 43880912973033 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2172569041/10000000000 : ℝ)^133 ≤ (6696930877093/50000000000000 : ℝ)^101 := by
    have hnat : (2172569041 : ℕ)^133*50000000000000^101 ≤ 6696930877093^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172569041 10000000000 6696930877093 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242546113/10000000000 : ℝ)^133 ≤ (42725225256147/100000000000000 : ℝ)^101 := by
    have hnat : (5242546113 : ℕ)^133*100000000000000^101 ≤ 42725225256147^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242546113 10000000000 42725225256147 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674943877/5000000000 : ℝ), (-2172569041/10000000000 : ℝ), (5242546113/10000000000 : ℝ)] ![(43880912973033/100000000000000 : ℝ), (6696930877093/50000000000000 : ℝ), (42725225256147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674943877/5000000000 : ℝ)|^133 ≤ (43880912973033/100000000000000 : ℝ)^101
        have hw : |(2674943877/5000000000 : ℝ)|=(2674943877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2172569041/10000000000 : ℝ)|^133 ≤ (6696930877093/50000000000000 : ℝ)^101
        have hw : |(-2172569041/10000000000 : ℝ)|=(2172569041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242546113/10000000000 : ℝ)|^133 ≤ (42725225256147/100000000000000 : ℝ)^101
        have hw : |(5242546113/10000000000 : ℝ)|=(5242546113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s5_2 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (21399551/40000000 : ℝ)*x 0 + (2621273057/5000000000 : ℝ)*x 1 + (-1086284523/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21399551/40000000 : ℝ)^133 ≤ (43880912929829/100000000000000 : ℝ)^101 := by
    have hnat : (21399551 : ℕ)^133*100000000000000^101 ≤ 43880912929829^101*40000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21399551 40000000 43880912929829 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621273057/5000000000 : ℝ)^133 ≤ (42725225266879/100000000000000 : ℝ)^101 := by
    have hnat : (2621273057 : ℕ)^133*100000000000000^101 ≤ 42725225266879^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621273057 5000000000 42725225266879 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086284523/5000000000 : ℝ)^133 ≤ (6696930897389/50000000000000 : ℝ)^101 := by
    have hnat : (1086284523 : ℕ)^133*50000000000000^101 ≤ 6696930897389^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086284523 5000000000 6696930897389 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21399551/40000000 : ℝ), (2621273057/5000000000 : ℝ), (-1086284523/5000000000 : ℝ)] ![(43880912929829/100000000000000 : ℝ), (42725225266879/100000000000000 : ℝ), (6696930897389/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21399551/40000000 : ℝ)|^133 ≤ (43880912929829/100000000000000 : ℝ)^101
        have hw : |(21399551/40000000 : ℝ)|=(21399551/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621273057/5000000000 : ℝ)|^133 ≤ (42725225266879/100000000000000 : ℝ)^101
        have hw : |(2621273057/5000000000 : ℝ)|=(2621273057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1086284523/5000000000 : ℝ)|^133 ≤ (6696930897389/50000000000000 : ℝ)^101
        have hw : |(-1086284523/5000000000 : ℝ)|=(1086284523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s5_3 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2169375423/5000000000 : ℝ)*x 0 + (1041017747/2500000000 : ℝ)*x 1 + (4520411743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2169375423/5000000000 : ℝ)^133 ≤ (33302003528071/100000000000000 : ℝ)^101 := by
    have hnat : (2169375423 : ℕ)^133*100000000000000^101 ≤ 33302003528071^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169375423 5000000000 33302003528071 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1041017747/2500000000 : ℝ)^133 ≤ (3154782417079/10000000000000 : ℝ)^101 := by
    have hnat : (1041017747 : ℕ)^133*10000000000000^101 ≤ 3154782417079^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041017747 2500000000 3154782417079 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4520411743/10000000000 : ℝ)^133 ≤ (35150172287219/100000000000000 : ℝ)^101 := by
    have hnat : (4520411743 : ℕ)^133*100000000000000^101 ≤ 35150172287219^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4520411743 10000000000 35150172287219 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2169375423/5000000000 : ℝ), (1041017747/2500000000 : ℝ), (4520411743/10000000000 : ℝ)] ![(33302003528071/100000000000000 : ℝ), (3154782417079/10000000000000 : ℝ), (35150172287219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2169375423/5000000000 : ℝ)|^133 ≤ (33302003528071/100000000000000 : ℝ)^101
        have hw : |(2169375423/5000000000 : ℝ)|=(2169375423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1041017747/2500000000 : ℝ)|^133 ≤ (3154782417079/10000000000000 : ℝ)^101
        have hw : |(1041017747/2500000000 : ℝ)|=(1041017747/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4520411743/10000000000 : ℝ)|^133 ≤ (35150172287219/100000000000000 : ℝ)^101
        have hw : |(4520411743/10000000000 : ℝ)|=(4520411743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s5_4 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2084326973/10000000000 : ℝ)*x 0 + (2621583991/5000000000 : ℝ)*x 1 + (541503869/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2084326973/10000000000 : ℝ)^133 ≤ (3170535796811/25000000000000 : ℝ)^101 := by
    have hnat : (2084326973 : ℕ)^133*25000000000000^101 ≤ 3170535796811^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084326973 10000000000 3170535796811 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621583991/5000000000 : ℝ)^133 ≤ (667685924253/1562500000000 : ℝ)^101 := by
    have hnat : (2621583991 : ℕ)^133*1562500000000^101 ≤ 667685924253^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621583991 5000000000 667685924253 1562500000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541503869/1000000000 : ℝ)^133 ≤ (44585957641289/100000000000000 : ℝ)^101 := by
    have hnat : (541503869 : ℕ)^133*100000000000000^101 ≤ 44585957641289^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541503869 1000000000 44585957641289 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2084326973/10000000000 : ℝ), (2621583991/5000000000 : ℝ), (541503869/1000000000 : ℝ)] ![(3170535796811/25000000000000 : ℝ), (667685924253/1562500000000 : ℝ), (44585957641289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2084326973/10000000000 : ℝ)|^133 ≤ (3170535796811/25000000000000 : ℝ)^101
        have hw : |(-2084326973/10000000000 : ℝ)|=(2084326973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621583991/5000000000 : ℝ)|^133 ≤ (667685924253/1562500000000 : ℝ)^101
        have hw : |(2621583991/5000000000 : ℝ)|=(2621583991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541503869/1000000000 : ℝ)|^133 ≤ (44585957641289/100000000000000 : ℝ)^101
        have hw : |(541503869/1000000000 : ℝ)|=(541503869/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s5_5 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1326385793/2500000000 : ℝ)*x 0 + (-2000076911/10000000000 : ℝ)*x 1 + (2707519001/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326385793/2500000000 : ℝ)^133 ≤ (1356330632779/3125000000000 : ℝ)^101 := by
    have hnat : (1326385793 : ℕ)^133*3125000000000^101 ≤ 1356330632779^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326385793 2500000000 1356330632779 3125000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2000076911/10000000000 : ℝ)^133 ≤ (6005734775663/50000000000000 : ℝ)^101 := by
    have hnat : (2000076911 : ℕ)^133*50000000000000^101 ≤ 6005734775663^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2000076911 10000000000 6005734775663 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707519001/5000000000 : ℝ)^133 ≤ (22292975090847/50000000000000 : ℝ)^101 := by
    have hnat : (2707519001 : ℕ)^133*50000000000000^101 ≤ 22292975090847^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707519001 5000000000 22292975090847 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326385793/2500000000 : ℝ), (-2000076911/10000000000 : ℝ), (2707519001/5000000000 : ℝ)] ![(1356330632779/3125000000000 : ℝ), (6005734775663/50000000000000 : ℝ), (22292975090847/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326385793/2500000000 : ℝ)|^133 ≤ (1356330632779/3125000000000 : ℝ)^101
        have hw : |(1326385793/2500000000 : ℝ)|=(1326385793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2000076911/10000000000 : ℝ)|^133 ≤ (6005734775663/50000000000000 : ℝ)^101
        have hw : |(-2000076911/10000000000 : ℝ)|=(2000076911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707519001/5000000000 : ℝ)|^133 ≤ (22292975090847/50000000000000 : ℝ)^101
        have hw : |(2707519001/5000000000 : ℝ)|=(2707519001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s5_6 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5305543131/10000000000 : ℝ)*x 0 + (10576247/19531250 : ℝ)*x 1 + (-1000038167/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305543131/10000000000 : ℝ)^133 ≤ (5425322475907/12500000000000 : ℝ)^101 := by
    have hnat : (5305543131 : ℕ)^133*12500000000000^101 ≤ 5425322475907^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305543131 10000000000 5425322475907 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10576247/19531250 : ℝ)^133 ≤ (22292977595449/50000000000000 : ℝ)^101 := by
    have hnat : (10576247 : ℕ)^133*50000000000000^101 ≤ 22292977595449^101*19531250^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10576247 19531250 22292977595449 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1000038167/5000000000 : ℝ)^133 ≤ (12011464988273/100000000000000 : ℝ)^101 := by
    have hnat : (1000038167 : ℕ)^133*100000000000000^101 ≤ 12011464988273^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000038167 5000000000 12011464988273 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305543131/10000000000 : ℝ), (10576247/19531250 : ℝ), (-1000038167/5000000000 : ℝ)] ![(5425322475907/12500000000000 : ℝ), (22292977595449/50000000000000 : ℝ), (12011464988273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305543131/10000000000 : ℝ)|^133 ≤ (5425322475907/12500000000000 : ℝ)^101
        have hw : |(5305543131/10000000000 : ℝ)|=(5305543131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(10576247/19531250 : ℝ)|^133 ≤ (22292977595449/50000000000000 : ℝ)^101
        have hw : |(10576247/19531250 : ℝ)|=(10576247/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1000038167/5000000000 : ℝ)|^133 ≤ (12011464988273/100000000000000 : ℝ)^101
        have hw : |(-1000038167/5000000000 : ℝ)|=(1000038167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1296_s5_7 (p : ℝ) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (867755389/2000000000 : ℝ)*x 0 + (4519132749/10000000000 : ℝ)*x 1 + (4165357129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (867755389/2000000000 : ℝ)^133 ≤ (4162783414901/12500000000000 : ℝ)^101 := by
    have hnat : (867755389 : ℕ)^133*12500000000000^101 ≤ 4162783414901^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      867755389 2000000000 4162783414901 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4519132749/10000000000 : ℝ)^133 ≤ (35137076585627/100000000000000 : ℝ)^101 := by
    have hnat : (4519132749 : ℕ)^133*100000000000000^101 ≤ 35137076585627^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4519132749 10000000000 35137076585627 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4165357129/10000000000 : ℝ)^133 ≤ (15780328041577/50000000000000 : ℝ)^101 := by
    have hnat : (4165357129 : ℕ)^133*50000000000000^101 ≤ 15780328041577^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4165357129 10000000000 15780328041577 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(867755389/2000000000 : ℝ), (4519132749/10000000000 : ℝ), (4165357129/10000000000 : ℝ)] ![(4162783414901/12500000000000 : ℝ), (35137076585627/100000000000000 : ℝ), (15780328041577/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(867755389/2000000000 : ℝ)|^133 ≤ (4162783414901/12500000000000 : ℝ)^101
        have hw : |(867755389/2000000000 : ℝ)|=(867755389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4519132749/10000000000 : ℝ)|^133 ≤ (35137076585627/100000000000000 : ℝ)^101
        have hw : |(4519132749/10000000000 : ℝ)|=(4519132749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4165357129/10000000000 : ℝ)|^133 ≤ (15780328041577/50000000000000 : ℝ)^101
        have hw : |(4165357129/10000000000 : ℝ)|=(4165357129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1296_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30583789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14751/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10967/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (441/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14689/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14751/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10967/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14751/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10967/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14751/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10967/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14751/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10967/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14751/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10967/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14751/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10967/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10967/100000 : ℝ) ^ (4255/1024 : ℝ) ≤ (5131833033582397/50000000000000000000 : ℝ) := by
    have hpowers : (10967/100000 : ℝ)^4255 ≤ (5131833033582397/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10967 : ℕ)^4255*50000000000000000000^1024 ≤ 5131833033582397^1024*100000^4255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10967 100000 5131833033582397 50000000000000000000 4255 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10967/100000 : ℝ)) (X := (5131833033582397/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14751/100000 : ℝ) ^ (4255/1024 : ℝ) ≤ (35174335642904307/100000000000000000000 : ℝ) := by
    have hpowers : (14751/100000 : ℝ)^4255 ≤ (35174335642904307/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14751 : ℕ)^4255*100000000000000000000^1024 ≤ 35174335642904307^1024*100000^4255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14751 100000 35174335642904307 100000000000000000000 4255 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14751/100000 : ℝ)) (X := (35174335642904307/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005131833033582397/25000000000000000000 : ℝ) ≤ (1250061746034319/1250000000000000 : ℝ) ^ (4255/1024 : ℝ) := by
    have hpowers : (25005131833033582397/25000000000000000000 : ℝ)^1024 ≤ (1250061746034319/1250000000000000 : ℝ)^4255 := by
      have hnat : (25005131833033582397 : ℕ)^1024*1250000000000000^4255 ≤ 1250061746034319^4255*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005131833033582397 25000000000000000000 1250061746034319 1250000000000000 1024 4255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250061746034319/1250000000000000 : ℝ)) (X := (25005131833033582397/25000000000000000000 : ℝ)) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045438001710069101/100000000000000000000 : ℝ) ≤ (10001093313490653/10000000000000000 : ℝ) ^ (4255/1024 : ℝ) := by
    have hpowers : (100045438001710069101/100000000000000000000 : ℝ)^1024 ≤ (10001093313490653/10000000000000000 : ℝ)^4255 := by
      have hnat : (100045438001710069101 : ℕ)^1024*10000000000000000^4255 ≤ 10001093313490653^4255*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045438001710069101 100000000000000000000 10001093313490653 10000000000000000 1024 4255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001093313490653/10000000000000000 : ℝ)) (X := (100045438001710069101/100000000000000000000 : ℝ)) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035174335642904307/50000000000000000000 : ℝ) ≤ (5000846329353377/5000000000000000 : ℝ) ^ (4255/1024 : ℝ) := by
    have hpowers : (50035174335642904307/50000000000000000000 : ℝ)^1024 ≤ (5000846329353377/5000000000000000 : ℝ)^4255 := by
      have hnat : (50035174335642904307 : ℕ)^1024*5000000000000000^4255 ≤ 5000846329353377^4255*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035174335642904307 50000000000000000000 5000846329353377 5000000000000000 1024 4255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000846329353377/5000000000000000 : ℝ)) (X := (50035174335642904307/50000000000000000000 : ℝ)) (by norm_num) 4255 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5131833033582397/50000000000000000000 : ℝ) ≤ ((1719487415362770247/1720000000000000000 : ℝ)+2*(599345216101/378400000000000 : ℝ)*(10967/100000 : ℝ))^(4255/1024 : ℝ) := by
    rw [show (1719487415362770247/1720000000000000000 : ℝ)+2*(599345216101/378400000000000 : ℝ)*(10967/100000 : ℝ)=(1250061746034319/1250000000000000 : ℝ) by norm_num, show 1+2*(5131833033582397/50000000000000000000 : ℝ)=(25005131833033582397/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35174335642904307/100000000000000000000 : ℝ)+(5131833033582397/50000000000000000000 : ℝ) ≤ ((1719487415362770247/1720000000000000000 : ℝ)+(599345216101/378400000000000 : ℝ)*((14751/100000 : ℝ)+(10967/100000 : ℝ)))^(4255/1024 : ℝ) := by
    rw [show (1719487415362770247/1720000000000000000 : ℝ)+(599345216101/378400000000000 : ℝ)*((14751/100000 : ℝ)+(10967/100000 : ℝ))=(10001093313490653/10000000000000000 : ℝ) by norm_num, show 1+(35174335642904307/100000000000000000000 : ℝ)+(5131833033582397/50000000000000000000 : ℝ)=(100045438001710069101/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35174335642904307/100000000000000000000 : ℝ) ≤ ((1719487415362770247/1720000000000000000 : ℝ)+2*(599345216101/378400000000000 : ℝ)*(14751/100000 : ℝ))^(4255/1024 : ℝ) := by
    rw [show (1719487415362770247/1720000000000000000 : ℝ)+2*(599345216101/378400000000000 : ℝ)*(14751/100000 : ℝ)=(5000846329353377/5000000000000000 : ℝ) by norm_num, show 1+2*(35174335642904307/100000000000000000000 : ℝ)=(50035174335642904307/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1719487415362770247/1720000000000000000 : ℝ)*(X 1 0+X 2 0)+(599345216101/378400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4255/1024 : ℝ)) (lo := (10967/100000 : ℝ)) (hi := (14751/100000 : ℝ)) (c := (1719487415362770247/1720000000000000000 : ℝ)) (alpha := (599345216101/378400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1719487415362770247/1720000000000000000 : ℝ)*(X 0 1+X 2 1)+(599345216101/378400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4255/1024 : ℝ)) (lo := (10967/100000 : ℝ)) (hi := (14751/100000 : ℝ)) (c := (1719487415362770247/1720000000000000000 : ℝ)) (alpha := (599345216101/378400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1719487415362770247/1720000000000000000 : ℝ)*(X 0 2+X 1 2)+(599345216101/378400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4255/1024 : ℝ)) (lo := (10967/100000 : ℝ)) (hi := (14751/100000 : ℝ)) (c := (1719487415362770247/1720000000000000000 : ℝ)) (alpha := (599345216101/378400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-260539337/1250000000 : ℝ)*X 0 0+(5415663289/10000000000 : ℝ)*X 0 1+(524254611/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674943877/5000000000 : ℝ)*X 1 0+(-2172569041/10000000000 : ℝ)*X 1 1+(5242546113/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((21399551/40000000 : ℝ)*X 2 0+(2621273057/5000000000 : ℝ)*X 2 1+(-1086284523/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2169375423/5000000000 : ℝ)*X 0 0+(1041017747/2500000000 : ℝ)*X 0 1+(4520411743/10000000000 : ℝ)*X 0 2+(2169375423/5000000000 : ℝ)*X 1 0+(1041017747/2500000000 : ℝ)*X 1 1+(4520411743/10000000000 : ℝ)*X 1 2+(2169375423/5000000000 : ℝ)*X 2 0+(1041017747/2500000000 : ℝ)*X 2 1+(4520411743/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2084326973/10000000000 : ℝ)*X 0 0+(2621583991/5000000000 : ℝ)*X 0 1+(541503869/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326385793/2500000000 : ℝ)*X 1 0+(-2000076911/10000000000 : ℝ)*X 1 1+(2707519001/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305543131/10000000000 : ℝ)*X 2 0+(10576247/19531250 : ℝ)*X 2 1+(-1000038167/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((867755389/2000000000 : ℝ)*X 0 0+(4519132749/10000000000 : ℝ)*X 0 1+(4165357129/10000000000 : ℝ)*X 0 2+(867755389/2000000000 : ℝ)*X 1 0+(4519132749/10000000000 : ℝ)*X 1 1+(4165357129/10000000000 : ℝ)*X 1 2+(867755389/2000000000 : ℝ)*X 2 0+(4519132749/10000000000 : ℝ)*X 2 1+(4165357129/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1296_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (597501787083442217730677763/94600000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (59069709/5000000000000 : ℝ)*(base19) + (1096614611/100000000000000 : ℝ)*(base23) + (21522763/50000000000000 : ℝ)*(lower2) + (79371441/50000000000000 : ℝ)*(upper3) + (92651521/100000000000000 : ℝ)*(upper5) + (429140451242729/10000000000000 : ℝ)*(major0) + (429140451242729/10000000000000 : ℝ)*(major1) + (429140451242729/10000000000000 : ℝ)*(major2) + (5776459071585789/100000000000000 : ℝ)*(sp0) + (288824068568477/5000000000000 : ℝ)*(sp1) + (5776481456149109/100000000000000 : ℝ)*(sp2) + (701578443836773/25000000000000 : ℝ)*(sp3) + (23481177931/100000000000000 : ℝ)*(sp4) + (12486207543/100000000000000 : ℝ)*(sp7) + (701581565388659/25000000000000 : ℝ)*(f.failure) + (144412063819093/2500000000000 : ℝ)*(f.sum) + (13402151239309/1892000000000000000000000000 : ℝ)*base65 + (493793846553374693/189200000000000000000000000000000 : ℝ)*base67 + (257197597296974693/189200000000000000000000000000000 : ℝ)*base69 + (348932627972174693/189200000000000000000000000000000 : ℝ)*base71 + (3079335851633/1892000000000000000000000000 : ℝ)*base73 + (518063371168974693/189200000000000000000000000000000 : ℝ)*base75 + (1832657647144174693/189200000000000000000000000000000 : ℝ)*base77 + (3364543011313774693/189200000000000000000000000000000 : ℝ)*base79 + (4445836696359/1892000000000000000000000000 : ℝ)*base82 + (151049/500000000000000000000 : ℝ)*base90 + (151049/500000000000000000000 : ℝ)*base92 + (151049/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4478542007155417251629073399/473000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (849275963/100000000000000 : ℝ)*(base19) + (755678593/50000000000000 : ℝ)*(base23) + (34674997/100000000000000 : ℝ)*(lower2) + (2727639/25000000000000 : ℝ)*(lower3) + (33048599/12500000000000 : ℝ)*(lower4) + (28225069/20000000000000 : ℝ)*(lower5) + (2161242697394683/50000000000000 : ℝ)*(major0) + (2161242697394683/50000000000000 : ℝ)*(major1) + (2161242697394683/50000000000000 : ℝ)*(major2) + (32791207801/100000000000000 : ℝ)*(sp2) + (5818319142576619/100000000000000 : ℝ)*(sp4) + (363644893331291/6250000000000 : ℝ)*(sp5) + (5818284840011631/100000000000000 : ℝ)*(sp6) + (1413325665694779/50000000000000 : ℝ)*(sp7) + (1413325665694779/50000000000000 : ℝ)*(f.failure) + (5818319142576619/100000000000000 : ℝ)*(f.sum) + (109544456986597/9460000000000000000000000000 : ℝ)*base66 + (13770867784758486289/946000000000000000000000000000000 : ℝ)*base68 + (12050661660990486289/946000000000000000000000000000000 : ℝ)*base70 + (1393321806290486289/946000000000000000000000000000000 : ℝ)*base72 + (24556858047023/9460000000000000000000000000 : ℝ)*base73 + (17799636292082486289/946000000000000000000000000000000 : ℝ)*base76 + (26275556412024486289/946000000000000000000000000000000 : ℝ)*base78 + (1329829973798486289/946000000000000000000000000000000 : ℝ)*base80 + (2400443622737/9460000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (662369/1000000000000000000000 : ℝ)*base90 + (662369/1000000000000000000000 : ℝ)*base92 + (662369/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1296_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30583789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14751/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10967/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (441/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14689/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1296_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1296_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30583789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16299/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4767/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (441/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14689/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1296_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1296_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1296_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4255/1024 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30583789/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16299/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4767/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (441/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14689/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1296_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
