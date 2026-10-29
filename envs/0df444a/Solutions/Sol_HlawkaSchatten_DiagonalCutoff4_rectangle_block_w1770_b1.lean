-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1770_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:34:02.927051+00:00
-- url     : https://prove2.me/submissions/caa2feb1-d414-49e0-b763-f08c91e470cb

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
theorem support_rectangle_w1770_s3_0 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-279799413/2500000000 : ℝ)*x 0 + (5471392583/10000000000 : ℝ)*x 1 + (5085783351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (279799413/2500000000 : ℝ)^6095 ≤ (719200707493/10000000000000 : ℝ)^5071 := by
    have hnat : (279799413 : ℕ)^6095*10000000000000^5071 ≤ 719200707493^5071*2500000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279799413 2500000000 719200707493 10000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5471392583/10000000000 : ℝ)^6095 ≤ (1937632022189/4000000000000 : ℝ)^5071 := by
    have hnat : (5471392583 : ℕ)^6095*4000000000000^5071 ≤ 1937632022189^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5471392583 10000000000 1937632022189 4000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5085783351/10000000000 : ℝ)^6095 ≤ (44367192350521/100000000000000 : ℝ)^5071 := by
    have hnat : (5085783351 : ℕ)^6095*100000000000000^5071 ≤ 44367192350521^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5085783351 10000000000 44367192350521 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-279799413/2500000000 : ℝ), (5471392583/10000000000 : ℝ), (5085783351/10000000000 : ℝ)] ![(719200707493/10000000000000 : ℝ), (1937632022189/4000000000000 : ℝ), (44367192350521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-279799413/2500000000 : ℝ)|^6095 ≤ (719200707493/10000000000000 : ℝ)^5071
        have hw : |(-279799413/2500000000 : ℝ)|=(279799413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5471392583/10000000000 : ℝ)|^6095 ≤ (1937632022189/4000000000000 : ℝ)^5071
        have hw : |(5471392583/10000000000 : ℝ)|=(5471392583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5085783351/10000000000 : ℝ)|^6095 ≤ (44367192350521/100000000000000 : ℝ)^5071
        have hw : |(5085783351/10000000000 : ℝ)|=(5085783351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1770_s3_1 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2661257971/5000000000 : ℝ)*x 0 + (-1320258717/10000000000 : ℝ)*x 1 + (5085783731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2661257971/5000000000 : ℝ)^6095 ≤ (23430474010071/50000000000000 : ℝ)^5071 := by
    have hnat : (2661257971 : ℕ)^6095*50000000000000^5071 ≤ 23430474010071^5071*5000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2661257971 5000000000 23430474010071 50000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1320258717/10000000000 : ℝ)^6095 ≤ (8771855627767/100000000000000 : ℝ)^5071 := by
    have hnat : (1320258717 : ℕ)^6095*100000000000000^5071 ≤ 8771855627767^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320258717 10000000000 8771855627767 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5085783731/10000000000 : ℝ)^6095 ≤ (22183598167483/50000000000000 : ℝ)^5071 := by
    have hnat : (5085783731 : ℕ)^6095*50000000000000^5071 ≤ 22183598167483^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5085783731 10000000000 22183598167483 50000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2661257971/5000000000 : ℝ), (-1320258717/10000000000 : ℝ), (5085783731/10000000000 : ℝ)] ![(23430474010071/50000000000000 : ℝ), (8771855627767/100000000000000 : ℝ), (22183598167483/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2661257971/5000000000 : ℝ)|^6095 ≤ (23430474010071/50000000000000 : ℝ)^5071
        have hw : |(2661257971/5000000000 : ℝ)|=(2661257971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1320258717/10000000000 : ℝ)|^6095 ≤ (8771855627767/100000000000000 : ℝ)^5071
        have hw : |(-1320258717/10000000000 : ℝ)|=(1320258717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5085783731/10000000000 : ℝ)|^6095 ≤ (22183598167483/50000000000000 : ℝ)^5071
        have hw : |(5085783731/10000000000 : ℝ)|=(5085783731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1770_s3_2 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5322515317/10000000000 : ℝ)*x 0 + (5085783767/10000000000 : ℝ)*x 1 + (-1320259499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5322515317/10000000000 : ℝ)^6095 ≤ (46860941406293/100000000000000 : ℝ)^5071 := by
    have hnat : (5322515317 : ℕ)^6095*100000000000000^5071 ≤ 46860941406293^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5322515317 10000000000 46860941406293 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5085783767/10000000000 : ℝ)^6095 ≤ (44367196712439/100000000000000 : ℝ)^5071 := by
    have hnat : (5085783767 : ℕ)^6095*100000000000000^5071 ≤ 44367196712439^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5085783767 10000000000 44367196712439 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1320259499/10000000000 : ℝ)^6095 ≤ (4385930936289/50000000000000 : ℝ)^5071 := by
    have hnat : (1320259499 : ℕ)^6095*50000000000000^5071 ≤ 4385930936289^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320259499 10000000000 4385930936289 50000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5322515317/10000000000 : ℝ), (5085783767/10000000000 : ℝ), (-1320259499/10000000000 : ℝ)] ![(46860941406293/100000000000000 : ℝ), (44367196712439/100000000000000 : ℝ), (4385930936289/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5322515317/10000000000 : ℝ)|^6095 ≤ (46860941406293/100000000000000 : ℝ)^5071
        have hw : |(5322515317/10000000000 : ℝ)|=(5322515317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5085783767/10000000000 : ℝ)|^6095 ≤ (44367196712439/100000000000000 : ℝ)^5071
        have hw : |(5085783767/10000000000 : ℝ)|=(5085783767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1320259499/10000000000 : ℝ)|^6095 ≤ (4385930936289/50000000000000 : ℝ)^5071
        have hw : |(-1320259499/10000000000 : ℝ)|=(1320259499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1770_s3_3 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1990765989/5000000000 : ℝ)*x 0 + (3325499941/10000000000 : ℝ)*x 1 + (939254699/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1990765989/5000000000 : ℝ)^6095 ≤ (3305881816629/10000000000000 : ℝ)^5071 := by
    have hnat : (1990765989 : ℕ)^6095*10000000000000^5071 ≤ 3305881816629^5071*5000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1990765989 5000000000 3305881816629 10000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3325499941/10000000000 : ℝ)^6095 ≤ (6656474965483/25000000000000 : ℝ)^5071 := by
    have hnat : (3325499941 : ℕ)^6095*25000000000000^5071 ≤ 6656474965483^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3325499941 10000000000 6656474965483 25000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (939254699/2000000000 : ℝ)^6095 ≤ (20157640975357/50000000000000 : ℝ)^5071 := by
    have hnat : (939254699 : ℕ)^6095*50000000000000^5071 ≤ 20157640975357^5071*2000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      939254699 2000000000 20157640975357 50000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1990765989/5000000000 : ℝ), (3325499941/10000000000 : ℝ), (939254699/2000000000 : ℝ)] ![(3305881816629/10000000000000 : ℝ), (6656474965483/25000000000000 : ℝ), (20157640975357/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1990765989/5000000000 : ℝ)|^6095 ≤ (3305881816629/10000000000000 : ℝ)^5071
        have hw : |(1990765989/5000000000 : ℝ)|=(1990765989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3325499941/10000000000 : ℝ)|^6095 ≤ (6656474965483/25000000000000 : ℝ)^5071
        have hw : |(3325499941/10000000000 : ℝ)|=(3325499941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(939254699/2000000000 : ℝ)|^6095 ≤ (20157640975357/50000000000000 : ℝ)^5071
        have hw : |(939254699/2000000000 : ℝ)|=(939254699/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1770_s3_4 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-55975551/500000000 : ℝ)*x 0 + (5092256803/10000000000 : ℝ)*x 1 + (1366196221/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (55975551/500000000 : ℝ)^6095 ≤ (1798606873181/25000000000000 : ℝ)^5071 := by
    have hnat : (55975551 : ℕ)^6095*25000000000000^5071 ≤ 1798606873181^5071*500000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55975551 500000000 1798606873181 25000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5092256803/10000000000 : ℝ)^6095 ≤ (5554384709669/12500000000000 : ℝ)^5071 := by
    have hnat : (5092256803 : ℕ)^6095*12500000000000^5071 ≤ 5554384709669^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5092256803 10000000000 5554384709669 12500000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1366196221/2500000000 : ℝ)^6095 ≤ (48370494810587/100000000000000 : ℝ)^5071 := by
    have hnat : (1366196221 : ℕ)^6095*100000000000000^5071 ≤ 48370494810587^5071*2500000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366196221 2500000000 48370494810587 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-55975551/500000000 : ℝ), (5092256803/10000000000 : ℝ), (1366196221/2500000000 : ℝ)] ![(1798606873181/25000000000000 : ℝ), (5554384709669/12500000000000 : ℝ), (48370494810587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-55975551/500000000 : ℝ)|^6095 ≤ (1798606873181/25000000000000 : ℝ)^5071
        have hw : |(-55975551/500000000 : ℝ)|=(55975551/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5092256803/10000000000 : ℝ)|^6095 ≤ (5554384709669/12500000000000 : ℝ)^5071
        have hw : |(5092256803/10000000000 : ℝ)|=(5092256803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1366196221/2500000000 : ℝ)|^6095 ≤ (48370494810587/100000000000000 : ℝ)^5071
        have hw : |(1366196221/2500000000 : ℝ)|=(1366196221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1770_s3_5 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (652625073/1250000000 : ℝ)*x 0 + (1366196219/2500000000 : ℝ)*x 1 + (-235314517/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (652625073/1250000000 : ℝ)^6095 ≤ (45788775853191/100000000000000 : ℝ)^5071 := by
    have hnat : (652625073 : ℕ)^6095*100000000000000^5071 ≤ 45788775853191^5071*1250000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652625073 1250000000 45788775853191 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1366196219/2500000000 : ℝ)^6095 ≤ (24185247362739/50000000000000 : ℝ)^5071 := by
    have hnat : (1366196219 : ℕ)^6095*50000000000000^5071 ≤ 24185247362739^5071*2500000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366196219 2500000000 24185247362739 50000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (235314517/2500000000 : ℝ)^6095 ≤ (1168145882989/20000000000000 : ℝ)^5071 := by
    have hnat : (235314517 : ℕ)^6095*20000000000000^5071 ≤ 1168145882989^5071*2500000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235314517 2500000000 1168145882989 20000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(652625073/1250000000 : ℝ), (1366196219/2500000000 : ℝ), (-235314517/2500000000 : ℝ)] ![(45788775853191/100000000000000 : ℝ), (24185247362739/50000000000000 : ℝ), (1168145882989/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(652625073/1250000000 : ℝ)|^6095 ≤ (45788775853191/100000000000000 : ℝ)^5071
        have hw : |(652625073/1250000000 : ℝ)|=(652625073/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1366196219/2500000000 : ℝ)|^6095 ≤ (24185247362739/50000000000000 : ℝ)^5071
        have hw : |(1366196219/2500000000 : ℝ)|=(1366196219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-235314517/2500000000 : ℝ)|^6095 ≤ (1168145882989/20000000000000 : ℝ)^5071
        have hw : |(-235314517/2500000000 : ℝ)|=(235314517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1770_s3_6 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1991323369/5000000000 : ℝ)*x 0 + (4673261503/10000000000 : ℝ)*x 1 + (1674494001/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1991323369/5000000000 : ℝ)^6095 ≤ (16534971722091/50000000000000 : ℝ)^5071 := by
    have hnat : (1991323369 : ℕ)^6095*50000000000000^5071 ≤ 16534971722091^5071*5000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1991323369 5000000000 16534971722091 50000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4673261503/10000000000 : ℝ)^6095 ≤ (10019490337703/25000000000000 : ℝ)^5071 := by
    have hnat : (4673261503 : ℕ)^6095*25000000000000^5071 ≤ 10019490337703^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4673261503 10000000000 10019490337703 25000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1674494001/5000000000 : ℝ)^6095 ≤ (26852095190871/100000000000000 : ℝ)^5071 := by
    have hnat : (1674494001 : ℕ)^6095*100000000000000^5071 ≤ 26852095190871^5071*5000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1674494001 5000000000 26852095190871 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1991323369/5000000000 : ℝ), (4673261503/10000000000 : ℝ), (1674494001/5000000000 : ℝ)] ![(16534971722091/50000000000000 : ℝ), (10019490337703/25000000000000 : ℝ), (26852095190871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1991323369/5000000000 : ℝ)|^6095 ≤ (16534971722091/50000000000000 : ℝ)^5071
        have hw : |(1991323369/5000000000 : ℝ)|=(1991323369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4673261503/10000000000 : ℝ)|^6095 ≤ (10019490337703/25000000000000 : ℝ)^5071
        have hw : |(4673261503/10000000000 : ℝ)|=(4673261503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1674494001/5000000000 : ℝ)|^6095 ≤ (26852095190871/100000000000000 : ℝ)^5071
        have hw : |(1674494001/5000000000 : ℝ)|=(1674494001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1770_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (227741437/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2199/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9249/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (37/400 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2199/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2199/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9249/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2199/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9249/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2199/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9249/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2199/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9249/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2199/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9249/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2199/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9249/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9249/100000 : ℝ) ^ (6079/1024 : ℝ) ≤ (9101384016699/12500000000000000000 : ℝ) := by
    have hpowers : (9249/100000 : ℝ)^6079 ≤ (9101384016699/12500000000000000000 : ℝ)^1024 := by
      have hnat : (9249 : ℕ)^6079*12500000000000000000^1024 ≤ 9101384016699^1024*100000^6079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9249 100000 9101384016699 12500000000000000000 6079 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9249/100000 : ℝ)) (X := (9101384016699/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 6079 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2199/12500 : ℝ) ^ (6079/1024 : ℝ) ≤ (3309756882625581/100000000000000000000 : ℝ) := by
    have hpowers : (2199/12500 : ℝ)^6079 ≤ (3309756882625581/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2199 : ℕ)^6079*100000000000000000000^1024 ≤ 3309756882625581^1024*12500^6079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2199 12500 3309756882625581 100000000000000000000 6079 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2199/12500 : ℝ)) (X := (3309756882625581/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6079 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250009101384016699/6250000000000000000 : ℝ) ≤ (200000049059709/200000000000000 : ℝ) ^ (6079/1024 : ℝ) := by
    have hpowers : (6250009101384016699/6250000000000000000 : ℝ)^1024 ≤ (200000049059709/200000000000000 : ℝ)^6079 := by
      have hnat : (6250009101384016699 : ℕ)^1024*200000000000000^6079 ≤ 200000049059709^6079*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250009101384016699 6250000000000000000 200000049059709 200000000000000 1024 6079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200000049059709/200000000000000 : ℝ)) (X := (6250009101384016699/6250000000000000000 : ℝ)) (by norm_num) 6079 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100003382567954759173/100000000000000000000 : ℝ) ≤ (10000056978135761/10000000000000000 : ℝ) ^ (6079/1024 : ℝ) := by
    have hpowers : (100003382567954759173/100000000000000000000 : ℝ)^1024 ≤ (10000056978135761/10000000000000000 : ℝ)^6079 := by
      have hnat : (100003382567954759173 : ℕ)^1024*10000000000000000^6079 ≤ 10000056978135761^6079*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100003382567954759173 100000000000000000000 10000056978135761 10000000000000000 1024 6079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000056978135761/10000000000000000 : ℝ)) (X := (100003382567954759173/100000000000000000000 : ℝ)) (by norm_num) 6079 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50003309756882625581/50000000000000000000 : ℝ) ≤ (1250013937910759/1250000000000000 : ℝ) ^ (6079/1024 : ℝ) := by
    have hpowers : (50003309756882625581/50000000000000000000 : ℝ)^1024 ≤ (1250013937910759/1250000000000000 : ℝ)^6079 := by
      have hnat : (50003309756882625581 : ℕ)^1024*1250000000000000^6079 ≤ 1250013937910759^6079*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50003309756882625581 50000000000000000000 1250013937910759 1250000000000000 1024 6079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250013937910759/1250000000000000 : ℝ)) (X := (50003309756882625581/50000000000000000000 : ℝ)) (by norm_num) 6079 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9101384016699/12500000000000000000 : ℝ) ≤ ((3476208827459464853/3476250000000000000 : ℝ)+2*(54525150311/834300000000000 : ℝ)*(9249/100000 : ℝ))^(6079/1024 : ℝ) := by
    rw [show (3476208827459464853/3476250000000000000 : ℝ)+2*(54525150311/834300000000000 : ℝ)*(9249/100000 : ℝ)=(200000049059709/200000000000000 : ℝ) by norm_num, show 1+2*(9101384016699/12500000000000000000 : ℝ)=(6250009101384016699/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3309756882625581/100000000000000000000 : ℝ)+(9101384016699/12500000000000000000 : ℝ) ≤ ((3476208827459464853/3476250000000000000 : ℝ)+(54525150311/834300000000000 : ℝ)*((2199/12500 : ℝ)+(9249/100000 : ℝ)))^(6079/1024 : ℝ) := by
    rw [show (3476208827459464853/3476250000000000000 : ℝ)+(54525150311/834300000000000 : ℝ)*((2199/12500 : ℝ)+(9249/100000 : ℝ))=(10000056978135761/10000000000000000 : ℝ) by norm_num, show 1+(3309756882625581/100000000000000000000 : ℝ)+(9101384016699/12500000000000000000 : ℝ)=(100003382567954759173/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3309756882625581/100000000000000000000 : ℝ) ≤ ((3476208827459464853/3476250000000000000 : ℝ)+2*(54525150311/834300000000000 : ℝ)*(2199/12500 : ℝ))^(6079/1024 : ℝ) := by
    rw [show (3476208827459464853/3476250000000000000 : ℝ)+2*(54525150311/834300000000000 : ℝ)*(2199/12500 : ℝ)=(1250013937910759/1250000000000000 : ℝ) by norm_num, show 1+2*(3309756882625581/100000000000000000000 : ℝ)=(50003309756882625581/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3476208827459464853/3476250000000000000 : ℝ)*(X 1 0+X 2 0)+(54525150311/834300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6079/1024 : ℝ)) (lo := (9249/100000 : ℝ)) (hi := (2199/12500 : ℝ)) (c := (3476208827459464853/3476250000000000000 : ℝ)) (alpha := (54525150311/834300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3476208827459464853/3476250000000000000 : ℝ)*(X 0 1+X 2 1)+(54525150311/834300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6079/1024 : ℝ)) (lo := (9249/100000 : ℝ)) (hi := (2199/12500 : ℝ)) (c := (3476208827459464853/3476250000000000000 : ℝ)) (alpha := (54525150311/834300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3476208827459464853/3476250000000000000 : ℝ)*(X 0 2+X 1 2)+(54525150311/834300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6079/1024 : ℝ)) (lo := (9249/100000 : ℝ)) (hi := (2199/12500 : ℝ)) (c := (3476208827459464853/3476250000000000000 : ℝ)) (alpha := (54525150311/834300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-279799413/2500000000 : ℝ)*X 0 0+(5471392583/10000000000 : ℝ)*X 0 1+(5085783351/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2661257971/5000000000 : ℝ)*X 1 0+(-1320258717/10000000000 : ℝ)*X 1 1+(5085783731/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5322515317/10000000000 : ℝ)*X 2 0+(5085783767/10000000000 : ℝ)*X 2 1+(-1320259499/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1990765989/5000000000 : ℝ)*X 0 0+(3325499941/10000000000 : ℝ)*X 0 1+(939254699/2000000000 : ℝ)*X 0 2+(1990765989/5000000000 : ℝ)*X 1 0+(3325499941/10000000000 : ℝ)*X 1 1+(939254699/2000000000 : ℝ)*X 1 2+(1990765989/5000000000 : ℝ)*X 2 0+(3325499941/10000000000 : ℝ)*X 2 1+(939254699/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-55975551/500000000 : ℝ)*X 0 0+(5092256803/10000000000 : ℝ)*X 0 1+(1366196221/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((652625073/1250000000 : ℝ)*X 2 0+(1366196219/2500000000 : ℝ)*X 2 1+(-235314517/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_s3_5 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1991323369/5000000000 : ℝ)*X 0 0+(4673261503/10000000000 : ℝ)*X 0 1+(1674494001/5000000000 : ℝ)*X 0 2+(1991323369/5000000000 : ℝ)*X 1 0+(4673261503/10000000000 : ℝ)*X 1 1+(1674494001/5000000000 : ℝ)*X 1 2+(1991323369/5000000000 : ℝ)*X 2 0+(4673261503/10000000000 : ℝ)*X 2 1+(1674494001/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_s3_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (223062599768626991401265459/43453125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (736475491/100000000000000 : ℝ)*(base19) + (430562391/100000000000000 : ℝ)*(base23) + (118033/312500000000 : ℝ)*(upper2) + (125314901/100000000000000 : ℝ)*(upper3) + (415355012824637/25000000000000 : ℝ)*(major0) + (415355012824637/25000000000000 : ℝ)*(major1) + (415355012824637/25000000000000 : ℝ)*(major2) + (2593310772288721/100000000000000 : ℝ)*(sp0) + (1296659439408899/50000000000000 : ℝ)*(sp1) + (518663078221909/20000000000000 : ℝ)*(sp2) + (145903512923633/20000000000000 : ℝ)*(sp3) + (1105375571/12500000000000 : ℝ)*(sp4) + (3793621353/100000000000000 : ℝ)*(sp5) + (1375786027/50000000000000 : ℝ)*(sp6) + (729520316190219/100000000000000 : ℝ)*(f.failure) + (2593319615293289/100000000000000 : ℝ)*(f.sum) + (84093362113561/20857500000000000000000000000 : ℝ)*base66 + (1794207915676350083/260718750000000000000000000000000 : ℝ)*base67 + (782340433346475083/260718750000000000000000000000000 : ℝ)*base69 + (478652894177850083/260718750000000000000000000000000 : ℝ)*base71 + (4372023139187/41715000000000000000000000000 : ℝ)*base74 + (1875948654497568833/260718750000000000000000000000000 : ℝ)*base75 + (148880242757868667/260718750000000000000000000000000 : ℝ)*base78 + (528996972519225083/260718750000000000000000000000000 : ℝ)*base79 + (17422014686183/10428750000000000000000000000 : ℝ)*base82 + (40404703/10000000000000000000000 : ℝ)*base89 + (40404703/10000000000000000000000 : ℝ)*base91 + (40404703/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1770_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (227741437/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2199/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9249/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (37/400 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2199/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1770_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1770_box_0 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-76301333/1000000000 : ℝ)*x 0 + (270230053/500000000 : ℝ)*x 1 + (5404599479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (76301333/1000000000 : ℝ)^6095 ≤ (4538151385449/100000000000000 : ℝ)^5071 := by
    have hnat : (76301333 : ℕ)^6095*100000000000000^5071 ≤ 4538151385449^5071*1000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76301333 1000000000 4538151385449 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270230053/500000000 : ℝ)^6095 ≤ (23865466345023/50000000000000 : ℝ)^5071 := by
    have hnat : (270230053 : ℕ)^6095*50000000000000^5071 ≤ 23865466345023^5071*500000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270230053 500000000 23865466345023 50000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5404599479/10000000000 : ℝ)^6095 ≤ (47730915907871/100000000000000 : ℝ)^5071 := by
    have hnat : (5404599479 : ℕ)^6095*100000000000000^5071 ≤ 47730915907871^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404599479 10000000000 47730915907871 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-76301333/1000000000 : ℝ), (270230053/500000000 : ℝ), (5404599479/10000000000 : ℝ)] ![(4538151385449/100000000000000 : ℝ), (23865466345023/50000000000000 : ℝ), (47730915907871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-76301333/1000000000 : ℝ)|^6095 ≤ (4538151385449/100000000000000 : ℝ)^5071
        have hw : |(-76301333/1000000000 : ℝ)|=(76301333/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270230053/500000000 : ℝ)|^6095 ≤ (23865466345023/50000000000000 : ℝ)^5071
        have hw : |(270230053/500000000 : ℝ)|=(270230053/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5404599479/10000000000 : ℝ)|^6095 ≤ (47730915907871/100000000000000 : ℝ)^5071
        have hw : |(5404599479/10000000000 : ℝ)|=(5404599479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1770_box_1 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1297957351/2500000000 : ℝ)*x 0 + (-1066588051/10000000000 : ℝ)*x 1 + (5404600339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1297957351/2500000000 : ℝ)^6095 ≤ (22740726818563/50000000000000 : ℝ)^5071 := by
    have hnat : (1297957351 : ℕ)^6095*50000000000000^5071 ≤ 22740726818563^5071*2500000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1297957351 2500000000 22740726818563 50000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1066588051/10000000000 : ℝ)^6095 ≤ (424226331741/6250000000000 : ℝ)^5071 := by
    have hnat : (1066588051 : ℕ)^6095*6250000000000^5071 ≤ 424226331741^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066588051 10000000000 424226331741 6250000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5404600339/10000000000 : ℝ)^6095 ≤ (9546185007339/20000000000000 : ℝ)^5071 := by
    have hnat : (5404600339 : ℕ)^6095*20000000000000^5071 ≤ 9546185007339^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404600339 10000000000 9546185007339 20000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1297957351/2500000000 : ℝ), (-1066588051/10000000000 : ℝ), (5404600339/10000000000 : ℝ)] ![(22740726818563/50000000000000 : ℝ), (424226331741/6250000000000 : ℝ), (9546185007339/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1297957351/2500000000 : ℝ)|^6095 ≤ (22740726818563/50000000000000 : ℝ)^5071
        have hw : |(1297957351/2500000000 : ℝ)|=(1297957351/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1066588051/10000000000 : ℝ)|^6095 ≤ (424226331741/6250000000000 : ℝ)^5071
        have hw : |(-1066588051/10000000000 : ℝ)|=(1066588051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5404600339/10000000000 : ℝ)|^6095 ≤ (9546185007339/20000000000000 : ℝ)^5071
        have hw : |(5404600339/10000000000 : ℝ)|=(5404600339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1770_box_2 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5191829567/10000000000 : ℝ)*x 0 + (5404600157/10000000000 : ℝ)*x 1 + (-13332351/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5191829567/10000000000 : ℝ)^6095 ≤ (45481455353381/100000000000000 : ℝ)^5071 := by
    have hnat : (5191829567 : ℕ)^6095*100000000000000^5071 ≤ 45481455353381^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5191829567 10000000000 45481455353381 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5404600157/10000000000 : ℝ)^6095 ≤ (47730923104781/100000000000000 : ℝ)^5071 := by
    have hnat : (5404600157 : ℕ)^6095*100000000000000^5071 ≤ 47730923104781^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404600157 10000000000 47730923104781 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13332351/125000000 : ℝ)^6095 ≤ (271504861187/4000000000000 : ℝ)^5071 := by
    have hnat : (13332351 : ℕ)^6095*4000000000000^5071 ≤ 271504861187^5071*125000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13332351 125000000 271504861187 4000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5191829567/10000000000 : ℝ), (5404600157/10000000000 : ℝ), (-13332351/125000000 : ℝ)] ![(45481455353381/100000000000000 : ℝ), (47730923104781/100000000000000 : ℝ), (271504861187/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5191829567/10000000000 : ℝ)|^6095 ≤ (45481455353381/100000000000000 : ℝ)^5071
        have hw : |(5191829567/10000000000 : ℝ)|=(5191829567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5404600157/10000000000 : ℝ)|^6095 ≤ (47730923104781/100000000000000 : ℝ)^5071
        have hw : |(5404600157/10000000000 : ℝ)|=(5404600157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-13332351/125000000 : ℝ)|^6095 ≤ (271504861187/4000000000000 : ℝ)^5071
        have hw : |(-13332351/125000000 : ℝ)|=(13332351/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1770_box_3 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4505094441/10000000000 : ℝ)*x 0 + (3756345517/10000000000 : ℝ)*x 1 + (3756345073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4505094441/10000000000 : ℝ)^6095 ≤ (38350889589629/100000000000000 : ℝ)^5071 := by
    have hnat : (4505094441 : ℕ)^6095*100000000000000^5071 ≤ 38350889589629^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505094441 10000000000 38350889589629 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3756345517/10000000000 : ℝ)^6095 ≤ (3082455738653/10000000000000 : ℝ)^5071 := by
    have hnat : (3756345517 : ℕ)^6095*10000000000000^5071 ≤ 3082455738653^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3756345517 10000000000 3082455738653 10000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3756345073/10000000000 : ℝ)^6095 ≤ (6164910601467/20000000000000 : ℝ)^5071 := by
    have hnat : (3756345073 : ℕ)^6095*20000000000000^5071 ≤ 6164910601467^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3756345073 10000000000 6164910601467 20000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4505094441/10000000000 : ℝ), (3756345517/10000000000 : ℝ), (3756345073/10000000000 : ℝ)] ![(38350889589629/100000000000000 : ℝ), (3082455738653/10000000000000 : ℝ), (6164910601467/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4505094441/10000000000 : ℝ)|^6095 ≤ (38350889589629/100000000000000 : ℝ)^5071
        have hw : |(4505094441/10000000000 : ℝ)|=(4505094441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3756345517/10000000000 : ℝ)|^6095 ≤ (3082455738653/10000000000000 : ℝ)^5071
        have hw : |(3756345517/10000000000 : ℝ)|=(3756345517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3756345073/10000000000 : ℝ)|^6095 ≤ (6164910601467/20000000000000 : ℝ)^5071
        have hw : |(3756345073/10000000000 : ℝ)|=(3756345073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1770_box_4 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-756869629/5000000000 : ℝ)*x 0 + (2564966531/5000000000 : ℝ)*x 1 + (5129932733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (756869629/5000000000 : ℝ)^6095 ≤ (5169478040941/50000000000000 : ℝ)^5071 := by
    have hnat : (756869629 : ℕ)^6095*50000000000000^5071 ≤ 5169478040941^5071*5000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      756869629 5000000000 5169478040941 50000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2564966531/5000000000 : ℝ)^6095 ≤ (22415261840329/50000000000000 : ℝ)^5071 := by
    have hnat : (2564966531 : ℕ)^6095*50000000000000^5071 ≤ 22415261840329^5071*5000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2564966531 5000000000 22415261840329 50000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5129932733/10000000000 : ℝ)^6095 ≤ (44830520224941/100000000000000 : ℝ)^5071 := by
    have hnat : (5129932733 : ℕ)^6095*100000000000000^5071 ≤ 44830520224941^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129932733 10000000000 44830520224941 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-756869629/5000000000 : ℝ), (2564966531/5000000000 : ℝ), (5129932733/10000000000 : ℝ)] ![(5169478040941/50000000000000 : ℝ), (22415261840329/50000000000000 : ℝ), (44830520224941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-756869629/5000000000 : ℝ)|^6095 ≤ (5169478040941/50000000000000 : ℝ)^5071
        have hw : |(-756869629/5000000000 : ℝ)|=(756869629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2564966531/5000000000 : ℝ)|^6095 ≤ (22415261840329/50000000000000 : ℝ)^5071
        have hw : |(2564966531/5000000000 : ℝ)|=(2564966531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5129932733/10000000000 : ℝ)|^6095 ≤ (44830520224941/100000000000000 : ℝ)^5071
        have hw : |(5129932733/10000000000 : ℝ)|=(5129932733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1770_box_5 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (214968081/400000000 : ℝ)*x 0 + (-1192396573/10000000000 : ℝ)*x 1 + (2564966621/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214968081/400000000 : ℝ)^6095 ≤ (47408433150351/100000000000000 : ℝ)^5071 := by
    have hnat : (214968081 : ℕ)^6095*100000000000000^5071 ≤ 47408433150351^5071*400000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214968081 400000000 47408433150351 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1192396573/10000000000 : ℝ)^6095 ≤ (1940260317249/25000000000000 : ℝ)^5071 := by
    have hnat : (1192396573 : ℕ)^6095*25000000000000^5071 ≤ 1940260317249^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1192396573 10000000000 1940260317249 25000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2564966621/5000000000 : ℝ)^6095 ≤ (44830525571323/100000000000000 : ℝ)^5071 := by
    have hnat : (2564966621 : ℕ)^6095*100000000000000^5071 ≤ 44830525571323^5071*5000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2564966621 5000000000 44830525571323 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214968081/400000000 : ℝ), (-1192396573/10000000000 : ℝ), (2564966621/5000000000 : ℝ)] ![(47408433150351/100000000000000 : ℝ), (1940260317249/25000000000000 : ℝ), (44830525571323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214968081/400000000 : ℝ)|^6095 ≤ (47408433150351/100000000000000 : ℝ)^5071
        have hw : |(214968081/400000000 : ℝ)|=(214968081/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1192396573/10000000000 : ℝ)|^6095 ≤ (1940260317249/25000000000000 : ℝ)^5071
        have hw : |(-1192396573/10000000000 : ℝ)|=(1192396573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2564966621/5000000000 : ℝ)|^6095 ≤ (44830525571323/100000000000000 : ℝ)^5071
        have hw : |(2564966621/5000000000 : ℝ)|=(2564966621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1770_box_6 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (537420247/1000000000 : ℝ)*x 0 + (320620801/625000000 : ℝ)*x 1 + (-1192396541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537420247/1000000000 : ℝ)^6095 ≤ (47408437868609/100000000000000 : ℝ)^5071 := by
    have hnat : (537420247 : ℕ)^6095*100000000000000^5071 ≤ 47408437868609^5071*1000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537420247 1000000000 47408437868609 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (320620801/625000000 : ℝ)^6095 ≤ (11207630274187/25000000000000 : ℝ)^5071 := by
    have hnat : (320620801 : ℕ)^6095*25000000000000^5071 ≤ 11207630274187^5071*625000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      320620801 625000000 11207630274187 25000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1192396541/10000000000 : ℝ)^6095 ≤ (242532531833/3125000000000 : ℝ)^5071 := by
    have hnat : (1192396541 : ℕ)^6095*3125000000000^5071 ≤ 242532531833^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1192396541 10000000000 242532531833 3125000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537420247/1000000000 : ℝ), (320620801/625000000 : ℝ), (-1192396541/10000000000 : ℝ)] ![(47408437868609/100000000000000 : ℝ), (11207630274187/25000000000000 : ℝ), (242532531833/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537420247/1000000000 : ℝ)|^6095 ≤ (47408437868609/100000000000000 : ℝ)^5071
        have hw : |(537420247/1000000000 : ℝ)|=(537420247/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(320620801/625000000 : ℝ)|^6095 ≤ (11207630274187/25000000000000 : ℝ)^5071
        have hw : |(320620801/625000000 : ℝ)|=(320620801/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1192396541/10000000000 : ℝ)|^6095 ≤ (242532531833/3125000000000 : ℝ)^5071
        have hw : |(-1192396541/10000000000 : ℝ)|=(1192396541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1770_box_7 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1709017351/5000000000 : ℝ)*x 0 + (859573557/2000000000 : ℝ)*x 1 + (859573547/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1709017351/5000000000 : ℝ)^6095 ≤ (5503776036279/20000000000000 : ℝ)^5071 := by
    have hnat : (1709017351 : ℕ)^6095*20000000000000^5071 ≤ 5503776036279^5071*5000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1709017351 5000000000 5503776036279 20000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (859573557/2000000000 : ℝ)^6095 ≤ (18120280078893/50000000000000 : ℝ)^5071 := by
    have hnat : (859573557 : ℕ)^6095*50000000000000^5071 ≤ 18120280078893^5071*2000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859573557 2000000000 18120280078893 50000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (859573547/2000000000 : ℝ)^6095 ≤ (18120279825519/50000000000000 : ℝ)^5071 := by
    have hnat : (859573547 : ℕ)^6095*50000000000000^5071 ≤ 18120279825519^5071*2000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859573547 2000000000 18120279825519 50000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1709017351/5000000000 : ℝ), (859573557/2000000000 : ℝ), (859573547/2000000000 : ℝ)] ![(5503776036279/20000000000000 : ℝ), (18120280078893/50000000000000 : ℝ), (18120279825519/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1709017351/5000000000 : ℝ)|^6095 ≤ (5503776036279/20000000000000 : ℝ)^5071
        have hw : |(1709017351/5000000000 : ℝ)|=(1709017351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(859573557/2000000000 : ℝ)|^6095 ≤ (18120280078893/50000000000000 : ℝ)^5071
        have hw : |(859573557/2000000000 : ℝ)|=(859573557/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(859573547/2000000000 : ℝ)|^6095 ≤ (18120279825519/50000000000000 : ℝ)^5071
        have hw : |(859573547/2000000000 : ℝ)|=(859573547/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1770_box_8 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1350079859/10000000000 : ℝ)*x 0 + (307432919/625000000 : ℝ)*x 1 + (2732180171/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1350079859/10000000000 : ℝ)^6095 ≤ (2252634484207/25000000000000 : ℝ)^5071 := by
    have hnat : (1350079859 : ℕ)^6095*25000000000000^5071 ≤ 2252634484207^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350079859 10000000000 2252634484207 25000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (307432919/625000000 : ℝ)^6095 ≤ (42623483763023/100000000000000 : ℝ)^5071 := by
    have hnat : (307432919 : ℕ)^6095*100000000000000^5071 ≤ 42623483763023^5071*625000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      307432919 625000000 42623483763023 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2732180171/5000000000 : ℝ)^6095 ≤ (48365978281481/100000000000000 : ℝ)^5071 := by
    have hnat : (2732180171 : ℕ)^6095*100000000000000^5071 ≤ 48365978281481^5071*5000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732180171 5000000000 48365978281481 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1350079859/10000000000 : ℝ), (307432919/625000000 : ℝ), (2732180171/5000000000 : ℝ)] ![(2252634484207/25000000000000 : ℝ), (42623483763023/100000000000000 : ℝ), (48365978281481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1350079859/10000000000 : ℝ)|^6095 ≤ (2252634484207/25000000000000 : ℝ)^5071
        have hw : |(-1350079859/10000000000 : ℝ)|=(1350079859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(307432919/625000000 : ℝ)|^6095 ≤ (42623483763023/100000000000000 : ℝ)^5071
        have hw : |(307432919/625000000 : ℝ)|=(307432919/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2732180171/5000000000 : ℝ)|^6095 ≤ (48365978281481/100000000000000 : ℝ)^5071
        have hw : |(2732180171/5000000000 : ℝ)|=(2732180171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1770_box_9 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2576115939/5000000000 : ℝ)*x 0 + (-1037950853/10000000000 : ℝ)*x 1 + (2732180171/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2576115939/5000000000 : ℝ)^6095 ≤ (45064846378497/100000000000000 : ℝ)^5071 := by
    have hnat : (2576115939 : ℕ)^6095*100000000000000^5071 ≤ 45064846378497^5071*5000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2576115939 5000000000 45064846378497 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1037950853/10000000000 : ℝ)^6095 ≤ (3284587663603/50000000000000 : ℝ)^5071 := by
    have hnat : (1037950853 : ℕ)^6095*50000000000000^5071 ≤ 3284587663603^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037950853 10000000000 3284587663603 50000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2732180171/5000000000 : ℝ)^6095 ≤ (48365978281481/100000000000000 : ℝ)^5071 := by
    have hnat : (2732180171 : ℕ)^6095*100000000000000^5071 ≤ 48365978281481^5071*5000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732180171 5000000000 48365978281481 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2576115939/5000000000 : ℝ), (-1037950853/10000000000 : ℝ), (2732180171/5000000000 : ℝ)] ![(45064846378497/100000000000000 : ℝ), (3284587663603/50000000000000 : ℝ), (48365978281481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2576115939/5000000000 : ℝ)|^6095 ≤ (45064846378497/100000000000000 : ℝ)^5071
        have hw : |(2576115939/5000000000 : ℝ)|=(2576115939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1037950853/10000000000 : ℝ)|^6095 ≤ (3284587663603/50000000000000 : ℝ)^5071
        have hw : |(-1037950853/10000000000 : ℝ)|=(1037950853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2732180171/5000000000 : ℝ)|^6095 ≤ (48365978281481/100000000000000 : ℝ)^5071
        have hw : |(2732180171/5000000000 : ℝ)|=(2732180171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1770_box_10 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (515223147/1000000000 : ℝ)*x 0 + (5464360379/10000000000 : ℝ)*x 1 + (-259487841/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (515223147/1000000000 : ℝ)^6095 ≤ (45064842089233/100000000000000 : ℝ)^5071 := by
    have hnat : (515223147 : ℕ)^6095*100000000000000^5071 ≤ 45064842089233^5071*1000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515223147 1000000000 45064842089233 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5464360379/10000000000 : ℝ)^6095 ≤ (24182989337553/50000000000000 : ℝ)^5071 := by
    have hnat : (5464360379 : ℕ)^6095*50000000000000^5071 ≤ 24182989337553^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5464360379 10000000000 24182989337553 50000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (259487841/2500000000 : ℝ)^6095 ≤ (656917921439/10000000000000 : ℝ)^5071 := by
    have hnat : (259487841 : ℕ)^6095*10000000000000^5071 ≤ 656917921439^5071*2500000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259487841 2500000000 656917921439 10000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(515223147/1000000000 : ℝ), (5464360379/10000000000 : ℝ), (-259487841/2500000000 : ℝ)] ![(45064842089233/100000000000000 : ℝ), (24182989337553/50000000000000 : ℝ), (656917921439/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(515223147/1000000000 : ℝ)|^6095 ≤ (45064842089233/100000000000000 : ℝ)^5071
        have hw : |(515223147/1000000000 : ℝ)|=(515223147/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5464360379/10000000000 : ℝ)|^6095 ≤ (24182989337553/50000000000000 : ℝ)^5071
        have hw : |(5464360379/10000000000 : ℝ)|=(5464360379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-259487841/2500000000 : ℝ)|^6095 ≤ (656917921439/10000000000000 : ℝ)^5071
        have hw : |(-259487841/2500000000 : ℝ)|=(259487841/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1770_box_11 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (295701517/625000000 : ℝ)*x 0 + (3638087861/10000000000 : ℝ)*x 1 + (3638087381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (295701517/625000000 : ℝ)^6095 ≤ (10169043813731/25000000000000 : ℝ)^5071 := by
    have hnat : (295701517 : ℕ)^6095*25000000000000^5071 ≤ 10169043813731^5071*625000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      295701517 625000000 10169043813731 25000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3638087861/10000000000 : ℝ)^6095 ≤ (29661914720243/100000000000000 : ℝ)^5071 := by
    have hnat : (3638087861 : ℕ)^6095*100000000000000^5071 ≤ 29661914720243^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3638087861 10000000000 29661914720243 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3638087381/10000000000 : ℝ)^6095 ≤ (29661910016459/100000000000000 : ℝ)^5071 := by
    have hnat : (3638087381 : ℕ)^6095*100000000000000^5071 ≤ 29661910016459^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3638087381 10000000000 29661910016459 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(295701517/625000000 : ℝ), (3638087861/10000000000 : ℝ), (3638087381/10000000000 : ℝ)] ![(10169043813731/25000000000000 : ℝ), (29661914720243/100000000000000 : ℝ), (29661910016459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(295701517/625000000 : ℝ)|^6095 ≤ (10169043813731/25000000000000 : ℝ)^5071
        have hw : |(295701517/625000000 : ℝ)|=(295701517/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3638087861/10000000000 : ℝ)|^6095 ≤ (29661914720243/100000000000000 : ℝ)^5071
        have hw : |(3638087861/10000000000 : ℝ)|=(3638087861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3638087381/10000000000 : ℝ)|^6095 ≤ (29661910016459/100000000000000 : ℝ)^5071
        have hw : |(3638087381/10000000000 : ℝ)|=(3638087381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1770_box_12 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-911999809/10000000000 : ℝ)*x 0 + (1400988773/2500000000 : ℝ)*x 1 + (5100536801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (911999809/10000000000 : ℝ)^6095 ≤ (224928153511/4000000000000 : ℝ)^5071 := by
    have hnat : (911999809 : ℕ)^6095*4000000000000^5071 ≤ 224928153511^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      911999809 10000000000 224928153511 4000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1400988773/2500000000 : ℝ)^6095 ≤ (9970972596777/20000000000000 : ℝ)^5071 := by
    have hnat : (1400988773 : ℕ)^6095*20000000000000^5071 ≤ 9970972596777^5071*2500000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1400988773 2500000000 9970972596777 20000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5100536801/10000000000 : ℝ)^6095 ≤ (44521933160369/100000000000000 : ℝ)^5071 := by
    have hnat : (5100536801 : ℕ)^6095*100000000000000^5071 ≤ 44521933160369^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5100536801 10000000000 44521933160369 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-911999809/10000000000 : ℝ), (1400988773/2500000000 : ℝ), (5100536801/10000000000 : ℝ)] ![(224928153511/4000000000000 : ℝ), (9970972596777/20000000000000 : ℝ), (44521933160369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-911999809/10000000000 : ℝ)|^6095 ≤ (224928153511/4000000000000 : ℝ)^5071
        have hw : |(-911999809/10000000000 : ℝ)|=(911999809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1400988773/2500000000 : ℝ)|^6095 ≤ (9970972596777/20000000000000 : ℝ)^5071
        have hw : |(1400988773/2500000000 : ℝ)|=(1400988773/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5100536801/10000000000 : ℝ)|^6095 ≤ (44521933160369/100000000000000 : ℝ)^5071
        have hw : |(5100536801/10000000000 : ℝ)|=(5100536801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1770_box_13 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (33711233/62500000 : ℝ)*x 0 + (-602630979/5000000000 : ℝ)*x 1 + (5100536251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33711233/62500000 : ℝ)^6095 ≤ (47616274679917/100000000000000 : ℝ)^5071 := by
    have hnat : (33711233 : ℕ)^6095*100000000000000^5071 ≤ 47616274679917^5071*62500000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33711233 62500000 47616274679917 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (602630979/5000000000 : ℝ)^6095 ≤ (982724738247/12500000000000 : ℝ)^5071 := by
    have hnat : (602630979 : ℕ)^6095*12500000000000^5071 ≤ 982724738247^5071*5000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      602630979 5000000000 982724738247 12500000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5100536251/10000000000 : ℝ)^6095 ≤ (11130481847509/25000000000000 : ℝ)^5071 := by
    have hnat : (5100536251 : ℕ)^6095*25000000000000^5071 ≤ 11130481847509^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5100536251 10000000000 11130481847509 25000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33711233/62500000 : ℝ), (-602630979/5000000000 : ℝ), (5100536251/10000000000 : ℝ)] ![(47616274679917/100000000000000 : ℝ), (982724738247/12500000000000 : ℝ), (11130481847509/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33711233/62500000 : ℝ)|^6095 ≤ (47616274679917/100000000000000 : ℝ)^5071
        have hw : |(33711233/62500000 : ℝ)|=(33711233/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-602630979/5000000000 : ℝ)|^6095 ≤ (982724738247/12500000000000 : ℝ)^5071
        have hw : |(-602630979/5000000000 : ℝ)|=(602630979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5100536251/10000000000 : ℝ)|^6095 ≤ (11130481847509/25000000000000 : ℝ)^5071
        have hw : |(5100536251/10000000000 : ℝ)|=(5100536251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1770_box_14 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2696898619/5000000000 : ℝ)*x 0 + (1020107121/2000000000 : ℝ)*x 1 + (-1205262881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2696898619/5000000000 : ℝ)^6095 ≤ (47616274234271/100000000000000 : ℝ)^5071 := by
    have hnat : (2696898619 : ℕ)^6095*100000000000000^5071 ≤ 47616274234271^5071*5000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696898619 5000000000 47616274234271 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1020107121/2000000000 : ℝ)^6095 ≤ (44521920612517/100000000000000 : ℝ)^5071 := by
    have hnat : (1020107121 : ℕ)^6095*100000000000000^5071 ≤ 44521920612517^5071*2000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020107121 2000000000 44521920612517 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1205262881/10000000000 : ℝ)^6095 ≤ (7861805142371/100000000000000 : ℝ)^5071 := by
    have hnat : (1205262881 : ℕ)^6095*100000000000000^5071 ≤ 7861805142371^5071*10000000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1205262881 10000000000 7861805142371 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2696898619/5000000000 : ℝ), (1020107121/2000000000 : ℝ), (-1205262881/10000000000 : ℝ)] ![(47616274234271/100000000000000 : ℝ), (44521920612517/100000000000000 : ℝ), (7861805142371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2696898619/5000000000 : ℝ)|^6095 ≤ (47616274234271/100000000000000 : ℝ)^5071
        have hw : |(2696898619/5000000000 : ℝ)|=(2696898619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1020107121/2000000000 : ℝ)|^6095 ≤ (44521920612517/100000000000000 : ℝ)^5071
        have hw : |(1020107121/2000000000 : ℝ)|=(1020107121/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1205262881/10000000000 : ℝ)|^6095 ≤ (7861805142371/100000000000000 : ℝ)^5071
        have hw : |(-1205262881/10000000000 : ℝ)|=(1205262881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1770_box_15 (p : ℝ) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (164826113/500000000 : ℝ)*x 0 + (136112101/312500000 : ℝ)*x 1 + (544448993/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (164826113/500000000 : ℝ)^6095 ≤ (26347282659741/100000000000000 : ℝ)^5071 := by
    have hnat : (164826113 : ℕ)^6095*100000000000000^5071 ≤ 26347282659741^5071*500000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164826113 500000000 26347282659741 100000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (136112101/312500000 : ℝ)^6095 ≤ (2301645920011/6250000000000 : ℝ)^5071 := by
    have hnat : (136112101 : ℕ)^6095*6250000000000^5071 ≤ 2301645920011^5071*312500000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136112101 312500000 2301645920011 6250000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (544448993/1250000000 : ℝ)^6095 ≤ (1473055304197/4000000000000 : ℝ)^5071 := by
    have hnat : (544448993 : ℕ)^6095*4000000000000^5071 ≤ 1473055304197^5071*1250000000^6095 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544448993 1250000000 1473055304197 4000000000000 6095 5071 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6095/1024 : ℝ)) 6095 5071 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(164826113/500000000 : ℝ), (136112101/312500000 : ℝ), (544448993/1250000000 : ℝ)] ![(26347282659741/100000000000000 : ℝ), (2301645920011/6250000000000 : ℝ), (1473055304197/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(164826113/500000000 : ℝ)|^6095 ≤ (26347282659741/100000000000000 : ℝ)^5071
        have hw : |(164826113/500000000 : ℝ)|=(164826113/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(136112101/312500000 : ℝ)|^6095 ≤ (2301645920011/6250000000000 : ℝ)^5071
        have hw : |(136112101/312500000 : ℝ)|=(136112101/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(544448993/1250000000 : ℝ)|^6095 ≤ (1473055304197/4000000000000 : ℝ)^5071
        have hw : |(544448993/1250000000 : ℝ)|=(544448993/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1770_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (227741437/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2199/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (37/400 : ℝ)*pair X i i ≤ pair X i h) :
    -(34657/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29541/50000 : ℝ) ∧ (82653/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (11657/12500 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2199/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (37/400 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2199/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (37/400 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2199/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (37/400 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2199/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (37/400 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2199/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (37/400 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2199/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (37/400 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (37/400 : ℝ) ^ (6079/1024 : ℝ) ≤ (72857818809431/100000000000000000000 : ℝ) := by
    have hpowers : (37/400 : ℝ)^6079 ≤ (72857818809431/100000000000000000000 : ℝ)^1024 := by
      have hnat : (37 : ℕ)^6079*100000000000000000000^1024 ≤ 72857818809431^1024*400^6079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37 400 72857818809431 100000000000000000000 6079 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (37/400 : ℝ)) (X := (72857818809431/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6079 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2199/12500 : ℝ) ^ (6079/1024 : ℝ) ≤ (3309756882625581/100000000000000000000 : ℝ) := by
    have hpowers : (2199/12500 : ℝ)^6079 ≤ (3309756882625581/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2199 : ℕ)^6079*100000000000000000000^1024 ≤ 3309756882625581^1024*12500^6079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2199 12500 3309756882625581 100000000000000000000 6079 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2199/12500 : ℝ)) (X := (3309756882625581/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6079 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000072857818809431/50000000000000000000 : ℝ) ≤ (10000002454560331/10000000000000000 : ℝ) ^ (6079/1024 : ℝ) := by
    have hpowers : (50000072857818809431/50000000000000000000 : ℝ)^1024 ≤ (10000002454560331/10000000000000000 : ℝ)^6079 := by
      have hnat : (50000072857818809431 : ℕ)^1024*10000000000000000^6079 ≤ 10000002454560331^6079*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000072857818809431 50000000000000000000 10000002454560331 10000000000000000 1024 6079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000002454560331/10000000000000000 : ℝ)) (X := (50000072857818809431/50000000000000000000 : ℝ)) (by norm_num) 6079 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25000845653675358753/25000000000000000000 : ℝ) ≤ (10000056978923181/10000000000000000 : ℝ) ^ (6079/1024 : ℝ) := by
    have hpowers : (25000845653675358753/25000000000000000000 : ℝ)^1024 ≤ (10000056978923181/10000000000000000 : ℝ)^6079 := by
      have hnat : (25000845653675358753 : ℕ)^1024*10000000000000000^6079 ≤ 10000056978923181^6079*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000845653675358753 25000000000000000000 10000056978923181 10000000000000000 1024 6079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000056978923181/10000000000000000 : ℝ)) (X := (25000845653675358753/25000000000000000000 : ℝ)) (by norm_num) 6079 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50003309756882625581/50000000000000000000 : ℝ) ≤ (10000111503286031/10000000000000000 : ℝ) ^ (6079/1024 : ℝ) := by
    have hpowers : (50003309756882625581/50000000000000000000 : ℝ)^1024 ≤ (10000111503286031/10000000000000000 : ℝ)^6079 := by
      have hnat : (50003309756882625581 : ℕ)^1024*10000000000000000^6079 ≤ 10000111503286031^6079*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50003309756882625581 50000000000000000000 10000111503286031 10000000000000000 1024 6079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000111503286031/10000000000000000 : ℝ)) (X := (50003309756882625581/50000000000000000000 : ℝ)) (by norm_num) 6079 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(72857818809431/100000000000000000000 : ℝ) ≤ ((41709505887614778101/41710000000000000000 : ℝ)+2*(1090487257/16684000000000 : ℝ)*(37/400 : ℝ))^(6079/1024 : ℝ) := by
    rw [show (41709505887614778101/41710000000000000000 : ℝ)+2*(1090487257/16684000000000 : ℝ)*(37/400 : ℝ)=(10000002454560331/10000000000000000 : ℝ) by norm_num, show 1+2*(72857818809431/100000000000000000000 : ℝ)=(50000072857818809431/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3309756882625581/100000000000000000000 : ℝ)+(72857818809431/100000000000000000000 : ℝ) ≤ ((41709505887614778101/41710000000000000000 : ℝ)+(1090487257/16684000000000 : ℝ)*((2199/12500 : ℝ)+(37/400 : ℝ)))^(6079/1024 : ℝ) := by
    rw [show (41709505887614778101/41710000000000000000 : ℝ)+(1090487257/16684000000000 : ℝ)*((2199/12500 : ℝ)+(37/400 : ℝ))=(10000056978923181/10000000000000000 : ℝ) by norm_num, show 1+(3309756882625581/100000000000000000000 : ℝ)+(72857818809431/100000000000000000000 : ℝ)=(25000845653675358753/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3309756882625581/100000000000000000000 : ℝ) ≤ ((41709505887614778101/41710000000000000000 : ℝ)+2*(1090487257/16684000000000 : ℝ)*(2199/12500 : ℝ))^(6079/1024 : ℝ) := by
    rw [show (41709505887614778101/41710000000000000000 : ℝ)+2*(1090487257/16684000000000 : ℝ)*(2199/12500 : ℝ)=(10000111503286031/10000000000000000 : ℝ) by norm_num, show 1+2*(3309756882625581/100000000000000000000 : ℝ)=(50003309756882625581/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (41709505887614778101/41710000000000000000 : ℝ)*(X 1 0+X 2 0)+(1090487257/16684000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6079/1024 : ℝ)) (lo := (37/400 : ℝ)) (hi := (2199/12500 : ℝ)) (c := (41709505887614778101/41710000000000000000 : ℝ)) (alpha := (1090487257/16684000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (41709505887614778101/41710000000000000000 : ℝ)*(X 0 1+X 2 1)+(1090487257/16684000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6079/1024 : ℝ)) (lo := (37/400 : ℝ)) (hi := (2199/12500 : ℝ)) (c := (41709505887614778101/41710000000000000000 : ℝ)) (alpha := (1090487257/16684000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (41709505887614778101/41710000000000000000 : ℝ)*(X 0 2+X 1 2)+(1090487257/16684000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6079/1024 : ℝ)) (lo := (37/400 : ℝ)) (hi := (2199/12500 : ℝ)) (c := (41709505887614778101/41710000000000000000 : ℝ)) (alpha := (1090487257/16684000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-76301333/1000000000 : ℝ)*X 0 0+(270230053/500000000 : ℝ)*X 0 1+(5404599479/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1297957351/2500000000 : ℝ)*X 1 0+(-1066588051/10000000000 : ℝ)*X 1 1+(5404600339/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5191829567/10000000000 : ℝ)*X 2 0+(5404600157/10000000000 : ℝ)*X 2 1+(-13332351/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4505094441/10000000000 : ℝ)*X 0 0+(3756345517/10000000000 : ℝ)*X 0 1+(3756345073/10000000000 : ℝ)*X 0 2+(4505094441/10000000000 : ℝ)*X 1 0+(3756345517/10000000000 : ℝ)*X 1 1+(3756345073/10000000000 : ℝ)*X 1 2+(4505094441/10000000000 : ℝ)*X 2 0+(3756345517/10000000000 : ℝ)*X 2 1+(3756345073/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-756869629/5000000000 : ℝ)*X 0 0+(2564966531/5000000000 : ℝ)*X 0 1+(5129932733/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((214968081/400000000 : ℝ)*X 1 0+(-1192396573/10000000000 : ℝ)*X 1 1+(2564966621/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((537420247/1000000000 : ℝ)*X 2 0+(320620801/625000000 : ℝ)*X 2 1+(-1192396541/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1709017351/5000000000 : ℝ)*X 0 0+(859573557/2000000000 : ℝ)*X 0 1+(859573547/2000000000 : ℝ)*X 0 2+(1709017351/5000000000 : ℝ)*X 1 0+(859573557/2000000000 : ℝ)*X 1 1+(859573547/2000000000 : ℝ)*X 1 2+(1709017351/5000000000 : ℝ)*X 2 0+(859573557/2000000000 : ℝ)*X 2 1+(859573547/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1350079859/10000000000 : ℝ)*X 0 0+(307432919/625000000 : ℝ)*X 0 1+(2732180171/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2576115939/5000000000 : ℝ)*X 1 0+(-1037950853/10000000000 : ℝ)*X 1 1+(2732180171/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((515223147/1000000000 : ℝ)*X 2 0+(5464360379/10000000000 : ℝ)*X 2 1+(-259487841/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((295701517/625000000 : ℝ)*X 0 0+(3638087861/10000000000 : ℝ)*X 0 1+(3638087381/10000000000 : ℝ)*X 0 2+(295701517/625000000 : ℝ)*X 1 0+(3638087861/10000000000 : ℝ)*X 1 1+(3638087381/10000000000 : ℝ)*X 1 2+(295701517/625000000 : ℝ)*X 2 0+(3638087861/10000000000 : ℝ)*X 2 1+(3638087381/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-911999809/10000000000 : ℝ)*X 0 0+(1400988773/2500000000 : ℝ)*X 0 1+(5100536801/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((33711233/62500000 : ℝ)*X 1 0+(-602630979/5000000000 : ℝ)*X 1 1+(5100536251/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2696898619/5000000000 : ℝ)*X 2 0+(1020107121/2000000000 : ℝ)*X 2 1+(-1205262881/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((164826113/500000000 : ℝ)*X 0 0+(136112101/312500000 : ℝ)*X 0 1+(544448993/1250000000 : ℝ)*X 0 2+(164826113/500000000 : ℝ)*X 1 0+(136112101/312500000 : ℝ)*X 1 1+(544448993/1250000000 : ℝ)*X 1 2+(164826113/500000000 : ℝ)*X 2 0+(136112101/312500000 : ℝ)*X 2 1+(544448993/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1770_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-34657/50000 : ℝ) ≤ (-361374776309142572362498221332331/521375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7816871/50000000000000 : ℝ)*(upper0) + (1390303/3125000000000 : ℝ)*(lower2) + (5099897/50000000000000 : ℝ)*(upper5) + (279467956957359/25000000000000 : ℝ)*(major0) + (279467956957359/25000000000000 : ℝ)*(major1) + (279467956957359/25000000000000 : ℝ)*(major2) + (152452137/50000000000000 : ℝ)*(sp2) + (14260751/12500000000000 : ℝ)*(sp3) + (1767994896046651/100000000000000 : ℝ)*(sp4) + (220997711805109/12500000000000 : ℝ)*(sp5) + (220999499740799/12500000000000 : ℝ)*(sp6) + (61356399538763/12500000000000 : ℝ)*(sp7) + (87924001/6250000000000 : ℝ)*(sp8) + (7304194897/50000000000000 : ℝ)*(sp13) + (30678206899757/6250000000000 : ℝ)*(f.failure) + (883998151415333/50000000000000 : ℝ)*(f.sum) + (6604156142823/2085500000000000000000000000 : ℝ)*base65 + (11017045358375995259/1042750000000000000000000000000000 : ℝ)*base67 + (4704977964784245259/1042750000000000000000000000000000 : ℝ)*base69 + (9493825090517495259/1042750000000000000000000000000000 : ℝ)*base71 + (3419446250779/521375000000000000000000000 : ℝ)*base73 + (10062764416440995259/1042750000000000000000000000000000 : ℝ)*base75 + (15729124441832995259/1042750000000000000000000000000000 : ℝ)*base77 + (8637894170089995259/1042750000000000000000000000000000 : ℝ)*base79 + (1101681661803/1042750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (869191/625000000000000000000 : ℝ)*base90 + (869191/625000000000000000000 : ℝ)*base92 + (869191/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (29541/50000 : ℝ) ≤ (308052345305081033337489205099929/521375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5231029/100000000000000 : ℝ)*(upper0) + (32319583/100000000000000 : ℝ)*(upper3) + (27272729/100000000000000 : ℝ)*(upper4) + (626684696321657/50000000000000 : ℝ)*(major0) + (626684696321657/50000000000000 : ℝ)*(major1) + (626684696321657/50000000000000 : ℝ)*(major2) + (484172731618921/25000000000000 : ℝ)*(sp0) + (968346339270733/50000000000000 : ℝ)*(sp1) + (968346457038409/50000000000000 : ℝ)*(sp2) + (550346509923659/100000000000000 : ℝ)*(sp3) + (14456333/390625000000 : ℝ)*(sp5) + (433160737/12500000000000 : ℝ)*(sp6) + (514281427/50000000000000 : ℝ)*(sp7) + (5452887029/100000000000000 : ℝ)*(sp8) + (550347538486513/100000000000000 : ℝ)*(f.failure) + (1936696379362713/100000000000000 : ℝ)*(f.sum) + (5090297058837/2085500000000000000000000000 : ℝ)*base65 + (15102796500158633357/2085500000000000000000000000000000 : ℝ)*base67 + (3239129705912366643/2085500000000000000000000000000000 : ℝ)*base70 + (2957178092567633357/2085500000000000000000000000000000 : ℝ)*base71 + (31788806949357/4171000000000000000000000000 : ℝ)*base73 + (393998079809633357/2085500000000000000000000000000000 : ℝ)*base75 + (8036731460566633357/2085500000000000000000000000000000 : ℝ)*base77 + (19000020181095633357/2085500000000000000000000000000000 : ℝ)*base79 + (6002719563701/4171000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (124260819/10000000000000000000000 : ℝ)*base90 + (124260819/10000000000000000000000 : ℝ)*base92 + (124260819/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (82653/100000 : ℝ) ≤ (3447577076207352038009239089/4171000000000000000000000000 : ℝ) := by norm_num
    linear_combination (51809553/100000000000000 : ℝ)*(upper1) + (1606857/1562500000000 : ℝ)*(upper2) + (46729157/100000000000000 : ℝ)*(lower5) + (74514248997071/6250000000000 : ℝ)*(major0) + (74514248997071/6250000000000 : ℝ)*(major1) + (74514248997071/6250000000000 : ℝ)*(major2) + (11571027369/100000000000000 : ℝ)*(sp1) + (2245362073/50000000000000 : ℝ)*(sp2) + (759995321/25000000000000 : ℝ)*(sp3) + (129616321/25000000000000 : ℝ)*(sp4) + (1833402801332619/100000000000000 : ℝ)*(sp8) + (916695874385267/50000000000000 : ℝ)*(sp9) + (458349707268439/25000000000000 : ℝ)*(sp10) + (130874411389623/25000000000000 : ℝ)*(sp11) + (8179698211559/1562500000000 : ℝ)*(f.failure) + (1833403319797903/100000000000000 : ℝ)*(f.sum) + (498180758613/834200000000000000000000000 : ℝ)*base66 + (1488402777100057829/260687500000000000000000000000000 : ℝ)*base68 + (320509550254317171/260687500000000000000000000000000 : ℝ)*base69 + (13759849063307829/260687500000000000000000000000000 : ℝ)*base72 + (40555516712589/4171000000000000000000000000 : ℝ)*base74 + (981130209381870329/260687500000000000000000000000000 : ℝ)*base76 + (1651229009639567171/260687500000000000000000000000000 : ℝ)*base77 + (650739655674817171/260687500000000000000000000000000 : ℝ)*base79 + (237267130187/52137500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (1670283/156250000000000000000 : ℝ)*base89 + (1670283/156250000000000000000 : ℝ)*base91 + (1670283/156250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-11657/12500 : ℝ) ≤ (-486198389381929401877132910275299/521375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15261399/100000000000000 : ℝ)*(lower3) + (63826609/25000000000000 : ℝ)*(lower4) + (11136241/5000000000000 : ℝ)*(upper5) + (313174255223711/25000000000000 : ℝ)*(major0) + (313174255223711/25000000000000 : ℝ)*(major1) + (313174255223711/25000000000000 : ℝ)*(major2) + (6344711901/100000000000000 : ℝ)*(sp4) + (38317836313/100000000000000 : ℝ)*(sp5) + (82177095271/50000000000000 : ℝ)*(sp6) + (7398054709/20000000000000 : ℝ)*(sp7) + (1986419762467843/100000000000000 : ℝ)*(sp12) + (1986387789343431/100000000000000 : ℝ)*(sp13) + (993130876494601/50000000000000 : ℝ)*(sp14) + (110003062702579/20000000000000 : ℝ)*(sp15) + (13751307594661/2500000000000 : ℝ)*(f.failure) + (62075815849367/3125000000000 : ℝ)*(f.sum) + (2954911042209/834200000000000000000000000 : ℝ)*base65 + (3634560072698002811/1042750000000000000000000000000000 : ℝ)*base67 + (4923031766096002811/1042750000000000000000000000000000 : ℝ)*base69 + (8394274916710002811/1042750000000000000000000000000000 : ℝ)*base71 + (450901742131/2085500000000000000000000000 : ℝ)*base73 + (4211367142365752811/1042750000000000000000000000000000 : ℝ)*base75 + (4638642584664752811/1042750000000000000000000000000000 : ℝ)*base77 + (4225501029462002811/1042750000000000000000000000000000 : ℝ)*base79 + (85101217801/4171000000000000000000000000 : ℝ)*base82 + (332143/250000000000000000000 : ℝ)*base90 + (332143/250000000000000000000 : ℝ)*base92 + (332143/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1770_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (227741437/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2199/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (37/400 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(34657/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29541/50000 : ℝ) else (82653/100000 : ℝ) ≤ X j i ∧ X j i ≤ (11657/12500 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1770_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1770_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (227741437/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2199/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9249/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(34657/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29541/50000 : ℝ) else (82653/100000 : ℝ) ≤ X j i ∧ X j i ≤ (11657/12500 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1770_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1770_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (6079/1024 : ℝ) ≤ p) (hpb : p ≤ (6095/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (227741437/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2199/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9249/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(34657/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29541/50000 : ℝ) else (82653/100000 : ℝ) ≤ X j i ∧ X j i ≤ (11657/12500 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1770_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
