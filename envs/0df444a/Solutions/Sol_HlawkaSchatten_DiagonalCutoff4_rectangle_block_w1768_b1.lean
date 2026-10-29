-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1768_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:30:51.245779+00:00
-- url     : https://prove2.me/submissions/5a713adf-fbea-4530-ba5d-d462b985fcb3

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
theorem support_rectangle_w1768_box_0 (p : ℝ) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-38487593/500000000 : ℝ)*x 0 + (675823047/1250000000 : ℝ)*x 1 + (5406584791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (38487593/500000000 : ℝ)^6063 ≤ (35713353247/781250000000 : ℝ)^5039 := by
    have hnat : (38487593 : ℕ)^6063*781250000000^5039 ≤ 35713353247^5039*500000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38487593 500000000 35713353247 781250000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (675823047/1250000000 : ℝ)^6063 ≤ (23857171590551/50000000000000 : ℝ)^5039 := by
    have hnat : (675823047 : ℕ)^6063*50000000000000^5039 ≤ 23857171590551^5039*1250000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675823047 1250000000 23857171590551 50000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406584791/10000000000 : ℝ)^6063 ≤ (37276834053/78125000000 : ℝ)^5039 := by
    have hnat : (5406584791 : ℕ)^6063*78125000000^5039 ≤ 37276834053^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406584791 10000000000 37276834053 78125000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6063/1024 : ℝ)) 6063 5039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-38487593/500000000 : ℝ), (675823047/1250000000 : ℝ), (5406584791/10000000000 : ℝ)] ![(35713353247/781250000000 : ℝ), (23857171590551/50000000000000 : ℝ), (37276834053/78125000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-38487593/500000000 : ℝ)|^6063 ≤ (35713353247/781250000000 : ℝ)^5039
        have hw : |(-38487593/500000000 : ℝ)|=(38487593/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(675823047/1250000000 : ℝ)|^6063 ≤ (23857171590551/50000000000000 : ℝ)^5039
        have hw : |(675823047/1250000000 : ℝ)|=(675823047/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406584791/10000000000 : ℝ)|^6063 ≤ (37276834053/78125000000 : ℝ)^5039
        have hw : |(5406584791/10000000000 : ℝ)|=(5406584791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1768_box_1 (p : ℝ) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2596069373/5000000000 : ℝ)*x 0 + (-537938863/5000000000 : ℝ)*x 1 + (5406584529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2596069373/5000000000 : ℝ)^6063 ≤ (11361624083917/25000000000000 : ℝ)^5039 := by
    have hnat : (2596069373 : ℕ)^6063*25000000000000^5039 ≤ 11361624083917^5039*5000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596069373 5000000000 11361624083917 25000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (537938863/5000000000 : ℝ)^6063 ≤ (341957942803/5000000000000 : ℝ)^5039 := by
    have hnat : (537938863 : ℕ)^6063*5000000000000^5039 ≤ 341957942803^5039*5000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537938863 5000000000 341957942803 5000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406584529/10000000000 : ℝ)^6063 ≤ (9542868961151/20000000000000 : ℝ)^5039 := by
    have hnat : (5406584529 : ℕ)^6063*20000000000000^5039 ≤ 9542868961151^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406584529 10000000000 9542868961151 20000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6063/1024 : ℝ)) 6063 5039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2596069373/5000000000 : ℝ), (-537938863/5000000000 : ℝ), (5406584529/10000000000 : ℝ)] ![(11361624083917/25000000000000 : ℝ), (341957942803/5000000000000 : ℝ), (9542868961151/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2596069373/5000000000 : ℝ)|^6063 ≤ (11361624083917/25000000000000 : ℝ)^5039
        have hw : |(2596069373/5000000000 : ℝ)|=(2596069373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-537938863/5000000000 : ℝ)|^6063 ≤ (341957942803/5000000000000 : ℝ)^5039
        have hw : |(-537938863/5000000000 : ℝ)|=(537938863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406584529/10000000000 : ℝ)|^6063 ≤ (9542868961151/20000000000000 : ℝ)^5039
        have hw : |(5406584529/10000000000 : ℝ)|=(5406584529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1768_box_2 (p : ℝ) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2596069089/5000000000 : ℝ)*x 0 + (5406585081/10000000000 : ℝ)*x 1 + (-1075877741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2596069089/5000000000 : ℝ)^6063 ≤ (22723245176839/50000000000000 : ℝ)^5039 := by
    have hnat : (2596069089 : ℕ)^6063*50000000000000^5039 ≤ 22723245176839^5039*5000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596069089 5000000000 22723245176839 50000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406585081/10000000000 : ℝ)^6063 ≤ (2982146916703/6250000000000 : ℝ)^5039 := by
    have hnat : (5406585081 : ℕ)^6063*6250000000000^5039 ≤ 2982146916703^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406585081 10000000000 2982146916703 6250000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1075877741/10000000000 : ℝ)^6063 ≤ (6839158970789/100000000000000 : ℝ)^5039 := by
    have hnat : (1075877741 : ℕ)^6063*100000000000000^5039 ≤ 6839158970789^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075877741 10000000000 6839158970789 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6063/1024 : ℝ)) 6063 5039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2596069089/5000000000 : ℝ), (5406585081/10000000000 : ℝ), (-1075877741/10000000000 : ℝ)] ![(22723245176839/50000000000000 : ℝ), (2982146916703/6250000000000 : ℝ), (6839158970789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2596069089/5000000000 : ℝ)|^6063 ≤ (22723245176839/50000000000000 : ℝ)^5039
        have hw : |(2596069089/5000000000 : ℝ)|=(2596069089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406585081/10000000000 : ℝ)|^6063 ≤ (2982146916703/6250000000000 : ℝ)^5039
        have hw : |(5406585081/10000000000 : ℝ)|=(5406585081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1075877741/10000000000 : ℝ)|^6063 ≤ (6839158970789/100000000000000 : ℝ)^5039
        have hw : |(-1075877741/10000000000 : ℝ)|=(1075877741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1768_box_3 (p : ℝ) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2254528783/5000000000 : ℝ)*x 0 + (3760198309/10000000000 : ℝ)*x 1 + (752039661/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2254528783/5000000000 : ℝ)^6063 ≤ (19176125017593/50000000000000 : ℝ)^5039 := by
    have hnat : (2254528783 : ℕ)^6063*50000000000000^5039 ≤ 19176125017593^5039*5000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254528783 5000000000 19176125017593 50000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3760198309/10000000000 : ℝ)^6063 ≤ (30823874995283/100000000000000 : ℝ)^5039 := by
    have hnat : (3760198309 : ℕ)^6063*100000000000000^5039 ≤ 30823874995283^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3760198309 10000000000 30823874995283 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (752039661/2000000000 : ℝ)^6063 ≤ (3082387495583/10000000000000 : ℝ)^5039 := by
    have hnat : (752039661 : ℕ)^6063*10000000000000^5039 ≤ 3082387495583^5039*2000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      752039661 2000000000 3082387495583 10000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6063/1024 : ℝ)) 6063 5039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2254528783/5000000000 : ℝ), (3760198309/10000000000 : ℝ), (752039661/2000000000 : ℝ)] ![(19176125017593/50000000000000 : ℝ), (30823874995283/100000000000000 : ℝ), (3082387495583/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2254528783/5000000000 : ℝ)|^6063 ≤ (19176125017593/50000000000000 : ℝ)^5039
        have hw : |(2254528783/5000000000 : ℝ)|=(2254528783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3760198309/10000000000 : ℝ)|^6063 ≤ (30823874995283/100000000000000 : ℝ)^5039
        have hw : |(3760198309/10000000000 : ℝ)|=(3760198309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(752039661/2000000000 : ℝ)|^6063 ≤ (3082387495583/10000000000000 : ℝ)^5039
        have hw : |(752039661/2000000000 : ℝ)|=(752039661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1768_box_4 (p : ℝ) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-381573133/2500000000 : ℝ)*x 0 + (5129871987/10000000000 : ℝ)*x 1 + (32061697/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (381573133/2500000000 : ℝ)^6063 ≤ (5208477558619/50000000000000 : ℝ)^5039 := by
    have hnat : (381573133 : ℕ)^6063*50000000000000^5039 ≤ 5208477558619^5039*2500000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      381573133 2500000000 5208477558619 50000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5129871987/10000000000 : ℝ)^6063 ≤ (44791524885969/100000000000000 : ℝ)^5039 := by
    have hnat : (5129871987 : ℕ)^6063*100000000000000^5039 ≤ 44791524885969^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129871987 10000000000 44791524885969 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32061697/62500000 : ℝ)^6063 ≤ (22395759989861/50000000000000 : ℝ)^5039 := by
    have hnat : (32061697 : ℕ)^6063*50000000000000^5039 ≤ 22395759989861^5039*62500000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32061697 62500000 22395759989861 50000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6063/1024 : ℝ)) 6063 5039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-381573133/2500000000 : ℝ), (5129871987/10000000000 : ℝ), (32061697/62500000 : ℝ)] ![(5208477558619/50000000000000 : ℝ), (44791524885969/100000000000000 : ℝ), (22395759989861/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-381573133/2500000000 : ℝ)|^6063 ≤ (5208477558619/50000000000000 : ℝ)^5039
        have hw : |(-381573133/2500000000 : ℝ)|=(381573133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5129871987/10000000000 : ℝ)|^6063 ≤ (44791524885969/100000000000000 : ℝ)^5039
        have hw : |(5129871987/10000000000 : ℝ)|=(5129871987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(32061697/62500000 : ℝ)|^6063 ≤ (22395759989861/50000000000000 : ℝ)^5039
        have hw : |(32061697/62500000 : ℝ)|=(32061697/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1768_box_5 (p : ℝ) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5376015089/10000000000 : ℝ)*x 0 + (-601229191/5000000000 : ℝ)*x 1 + (5129871363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376015089/10000000000 : ℝ)^6063 ≤ (47389925485191/100000000000000 : ℝ)^5039 := by
    have hnat : (5376015089 : ℕ)^6063*100000000000000^5039 ≤ 47389925485191^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376015089 10000000000 47389925485191 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (601229191/5000000000 : ℝ)^6063 ≤ (1954639041579/25000000000000 : ℝ)^5039 := by
    have hnat : (601229191 : ℕ)^6063*25000000000000^5039 ≤ 1954639041579^5039*5000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      601229191 5000000000 1954639041579 25000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5129871363/10000000000 : ℝ)^6063 ≤ (22395759165149/50000000000000 : ℝ)^5039 := by
    have hnat : (5129871363 : ℕ)^6063*50000000000000^5039 ≤ 22395759165149^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129871363 10000000000 22395759165149 50000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6063/1024 : ℝ)) 6063 5039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376015089/10000000000 : ℝ), (-601229191/5000000000 : ℝ), (5129871363/10000000000 : ℝ)] ![(47389925485191/100000000000000 : ℝ), (1954639041579/25000000000000 : ℝ), (22395759165149/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376015089/10000000000 : ℝ)|^6063 ≤ (47389925485191/100000000000000 : ℝ)^5039
        have hw : |(5376015089/10000000000 : ℝ)|=(5376015089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-601229191/5000000000 : ℝ)|^6063 ≤ (1954639041579/25000000000000 : ℝ)^5039
        have hw : |(-601229191/5000000000 : ℝ)|=(601229191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5129871363/10000000000 : ℝ)|^6063 ≤ (22395759165149/50000000000000 : ℝ)^5039
        have hw : |(5129871363/10000000000 : ℝ)|=(5129871363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1768_box_6 (p : ℝ) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2688007397/5000000000 : ℝ)*x 0 + (5129871577/10000000000 : ℝ)*x 1 + (-240491699/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688007397/5000000000 : ℝ)^6063 ≤ (47389922356297/100000000000000 : ℝ)^5039 := by
    have hnat : (2688007397 : ℕ)^6063*100000000000000^5039 ≤ 47389922356297^5039*5000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688007397 5000000000 47389922356297 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5129871577/10000000000 : ℝ)^6063 ≤ (44791520578557/100000000000000 : ℝ)^5039 := by
    have hnat : (5129871577 : ℕ)^6063*100000000000000^5039 ≤ 44791520578557^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129871577 10000000000 44791520578557 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (240491699/2000000000 : ℝ)^6063 ≤ (7818557050369/100000000000000 : ℝ)^5039 := by
    have hnat : (240491699 : ℕ)^6063*100000000000000^5039 ≤ 7818557050369^5039*2000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240491699 2000000000 7818557050369 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6063/1024 : ℝ)) 6063 5039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688007397/5000000000 : ℝ), (5129871577/10000000000 : ℝ), (-240491699/2000000000 : ℝ)] ![(47389922356297/100000000000000 : ℝ), (44791520578557/100000000000000 : ℝ), (7818557050369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688007397/5000000000 : ℝ)|^6063 ≤ (47389922356297/100000000000000 : ℝ)^5039
        have hw : |(2688007397/5000000000 : ℝ)|=(2688007397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5129871577/10000000000 : ℝ)|^6063 ≤ (44791520578557/100000000000000 : ℝ)^5039
        have hw : |(5129871577/10000000000 : ℝ)|=(5129871577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-240491699/2000000000 : ℝ)|^6063 ≤ (7818557050369/100000000000000 : ℝ)^5039
        have hw : |(-240491699/2000000000 : ℝ)|=(240491699/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1768_box_7 (p : ℝ) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3421854227/10000000000 : ℝ)*x 0 + (430178257/1000000000 : ℝ)*x 1 + (2150890959/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3421854227/10000000000 : ℝ)^6063 ≤ (27517976256949/100000000000000 : ℝ)^5039 := by
    have hnat : (3421854227 : ℕ)^6063*100000000000000^5039 ≤ 27517976256949^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3421854227 10000000000 27517976256949 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (430178257/1000000000 : ℝ)^6063 ≤ (7248203033479/20000000000000 : ℝ)^5039 := by
    have hnat : (430178257 : ℕ)^6063*20000000000000^5039 ≤ 7248203033479^5039*1000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430178257 1000000000 7248203033479 20000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2150890959/5000000000 : ℝ)^6063 ≤ (3624100855829/10000000000000 : ℝ)^5039 := by
    have hnat : (2150890959 : ℕ)^6063*10000000000000^5039 ≤ 3624100855829^5039*5000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150890959 5000000000 3624100855829 10000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6063/1024 : ℝ)) 6063 5039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3421854227/10000000000 : ℝ), (430178257/1000000000 : ℝ), (2150890959/5000000000 : ℝ)] ![(27517976256949/100000000000000 : ℝ), (7248203033479/20000000000000 : ℝ), (3624100855829/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3421854227/10000000000 : ℝ)|^6063 ≤ (27517976256949/100000000000000 : ℝ)^5039
        have hw : |(3421854227/10000000000 : ℝ)|=(3421854227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(430178257/1000000000 : ℝ)|^6063 ≤ (7248203033479/20000000000000 : ℝ)^5039
        have hw : |(430178257/1000000000 : ℝ)|=(430178257/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2150890959/5000000000 : ℝ)|^6063 ≤ (3624100855829/10000000000000 : ℝ)^5039
        have hw : |(2150890959/5000000000 : ℝ)|=(2150890959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1768_box_8 (p : ℝ) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1361395103/10000000000 : ℝ)*x 0 + (4917476189/10000000000 : ℝ)*x 1 + (1093318193/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1361395103/10000000000 : ℝ)^6063 ≤ (4539069688871/50000000000000 : ℝ)^5039 := by
    have hnat : (1361395103 : ℕ)^6063*50000000000000^5039 ≤ 4539069688871^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1361395103 10000000000 4539069688871 50000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4917476189/10000000000 : ℝ)^6063 ≤ (42569612190197/100000000000000 : ℝ)^5039 := by
    have hnat : (4917476189 : ℕ)^6063*100000000000000^5039 ≤ 42569612190197^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4917476189 10000000000 42569612190197 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1093318193/2000000000 : ℝ)^6063 ≤ (24176124208779/50000000000000 : ℝ)^5039 := by
    have hnat : (1093318193 : ℕ)^6063*50000000000000^5039 ≤ 24176124208779^5039*2000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093318193 2000000000 24176124208779 50000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6063/1024 : ℝ)) 6063 5039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1361395103/10000000000 : ℝ), (4917476189/10000000000 : ℝ), (1093318193/2000000000 : ℝ)] ![(4539069688871/50000000000000 : ℝ), (42569612190197/100000000000000 : ℝ), (24176124208779/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1361395103/10000000000 : ℝ)|^6063 ≤ (4539069688871/50000000000000 : ℝ)^5039
        have hw : |(-1361395103/10000000000 : ℝ)|=(1361395103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4917476189/10000000000 : ℝ)|^6063 ≤ (42569612190197/100000000000000 : ℝ)^5039
        have hw : |(4917476189/10000000000 : ℝ)|=(4917476189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1093318193/2000000000 : ℝ)|^6063 ≤ (24176124208779/50000000000000 : ℝ)^5039
        have hw : |(1093318193/2000000000 : ℝ)|=(1093318193/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1768_box_9 (p : ℝ) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2576172613/5000000000 : ℝ)*x 0 + (-1047149091/10000000000 : ℝ)*x 1 + (5466590547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2576172613/5000000000 : ℝ)^6063 ≤ (11256932765617/25000000000000 : ℝ)^5039 := by
    have hnat : (2576172613 : ℕ)^6063*25000000000000^5039 ≤ 11256932765617^5039*5000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2576172613 5000000000 11256932765617 25000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1047149091/10000000000 : ℝ)^6063 ≤ (6620024951561/100000000000000 : ℝ)^5039 := by
    have hnat : (1047149091 : ℕ)^6063*100000000000000^5039 ≤ 6620024951561^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047149091 10000000000 6620024951561 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5466590547/10000000000 : ℝ)^6063 ≤ (48352243968997/100000000000000 : ℝ)^5039 := by
    have hnat : (5466590547 : ℕ)^6063*100000000000000^5039 ≤ 48352243968997^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5466590547 10000000000 48352243968997 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6063/1024 : ℝ)) 6063 5039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2576172613/5000000000 : ℝ), (-1047149091/10000000000 : ℝ), (5466590547/10000000000 : ℝ)] ![(11256932765617/25000000000000 : ℝ), (6620024951561/100000000000000 : ℝ), (48352243968997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2576172613/5000000000 : ℝ)|^6063 ≤ (11256932765617/25000000000000 : ℝ)^5039
        have hw : |(2576172613/5000000000 : ℝ)|=(2576172613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1047149091/10000000000 : ℝ)|^6063 ≤ (6620024951561/100000000000000 : ℝ)^5039
        have hw : |(-1047149091/10000000000 : ℝ)|=(1047149091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5466590547/10000000000 : ℝ)|^6063 ≤ (48352243968997/100000000000000 : ℝ)^5039
        have hw : |(5466590547/10000000000 : ℝ)|=(5466590547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1768_box_10 (p : ℝ) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2576172493/5000000000 : ℝ)*x 0 + (683323837/1250000000 : ℝ)*x 1 + (-32723413/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2576172493/5000000000 : ℝ)^6063 ≤ (703558258419/1562500000000 : ℝ)^5039 := by
    have hnat : (2576172493 : ℕ)^6063*1562500000000^5039 ≤ 703558258419^5039*5000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2576172493 5000000000 703558258419 1562500000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (683323837/1250000000 : ℝ)^6063 ≤ (6044030694341/12500000000000 : ℝ)^5039 := by
    have hnat : (683323837 : ℕ)^6063*12500000000000^5039 ≤ 6044030694341^5039*1250000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683323837 1250000000 6044030694341 12500000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32723413/312500000 : ℝ)^6063 ≤ (1324005180479/20000000000000 : ℝ)^5039 := by
    have hnat : (32723413 : ℕ)^6063*20000000000000^5039 ≤ 1324005180479^5039*312500000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32723413 312500000 1324005180479 20000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6063/1024 : ℝ)) 6063 5039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2576172493/5000000000 : ℝ), (683323837/1250000000 : ℝ), (-32723413/312500000 : ℝ)] ![(703558258419/1562500000000 : ℝ), (6044030694341/12500000000000 : ℝ), (1324005180479/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2576172493/5000000000 : ℝ)|^6063 ≤ (703558258419/1562500000000 : ℝ)^5039
        have hw : |(2576172493/5000000000 : ℝ)|=(2576172493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(683323837/1250000000 : ℝ)|^6063 ≤ (6044030694341/12500000000000 : ℝ)^5039
        have hw : |(683323837/1250000000 : ℝ)|=(683323837/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-32723413/312500000 : ℝ)|^6063 ≤ (1324005180479/20000000000000 : ℝ)^5039
        have hw : |(-32723413/312500000 : ℝ)|=(32723413/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1768_box_11 (p : ℝ) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2367208037/5000000000 : ℝ)*x 0 + (3642317729/10000000000 : ℝ)*x 1 + (728463657/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2367208037/5000000000 : ℝ)^6063 ≤ (10167536070801/25000000000000 : ℝ)^5039 := by
    have hnat : (2367208037 : ℕ)^6063*25000000000000^5039 ≤ 10167536070801^5039*5000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2367208037 5000000000 10167536070801 25000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3642317729/10000000000 : ℝ)^6063 ≤ (14832462563997/50000000000000 : ℝ)^5039 := by
    have hnat : (3642317729 : ℕ)^6063*50000000000000^5039 ≤ 14832462563997^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3642317729 10000000000 14832462563997 50000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (728463657/2000000000 : ℝ)^6063 ≤ (1186597223063/4000000000000 : ℝ)^5039 := by
    have hnat : (728463657 : ℕ)^6063*4000000000000^5039 ≤ 1186597223063^5039*2000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      728463657 2000000000 1186597223063 4000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6063/1024 : ℝ)) 6063 5039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2367208037/5000000000 : ℝ), (3642317729/10000000000 : ℝ), (728463657/2000000000 : ℝ)] ![(10167536070801/25000000000000 : ℝ), (14832462563997/50000000000000 : ℝ), (1186597223063/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2367208037/5000000000 : ℝ)|^6063 ≤ (10167536070801/25000000000000 : ℝ)^5039
        have hw : |(2367208037/5000000000 : ℝ)|=(2367208037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3642317729/10000000000 : ℝ)|^6063 ≤ (14832462563997/50000000000000 : ℝ)^5039
        have hw : |(3642317729/10000000000 : ℝ)|=(3642317729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(728463657/2000000000 : ℝ)|^6063 ≤ (1186597223063/4000000000000 : ℝ)^5039
        have hw : |(728463657/2000000000 : ℝ)|=(728463657/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1768_box_12 (p : ℝ) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-460026747/5000000000 : ℝ)*x 0 + (5607182267/10000000000 : ℝ)*x 1 + (5100397037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (460026747/5000000000 : ℝ)^6063 ≤ (5665580738841/100000000000000 : ℝ)^5039 := by
    have hnat : (460026747 : ℕ)^6063*100000000000000^5039 ≤ 5665580738841^5039*5000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      460026747 5000000000 5665580738841 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5607182267/10000000000 : ℝ)^6063 ≤ (9970474731517/20000000000000 : ℝ)^5039 := by
    have hnat : (5607182267 : ℕ)^6063*20000000000000^5039 ≤ 9970474731517^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5607182267 10000000000 9970474731517 20000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5100397037/10000000000 : ℝ)^6063 ≤ (8896409118161/20000000000000 : ℝ)^5039 := by
    have hnat : (5100397037 : ℕ)^6063*20000000000000^5039 ≤ 8896409118161^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5100397037 10000000000 8896409118161 20000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6063/1024 : ℝ)) 6063 5039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-460026747/5000000000 : ℝ), (5607182267/10000000000 : ℝ), (5100397037/10000000000 : ℝ)] ![(5665580738841/100000000000000 : ℝ), (9970474731517/20000000000000 : ℝ), (8896409118161/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-460026747/5000000000 : ℝ)|^6063 ≤ (5665580738841/100000000000000 : ℝ)^5039
        have hw : |(-460026747/5000000000 : ℝ)|=(460026747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5607182267/10000000000 : ℝ)|^6063 ≤ (9970474731517/20000000000000 : ℝ)^5039
        have hw : |(5607182267/10000000000 : ℝ)|=(5607182267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5100397037/10000000000 : ℝ)|^6063 ≤ (8896409118161/20000000000000 : ℝ)^5039
        have hw : |(5100397037/10000000000 : ℝ)|=(5100397037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1768_box_13 (p : ℝ) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1079135571/2000000000 : ℝ)*x 0 + (-1215336421/10000000000 : ℝ)*x 1 + (5100395459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079135571/2000000000 : ℝ)^6063 ≤ (23799277218861/50000000000000 : ℝ)^5039 := by
    have hnat : (1079135571 : ℕ)^6063*50000000000000^5039 ≤ 23799277218861^5039*2000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079135571 2000000000 23799277218861 50000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1215336421/10000000000 : ℝ)^6063 ≤ (3959708256237/50000000000000 : ℝ)^5039 := by
    have hnat : (1215336421 : ℕ)^6063*50000000000000^5039 ≤ 3959708256237^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1215336421 10000000000 3959708256237 50000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5100395459/10000000000 : ℝ)^6063 ≤ (1779281161277/4000000000000 : ℝ)^5039 := by
    have hnat : (5100395459 : ℕ)^6063*4000000000000^5039 ≤ 1779281161277^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5100395459 10000000000 1779281161277 4000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6063/1024 : ℝ)) 6063 5039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079135571/2000000000 : ℝ), (-1215336421/10000000000 : ℝ), (5100395459/10000000000 : ℝ)] ![(23799277218861/50000000000000 : ℝ), (3959708256237/50000000000000 : ℝ), (1779281161277/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079135571/2000000000 : ℝ)|^6063 ≤ (23799277218861/50000000000000 : ℝ)^5039
        have hw : |(1079135571/2000000000 : ℝ)|=(1079135571/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1215336421/10000000000 : ℝ)|^6063 ≤ (3959708256237/50000000000000 : ℝ)^5039
        have hw : |(-1215336421/10000000000 : ℝ)|=(1215336421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5100395459/10000000000 : ℝ)|^6063 ≤ (1779281161277/4000000000000 : ℝ)^5039
        have hw : |(5100395459/10000000000 : ℝ)|=(5100395459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1768_box_14 (p : ℝ) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1079135507/2000000000 : ℝ)*x 0 + (5100395093/10000000000 : ℝ)*x 1 + (-607668673/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079135507/2000000000 : ℝ)^6063 ≤ (47598551041149/100000000000000 : ℝ)^5039 := by
    have hnat : (1079135507 : ℕ)^6063*100000000000000^5039 ≤ 47598551041149^5039*2000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079135507 2000000000 47598551041149 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5100395093/10000000000 : ℝ)^6063 ≤ (5560253148909/12500000000000 : ℝ)^5039 := by
    have hnat : (5100395093 : ℕ)^6063*12500000000000^5039 ≤ 5560253148909^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5100395093 10000000000 5560253148909 12500000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (607668673/5000000000 : ℝ)^6063 ≤ (989927970609/12500000000000 : ℝ)^5039 := by
    have hnat : (607668673 : ℕ)^6063*12500000000000^5039 ≤ 989927970609^5039*5000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      607668673 5000000000 989927970609 12500000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6063/1024 : ℝ)) 6063 5039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079135507/2000000000 : ℝ), (5100395093/10000000000 : ℝ), (-607668673/5000000000 : ℝ)] ![(47598551041149/100000000000000 : ℝ), (5560253148909/12500000000000 : ℝ), (989927970609/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079135507/2000000000 : ℝ)|^6063 ≤ (47598551041149/100000000000000 : ℝ)^5039
        have hw : |(1079135507/2000000000 : ℝ)|=(1079135507/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5100395093/10000000000 : ℝ)|^6063 ≤ (5560253148909/12500000000000 : ℝ)^5039
        have hw : |(5100395093/10000000000 : ℝ)|=(5100395093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-607668673/5000000000 : ℝ)|^6063 ≤ (989927970609/12500000000000 : ℝ)^5039
        have hw : |(-607668673/5000000000 : ℝ)|=(607668673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1768_box_15 (p : ℝ) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (330087053/1000000000 : ℝ)*x 0 + (4359235853/10000000000 : ℝ)*x 1 + (2179620281/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330087053/1000000000 : ℝ)^6063 ≤ (26351577319637/100000000000000 : ℝ)^5039 := by
    have hnat : (330087053 : ℕ)^6063*100000000000000^5039 ≤ 26351577319637^5039*1000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330087053 1000000000 26351577319637 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4359235853/10000000000 : ℝ)^6063 ≤ (36824187401517/100000000000000 : ℝ)^5039 := by
    have hnat : (4359235853 : ℕ)^6063*100000000000000^5039 ≤ 36824187401517^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359235853 10000000000 36824187401517 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2179620281/5000000000 : ℝ)^6063 ≤ (9206058815987/25000000000000 : ℝ)^5039 := by
    have hnat : (2179620281 : ℕ)^6063*25000000000000^5039 ≤ 9206058815987^5039*5000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179620281 5000000000 9206058815987 25000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6063/1024 : ℝ)) 6063 5039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330087053/1000000000 : ℝ), (4359235853/10000000000 : ℝ), (2179620281/5000000000 : ℝ)] ![(26351577319637/100000000000000 : ℝ), (36824187401517/100000000000000 : ℝ), (9206058815987/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330087053/1000000000 : ℝ)|^6063 ≤ (26351577319637/100000000000000 : ℝ)^5039
        have hw : |(330087053/1000000000 : ℝ)|=(330087053/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4359235853/10000000000 : ℝ)|^6063 ≤ (36824187401517/100000000000000 : ℝ)^5039
        have hw : |(4359235853/10000000000 : ℝ)|=(4359235853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2179620281/5000000000 : ℝ)|^6063 ≤ (9206058815987/25000000000000 : ℝ)^5039
        have hw : |(2179620281/5000000000 : ℝ)|=(2179620281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1768_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (45278133/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1763/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (577/6250 : ℝ)*pair X i i ≤ pair X i h) :
    -(8659/12500 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58987/100000 : ℝ) ∧ (82551/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (93221/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1763/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (577/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1763/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (577/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1763/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (577/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1763/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (577/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1763/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (577/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1763/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (577/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (577/6250 : ℝ) ^ (6047/1024 : ℝ) ≤ (77586962071147/100000000000000000000 : ℝ) := by
    have hpowers : (577/6250 : ℝ)^6047 ≤ (77586962071147/100000000000000000000 : ℝ)^1024 := by
      have hnat : (577 : ℕ)^6047*100000000000000000000^1024 ≤ 77586962071147^1024*6250^6047 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        577 6250 77586962071147 100000000000000000000 6047 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (577/6250 : ℝ)) (X := (77586962071147/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6047 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1763/10000 : ℝ) ^ (6047/1024 : ℝ) ≤ (44240885834247/1250000000000000000 : ℝ) := by
    have hpowers : (1763/10000 : ℝ)^6047 ≤ (44240885834247/1250000000000000000 : ℝ)^1024 := by
      have hnat : (1763 : ℕ)^6047*1250000000000000000^1024 ≤ 44240885834247^1024*10000^6047 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1763 10000 44240885834247 1250000000000000000 6047 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1763/10000 : ℝ)) (X := (44240885834247/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 6047 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000077586962071147/50000000000000000000 : ℝ) ≤ (2500000656929039/2500000000000000 : ℝ) ^ (6047/1024 : ℝ) := by
    have hpowers : (50000077586962071147/50000000000000000000 : ℝ)^1024 ≤ (2500000656929039/2500000000000000 : ℝ)^6047 := by
      have hnat : (50000077586962071147 : ℕ)^1024*2500000000000000^6047 ≤ 2500000656929039^6047*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000077586962071147 50000000000000000000 2500000656929039 2500000000000000 1024 6047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000656929039/2500000000000000 : ℝ)) (X := (50000077586962071147/50000000000000000000 : ℝ)) (by norm_num) 6047 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100003616857828810907/100000000000000000000 : ℝ) ≤ (10000061247011443/10000000000000000 : ℝ) ^ (6047/1024 : ℝ) := by
    have hpowers : (100003616857828810907/100000000000000000000 : ℝ)^1024 ≤ (10000061247011443/10000000000000000 : ℝ)^6047 := by
      have hnat : (100003616857828810907 : ℕ)^1024*10000000000000000^6047 ≤ 10000061247011443^6047*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100003616857828810907 100000000000000000000 10000061247011443 10000000000000000 1024 6047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000061247011443/10000000000000000 : ℝ)) (X := (100003616857828810907/100000000000000000000 : ℝ)) (by norm_num) 6047 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (625044240885834247/625000000000000000 : ℝ) ≤ (1000011986630673/1000000000000000 : ℝ) ^ (6047/1024 : ℝ) := by
    have hpowers : (625044240885834247/625000000000000000 : ℝ)^1024 ≤ (1000011986630673/1000000000000000 : ℝ)^6047 := by
      have hnat : (625044240885834247 : ℕ)^1024*1000000000000000^6047 ≤ 1000011986630673^6047*625000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625044240885834247 625000000000000000 1000011986630673 1000000000000000 1024 6047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000011986630673/1000000000000000 : ℝ)) (X := (625044240885834247/625000000000000000 : ℝ)) (by norm_num) 6047 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(77586962071147/100000000000000000000 : ℝ) ≤ ((2099473493022302473/2099500000000000000 : ℝ)+2*(58619295287/839800000000000 : ℝ)*(577/6250 : ℝ))^(6047/1024 : ℝ) := by
    rw [show (2099473493022302473/2099500000000000000 : ℝ)+2*(58619295287/839800000000000 : ℝ)*(577/6250 : ℝ)=(2500000656929039/2500000000000000 : ℝ) by norm_num, show 1+2*(77586962071147/100000000000000000000 : ℝ)=(50000077586962071147/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(44240885834247/1250000000000000000 : ℝ)+(77586962071147/100000000000000000000 : ℝ) ≤ ((2099473493022302473/2099500000000000000 : ℝ)+(58619295287/839800000000000 : ℝ)*((1763/10000 : ℝ)+(577/6250 : ℝ)))^(6047/1024 : ℝ) := by
    rw [show (2099473493022302473/2099500000000000000 : ℝ)+(58619295287/839800000000000 : ℝ)*((1763/10000 : ℝ)+(577/6250 : ℝ))=(10000061247011443/10000000000000000 : ℝ) by norm_num, show 1+(44240885834247/1250000000000000000 : ℝ)+(77586962071147/100000000000000000000 : ℝ)=(100003616857828810907/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(44240885834247/1250000000000000000 : ℝ) ≤ ((2099473493022302473/2099500000000000000 : ℝ)+2*(58619295287/839800000000000 : ℝ)*(1763/10000 : ℝ))^(6047/1024 : ℝ) := by
    rw [show (2099473493022302473/2099500000000000000 : ℝ)+2*(58619295287/839800000000000 : ℝ)*(1763/10000 : ℝ)=(1000011986630673/1000000000000000 : ℝ) by norm_num, show 1+2*(44240885834247/1250000000000000000 : ℝ)=(625044240885834247/625000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2099473493022302473/2099500000000000000 : ℝ)*(X 1 0+X 2 0)+(58619295287/839800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6047/1024 : ℝ)) (lo := (577/6250 : ℝ)) (hi := (1763/10000 : ℝ)) (c := (2099473493022302473/2099500000000000000 : ℝ)) (alpha := (58619295287/839800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2099473493022302473/2099500000000000000 : ℝ)*(X 0 1+X 2 1)+(58619295287/839800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6047/1024 : ℝ)) (lo := (577/6250 : ℝ)) (hi := (1763/10000 : ℝ)) (c := (2099473493022302473/2099500000000000000 : ℝ)) (alpha := (58619295287/839800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2099473493022302473/2099500000000000000 : ℝ)*(X 0 2+X 1 2)+(58619295287/839800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6047/1024 : ℝ)) (lo := (577/6250 : ℝ)) (hi := (1763/10000 : ℝ)) (c := (2099473493022302473/2099500000000000000 : ℝ)) (alpha := (58619295287/839800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-38487593/500000000 : ℝ)*X 0 0+(675823047/1250000000 : ℝ)*X 0 1+(5406584791/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1768_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2596069373/5000000000 : ℝ)*X 1 0+(-537938863/5000000000 : ℝ)*X 1 1+(5406584529/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1768_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2596069089/5000000000 : ℝ)*X 2 0+(5406585081/10000000000 : ℝ)*X 2 1+(-1075877741/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1768_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2254528783/5000000000 : ℝ)*X 0 0+(3760198309/10000000000 : ℝ)*X 0 1+(752039661/2000000000 : ℝ)*X 0 2+(2254528783/5000000000 : ℝ)*X 1 0+(3760198309/10000000000 : ℝ)*X 1 1+(752039661/2000000000 : ℝ)*X 1 2+(2254528783/5000000000 : ℝ)*X 2 0+(3760198309/10000000000 : ℝ)*X 2 1+(752039661/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1768_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-381573133/2500000000 : ℝ)*X 0 0+(5129871987/10000000000 : ℝ)*X 0 1+(32061697/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1768_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5376015089/10000000000 : ℝ)*X 1 0+(-601229191/5000000000 : ℝ)*X 1 1+(5129871363/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1768_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2688007397/5000000000 : ℝ)*X 2 0+(5129871577/10000000000 : ℝ)*X 2 1+(-240491699/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1768_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3421854227/10000000000 : ℝ)*X 0 0+(430178257/1000000000 : ℝ)*X 0 1+(2150890959/5000000000 : ℝ)*X 0 2+(3421854227/10000000000 : ℝ)*X 1 0+(430178257/1000000000 : ℝ)*X 1 1+(2150890959/5000000000 : ℝ)*X 1 2+(3421854227/10000000000 : ℝ)*X 2 0+(430178257/1000000000 : ℝ)*X 2 1+(2150890959/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1768_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1361395103/10000000000 : ℝ)*X 0 0+(4917476189/10000000000 : ℝ)*X 0 1+(1093318193/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1768_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2576172613/5000000000 : ℝ)*X 1 0+(-1047149091/10000000000 : ℝ)*X 1 1+(5466590547/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1768_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2576172493/5000000000 : ℝ)*X 2 0+(683323837/1250000000 : ℝ)*X 2 1+(-32723413/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1768_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2367208037/5000000000 : ℝ)*X 0 0+(3642317729/10000000000 : ℝ)*X 0 1+(728463657/2000000000 : ℝ)*X 0 2+(2367208037/5000000000 : ℝ)*X 1 0+(3642317729/10000000000 : ℝ)*X 1 1+(728463657/2000000000 : ℝ)*X 1 2+(2367208037/5000000000 : ℝ)*X 2 0+(3642317729/10000000000 : ℝ)*X 2 1+(728463657/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1768_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-460026747/5000000000 : ℝ)*X 0 0+(5607182267/10000000000 : ℝ)*X 0 1+(5100397037/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1768_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1079135571/2000000000 : ℝ)*X 1 0+(-1215336421/10000000000 : ℝ)*X 1 1+(5100395459/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1768_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1079135507/2000000000 : ℝ)*X 2 0+(5100395093/10000000000 : ℝ)*X 2 1+(-607668673/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1768_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((330087053/1000000000 : ℝ)*X 0 0+(4359235853/10000000000 : ℝ)*X 0 1+(2179620281/5000000000 : ℝ)*X 0 2+(330087053/1000000000 : ℝ)*X 1 0+(4359235853/10000000000 : ℝ)*X 1 1+(2179620281/5000000000 : ℝ)*X 1 2+(330087053/1000000000 : ℝ)*X 2 0+(4359235853/10000000000 : ℝ)*X 2 1+(2179620281/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1768_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-8659/12500 : ℝ) ≤ (-36357989621478190013306148397359/52487500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (41569397/100000000000000 : ℝ)*(upper3) + (13486959/100000000000000 : ℝ)*(lower4) + (36599297/100000000000000 : ℝ)*(lower5) + (555535552919261/50000000000000 : ℝ)*(major0) + (555535552919261/50000000000000 : ℝ)*(major1) + (555535552919261/50000000000000 : ℝ)*(major2) + (3025332683/100000000000000 : ℝ)*(sp1) + (472034303/50000000000000 : ℝ)*(sp2) + (381638927/100000000000000 : ℝ)*(sp3) + (1754455688884987/100000000000000 : ℝ)*(sp4) + (109653318572809/6250000000000 : ℝ)*(sp5) + (1754455178429021/100000000000000 : ℝ)*(sp6) + (490775642999069/100000000000000 : ℝ)*(sp7) + (433612641/100000000000000 : ℝ)*(sp8) + (122694006159499/25000000000000 : ℝ)*(f.failure) + (438614030624407/25000000000000 : ℝ)*(f.sum) + (57911926186097/20995000000000000000000000000 : ℝ)*base65 + (60682404688909619/8075000000000000000000000000000 : ℝ)*base68 + (54322904451234619/8075000000000000000000000000000 : ℝ)*base70 + (56744279322990381/8075000000000000000000000000000 : ℝ)*base71 + (69853331006279/10497500000000000000000000000 : ℝ)*base74 + (20518608568715381/8075000000000000000000000000000 : ℝ)*base75 + (29059133683390381/8075000000000000000000000000000 : ℝ)*base77 + (23807621314715381/8075000000000000000000000000000 : ℝ)*base79 + (92229583679913/20995000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (4935367/500000000000000000000 : ℝ)*base89 + (4935367/500000000000000000000 : ℝ)*base91 + (4935367/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (58987/100000 : ℝ) ≤ (4763388840788187288672835161309/8075000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (45996113/50000000000000 : ℝ)*(upper2) + (32603653/50000000000000 : ℝ)*(upper3) + (1695847/4000000000000 : ℝ)*(upper4) + (20459219/100000000000000 : ℝ)*(upper5) + (1245360369884319/100000000000000 : ℝ)*(major0) + (1245360369884319/100000000000000 : ℝ)*(major1) + (1245360369884319/100000000000000 : ℝ)*(major2) + (1920961331653697/100000000000000 : ℝ)*(sp0) + (480239760526877/25000000000000 : ℝ)*(sp1) + (1920961971978689/100000000000000 : ℝ)*(sp2) + (275046758196571/50000000000000 : ℝ)*(sp3) + (534891729/25000000000000 : ℝ)*(sp6) + (2534719049/50000000000000 : ℝ)*(sp9) + (694972977/25000000000000 : ℝ)*(sp12) + (275046758196571/50000000000000 : ℝ)*(f.failure) + (960482055772803/50000000000000 : ℝ)*(f.sum) + (24947989207581/3230000000000000000000000000 : ℝ)*base65 + (102711436327561799/16150000000000000000000000000000 : ℝ)*base67 + (39826681848511799/16150000000000000000000000000000 : ℝ)*base69 + (136401836630261799/16150000000000000000000000000000 : ℝ)*base71 + (1545664548621/3230000000000000000000000000 : ℝ)*base73 + (13770200546261799/16150000000000000000000000000000 : ℝ)*base75 + (136222267525761799/16150000000000000000000000000000 : ℝ)*base77 + (162174899224611799/16150000000000000000000000000000 : ℝ)*base79 + (14939771561849/3230000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (8118057/1000000000000000000000 : ℝ)*base90 + (8118057/1000000000000000000000 : ℝ)*base92 + (8118057/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (82551/100000 : ℝ) ≤ (43330251497423784490162752693687/52487500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2009063/20000000000000 : ℝ)*(upper0) + (43706749/100000000000000 : ℝ)*(upper2) + (4503751/20000000000000 : ℝ)*(lower3) + (5238553/20000000000000 : ℝ)*(lower5) + (593162213580973/50000000000000 : ℝ)*(major0) + (593162213580973/50000000000000 : ℝ)*(major1) + (593162213580973/50000000000000 : ℝ)*(major2) + (286206421/20000000000000 : ℝ)*(sp3) + (559710093/100000000000000 : ℝ)*(sp4) + (1821113028064423/100000000000000 : ℝ)*(sp8) + (455278634231189/25000000000000 : ℝ)*(sp9) + (455278634231189/25000000000000 : ℝ)*(sp10) + (131003765928119/25000000000000 : ℝ)*(sp11) + (5932189/625000000000 : ℝ)*(sp12) + (524016494744581/100000000000000 : ℝ)*(f.failure) + (455278634231189/25000000000000 : ℝ)*(f.sum) + (2111968356219/1312187500000000000000000000 : ℝ)*base66 + (39852509983919133/8075000000000000000000000000000 : ℝ)*base67 + (20715269879055867/8075000000000000000000000000000 : ℝ)*base70 + (6878003271694133/8075000000000000000000000000000 : ℝ)*base71 + (3434737733871/5248750000000000000000000000 : ℝ)*base74 + (21434373637330867/8075000000000000000000000000000 : ℝ)*base76 + (2311819600305867/8075000000000000000000000000000 : ℝ)*base78 + (35830325431930867/8075000000000000000000000000000 : ℝ)*base80 + (16999679330701/5248750000000000000000000000 : ℝ)*base82 + (19547273/2000000000000000000000 : ℝ)*base89 + (19547273/2000000000000000000000 : ℝ)*base91 + (19547273/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-93221/100000 : ℝ) ≤ (-97856527948067813619937148446191/104975000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9715033/100000000000000 : ℝ)*(lower3) + (276347397/100000000000000 : ℝ)*(lower4) + (103315571/50000000000000 : ℝ)*(upper5) + (1246343482402937/100000000000000 : ℝ)*(major0) + (1246343482402937/100000000000000 : ℝ)*(major1) + (1246343482402937/100000000000000 : ℝ)*(major2) + (4540006597/50000000000000 : ℝ)*(sp4) + (696382099/625000000000 : ℝ)*(sp5) + (54962929673/25000000000000 : ℝ)*(sp6) + (53268330003/100000000000000 : ℝ)*(sp7) + (78928923050737/4000000000000 : ℝ)*(sp12) + (98656036757289/5000000000000 : ℝ)*(sp13) + (1973012304562927/100000000000000 : ℝ)*(sp14) + (550474502946669/100000000000000 : ℝ)*(sp15) + (4300998213099/781250000000 : ℝ)*(f.failure) + (1973232156281619/100000000000000 : ℝ)*(f.sum) + (8452643582849/41990000000000000000000000000 : ℝ)*base65 + (6778068593203023/16150000000000000000000000000000 : ℝ)*base68 + (117437513567753023/16150000000000000000000000000000 : ℝ)*base70 + (165820710287853023/16150000000000000000000000000000 : ℝ)*base72 + (129188001634989/41990000000000000000000000000 : ℝ)*base73 + (142509925628003023/16150000000000000000000000000000 : ℝ)*base76 + (53169336425803023/16150000000000000000000000000000 : ℝ)*base78 + (13042953046503023/16150000000000000000000000000000 : ℝ)*base80 + (57075705707581/41990000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (42083/15625000000000000000 : ℝ)*base90 + (42083/15625000000000000000 : ℝ)*base92 + (42083/15625000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1768_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (45278133/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1763/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (577/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(8659/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(58987/100000 : ℝ) else (82551/100000 : ℝ) ≤ X j i ∧ X j i ≤ (93221/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1768_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1768_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (45278133/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1763/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (577/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(8659/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(58987/100000 : ℝ) else (82551/100000 : ℝ) ≤ X j i ∧ X j i ≤ (93221/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1768_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (45278133/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1763/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (577/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(8659/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(58987/100000 : ℝ) else (82551/100000 : ℝ) ≤ X j i ∧ X j i ≤ (93221/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1768_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
