-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1759_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:24:56.492841+00:00
-- url     : https://prove2.me/submissions/12aac207-77fc-40a7-886e-0e70753db7c4

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
theorem support_rectangle_w1759_s0_0 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-567670253/5000000000 : ℝ)*x 0 + (5603697109/10000000000 : ℝ)*x 1 + (4990804677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (567670253/5000000000 : ℝ)^5919 ≤ (1800549607327/25000000000000 : ℝ)^4895 := by
    have hnat : (567670253 : ℕ)^5919*25000000000000^4895 ≤ 1800549607327^4895*5000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      567670253 5000000000 1800549607327 25000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5603697109/10000000000 : ℝ)^5919 ≤ (6205364691017/12500000000000 : ℝ)^4895 := by
    have hnat : (5603697109 : ℕ)^5919*12500000000000^4895 ≤ 6205364691017^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5603697109 10000000000 6205364691017 12500000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4990804677/10000000000 : ℝ)^5919 ≤ (43154884025259/100000000000000 : ℝ)^4895 := by
    have hnat : (4990804677 : ℕ)^5919*100000000000000^4895 ≤ 43154884025259^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4990804677 10000000000 43154884025259 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-567670253/5000000000 : ℝ), (5603697109/10000000000 : ℝ), (4990804677/10000000000 : ℝ)] ![(1800549607327/25000000000000 : ℝ), (6205364691017/12500000000000 : ℝ), (43154884025259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-567670253/5000000000 : ℝ)|^5919 ≤ (1800549607327/25000000000000 : ℝ)^4895
        have hw : |(-567670253/5000000000 : ℝ)|=(567670253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5603697109/10000000000 : ℝ)|^5919 ≤ (6205364691017/12500000000000 : ℝ)^4895
        have hw : |(5603697109/10000000000 : ℝ)|=(5603697109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4990804677/10000000000 : ℝ)|^5919 ≤ (43154884025259/100000000000000 : ℝ)^4895
        have hw : |(4990804677/10000000000 : ℝ)|=(4990804677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1759_s0_1 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5361538959/10000000000 : ℝ)*x 0 + (-36568999/250000000 : ℝ)*x 1 + (2495402663/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5361538959/10000000000 : ℝ)^5919 ≤ (23530367335057/50000000000000 : ℝ)^4895 := by
    have hnat : (5361538959 : ℕ)^5919*50000000000000^4895 ≤ 23530367335057^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361538959 10000000000 23530367335057 50000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (36568999/250000000 : ℝ)^5919 ≤ (4892187254357/50000000000000 : ℝ)^4895 := by
    have hnat : (36568999 : ℕ)^5919*50000000000000^4895 ≤ 4892187254357^4895*250000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36568999 250000000 4892187254357 50000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2495402663/5000000000 : ℝ)^5919 ≤ (43154890811039/100000000000000 : ℝ)^4895 := by
    have hnat : (2495402663 : ℕ)^5919*100000000000000^4895 ≤ 43154890811039^4895*5000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2495402663 5000000000 43154890811039 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5361538959/10000000000 : ℝ), (-36568999/250000000 : ℝ), (2495402663/5000000000 : ℝ)] ![(23530367335057/50000000000000 : ℝ), (4892187254357/50000000000000 : ℝ), (43154890811039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5361538959/10000000000 : ℝ)|^5919 ≤ (23530367335057/50000000000000 : ℝ)^4895
        have hw : |(5361538959/10000000000 : ℝ)|=(5361538959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-36568999/250000000 : ℝ)|^5919 ≤ (4892187254357/50000000000000 : ℝ)^4895
        have hw : |(-36568999/250000000 : ℝ)|=(36568999/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2495402663/5000000000 : ℝ)|^5919 ≤ (43154890811039/100000000000000 : ℝ)^4895
        have hw : |(2495402663/5000000000 : ℝ)|=(2495402663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1759_s0_2 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5361542603/10000000000 : ℝ)*x 0 + (2495401691/5000000000 : ℝ)*x 1 + (-146275769/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5361542603/10000000000 : ℝ)^5919 ≤ (47060773346267/100000000000000 : ℝ)^4895 := by
    have hnat : (5361542603 : ℕ)^5919*100000000000000^4895 ≤ 47060773346267^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361542603 10000000000 47060773346267 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2495401691/5000000000 : ℝ)^5919 ≤ (43154870485069/100000000000000 : ℝ)^4895 := by
    have hnat : (2495401691 : ℕ)^5919*100000000000000^4895 ≤ 43154870485069^4895*5000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2495401691 5000000000 43154870485069 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (146275769/1000000000 : ℝ)^5919 ≤ (1223044518543/12500000000000 : ℝ)^4895 := by
    have hnat : (146275769 : ℕ)^5919*12500000000000^4895 ≤ 1223044518543^4895*1000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      146275769 1000000000 1223044518543 12500000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5361542603/10000000000 : ℝ), (2495401691/5000000000 : ℝ), (-146275769/1000000000 : ℝ)] ![(47060773346267/100000000000000 : ℝ), (43154870485069/100000000000000 : ℝ), (1223044518543/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5361542603/10000000000 : ℝ)|^5919 ≤ (47060773346267/100000000000000 : ℝ)^4895
        have hw : |(5361542603/10000000000 : ℝ)|=(5361542603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2495401691/5000000000 : ℝ)|^5919 ≤ (43154870485069/100000000000000 : ℝ)^4895
        have hw : |(2495401691/5000000000 : ℝ)|=(2495401691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-146275769/1000000000 : ℝ)|^5919 ≤ (1223044518543/12500000000000 : ℝ)^4895
        have hw : |(-146275769/1000000000 : ℝ)|=(146275769/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1759_s0_3 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (792885723/2000000000 : ℝ)*x 0 + (2991966259/10000000000 : ℝ)*x 1 + (5079781853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (792885723/2000000000 : ℝ)^5919 ≤ (8167004291931/25000000000000 : ℝ)^4895 := by
    have hnat : (792885723 : ℕ)^5919*25000000000000^4895 ≤ 8167004291931^4895*2000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      792885723 2000000000 8167004291931 25000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2991966259/10000000000 : ℝ)^5919 ≤ (116225246447/500000000000 : ℝ)^4895 := by
    have hnat : (2991966259 : ℕ)^5919*500000000000^4895 ≤ 116225246447^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2991966259 10000000000 116225246447 500000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5079781853/10000000000 : ℝ)^5919 ≤ (44086933526461/100000000000000 : ℝ)^4895 := by
    have hnat : (5079781853 : ℕ)^5919*100000000000000^4895 ≤ 44086933526461^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5079781853 10000000000 44086933526461 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(792885723/2000000000 : ℝ), (2991966259/10000000000 : ℝ), (5079781853/10000000000 : ℝ)] ![(8167004291931/25000000000000 : ℝ), (116225246447/500000000000 : ℝ), (44086933526461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(792885723/2000000000 : ℝ)|^5919 ≤ (8167004291931/25000000000000 : ℝ)^4895
        have hw : |(792885723/2000000000 : ℝ)|=(792885723/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2991966259/10000000000 : ℝ)|^5919 ≤ (116225246447/500000000000 : ℝ)^4895
        have hw : |(2991966259/10000000000 : ℝ)|=(2991966259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5079781853/10000000000 : ℝ)|^5919 ≤ (44086933526461/100000000000000 : ℝ)^4895
        have hw : |(5079781853/10000000000 : ℝ)|=(5079781853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1759_s0_4 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1136529791/10000000000 : ℝ)*x 0 + (2503098621/5000000000 : ℝ)*x 1 + (1396952943/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1136529791/10000000000 : ℝ)^5919 ≤ (7211322068527/100000000000000 : ℝ)^4895 := by
    have hnat : (1136529791 : ℕ)^5919*100000000000000^4895 ≤ 7211322068527^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136529791 10000000000 7211322068527 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2503098621/5000000000 : ℝ)^5919 ≤ (21657938325827/50000000000000 : ℝ)^4895 := by
    have hnat : (2503098621 : ℕ)^5919*50000000000000^4895 ≤ 21657938325827^4895*5000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2503098621 5000000000 21657938325827 50000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1396952943/2500000000 : ℝ)^5919 ≤ (49472801265539/100000000000000 : ℝ)^4895 := by
    have hnat : (1396952943 : ℕ)^5919*100000000000000^4895 ≤ 49472801265539^4895*2500000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1396952943 2500000000 49472801265539 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1136529791/10000000000 : ℝ), (2503098621/5000000000 : ℝ), (1396952943/2500000000 : ℝ)] ![(7211322068527/100000000000000 : ℝ), (21657938325827/50000000000000 : ℝ), (49472801265539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1136529791/10000000000 : ℝ)|^5919 ≤ (7211322068527/100000000000000 : ℝ)^4895
        have hw : |(-1136529791/10000000000 : ℝ)|=(1136529791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2503098621/5000000000 : ℝ)|^5919 ≤ (21657938325827/50000000000000 : ℝ)^4895
        have hw : |(2503098621/5000000000 : ℝ)|=(2503098621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1396952943/2500000000 : ℝ)|^5919 ≤ (49472801265539/100000000000000 : ℝ)^4895
        have hw : |(1396952943/2500000000 : ℝ)|=(1396952943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1759_s0_5 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (324918837/625000000 : ℝ)*x 0 + (-216437739/2500000000 : ℝ)*x 1 + (5587811763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (324918837/625000000 : ℝ)^5919 ≤ (22668984096633/50000000000000 : ℝ)^4895 := by
    have hnat : (324918837 : ℕ)^5919*50000000000000^4895 ≤ 22668984096633^4895*625000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324918837 625000000 22668984096633 50000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216437739/2500000000 : ℝ)^5919 ≤ (2594615308963/50000000000000 : ℝ)^4895 := by
    have hnat : (216437739 : ℕ)^5919*50000000000000^4895 ≤ 2594615308963^4895*2500000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216437739 2500000000 2594615308963 50000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5587811763/10000000000 : ℝ)^5919 ≤ (49472801169187/100000000000000 : ℝ)^4895 := by
    have hnat : (5587811763 : ℕ)^5919*100000000000000^4895 ≤ 49472801169187^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5587811763 10000000000 49472801169187 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(324918837/625000000 : ℝ), (-216437739/2500000000 : ℝ), (5587811763/10000000000 : ℝ)] ![(22668984096633/50000000000000 : ℝ), (2594615308963/50000000000000 : ℝ), (49472801169187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(324918837/625000000 : ℝ)|^5919 ≤ (22668984096633/50000000000000 : ℝ)^4895
        have hw : |(324918837/625000000 : ℝ)|=(324918837/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-216437739/2500000000 : ℝ)|^5919 ≤ (2594615308963/50000000000000 : ℝ)^4895
        have hw : |(-216437739/2500000000 : ℝ)|=(216437739/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5587811763/10000000000 : ℝ)|^5919 ≤ (49472801169187/100000000000000 : ℝ)^4895
        have hw : |(5587811763/10000000000 : ℝ)|=(5587811763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1759_s0_6 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2599350319/5000000000 : ℝ)*x 0 + (5587812037/10000000000 : ℝ)*x 1 + (-865751649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2599350319/5000000000 : ℝ)^5919 ≤ (22668980121019/50000000000000 : ℝ)^4895 := by
    have hnat : (2599350319 : ℕ)^5919*50000000000000^4895 ≤ 22668980121019^4895*5000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2599350319 5000000000 22668980121019 50000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5587812037/10000000000 : ℝ)^5919 ≤ (6184100512823/12500000000000 : ℝ)^4895 := by
    have hnat : (5587812037 : ℕ)^5919*12500000000000^4895 ≤ 6184100512823^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5587812037 10000000000 6184100512823 12500000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (865751649/10000000000 : ℝ)^5919 ≤ (2594617820323/50000000000000 : ℝ)^4895 := by
    have hnat : (865751649 : ℕ)^5919*50000000000000^4895 ≤ 2594617820323^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865751649 10000000000 2594617820323 50000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2599350319/5000000000 : ℝ), (5587812037/10000000000 : ℝ), (-865751649/10000000000 : ℝ)] ![(22668980121019/50000000000000 : ℝ), (6184100512823/12500000000000 : ℝ), (2594617820323/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2599350319/5000000000 : ℝ)|^5919 ≤ (22668980121019/50000000000000 : ℝ)^4895
        have hw : |(2599350319/5000000000 : ℝ)|=(2599350319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5587812037/10000000000 : ℝ)|^5919 ≤ (6184100512823/12500000000000 : ℝ)^4895
        have hw : |(5587812037/10000000000 : ℝ)|=(5587812037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-865751649/10000000000 : ℝ)|^5919 ≤ (2594617820323/50000000000000 : ℝ)^4895
        have hw : |(-865751649/10000000000 : ℝ)|=(865751649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1759_s0_7 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (992120423/2500000000 : ℝ)*x 0 + (1005468781/2000000000 : ℝ)*x 1 + (3046079929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (992120423/2500000000 : ℝ)^5919 ≤ (32708406725467/100000000000000 : ℝ)^4895 := by
    have hnat : (992120423 : ℕ)^5919*100000000000000^4895 ≤ 32708406725467^4895*2500000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      992120423 2500000000 32708406725467 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1005468781/2000000000 : ℝ)^5919 ≤ (43537220913023/100000000000000 : ℝ)^4895 := by
    have hnat : (1005468781 : ℕ)^5919*100000000000000^4895 ≤ 43537220913023^4895*2000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005468781 2000000000 43537220913023 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3046079929/10000000000 : ℝ)^5919 ≤ (5938593088019/25000000000000 : ℝ)^4895 := by
    have hnat : (3046079929 : ℕ)^5919*25000000000000^4895 ≤ 5938593088019^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3046079929 10000000000 5938593088019 25000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(992120423/2500000000 : ℝ), (1005468781/2000000000 : ℝ), (3046079929/10000000000 : ℝ)] ![(32708406725467/100000000000000 : ℝ), (43537220913023/100000000000000 : ℝ), (5938593088019/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(992120423/2500000000 : ℝ)|^5919 ≤ (32708406725467/100000000000000 : ℝ)^4895
        have hw : |(992120423/2500000000 : ℝ)|=(992120423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1005468781/2000000000 : ℝ)|^5919 ≤ (43537220913023/100000000000000 : ℝ)^4895
        have hw : |(1005468781/2000000000 : ℝ)|=(1005468781/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3046079929/10000000000 : ℝ)|^5919 ≤ (5938593088019/25000000000000 : ℝ)^4895
        have hw : |(3046079929/10000000000 : ℝ)|=(3046079929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1759_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (220324357/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (7067/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10173/50000 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (5903/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5903 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5903*1^1024 ≤ 0^1024*1^5903 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5903 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5903 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5903/1024 : ℝ) ≤ (508177872584757577/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5903 ≤ (508177872584757577/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5903*100000000000000000000^1024 ≤ 508177872584757577^1024*5^5903 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 508177872584757577 100000000000000000000 5903 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (508177872584757577/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5903 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5903/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5903 := by
      have hnat : (1 : ℕ)^1024*1^5903 ≤ 1^5903*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5903 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5903 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100508177872584757577/100000000000000000000 : ℝ) ≤ (10008796961940919/10000000000000000 : ℝ) ^ (5903/1024 : ℝ) := by
    have hpowers : (100508177872584757577/100000000000000000000 : ℝ)^1024 ≤ (10008796961940919/10000000000000000 : ℝ)^5903 := by
      have hnat : (100508177872584757577 : ℕ)^1024*10000000000000000^5903 ≤ 10008796961940919^5903*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100508177872584757577 100000000000000000000 10008796961940919 10000000000000000 1024 5903 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008796961940919/10000000000000000 : ℝ)) (X := (100508177872584757577/100000000000000000000 : ℝ)) (by norm_num) 5903 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50508177872584757577/50000000000000000000 : ℝ) ≤ (5008796961940919/5000000000000000 : ℝ) ^ (5903/1024 : ℝ) := by
    have hpowers : (50508177872584757577/50000000000000000000 : ℝ)^1024 ≤ (5008796961940919/5000000000000000 : ℝ)^5903 := by
      have hnat : (50508177872584757577 : ℕ)^1024*5000000000000000^5903 ≤ 5008796961940919^5903*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50508177872584757577 50000000000000000000 5008796961940919 5000000000000000 1024 5903 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5008796961940919/5000000000000000 : ℝ)) (X := (50508177872584757577/50000000000000000000 : ℝ)) (by norm_num) 5903 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(8796961940919/4000000000000000 : ℝ)*(0 : ℝ))^(5903/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(8796961940919/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(508177872584757577/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(8796961940919/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5903/1024 : ℝ) := by
    rw [show (1 : ℝ)+(8796961940919/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10008796961940919/10000000000000000 : ℝ) by norm_num, show 1+(508177872584757577/100000000000000000000 : ℝ)+(0 : ℝ)=(100508177872584757577/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(508177872584757577/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(8796961940919/4000000000000000 : ℝ)*(2/5 : ℝ))^(5903/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(8796961940919/4000000000000000 : ℝ)*(2/5 : ℝ)=(5008796961940919/5000000000000000 : ℝ) by norm_num, show 1+2*(508177872584757577/100000000000000000000 : ℝ)=(50508177872584757577/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(8796961940919/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5903/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (8796961940919/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(8796961940919/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5903/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (8796961940919/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(8796961940919/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5903/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (8796961940919/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-567670253/5000000000 : ℝ)*X 0 0+(5603697109/10000000000 : ℝ)*X 0 1+(4990804677/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5361538959/10000000000 : ℝ)*X 1 0+(-36568999/250000000 : ℝ)*X 1 1+(2495402663/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5361542603/10000000000 : ℝ)*X 2 0+(2495401691/5000000000 : ℝ)*X 2 1+(-146275769/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((792885723/2000000000 : ℝ)*X 0 0+(2991966259/10000000000 : ℝ)*X 0 1+(5079781853/10000000000 : ℝ)*X 0 2+(792885723/2000000000 : ℝ)*X 1 0+(2991966259/10000000000 : ℝ)*X 1 1+(5079781853/10000000000 : ℝ)*X 1 2+(792885723/2000000000 : ℝ)*X 2 0+(2991966259/10000000000 : ℝ)*X 2 1+(5079781853/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1136529791/10000000000 : ℝ)*X 0 0+(2503098621/5000000000 : ℝ)*X 0 1+(1396952943/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((324918837/625000000 : ℝ)*X 1 0+(-216437739/2500000000 : ℝ)*X 1 1+(5587811763/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2599350319/5000000000 : ℝ)*X 2 0+(5587812037/10000000000 : ℝ)*X 2 1+(-865751649/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((992120423/2500000000 : ℝ)*X 0 0+(1005468781/2000000000 : ℝ)*X 0 1+(3046079929/10000000000 : ℝ)*X 0 2+(992120423/2500000000 : ℝ)*X 1 0+(1005468781/2000000000 : ℝ)*X 1 1+(3046079929/10000000000 : ℝ)*X 1 2+(992120423/2500000000 : ℝ)*X 2 0+(1005468781/2000000000 : ℝ)*X 2 1+(3046079929/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1085322801786044451059037/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (719230019/100000000000000 : ℝ)*(base19) + (263512991/20000000000000 : ℝ)*(base23) + (14923741/6250000000000 : ℝ)*(base24) + (145737907/100000000000000 : ℝ)*(upper4) + (292838287/100000000000000 : ℝ)*(upper5) + (1055294640681959/100000000000000 : ℝ)*(major0) + (1055294640681959/100000000000000 : ℝ)*(major1) + (1055294640681959/100000000000000 : ℝ)*(major2) + (407902021019549/25000000000000 : ℝ)*(sp0) + (815807586633889/50000000000000 : ℝ)*(sp1) + (326322867230597/20000000000000 : ℝ)*(sp2) + (95794280589937/20000000000000 : ℝ)*(sp3) + (7808419601/100000000000000 : ℝ)*(sp4) + (902514647/50000000000000 : ℝ)*(sp7) + (478973207978979/100000000000000 : ℝ)*(f.failure) + (407903973124449/25000000000000 : ℝ)*(f.sum) + (340633804019679/200000000000000000000000000000 : ℝ)*base66 + (227899510780321/400000000000000000000000000000 : ℝ)*base67 + (880993589180321/400000000000000000000000000000 : ℝ)*base69 + (1202571502819679/400000000000000000000000000000 : ℝ)*base72 + (561649906180321/200000000000000000000000000000 : ℝ)*base73 + (3979905603580321/400000000000000000000000000000 : ℝ)*base75 + (750725755980321/400000000000000000000000000000 : ℝ)*base77 + (1968971725180321/400000000000000000000000000000 : ℝ)*base79 + (1099317929019679/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (82308497/10000000000000000000000 : ℝ)*base90 + (82308497/10000000000000000000000 : ℝ)*base92 + (82308497/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1923061645733235201/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (924862931/100000000000000 : ℝ)*(base19) + (156646131/20000000000000 : ℝ)*(base23) + (77227701/100000000000000 : ℝ)*(upper2) + (31486467/20000000000000 : ℝ)*(upper3) + (60312501/50000000000000 : ℝ)*(upper5) + (1112039196414923/100000000000000 : ℝ)*(major0) + (1112039196414923/100000000000000 : ℝ)*(major1) + (1112039196414923/100000000000000 : ℝ)*(major2) + (2086134831/50000000000000 : ℝ)*(sp1) + (2869105121/100000000000000 : ℝ)*(sp2) + (429837528191551/25000000000000 : ℝ)*(sp4) + (429836253908403/25000000000000 : ℝ)*(sp5) + (1719346460430429/100000000000000 : ℝ)*(sp6) + (25236410798079/5000000000000 : ℝ)*(sp7) + (25236410798079/5000000000000 : ℝ)*(f.failure) + (429837528191551/25000000000000 : ℝ)*(f.sum) + (202181463265763/200000000000000000000000000000 : ℝ)*base66 + (872988828734237/400000000000000000000000000000 : ℝ)*base67 + (38868012734237/400000000000000000000000000000 : ℝ)*base69 + (1029316712865763/400000000000000000000000000000 : ℝ)*base72 + (1326879874334237/200000000000000000000000000000 : ℝ)*base73 + (1742989699265763/400000000000000000000000000000 : ℝ)*base76 + (1425610274065763/400000000000000000000000000000 : ℝ)*base78 + (1971804662065763/400000000000000000000000000000 : ℝ)*base80 + (235006554134237/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2489797/500000000000000000000 : ℝ)*base90 + (2489797/500000000000000000000 : ℝ)*base92 + (2489797/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1759_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (220324357/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7067/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10173/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1759_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1759_s1_0 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1173087413/10000000000 : ℝ)*x 0 + (5487390381/10000000000 : ℝ)*x 1 + (31760897/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1173087413/10000000000 : ℝ)^5919 ≤ (7492741568733/100000000000000 : ℝ)^4895 := by
    have hnat : (1173087413 : ℕ)^5919*100000000000000^4895 ≤ 7492741568733^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1173087413 10000000000 7492741568733 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5487390381/10000000000 : ℝ)^5919 ≤ (48399737407577/100000000000000 : ℝ)^4895 := by
    have hnat : (5487390381 : ℕ)^5919*100000000000000^4895 ≤ 48399737407577^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5487390381 10000000000 48399737407577 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (31760897/62500000 : ℝ)^5919 ≤ (22053760505837/50000000000000 : ℝ)^4895 := by
    have hnat : (31760897 : ℕ)^5919*50000000000000^4895 ≤ 22053760505837^4895*62500000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31760897 62500000 22053760505837 50000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1173087413/10000000000 : ℝ), (5487390381/10000000000 : ℝ), (31760897/62500000 : ℝ)] ![(7492741568733/100000000000000 : ℝ), (48399737407577/100000000000000 : ℝ), (22053760505837/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1173087413/10000000000 : ℝ)|^5919 ≤ (7492741568733/100000000000000 : ℝ)^4895
        have hw : |(-1173087413/10000000000 : ℝ)|=(1173087413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5487390381/10000000000 : ℝ)|^5919 ≤ (48399737407577/100000000000000 : ℝ)^4895
        have hw : |(5487390381/10000000000 : ℝ)|=(5487390381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(31760897/62500000 : ℝ)|^5919 ≤ (22053760505837/50000000000000 : ℝ)^4895
        have hw : |(31760897/62500000 : ℝ)|=(31760897/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1759_s1_1 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5330649897/10000000000 : ℝ)*x 0 + (-1385051941/10000000000 : ℝ)*x 1 + (5081743387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5330649897/10000000000 : ℝ)^5919 ≤ (2336654337503/5000000000000 : ℝ)^4895 := by
    have hnat : (5330649897 : ℕ)^5919*5000000000000^4895 ≤ 2336654337503^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5330649897 10000000000 2336654337503 5000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1385051941/10000000000 : ℝ)^5919 ≤ (572462101653/6250000000000 : ℝ)^4895 := by
    have hnat : (1385051941 : ℕ)^5919*6250000000000^4895 ≤ 572462101653^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1385051941 10000000000 572462101653 6250000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5081743387/10000000000 : ℝ)^5919 ≤ (44107519615797/100000000000000 : ℝ)^4895 := by
    have hnat : (5081743387 : ℕ)^5919*100000000000000^4895 ≤ 44107519615797^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5081743387 10000000000 44107519615797 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5330649897/10000000000 : ℝ), (-1385051941/10000000000 : ℝ), (5081743387/10000000000 : ℝ)] ![(2336654337503/5000000000000 : ℝ), (572462101653/6250000000000 : ℝ), (44107519615797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5330649897/10000000000 : ℝ)|^5919 ≤ (2336654337503/5000000000000 : ℝ)^4895
        have hw : |(5330649897/10000000000 : ℝ)|=(5330649897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1385051941/10000000000 : ℝ)|^5919 ≤ (572462101653/6250000000000 : ℝ)^4895
        have hw : |(-1385051941/10000000000 : ℝ)|=(1385051941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5081743387/10000000000 : ℝ)|^5919 ≤ (44107519615797/100000000000000 : ℝ)^4895
        have hw : |(5081743387/10000000000 : ℝ)|=(5081743387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1759_s1_2 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5330649663/10000000000 : ℝ)*x 0 + (1270435913/2500000000 : ℝ)*x 1 + (-692525951/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5330649663/10000000000 : ℝ)^5919 ≤ (9346616853893/20000000000000 : ℝ)^4895 := by
    have hnat : (5330649663 : ℕ)^5919*20000000000000^4895 ≤ 9346616853893^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5330649663 10000000000 9346616853893 20000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1270435913/2500000000 : ℝ)^5919 ≤ (344590018727/781250000000 : ℝ)^4895 := by
    have hnat : (1270435913 : ℕ)^5919*781250000000^4895 ≤ 344590018727^4895*2500000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1270435913 2500000000 344590018727 781250000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (692525951/5000000000 : ℝ)^5919 ≤ (9159393314587/100000000000000 : ℝ)^4895 := by
    have hnat : (692525951 : ℕ)^5919*100000000000000^4895 ≤ 9159393314587^4895*5000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      692525951 5000000000 9159393314587 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5330649663/10000000000 : ℝ), (1270435913/2500000000 : ℝ), (-692525951/5000000000 : ℝ)] ![(9346616853893/20000000000000 : ℝ), (344590018727/781250000000 : ℝ), (9159393314587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5330649663/10000000000 : ℝ)|^5919 ≤ (9346616853893/20000000000000 : ℝ)^4895
        have hw : |(5330649663/10000000000 : ℝ)|=(5330649663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1270435913/2500000000 : ℝ)|^5919 ≤ (344590018727/781250000000 : ℝ)^4895
        have hw : |(1270435913/2500000000 : ℝ)|=(1270435913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-692525951/5000000000 : ℝ)|^5919 ≤ (9159393314587/100000000000000 : ℝ)^4895
        have hw : |(-692525951/5000000000 : ℝ)|=(692525951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1759_s1_3 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4002033393/10000000000 : ℝ)*x 0 + (3342257041/10000000000 : ℝ)*x 1 + (4724087909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4002033393/10000000000 : ℝ)^5919 ≤ (33043085543843/100000000000000 : ℝ)^4895 := by
    have hnat : (4002033393 : ℕ)^5919*100000000000000^4895 ≤ 33043085543843^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4002033393 10000000000 33043085543843 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3342257041/10000000000 : ℝ)^5919 ≤ (26574939763269/100000000000000 : ℝ)^4895 := by
    have hnat : (3342257041 : ℕ)^5919*100000000000000^4895 ≤ 26574939763269^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3342257041 10000000000 26574939763269 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4724087909/10000000000 : ℝ)^5919 ≤ (40381974691379/100000000000000 : ℝ)^4895 := by
    have hnat : (4724087909 : ℕ)^5919*100000000000000^4895 ≤ 40381974691379^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4724087909 10000000000 40381974691379 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4002033393/10000000000 : ℝ), (3342257041/10000000000 : ℝ), (4724087909/10000000000 : ℝ)] ![(33043085543843/100000000000000 : ℝ), (26574939763269/100000000000000 : ℝ), (40381974691379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4002033393/10000000000 : ℝ)|^5919 ≤ (33043085543843/100000000000000 : ℝ)^4895
        have hw : |(4002033393/10000000000 : ℝ)|=(4002033393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3342257041/10000000000 : ℝ)|^5919 ≤ (26574939763269/100000000000000 : ℝ)^4895
        have hw : |(3342257041/10000000000 : ℝ)|=(3342257041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4724087909/10000000000 : ℝ)|^5919 ≤ (40381974691379/100000000000000 : ℝ)^4895
        have hw : |(4724087909/10000000000 : ℝ)|=(4724087909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1759_s1_4 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-586714951/5000000000 : ℝ)*x 0 + (1272125901/2500000000 : ℝ)*x 1 + (2740244089/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (586714951/5000000000 : ℝ)^5919 ≤ (7495386813787/100000000000000 : ℝ)^4895 := by
    have hnat : (586714951 : ℕ)^5919*100000000000000^4895 ≤ 7495386813787^4895*5000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      586714951 5000000000 7495386813787 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1272125901/2500000000 : ℝ)^5919 ≤ (44178480103241/100000000000000 : ℝ)^4895 := by
    have hnat : (1272125901 : ℕ)^5919*100000000000000^4895 ≤ 44178480103241^4895*2500000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1272125901 2500000000 44178480103241 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2740244089/5000000000 : ℝ)^5919 ≤ (24163066539177/50000000000000 : ℝ)^4895 := by
    have hnat : (2740244089 : ℕ)^5919*50000000000000^4895 ≤ 24163066539177^4895*5000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2740244089 5000000000 24163066539177 50000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-586714951/5000000000 : ℝ), (1272125901/2500000000 : ℝ), (2740244089/5000000000 : ℝ)] ![(7495386813787/100000000000000 : ℝ), (44178480103241/100000000000000 : ℝ), (24163066539177/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-586714951/5000000000 : ℝ)|^5919 ≤ (7495386813787/100000000000000 : ℝ)^4895
        have hw : |(-586714951/5000000000 : ℝ)|=(586714951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1272125901/2500000000 : ℝ)|^5919 ≤ (44178480103241/100000000000000 : ℝ)^4895
        have hw : |(1272125901/2500000000 : ℝ)|=(1272125901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2740244089/5000000000 : ℝ)|^5919 ≤ (24163066539177/50000000000000 : ℝ)^4895
        have hw : |(2740244089/5000000000 : ℝ)|=(2740244089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1759_s1_5 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (522340247/1000000000 : ℝ)*x 0 + (-30822113/312500000 : ℝ)*x 1 + (1096097641/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (522340247/1000000000 : ℝ)^5919 ≤ (11399645023509/25000000000000 : ℝ)^4895 := by
    have hnat : (522340247 : ℕ)^5919*25000000000000^4895 ≤ 11399645023509^4895*1000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522340247 1000000000 11399645023509 25000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (30822113/312500000 : ℝ)^5919 ≤ (6075286528659/100000000000000 : ℝ)^4895 := by
    have hnat : (30822113 : ℕ)^5919*100000000000000^4895 ≤ 6075286528659^4895*312500000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30822113 312500000 6075286528659 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1096097641/2000000000 : ℝ)^5919 ≤ (48326133366241/100000000000000 : ℝ)^4895 := by
    have hnat : (1096097641 : ℕ)^5919*100000000000000^4895 ≤ 48326133366241^4895*2000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096097641 2000000000 48326133366241 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(522340247/1000000000 : ℝ), (-30822113/312500000 : ℝ), (1096097641/2000000000 : ℝ)] ![(11399645023509/25000000000000 : ℝ), (6075286528659/100000000000000 : ℝ), (48326133366241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(522340247/1000000000 : ℝ)|^5919 ≤ (11399645023509/25000000000000 : ℝ)^4895
        have hw : |(522340247/1000000000 : ℝ)|=(522340247/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-30822113/312500000 : ℝ)|^5919 ≤ (6075286528659/100000000000000 : ℝ)^4895
        have hw : |(-30822113/312500000 : ℝ)|=(30822113/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1096097641/2000000000 : ℝ)|^5919 ≤ (48326133366241/100000000000000 : ℝ)^4895
        have hw : |(1096097641/2000000000 : ℝ)|=(1096097641/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1759_s1_6 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1305851077/2500000000 : ℝ)*x 0 + (2740243091/5000000000 : ℝ)*x 1 + (-986307907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1305851077/2500000000 : ℝ)^5919 ≤ (45598599495701/100000000000000 : ℝ)^4895 := by
    have hnat : (1305851077 : ℕ)^5919*100000000000000^4895 ≤ 45598599495701^4895*2500000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305851077 2500000000 45598599495701 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2740243091/5000000000 : ℝ)^5919 ≤ (24163055898017/50000000000000 : ℝ)^4895 := by
    have hnat : (2740243091 : ℕ)^5919*50000000000000^4895 ≤ 24163055898017^4895*5000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2740243091 5000000000 24163055898017 50000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (986307907/10000000000 : ℝ)^5919 ≤ (6075288696079/100000000000000 : ℝ)^4895 := by
    have hnat : (986307907 : ℕ)^5919*100000000000000^4895 ≤ 6075288696079^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      986307907 10000000000 6075288696079 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1305851077/2500000000 : ℝ), (2740243091/5000000000 : ℝ), (-986307907/10000000000 : ℝ)] ![(45598599495701/100000000000000 : ℝ), (24163055898017/50000000000000 : ℝ), (6075288696079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1305851077/2500000000 : ℝ)|^5919 ≤ (45598599495701/100000000000000 : ℝ)^4895
        have hw : |(1305851077/2500000000 : ℝ)|=(1305851077/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2740243091/5000000000 : ℝ)|^5919 ≤ (24163055898017/50000000000000 : ℝ)^4895
        have hw : |(2740243091/5000000000 : ℝ)|=(2740243091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-986307907/10000000000 : ℝ)|^5919 ≤ (6075288696079/100000000000000 : ℝ)^4895
        have hw : |(-986307907/10000000000 : ℝ)|=(986307907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1759_s1_7 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1000800987/2500000000 : ℝ)*x 0 + (188042307/400000000 : ℝ)*x 1 + (1682885357/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1000800987/2500000000 : ℝ)^5919 ≤ (16527386239577/50000000000000 : ℝ)^4895 := by
    have hnat : (1000800987 : ℕ)^5919*50000000000000^4895 ≤ 16527386239577^4895*2500000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000800987 2500000000 16527386239577 50000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (188042307/400000000 : ℝ)^5919 ≤ (10036012189589/25000000000000 : ℝ)^4895 := by
    have hnat : (188042307 : ℕ)^5919*25000000000000^4895 ≤ 10036012189589^4895*400000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188042307 400000000 10036012189589 25000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1682885357/5000000000 : ℝ)^5919 ≤ (2680117874323/10000000000000 : ℝ)^4895 := by
    have hnat : (1682885357 : ℕ)^5919*10000000000000^4895 ≤ 2680117874323^4895*5000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1682885357 5000000000 2680117874323 10000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1000800987/2500000000 : ℝ), (188042307/400000000 : ℝ), (1682885357/5000000000 : ℝ)] ![(16527386239577/50000000000000 : ℝ), (10036012189589/25000000000000 : ℝ), (2680117874323/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1000800987/2500000000 : ℝ)|^5919 ≤ (16527386239577/50000000000000 : ℝ)^4895
        have hw : |(1000800987/2500000000 : ℝ)|=(1000800987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(188042307/400000000 : ℝ)|^5919 ≤ (10036012189589/25000000000000 : ℝ)^4895
        have hw : |(188042307/400000000 : ℝ)|=(188042307/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1682885357/5000000000 : ℝ)|^5919 ≤ (2680117874323/10000000000000 : ℝ)^4895
        have hw : |(1682885357/5000000000 : ℝ)|=(1682885357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1759_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (220324357/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10173/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7067/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4553/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17849/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10173/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7067/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10173/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7067/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10173/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7067/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10173/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7067/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10173/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7067/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10173/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7067/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7067/100000 : ℝ) ^ (5903/1024 : ℝ) ≤ (23240467887523/100000000000000000000 : ℝ) := by
    have hpowers : (7067/100000 : ℝ)^5903 ≤ (23240467887523/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7067 : ℕ)^5903*100000000000000000000^1024 ≤ 23240467887523^1024*100000^5903 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7067 100000 23240467887523 100000000000000000000 5903 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7067/100000 : ℝ)) (X := (23240467887523/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5903 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (10173/50000 : ℝ) ^ (5903/1024 : ℝ) ≤ (2063739017123233/20000000000000000000 : ℝ) := by
    have hpowers : (10173/50000 : ℝ)^5903 ≤ (2063739017123233/20000000000000000000 : ℝ)^1024 := by
      have hnat : (10173 : ℕ)^5903*20000000000000000000^1024 ≤ 2063739017123233^1024*50000^5903 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10173 50000 2063739017123233 20000000000000000000 5903 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10173/50000 : ℝ)) (X := (2063739017123233/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5903 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000023240467887523/50000000000000000000 : ℝ) ≤ (2500000201577457/2500000000000000 : ℝ) ^ (5903/1024 : ℝ) := by
    have hpowers : (50000023240467887523/50000000000000000000 : ℝ)^1024 ≤ (2500000201577457/2500000000000000 : ℝ)^5903 := by
      have hnat : (50000023240467887523 : ℕ)^1024*2500000000000000^5903 ≤ 2500000201577457^5903*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000023240467887523 50000000000000000000 2500000201577457 2500000000000000 1024 5903 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000201577457/2500000000000000 : ℝ)) (X := (50000023240467887523/50000000000000000000 : ℝ)) (by norm_num) 5903 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12501292741944187961/12500000000000000000 : ℝ) ≤ (2000035879008699/2000000000000000 : ℝ) ^ (5903/1024 : ℝ) := by
    have hpowers : (12501292741944187961/12500000000000000000 : ℝ)^1024 ≤ (2000035879008699/2000000000000000 : ℝ)^5903 := by
      have hnat : (12501292741944187961 : ℕ)^1024*2000000000000000^5903 ≤ 2000035879008699^5903*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501292741944187961 12500000000000000000 2000035879008699 2000000000000000 1024 5903 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000035879008699/2000000000000000 : ℝ)) (X := (12501292741944187961/12500000000000000000 : ℝ)) (by norm_num) 5903 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10002063739017123233/10000000000000000000 : ℝ) ≤ (5000178991888581/5000000000000000 : ℝ) ^ (5903/1024 : ℝ) := by
    have hpowers : (10002063739017123233/10000000000000000000 : ℝ)^1024 ≤ (5000178991888581/5000000000000000 : ℝ)^5903 := by
      have hnat : (10002063739017123233 : ℕ)^1024*5000000000000000^5903 ≤ 5000178991888581^5903*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002063739017123233 10000000000000000000 5000178991888581 5000000000000000 1024 5903 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000178991888581/5000000000000000 : ℝ)) (X := (10002063739017123233/10000000000000000000 : ℝ)) (by norm_num) 5903 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(23240467887523/100000000000000000000 : ℝ) ≤ ((66393743266913278317/66395000000000000000 : ℝ)+2*(178588733667/1327900000000000 : ℝ)*(7067/100000 : ℝ))^(5903/1024 : ℝ) := by
    rw [show (66393743266913278317/66395000000000000000 : ℝ)+2*(178588733667/1327900000000000 : ℝ)*(7067/100000 : ℝ)=(2500000201577457/2500000000000000 : ℝ) by norm_num, show 1+2*(23240467887523/100000000000000000000 : ℝ)=(50000023240467887523/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2063739017123233/20000000000000000000 : ℝ)+(23240467887523/100000000000000000000 : ℝ) ≤ ((66393743266913278317/66395000000000000000 : ℝ)+(178588733667/1327900000000000 : ℝ)*((10173/50000 : ℝ)+(7067/100000 : ℝ)))^(5903/1024 : ℝ) := by
    rw [show (66393743266913278317/66395000000000000000 : ℝ)+(178588733667/1327900000000000 : ℝ)*((10173/50000 : ℝ)+(7067/100000 : ℝ))=(2000035879008699/2000000000000000 : ℝ) by norm_num, show 1+(2063739017123233/20000000000000000000 : ℝ)+(23240467887523/100000000000000000000 : ℝ)=(12501292741944187961/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2063739017123233/20000000000000000000 : ℝ) ≤ ((66393743266913278317/66395000000000000000 : ℝ)+2*(178588733667/1327900000000000 : ℝ)*(10173/50000 : ℝ))^(5903/1024 : ℝ) := by
    rw [show (66393743266913278317/66395000000000000000 : ℝ)+2*(178588733667/1327900000000000 : ℝ)*(10173/50000 : ℝ)=(5000178991888581/5000000000000000 : ℝ) by norm_num, show 1+2*(2063739017123233/20000000000000000000 : ℝ)=(10002063739017123233/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (66393743266913278317/66395000000000000000 : ℝ)*(X 1 0+X 2 0)+(178588733667/1327900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5903/1024 : ℝ)) (lo := (7067/100000 : ℝ)) (hi := (10173/50000 : ℝ)) (c := (66393743266913278317/66395000000000000000 : ℝ)) (alpha := (178588733667/1327900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (66393743266913278317/66395000000000000000 : ℝ)*(X 0 1+X 2 1)+(178588733667/1327900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5903/1024 : ℝ)) (lo := (7067/100000 : ℝ)) (hi := (10173/50000 : ℝ)) (c := (66393743266913278317/66395000000000000000 : ℝ)) (alpha := (178588733667/1327900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (66393743266913278317/66395000000000000000 : ℝ)*(X 0 2+X 1 2)+(178588733667/1327900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5903/1024 : ℝ)) (lo := (7067/100000 : ℝ)) (hi := (10173/50000 : ℝ)) (c := (66393743266913278317/66395000000000000000 : ℝ)) (alpha := (178588733667/1327900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1173087413/10000000000 : ℝ)*X 0 0+(5487390381/10000000000 : ℝ)*X 0 1+(31760897/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5330649897/10000000000 : ℝ)*X 1 0+(-1385051941/10000000000 : ℝ)*X 1 1+(5081743387/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5330649663/10000000000 : ℝ)*X 2 0+(1270435913/2500000000 : ℝ)*X 2 1+(-692525951/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4002033393/10000000000 : ℝ)*X 0 0+(3342257041/10000000000 : ℝ)*X 0 1+(4724087909/10000000000 : ℝ)*X 0 2+(4002033393/10000000000 : ℝ)*X 1 0+(3342257041/10000000000 : ℝ)*X 1 1+(4724087909/10000000000 : ℝ)*X 1 2+(4002033393/10000000000 : ℝ)*X 2 0+(3342257041/10000000000 : ℝ)*X 2 1+(4724087909/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-586714951/5000000000 : ℝ)*X 0 0+(1272125901/2500000000 : ℝ)*X 0 1+(2740244089/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((522340247/1000000000 : ℝ)*X 1 0+(-30822113/312500000 : ℝ)*X 1 1+(1096097641/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1305851077/2500000000 : ℝ)*X 2 0+(2740243091/5000000000 : ℝ)*X 2 1+(-986307907/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1000800987/2500000000 : ℝ)*X 0 0+(188042307/400000000 : ℝ)*X 0 1+(1682885357/5000000000 : ℝ)*X 0 2+(1000800987/2500000000 : ℝ)*X 1 0+(188042307/400000000 : ℝ)*X 1 1+(1682885357/5000000000 : ℝ)*X 1 2+(1000800987/2500000000 : ℝ)*X 2 0+(188042307/400000000 : ℝ)*X 2 1+(1682885357/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17329076151833892134781403557/1659875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (749106383/50000000000000 : ℝ)*(base19) + (52861259/4000000000000 : ℝ)*(base23) + (36496459/100000000000000 : ℝ)*(lower2) + (123805431/50000000000000 : ℝ)*(upper3) + (102559937/50000000000000 : ℝ)*(upper5) + (1594453123328907/100000000000000 : ℝ)*(major0) + (1594453123328907/100000000000000 : ℝ)*(major1) + (1594453123328907/100000000000000 : ℝ)*(major2) + (1232604997842319/50000000000000 : ℝ)*(sp0) + (493043988985491/20000000000000 : ℝ)*(sp1) + (1232610060804373/50000000000000 : ℝ)*(sp2) + (45230053146851/6250000000000 : ℝ)*(sp3) + (11447455583/100000000000000 : ℝ)*(sp4) + (3605168349/100000000000000 : ℝ)*(sp7) + (144736891103593/20000000000000 : ℝ)*(f.failure) + (123261072157011/5000000000000 : ℝ)*(f.sum) + (120740126422869/66395000000000000000000000000 : ℝ)*base65 + (39677724170498640481/6639500000000000000000000000000000 : ℝ)*base68 + (33676974764907140481/6639500000000000000000000000000000 : ℝ)*base70 + (27520469197758359519/6639500000000000000000000000000000 : ℝ)*base71 + (55563171101051/66395000000000000000000000000 : ℝ)*base74 + (104781681190271640481/6639500000000000000000000000000000 : ℝ)*base76 + (20380405811330140481/6639500000000000000000000000000000 : ℝ)*base78 + (27840107712887640481/6639500000000000000000000000000000 : ℝ)*base80 + (7116725754959/66395000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (8114701/2000000000000000000000 : ℝ)*base89 + (8114701/2000000000000000000000 : ℝ)*base91 + (8114701/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1877004309752158124550119577/207484375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (847332701/100000000000000 : ℝ)*(base19) + (9263381/390625000000 : ℝ)*(base23) + (1614547/1562500000000 : ℝ)*(upper3) + (160373871/50000000000000 : ℝ)*(lower4) + (326997537/100000000000000 : ℝ)*(upper5) + (103125763139677/6250000000000 : ℝ)*(major0) + (103125763139677/6250000000000 : ℝ)*(major1) + (103125763139677/6250000000000 : ℝ)*(major2) + (7185298069/100000000000000 : ℝ)*(sp1) + (7786989067/100000000000000 : ℝ)*(sp2) + (2551122711603291/100000000000000 : ℝ)*(sp4) + (1275557339486261/50000000000000 : ℝ)*(sp5) + (159444534574293/6250000000000 : ℝ)*(sp6) + (5850792244663/781250000000 : ℝ)*(sp7) + (5850792244663/781250000000 : ℝ)*(f.failure) + (2551122711603291/100000000000000 : ℝ)*(f.sum) + (63745247385447/33197500000000000000000000000 : ℝ)*base65 + (61864271311691391/414968750000000000000000000000000 : ℝ)*base68 + (789313922301378891/414968750000000000000000000000000 : ℝ)*base70 + (600811301409785141/414968750000000000000000000000000 : ℝ)*base72 + (5168715644061/66395000000000000000000000000 : ℝ)*base74 + (2595809380497785141/414968750000000000000000000000000 : ℝ)*base76 + (263060644913089859/414968750000000000000000000000000 : ℝ)*base77 + (1941770369783808609/414968750000000000000000000000000 : ℝ)*base79 + (102236869839113/33197500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (343309/78125000000000000000 : ℝ)*base90 + (343309/78125000000000000000 : ℝ)*base92 + (343309/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1759_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (220324357/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10173/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7067/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4553/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17849/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1759_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1759_s2_0 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1173773609/10000000000 : ℝ)*x 0 + (5485181503/10000000000 : ℝ)*x 1 + (2541741511/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1173773609/10000000000 : ℝ)^5919 ≤ (3749020814277/50000000000000 : ℝ)^4895 := by
    have hnat : (1173773609 : ℕ)^5919*50000000000000^4895 ≤ 3749020814277^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1173773609 10000000000 3749020814277 50000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5485181503/10000000000 : ℝ)^5919 ≤ (48376180068479/100000000000000 : ℝ)^4895 := by
    have hnat : (5485181503 : ℕ)^5919*100000000000000^4895 ≤ 48376180068479^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5485181503 10000000000 48376180068479 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2541741511/5000000000 : ℝ)^5919 ≤ (11031444572451/25000000000000 : ℝ)^4895 := by
    have hnat : (2541741511 : ℕ)^5919*25000000000000^4895 ≤ 11031444572451^4895*5000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2541741511 5000000000 11031444572451 25000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1173773609/10000000000 : ℝ), (5485181503/10000000000 : ℝ), (2541741511/5000000000 : ℝ)] ![(3749020814277/50000000000000 : ℝ), (48376180068479/100000000000000 : ℝ), (11031444572451/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1173773609/10000000000 : ℝ)|^5919 ≤ (3749020814277/50000000000000 : ℝ)^4895
        have hw : |(-1173773609/10000000000 : ℝ)|=(1173773609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5485181503/10000000000 : ℝ)|^5919 ≤ (48376180068479/100000000000000 : ℝ)^4895
        have hw : |(5485181503/10000000000 : ℝ)|=(5485181503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2541741511/5000000000 : ℝ)|^5919 ≤ (11031444572451/25000000000000 : ℝ)^4895
        have hw : |(2541741511/5000000000 : ℝ)|=(2541741511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1759_s2_1 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5330032939/10000000000 : ℝ)*x 0 + (-1383586269/10000000000 : ℝ)*x 1 + (317717691/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5330032939/10000000000 : ℝ)^5919 ≤ (46726546561141/100000000000000 : ℝ)^4895 := by
    have hnat : (5330032939 : ℕ)^5919*100000000000000^4895 ≤ 46726546561141^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5330032939 10000000000 46726546561141 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1383586269/10000000000 : ℝ)^5919 ≤ (9147674775993/100000000000000 : ℝ)^4895 := by
    have hnat : (1383586269 : ℕ)^5919*100000000000000^4895 ≤ 9147674775993^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1383586269 10000000000 9147674775993 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (317717691/625000000 : ℝ)^5919 ≤ (4412577864667/10000000000000 : ℝ)^4895 := by
    have hnat : (317717691 : ℕ)^5919*10000000000000^4895 ≤ 4412577864667^4895*625000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317717691 625000000 4412577864667 10000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5330032939/10000000000 : ℝ), (-1383586269/10000000000 : ℝ), (317717691/625000000 : ℝ)] ![(46726546561141/100000000000000 : ℝ), (9147674775993/100000000000000 : ℝ), (4412577864667/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5330032939/10000000000 : ℝ)|^5919 ≤ (46726546561141/100000000000000 : ℝ)^4895
        have hw : |(5330032939/10000000000 : ℝ)|=(5330032939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1383586269/10000000000 : ℝ)|^5919 ≤ (9147674775993/100000000000000 : ℝ)^4895
        have hw : |(-1383586269/10000000000 : ℝ)|=(1383586269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(317717691/625000000 : ℝ)|^5919 ≤ (4412577864667/10000000000000 : ℝ)^4895
        have hw : |(317717691/625000000 : ℝ)|=(317717691/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1759_s2_2 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5330032949/10000000000 : ℝ)*x 0 + (5083483029/10000000000 : ℝ)*x 1 + (-345896573/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5330032949/10000000000 : ℝ)^5919 ≤ (46726546667147/100000000000000 : ℝ)^4895 := by
    have hnat : (5330032949 : ℕ)^5919*100000000000000^4895 ≤ 46726546667147^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5330032949 10000000000 46726546667147 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5083483029/10000000000 : ℝ)^5919 ≤ (11031444590819/25000000000000 : ℝ)^4895 := by
    have hnat : (5083483029 : ℕ)^5919*25000000000000^4895 ≤ 11031444590819^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5083483029 10000000000 11031444590819 25000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (345896573/2500000000 : ℝ)^5919 ≤ (914767495987/10000000000000 : ℝ)^4895 := by
    have hnat : (345896573 : ℕ)^5919*10000000000000^4895 ≤ 914767495987^4895*2500000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345896573 2500000000 914767495987 10000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5330032949/10000000000 : ℝ), (5083483029/10000000000 : ℝ), (-345896573/2500000000 : ℝ)] ![(46726546667147/100000000000000 : ℝ), (11031444590819/25000000000000 : ℝ), (914767495987/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5330032949/10000000000 : ℝ)|^5919 ≤ (46726546667147/100000000000000 : ℝ)^4895
        have hw : |(5330032949/10000000000 : ℝ)|=(5330032949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5083483029/10000000000 : ℝ)|^5919 ≤ (11031444590819/25000000000000 : ℝ)^4895
        have hw : |(5083483029/10000000000 : ℝ)|=(5083483029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-345896573/2500000000 : ℝ)|^5919 ≤ (914767495987/10000000000000 : ℝ)^4895
        have hw : |(-345896573/2500000000 : ℝ)|=(345896573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1759_s2_3 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (800519613/2000000000 : ℝ)*x 0 + (3348941527/10000000000 : ℝ)*x 1 + (943464491/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (800519613/2000000000 : ℝ)^5919 ≤ (16524361597457/50000000000000 : ℝ)^4895 := by
    have hnat : (800519613 : ℕ)^5919*50000000000000^4895 ≤ 16524361597457^4895*2000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      800519613 2000000000 16524361597457 50000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3348941527/10000000000 : ℝ)^5919 ≤ (26639221395747/100000000000000 : ℝ)^4895 := by
    have hnat : (3348941527 : ℕ)^5919*100000000000000^4895 ≤ 26639221395747^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3348941527 10000000000 26639221395747 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (943464491/2000000000 : ℝ)^5919 ≤ (629875865453/1562500000000 : ℝ)^4895 := by
    have hnat : (943464491 : ℕ)^5919*1562500000000^4895 ≤ 629875865453^4895*2000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      943464491 2000000000 629875865453 1562500000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(800519613/2000000000 : ℝ), (3348941527/10000000000 : ℝ), (943464491/2000000000 : ℝ)] ![(16524361597457/50000000000000 : ℝ), (26639221395747/100000000000000 : ℝ), (629875865453/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(800519613/2000000000 : ℝ)|^5919 ≤ (16524361597457/50000000000000 : ℝ)^4895
        have hw : |(800519613/2000000000 : ℝ)|=(800519613/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3348941527/10000000000 : ℝ)|^5919 ≤ (26639221395747/100000000000000 : ℝ)^4895
        have hw : |(3348941527/10000000000 : ℝ)|=(3348941527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(943464491/2000000000 : ℝ)|^5919 ≤ (629875865453/1562500000000 : ℝ)^4895
        have hw : |(943464491/2000000000 : ℝ)|=(943464491/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1759_s2_4 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1174106799/10000000000 : ℝ)*x 0 + (5090112609/10000000000 : ℝ)*x 1 + (1095682691/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1174106799/10000000000 : ℝ)^5919 ≤ (1500123072917/20000000000000 : ℝ)^4895 := by
    have hnat : (1174106799 : ℕ)^5919*20000000000000^4895 ≤ 1500123072917^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1174106799 10000000000 1500123072917 20000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5090112609/10000000000 : ℝ)^5919 ≤ (8839074475189/20000000000000 : ℝ)^4895 := by
    have hnat : (5090112609 : ℕ)^5919*20000000000000^4895 ≤ 8839074475189^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5090112609 10000000000 8839074475189 20000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1095682691/2000000000 : ℝ)^5919 ≤ (24152006125483/50000000000000 : ℝ)^4895 := by
    have hnat : (1095682691 : ℕ)^5919*50000000000000^4895 ≤ 24152006125483^4895*2000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095682691 2000000000 24152006125483 50000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1174106799/10000000000 : ℝ), (5090112609/10000000000 : ℝ), (1095682691/2000000000 : ℝ)] ![(1500123072917/20000000000000 : ℝ), (8839074475189/20000000000000 : ℝ), (24152006125483/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1174106799/10000000000 : ℝ)|^5919 ≤ (1500123072917/20000000000000 : ℝ)^4895
        have hw : |(-1174106799/10000000000 : ℝ)|=(1174106799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5090112609/10000000000 : ℝ)|^5919 ≤ (8839074475189/20000000000000 : ℝ)^4895
        have hw : |(5090112609/10000000000 : ℝ)|=(5090112609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1095682691/2000000000 : ℝ)|^5919 ≤ (24152006125483/50000000000000 : ℝ)^4895
        have hw : |(1095682691/2000000000 : ℝ)|=(1095682691/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1759_s2_5 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (208953633/400000000 : ℝ)*x 0 + (-494327783/5000000000 : ℝ)*x 1 + (5478413601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (208953633/400000000 : ℝ)^5919 ≤ (1140080183677/2500000000000 : ℝ)^4895 := by
    have hnat : (208953633 : ℕ)^5919*2500000000000^4895 ≤ 1140080183677^4895*400000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208953633 400000000 1140080183677 2500000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (494327783/5000000000 : ℝ)^5919 ≤ (6092778828921/100000000000000 : ℝ)^4895 := by
    have hnat : (494327783 : ℕ)^5919*100000000000000^4895 ≤ 6092778828921^4895*5000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      494327783 5000000000 6092778828921 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5478413601/10000000000 : ℝ)^5919 ≤ (24152006903783/50000000000000 : ℝ)^4895 := by
    have hnat : (5478413601 : ℕ)^5919*50000000000000^4895 ≤ 24152006903783^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5478413601 10000000000 24152006903783 50000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(208953633/400000000 : ℝ), (-494327783/5000000000 : ℝ), (5478413601/10000000000 : ℝ)] ![(1140080183677/2500000000000 : ℝ), (6092778828921/100000000000000 : ℝ), (24152006903783/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(208953633/400000000 : ℝ)|^5919 ≤ (1140080183677/2500000000000 : ℝ)^4895
        have hw : |(208953633/400000000 : ℝ)|=(208953633/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-494327783/5000000000 : ℝ)|^5919 ≤ (6092778828921/100000000000000 : ℝ)^4895
        have hw : |(-494327783/5000000000 : ℝ)|=(494327783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5478413601/10000000000 : ℝ)|^5919 ≤ (24152006903783/50000000000000 : ℝ)^4895
        have hw : |(5478413601/10000000000 : ℝ)|=(5478413601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1759_s2_6 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5223840983/10000000000 : ℝ)*x 0 + (1095682691/2000000000 : ℝ)*x 1 + (-988655551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5223840983/10000000000 : ℝ)^5919 ≤ (22801604507467/50000000000000 : ℝ)^4895 := by
    have hnat : (5223840983 : ℕ)^5919*50000000000000^4895 ≤ 22801604507467^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5223840983 10000000000 22801604507467 50000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1095682691/2000000000 : ℝ)^5919 ≤ (24152006125483/50000000000000 : ℝ)^4895 := by
    have hnat : (1095682691 : ℕ)^5919*50000000000000^4895 ≤ 24152006125483^4895*2000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095682691 2000000000 24152006125483 50000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (988655551/10000000000 : ℝ)^5919 ≤ (6092778717143/100000000000000 : ℝ)^4895 := by
    have hnat : (988655551 : ℕ)^5919*100000000000000^4895 ≤ 6092778717143^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      988655551 10000000000 6092778717143 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5223840983/10000000000 : ℝ), (1095682691/2000000000 : ℝ), (-988655551/10000000000 : ℝ)] ![(22801604507467/50000000000000 : ℝ), (24152006125483/50000000000000 : ℝ), (6092778717143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5223840983/10000000000 : ℝ)|^5919 ≤ (22801604507467/50000000000000 : ℝ)^4895
        have hw : |(5223840983/10000000000 : ℝ)|=(5223840983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1095682691/2000000000 : ℝ)|^5919 ≤ (24152006125483/50000000000000 : ℝ)^4895
        have hw : |(1095682691/2000000000 : ℝ)|=(1095682691/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-988655551/10000000000 : ℝ)|^5919 ≤ (6092778717143/100000000000000 : ℝ)^4895
        have hw : |(-988655551/10000000000 : ℝ)|=(988655551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1759_s2_7 (p : ℝ) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4003732589/10000000000 : ℝ)*x 0 + (469473943/1000000000 : ℝ)*x 1 + (1685998027/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4003732589/10000000000 : ℝ)^5919 ≤ (33060050716813/100000000000000 : ℝ)^4895 := by
    have hnat : (4003732589 : ℕ)^5919*100000000000000^4895 ≤ 33060050716813^4895*10000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4003732589 10000000000 33060050716813 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (469473943/1000000000 : ℝ)^5919 ≤ (40078817370297/100000000000000 : ℝ)^4895 := by
    have hnat : (469473943 : ℕ)^5919*100000000000000^4895 ≤ 40078817370297^4895*1000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469473943 1000000000 40078817370297 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1685998027/5000000000 : ℝ)^5919 ≤ (26861131900341/100000000000000 : ℝ)^4895 := by
    have hnat : (1685998027 : ℕ)^5919*100000000000000^4895 ≤ 26861131900341^4895*5000000000^5919 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1685998027 5000000000 26861131900341 100000000000000 5919 4895 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5919/1024 : ℝ)) 5919 4895 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4003732589/10000000000 : ℝ), (469473943/1000000000 : ℝ), (1685998027/5000000000 : ℝ)] ![(33060050716813/100000000000000 : ℝ), (40078817370297/100000000000000 : ℝ), (26861131900341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4003732589/10000000000 : ℝ)|^5919 ≤ (33060050716813/100000000000000 : ℝ)^4895
        have hw : |(4003732589/10000000000 : ℝ)|=(4003732589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(469473943/1000000000 : ℝ)|^5919 ≤ (40078817370297/100000000000000 : ℝ)^4895
        have hw : |(469473943/1000000000 : ℝ)|=(469473943/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1685998027/5000000000 : ℝ)|^5919 ≤ (26861131900341/100000000000000 : ℝ)^4895
        have hw : |(1685998027/5000000000 : ℝ)|=(1685998027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1759_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (220324357/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17849/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4553/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1829/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8901/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17849/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4553/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17849/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4553/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17849/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4553/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17849/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4553/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17849/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4553/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17849/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4553/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4553/50000 : ℝ) ^ (5903/1024 : ℝ) ≤ (100205080301679/100000000000000000000 : ℝ) := by
    have hpowers : (4553/50000 : ℝ)^5903 ≤ (100205080301679/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4553 : ℕ)^5903*100000000000000000000^1024 ≤ 100205080301679^1024*50000^5903 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4553 50000 100205080301679 100000000000000000000 5903 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4553/50000 : ℝ)) (X := (100205080301679/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5903 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17849/100000 : ℝ) ^ (5903/1024 : ℝ) ≤ (970168508452617/20000000000000000000 : ℝ) := by
    have hpowers : (17849/100000 : ℝ)^5903 ≤ (970168508452617/20000000000000000000 : ℝ)^1024 := by
      have hnat : (17849 : ℕ)^5903*20000000000000000000^1024 ≤ 970168508452617^1024*100000^5903 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17849 100000 970168508452617 20000000000000000000 5903 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17849/100000 : ℝ)) (X := (970168508452617/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5903 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000100205080301679/50000000000000000000 : ℝ) ≤ (10000003476534551/10000000000000000 : ℝ) ^ (5903/1024 : ℝ) := by
    have hpowers : (50000100205080301679/50000000000000000000 : ℝ)^1024 ≤ (10000003476534551/10000000000000000 : ℝ)^5903 := by
      have hnat : (50000100205080301679 : ℕ)^1024*10000000000000000^5903 ≤ 10000003476534551^5903*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000100205080301679 50000000000000000000 10000003476534551 10000000000000000 1024 5903 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000003476534551/10000000000000000 : ℝ)) (X := (50000100205080301679/50000000000000000000 : ℝ)) (by norm_num) 5903 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25001237761905641191/25000000000000000000 : ℝ) ≤ (5000042942309287/5000000000000000 : ℝ) ^ (5903/1024 : ℝ) := by
    have hpowers : (25001237761905641191/25000000000000000000 : ℝ)^1024 ≤ (5000042942309287/5000000000000000 : ℝ)^5903 := by
      have hnat : (25001237761905641191 : ℕ)^1024*5000000000000000^5903 ≤ 5000042942309287^5903*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001237761905641191 25000000000000000000 5000042942309287 5000000000000000 1024 5903 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000042942309287/5000000000000000 : ℝ)) (X := (25001237761905641191/25000000000000000000 : ℝ)) (by norm_num) 5903 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10000970168508452617/10000000000000000000 : ℝ) ≤ (10000168292702597/10000000000000000 : ℝ) ^ (5903/1024 : ℝ) := by
    have hpowers : (10000970168508452617/10000000000000000000 : ℝ)^1024 ≤ (10000168292702597/10000000000000000 : ℝ)^5903 := by
      have hnat : (10000970168508452617 : ℕ)^1024*10000000000000000^5903 ≤ 10000168292702597^5903*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000970168508452617 10000000000000000000 10000168292702597 10000000000000000 1024 5903 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000168292702597/10000000000000000 : ℝ)) (X := (10000970168508452617/10000000000000000000 : ℝ)) (by norm_num) 5903 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(100205080301679/100000000000000000000 : ℝ) ≤ ((87428529579315352517/87430000000000000000 : ℝ)+2*(82408084023/874300000000000 : ℝ)*(4553/50000 : ℝ))^(5903/1024 : ℝ) := by
    rw [show (87428529579315352517/87430000000000000000 : ℝ)+2*(82408084023/874300000000000 : ℝ)*(4553/50000 : ℝ)=(10000003476534551/10000000000000000 : ℝ) by norm_num, show 1+2*(100205080301679/100000000000000000000 : ℝ)=(50000100205080301679/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(970168508452617/20000000000000000000 : ℝ)+(100205080301679/100000000000000000000 : ℝ) ≤ ((87428529579315352517/87430000000000000000 : ℝ)+(82408084023/874300000000000 : ℝ)*((17849/100000 : ℝ)+(4553/50000 : ℝ)))^(5903/1024 : ℝ) := by
    rw [show (87428529579315352517/87430000000000000000 : ℝ)+(82408084023/874300000000000 : ℝ)*((17849/100000 : ℝ)+(4553/50000 : ℝ))=(5000042942309287/5000000000000000 : ℝ) by norm_num, show 1+(970168508452617/20000000000000000000 : ℝ)+(100205080301679/100000000000000000000 : ℝ)=(25001237761905641191/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(970168508452617/20000000000000000000 : ℝ) ≤ ((87428529579315352517/87430000000000000000 : ℝ)+2*(82408084023/874300000000000 : ℝ)*(17849/100000 : ℝ))^(5903/1024 : ℝ) := by
    rw [show (87428529579315352517/87430000000000000000 : ℝ)+2*(82408084023/874300000000000 : ℝ)*(17849/100000 : ℝ)=(10000168292702597/10000000000000000 : ℝ) by norm_num, show 1+2*(970168508452617/20000000000000000000 : ℝ)=(10000970168508452617/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (87428529579315352517/87430000000000000000 : ℝ)*(X 1 0+X 2 0)+(82408084023/874300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5903/1024 : ℝ)) (lo := (4553/50000 : ℝ)) (hi := (17849/100000 : ℝ)) (c := (87428529579315352517/87430000000000000000 : ℝ)) (alpha := (82408084023/874300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (87428529579315352517/87430000000000000000 : ℝ)*(X 0 1+X 2 1)+(82408084023/874300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5903/1024 : ℝ)) (lo := (4553/50000 : ℝ)) (hi := (17849/100000 : ℝ)) (c := (87428529579315352517/87430000000000000000 : ℝ)) (alpha := (82408084023/874300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (87428529579315352517/87430000000000000000 : ℝ)*(X 0 2+X 1 2)+(82408084023/874300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5903/1024 : ℝ)) (lo := (4553/50000 : ℝ)) (hi := (17849/100000 : ℝ)) (c := (87428529579315352517/87430000000000000000 : ℝ)) (alpha := (82408084023/874300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1173773609/10000000000 : ℝ)*X 0 0+(5485181503/10000000000 : ℝ)*X 0 1+(2541741511/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5330032939/10000000000 : ℝ)*X 1 0+(-1383586269/10000000000 : ℝ)*X 1 1+(317717691/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5330032949/10000000000 : ℝ)*X 2 0+(5083483029/10000000000 : ℝ)*X 2 1+(-345896573/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((800519613/2000000000 : ℝ)*X 0 0+(3348941527/10000000000 : ℝ)*X 0 1+(943464491/2000000000 : ℝ)*X 0 2+(800519613/2000000000 : ℝ)*X 1 0+(3348941527/10000000000 : ℝ)*X 1 1+(943464491/2000000000 : ℝ)*X 1 2+(800519613/2000000000 : ℝ)*X 2 0+(3348941527/10000000000 : ℝ)*X 2 1+(943464491/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1174106799/10000000000 : ℝ)*X 0 0+(5090112609/10000000000 : ℝ)*X 0 1+(1095682691/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((208953633/400000000 : ℝ)*X 1 0+(-494327783/5000000000 : ℝ)*X 1 1+(5478413601/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5223840983/10000000000 : ℝ)*X 2 0+(1095682691/2000000000 : ℝ)*X 2 1+(-988655551/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4003732589/10000000000 : ℝ)*X 0 0+(469473943/1000000000 : ℝ)*X 0 1+(1685998027/5000000000 : ℝ)*X 0 2+(4003732589/10000000000 : ℝ)*X 1 0+(469473943/1000000000 : ℝ)*X 1 1+(1685998027/5000000000 : ℝ)*X 1 2+(4003732589/10000000000 : ℝ)*X 2 0+(469473943/1000000000 : ℝ)*X 2 1+(1685998027/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1759_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2590258125193541171584121439/437150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (194873701/25000000000000 : ℝ)*(base19) + (743499059/100000000000000 : ℝ)*(base23) + (21675293/100000000000000 : ℝ)*(lower2) + (142180077/100000000000000 : ℝ)*(upper3) + (101826159/100000000000000 : ℝ)*(upper5) + (161011849806837/10000000000000 : ℝ)*(major0) + (161011849806837/10000000000000 : ℝ)*(major1) + (161011849806837/10000000000000 : ℝ)*(major2) + (497887176577773/20000000000000 : ℝ)*(sp0) + (155590088848081/6250000000000 : ℝ)*(sp1) + (1244720728782521/50000000000000 : ℝ)*(sp2) + (365396242332479/50000000000000 : ℝ)*(sp3) + (1263635047/20000000000000 : ℝ)*(sp4) + (1056448329/50000000000000 : ℝ)*(sp7) + (45674662347601/6250000000000 : ℝ)*(f.failure) + (24894422010641/1000000000000 : ℝ)*(f.sum) + (4825382007997/1092875000000000000000000000 : ℝ)*base65 + (1176101602021151247/124900000000000000000000000000000 : ℝ)*base67 + (320296998732251247/124900000000000000000000000000000 : ℝ)*base69 + (693113706697151247/124900000000000000000000000000000 : ℝ)*base71 + (15783690215569/2185750000000000000000000000 : ℝ)*base73 + (928096417269351247/124900000000000000000000000000000 : ℝ)*base75 + (1140314670238551247/124900000000000000000000000000000 : ℝ)*base77 + (99092648021951247/124900000000000000000000000000000 : ℝ)*base79 + (3938498098973/2185750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (11682443/625000000000000000000 : ℝ)*base90 + (11682443/625000000000000000000 : ℝ)*base92 + (11682443/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24232130165154939403712757027/2185750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (158792913/10000000000000 : ℝ)*(base19) + (426836073/25000000000000 : ℝ)*(base23) + (459414509/100000000000000 : ℝ)*(lower1) + (74045221/25000000000000 : ℝ)*(upper3) + (5249623/100000000000000 : ℝ)*(lower4) + (18577003/10000000000000 : ℝ)*(upper5) + (1665655575095677/100000000000000 : ℝ)*(major0) + (1665655575095677/100000000000000 : ℝ)*(major1) + (1665655575095677/100000000000000 : ℝ)*(major2) + (309648603/20000000000000 : ℝ)*(sp2) + (64382730526139/2500000000000 : ℝ)*(sp4) + (257530763311643/10000000000000 : ℝ)*(sp5) + (2575305965458253/100000000000000 : ℝ)*(sp6) + (756001559598641/100000000000000 : ℝ)*(sp7) + (756001559598641/100000000000000 : ℝ)*(f.failure) + (64382730526139/2500000000000 : ℝ)*(f.sum) + (35003067932841/10928750000000000000000000000 : ℝ)*base66 + (12030046643385018713/1249000000000000000000000000000000 : ℝ)*base68 + (12479176731641018713/1249000000000000000000000000000000 : ℝ)*base70 + (21390659194006018713/1249000000000000000000000000000000 : ℝ)*base72 + (209279394835179/43715000000000000000000000000 : ℝ)*base74 + (21173186535488981287/1249000000000000000000000000000000 : ℝ)*base75 + (6894551844822018713/1249000000000000000000000000000000 : ℝ)*base78 + (8129195460375018713/1249000000000000000000000000000000 : ℝ)*base80 + (15177990228203/21857500000000000000000000000 : ℝ)*base81 + (56398837/10000000000000000000000 : ℝ)*base89 + (56398837/10000000000000000000000 : ℝ)*base91 + (56398837/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1759_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (220324357/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17849/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4553/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1829/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8901/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1759_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1759_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (220324357/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1829/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8901/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1759_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1759_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1759_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5903/1024 : ℝ) ≤ p) (hpb : p ≤ (5919/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (220324357/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1829/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8901/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1759_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
