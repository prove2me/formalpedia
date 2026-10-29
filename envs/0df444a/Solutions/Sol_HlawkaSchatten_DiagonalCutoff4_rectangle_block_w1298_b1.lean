-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1298_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:35:27.081809+00:00
-- url     : https://prove2.me/submissions/1a069e03-3d4b-4a0a-ae33-f56bd56ae522

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
theorem support_rectangle_w1298_s3_0 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2080330247/10000000000 : ℝ)*x 0 + (339574557/625000000 : ℝ)*x 1 + (5226426399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2080330247/10000000000 : ℝ)^2129 ≤ (6327011085123/50000000000000 : ℝ)^1617 := by
    have hnat : (2080330247 : ℕ)^2129*50000000000000^1617 ≤ 6327011085123^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080330247 10000000000 6327011085123 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339574557/625000000 : ℝ)^2129 ≤ (22394125719973/50000000000000 : ℝ)^1617 := by
    have hnat : (339574557 : ℕ)^2129*50000000000000^1617 ≤ 22394125719973^1617*625000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339574557 625000000 22394125719973 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5226426399/10000000000 : ℝ)^2129 ≤ (531971579737/1250000000000 : ℝ)^1617 := by
    have hnat : (5226426399 : ℕ)^2129*1250000000000^1617 ≤ 531971579737^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226426399 10000000000 531971579737 1250000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2080330247/10000000000 : ℝ), (339574557/625000000 : ℝ), (5226426399/10000000000 : ℝ)] ![(6327011085123/50000000000000 : ℝ), (22394125719973/50000000000000 : ℝ), (531971579737/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2080330247/10000000000 : ℝ)|^2129 ≤ (6327011085123/50000000000000 : ℝ)^1617
        have hw : |(-2080330247/10000000000 : ℝ)|=(2080330247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339574557/625000000 : ℝ)|^2129 ≤ (22394125719973/50000000000000 : ℝ)^1617
        have hw : |(339574557/625000000 : ℝ)|=(339574557/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5226426399/10000000000 : ℝ)|^2129 ≤ (531971579737/1250000000000 : ℝ)^1617
        have hw : |(5226426399/10000000000 : ℝ)|=(5226426399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s3_1 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1070864103/2000000000 : ℝ)*x 0 + (-2186131421/10000000000 : ℝ)*x 1 + (5226426613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070864103/2000000000 : ℝ)^2129 ≤ (43934174368719/100000000000000 : ℝ)^1617 := by
    have hnat : (1070864103 : ℕ)^2129*100000000000000^1617 ≤ 43934174368719^1617*2000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070864103 2000000000 43934174368719 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2186131421/10000000000 : ℝ)^2129 ≤ (13508096946457/100000000000000 : ℝ)^1617 := by
    have hnat : (2186131421 : ℕ)^2129*100000000000000^1617 ≤ 13508096946457^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186131421 10000000000 13508096946457 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5226426613/10000000000 : ℝ)^2129 ≤ (1702309146931/4000000000000 : ℝ)^1617 := by
    have hnat : (5226426613 : ℕ)^2129*4000000000000^1617 ≤ 1702309146931^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226426613 10000000000 1702309146931 4000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070864103/2000000000 : ℝ), (-2186131421/10000000000 : ℝ), (5226426613/10000000000 : ℝ)] ![(43934174368719/100000000000000 : ℝ), (13508096946457/100000000000000 : ℝ), (1702309146931/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070864103/2000000000 : ℝ)|^2129 ≤ (43934174368719/100000000000000 : ℝ)^1617
        have hw : |(1070864103/2000000000 : ℝ)|=(1070864103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2186131421/10000000000 : ℝ)|^2129 ≤ (13508096946457/100000000000000 : ℝ)^1617
        have hw : |(-2186131421/10000000000 : ℝ)|=(2186131421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5226426613/10000000000 : ℝ)|^2129 ≤ (1702309146931/4000000000000 : ℝ)^1617
        have hw : |(5226426613/10000000000 : ℝ)|=(5226426613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s3_2 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1338580157/2500000000 : ℝ)*x 0 + (1045285219/2000000000 : ℝ)*x 1 + (-2186131953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338580157/2500000000 : ℝ)^2129 ≤ (5491771948689/12500000000000 : ℝ)^1617 := by
    have hnat : (1338580157 : ℕ)^2129*12500000000000^1617 ≤ 5491771948689^1617*2500000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338580157 2500000000 5491771948689 12500000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1045285219/2000000000 : ℝ)^2129 ≤ (42557723119747/100000000000000 : ℝ)^1617 := by
    have hnat : (1045285219 : ℕ)^2129*100000000000000^1617 ≤ 42557723119747^1617*2000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045285219 2000000000 42557723119747 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2186131953/10000000000 : ℝ)^2129 ≤ (1688512659317/12500000000000 : ℝ)^1617 := by
    have hnat : (2186131953 : ℕ)^2129*12500000000000^1617 ≤ 1688512659317^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186131953 10000000000 1688512659317 12500000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338580157/2500000000 : ℝ), (1045285219/2000000000 : ℝ), (-2186131953/10000000000 : ℝ)] ![(5491771948689/12500000000000 : ℝ), (42557723119747/100000000000000 : ℝ), (1688512659317/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338580157/2500000000 : ℝ)|^2129 ≤ (5491771948689/12500000000000 : ℝ)^1617
        have hw : |(1338580157/2500000000 : ℝ)|=(1338580157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1045285219/2000000000 : ℝ)|^2129 ≤ (42557723119747/100000000000000 : ℝ)^1617
        have hw : |(1045285219/2000000000 : ℝ)|=(1045285219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2186131953/10000000000 : ℝ)|^2129 ≤ (1688512659317/12500000000000 : ℝ)^1617
        have hw : |(-2186131953/10000000000 : ℝ)|=(2186131953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s3_3 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2168443911/5000000000 : ℝ)*x 0 + (516112951/1250000000 : ℝ)*x 1 + (4554832979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2168443911/5000000000 : ℝ)^2129 ≤ (4161077908937/12500000000000 : ℝ)^1617 := by
    have hnat : (2168443911 : ℕ)^2129*12500000000000^1617 ≤ 4161077908937^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168443911 5000000000 4161077908937 12500000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (516112951/1250000000 : ℝ)^2129 ≤ (7800713015103/25000000000000 : ℝ)^1617 := by
    have hnat : (516112951 : ℕ)^2129*25000000000000^1617 ≤ 7800713015103^1617*1250000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516112951 1250000000 7800713015103 25000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4554832979/10000000000 : ℝ)^2129 ≤ (35508524659937/100000000000000 : ℝ)^1617 := by
    have hnat : (4554832979 : ℕ)^2129*100000000000000^1617 ≤ 35508524659937^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4554832979 10000000000 35508524659937 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2168443911/5000000000 : ℝ), (516112951/1250000000 : ℝ), (4554832979/10000000000 : ℝ)] ![(4161077908937/12500000000000 : ℝ), (7800713015103/25000000000000 : ℝ), (35508524659937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2168443911/5000000000 : ℝ)|^2129 ≤ (4161077908937/12500000000000 : ℝ)^1617
        have hw : |(2168443911/5000000000 : ℝ)|=(2168443911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(516112951/1250000000 : ℝ)|^2129 ≤ (7800713015103/25000000000000 : ℝ)^1617
        have hw : |(516112951/1250000000 : ℝ)|=(516112951/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4554832979/10000000000 : ℝ)|^2129 ≤ (35508524659937/100000000000000 : ℝ)^1617
        have hw : |(4554832979/10000000000 : ℝ)|=(4554832979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s3_4 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1040176201/5000000000 : ℝ)*x 0 + (2613656459/5000000000 : ℝ)*x 1 + (2716150411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1040176201/5000000000 : ℝ)^2129 ≤ (6327099801631/50000000000000 : ℝ)^1617 := by
    have hnat : (1040176201 : ℕ)^2129*50000000000000^1617 ≤ 6327099801631^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040176201 5000000000 6327099801631 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2613656459/5000000000 : ℝ)^2129 ≤ (1702689243611/4000000000000 : ℝ)^1617 := by
    have hnat : (2613656459 : ℕ)^2129*4000000000000^1617 ≤ 1702689243611^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613656459 5000000000 1702689243611 4000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2716150411/5000000000 : ℝ)^2129 ≤ (11194642321381/25000000000000 : ℝ)^1617 := by
    have hnat : (2716150411 : ℕ)^2129*25000000000000^1617 ≤ 11194642321381^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716150411 5000000000 11194642321381 25000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1040176201/5000000000 : ℝ), (2613656459/5000000000 : ℝ), (2716150411/5000000000 : ℝ)] ![(6327099801631/50000000000000 : ℝ), (1702689243611/4000000000000 : ℝ), (11194642321381/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1040176201/5000000000 : ℝ)|^2129 ≤ (6327099801631/50000000000000 : ℝ)^1617
        have hw : |(-1040176201/5000000000 : ℝ)|=(1040176201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2613656459/5000000000 : ℝ)|^2129 ≤ (1702689243611/4000000000000 : ℝ)^1617
        have hw : |(2613656459/5000000000 : ℝ)|=(2613656459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2716150411/5000000000 : ℝ)|^2129 ≤ (11194642321381/25000000000000 : ℝ)^1617
        have hw : |(2716150411/5000000000 : ℝ)|=(2716150411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s3_5 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5301339403/10000000000 : ℝ)*x 0 + (-396051421/2000000000 : ℝ)*x 1 + (339518799/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301339403/10000000000 : ℝ)^2129 ≤ (43362692584849/100000000000000 : ℝ)^1617 := by
    have hnat : (5301339403 : ℕ)^2129*100000000000000^1617 ≤ 43362692584849^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301339403 10000000000 43362692584849 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (396051421/2000000000 : ℝ)^2129 ≤ (11858738532679/100000000000000 : ℝ)^1617 := by
    have hnat : (396051421 : ℕ)^2129*100000000000000^1617 ≤ 11858738532679^1617*2000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396051421 2000000000 11858738532679 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339518799/625000000 : ℝ)^2129 ≤ (11194642218277/25000000000000 : ℝ)^1617 := by
    have hnat : (339518799 : ℕ)^2129*25000000000000^1617 ≤ 11194642218277^1617*625000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339518799 625000000 11194642218277 25000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301339403/10000000000 : ℝ), (-396051421/2000000000 : ℝ), (339518799/625000000 : ℝ)] ![(43362692584849/100000000000000 : ℝ), (11858738532679/100000000000000 : ℝ), (11194642218277/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301339403/10000000000 : ℝ)|^2129 ≤ (43362692584849/100000000000000 : ℝ)^1617
        have hw : |(5301339403/10000000000 : ℝ)|=(5301339403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-396051421/2000000000 : ℝ)|^2129 ≤ (11858738532679/100000000000000 : ℝ)^1617
        have hw : |(-396051421/2000000000 : ℝ)|=(396051421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(339518799/625000000 : ℝ)|^2129 ≤ (11194642218277/25000000000000 : ℝ)^1617
        have hw : |(339518799/625000000 : ℝ)|=(339518799/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s3_6 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (212053579/400000000 : ℝ)*x 0 + (679037587/1250000000 : ℝ)*x 1 + (-1980257127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212053579/400000000 : ℝ)^2129 ≤ (21681346680127/50000000000000 : ℝ)^1617 := by
    have hnat : (212053579 : ℕ)^2129*50000000000000^1617 ≤ 21681346680127^1617*400000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212053579 400000000 21681346680127 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (679037587/1250000000 : ℝ)^2129 ≤ (44778567918039/100000000000000 : ℝ)^1617 := by
    have hnat : (679037587 : ℕ)^2129*100000000000000^1617 ≤ 44778567918039^1617*1250000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679037587 1250000000 44778567918039 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1980257127/10000000000 : ℝ)^2129 ≤ (11858738706141/100000000000000 : ℝ)^1617 := by
    have hnat : (1980257127 : ℕ)^2129*100000000000000^1617 ≤ 11858738706141^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1980257127 10000000000 11858738706141 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212053579/400000000 : ℝ), (679037587/1250000000 : ℝ), (-1980257127/10000000000 : ℝ)] ![(21681346680127/50000000000000 : ℝ), (44778567918039/100000000000000 : ℝ), (11858738706141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212053579/400000000 : ℝ)|^2129 ≤ (21681346680127/50000000000000 : ℝ)^1617
        have hw : |(212053579/400000000 : ℝ)|=(212053579/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(679037587/1250000000 : ℝ)|^2129 ≤ (44778567918039/100000000000000 : ℝ)^1617
        have hw : |(679037587/1250000000 : ℝ)|=(679037587/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1980257127/10000000000 : ℝ)|^2129 ≤ (11858738706141/100000000000000 : ℝ)^1617
        have hw : |(-1980257127/10000000000 : ℝ)|=(1980257127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s3_7 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4336932869/10000000000 : ℝ)*x 0 + (4553006523/10000000000 : ℝ)*x 1 + (4130741731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4336932869/10000000000 : ℝ)^2129 ≤ (33289078521413/100000000000000 : ℝ)^1617 := by
    have hnat : (4336932869 : ℕ)^2129*100000000000000^1617 ≤ 33289078521413^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4336932869 10000000000 33289078521413 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4553006523/10000000000 : ℝ)^2129 ≤ (35489778709979/100000000000000 : ℝ)^1617 := by
    have hnat : (4553006523 : ℕ)^2129*100000000000000^1617 ≤ 35489778709979^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4553006523 10000000000 35489778709979 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4130741731/10000000000 : ℝ)^2129 ≤ (60978794457/195312500000 : ℝ)^1617 := by
    have hnat : (4130741731 : ℕ)^2129*195312500000^1617 ≤ 60978794457^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4130741731 10000000000 60978794457 195312500000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4336932869/10000000000 : ℝ), (4553006523/10000000000 : ℝ), (4130741731/10000000000 : ℝ)] ![(33289078521413/100000000000000 : ℝ), (35489778709979/100000000000000 : ℝ), (60978794457/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4336932869/10000000000 : ℝ)|^2129 ≤ (33289078521413/100000000000000 : ℝ)^1617
        have hw : |(4336932869/10000000000 : ℝ)|=(4336932869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4553006523/10000000000 : ℝ)|^2129 ≤ (35489778709979/100000000000000 : ℝ)^1617
        have hw : |(4553006523/10000000000 : ℝ)|=(4553006523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4130741731/10000000000 : ℝ)|^2129 ≤ (60978794457/195312500000 : ℝ)^1617
        have hw : |(4130741731/10000000000 : ℝ)|=(4130741731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1298_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76498753/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1629/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2387/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2671/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7529/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1629/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2387/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1629/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2387/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1629/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2387/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1629/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2387/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1629/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2387/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1629/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2387/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2387/25000 : ℝ) ^ (4257/1024 : ℝ) ≤ (2872332951565401/50000000000000000000 : ℝ) := by
    have hpowers : (2387/25000 : ℝ)^4257 ≤ (2872332951565401/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2387 : ℕ)^4257*50000000000000000000^1024 ≤ 2872332951565401^1024*25000^4257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2387 25000 2872332951565401 50000000000000000000 4257 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2387/25000 : ℝ)) (X := (2872332951565401/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1629/10000 : ℝ) ^ (4257/1024 : ℝ) ≤ (5293920295519891/10000000000000000000 : ℝ) := by
    have hpowers : (1629/10000 : ℝ)^4257 ≤ (5293920295519891/10000000000000000000 : ℝ)^1024 := by
      have hnat : (1629 : ℕ)^4257*10000000000000000000^1024 ≤ 5293920295519891^1024*10000^4257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1629 10000 5293920295519891 10000000000000000000 4257 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1629/10000 : ℝ)) (X := (5293920295519891/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002872332951565401/25000000000000000000 : ℝ) ≤ (5000138179028843/5000000000000000 : ℝ) ^ (4257/1024 : ℝ) := by
    have hpowers : (25002872332951565401/25000000000000000000 : ℝ)^1024 ≤ (5000138179028843/5000000000000000 : ℝ)^4257 := by
      have hnat : (25002872332951565401 : ℕ)^1024*5000000000000000^4257 ≤ 5000138179028843^4257*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002872332951565401 25000000000000000000 5000138179028843 5000000000000000 1024 4257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000138179028843/5000000000000000 : ℝ)) (X := (25002872332951565401/25000000000000000000 : ℝ)) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6253667741803645607/6250000000000000000 : ℝ) ≤ (1000141129658037/1000000000000000 : ℝ) ^ (4257/1024 : ℝ) := by
    have hpowers : (6253667741803645607/6250000000000000000 : ℝ)^1024 ≤ (1000141129658037/1000000000000000 : ℝ)^4257 := by
      have hnat : (6253667741803645607 : ℕ)^1024*1000000000000000^4257 ≤ 1000141129658037^4257*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253667741803645607 6250000000000000000 1000141129658037 1000000000000000 1024 4257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000141129658037/1000000000000000 : ℝ)) (X := (6253667741803645607/6250000000000000000 : ℝ)) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5005293920295519891/5000000000000000000 : ℝ) ≤ (5001273117551527/5000000000000000 : ℝ) ^ (4257/1024 : ℝ) := by
    have hpowers : (5005293920295519891/5000000000000000000 : ℝ)^1024 ≤ (5001273117551527/5000000000000000 : ℝ)^4257 := by
      have hnat : (5005293920295519891 : ℕ)^1024*5000000000000000^4257 ≤ 5001273117551527^4257*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5005293920295519891 5000000000000000000 5001273117551527 5000000000000000 1024 4257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001273117551527/5000000000000000 : ℝ)) (X := (5005293920295519891/5000000000000000000 : ℝ)) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2872332951565401/50000000000000000000 : ℝ) ≤ ((16850047604998936337/16855000000000000000 : ℝ)+2*(283734630671/168550000000000 : ℝ)*(2387/25000 : ℝ))^(4257/1024 : ℝ) := by
    rw [show (16850047604998936337/16855000000000000000 : ℝ)+2*(283734630671/168550000000000 : ℝ)*(2387/25000 : ℝ)=(5000138179028843/5000000000000000 : ℝ) by norm_num, show 1+2*(2872332951565401/50000000000000000000 : ℝ)=(25002872332951565401/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5293920295519891/10000000000000000000 : ℝ)+(2872332951565401/50000000000000000000 : ℝ) ≤ ((16850047604998936337/16855000000000000000 : ℝ)+(283734630671/168550000000000 : ℝ)*((1629/10000 : ℝ)+(2387/25000 : ℝ)))^(4257/1024 : ℝ) := by
    rw [show (16850047604998936337/16855000000000000000 : ℝ)+(283734630671/168550000000000 : ℝ)*((1629/10000 : ℝ)+(2387/25000 : ℝ))=(1000141129658037/1000000000000000 : ℝ) by norm_num, show 1+(5293920295519891/10000000000000000000 : ℝ)+(2872332951565401/50000000000000000000 : ℝ)=(6253667741803645607/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5293920295519891/10000000000000000000 : ℝ) ≤ ((16850047604998936337/16855000000000000000 : ℝ)+2*(283734630671/168550000000000 : ℝ)*(1629/10000 : ℝ))^(4257/1024 : ℝ) := by
    rw [show (16850047604998936337/16855000000000000000 : ℝ)+2*(283734630671/168550000000000 : ℝ)*(1629/10000 : ℝ)=(5001273117551527/5000000000000000 : ℝ) by norm_num, show 1+2*(5293920295519891/10000000000000000000 : ℝ)=(5005293920295519891/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16850047604998936337/16855000000000000000 : ℝ)*(X 1 0+X 2 0)+(283734630671/168550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4257/1024 : ℝ)) (lo := (2387/25000 : ℝ)) (hi := (1629/10000 : ℝ)) (c := (16850047604998936337/16855000000000000000 : ℝ)) (alpha := (283734630671/168550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16850047604998936337/16855000000000000000 : ℝ)*(X 0 1+X 2 1)+(283734630671/168550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4257/1024 : ℝ)) (lo := (2387/25000 : ℝ)) (hi := (1629/10000 : ℝ)) (c := (16850047604998936337/16855000000000000000 : ℝ)) (alpha := (283734630671/168550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16850047604998936337/16855000000000000000 : ℝ)*(X 0 2+X 1 2)+(283734630671/168550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4257/1024 : ℝ)) (lo := (2387/25000 : ℝ)) (hi := (1629/10000 : ℝ)) (c := (16850047604998936337/16855000000000000000 : ℝ)) (alpha := (283734630671/168550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2080330247/10000000000 : ℝ)*X 0 0+(339574557/625000000 : ℝ)*X 0 1+(5226426399/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070864103/2000000000 : ℝ)*X 1 0+(-2186131421/10000000000 : ℝ)*X 1 1+(5226426613/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338580157/2500000000 : ℝ)*X 2 0+(1045285219/2000000000 : ℝ)*X 2 1+(-2186131953/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2168443911/5000000000 : ℝ)*X 0 0+(516112951/1250000000 : ℝ)*X 0 1+(4554832979/10000000000 : ℝ)*X 0 2+(2168443911/5000000000 : ℝ)*X 1 0+(516112951/1250000000 : ℝ)*X 1 1+(4554832979/10000000000 : ℝ)*X 1 2+(2168443911/5000000000 : ℝ)*X 2 0+(516112951/1250000000 : ℝ)*X 2 1+(4554832979/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1040176201/5000000000 : ℝ)*X 0 0+(2613656459/5000000000 : ℝ)*X 0 1+(2716150411/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5301339403/10000000000 : ℝ)*X 1 0+(-396051421/2000000000 : ℝ)*X 1 1+(339518799/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((212053579/400000000 : ℝ)*X 2 0+(679037587/1250000000 : ℝ)*X 2 1+(-1980257127/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4336932869/10000000000 : ℝ)*X 0 0+(4553006523/10000000000 : ℝ)*X 0 1+(4130741731/10000000000 : ℝ)*X 0 2+(4336932869/10000000000 : ℝ)*X 1 0+(4553006523/10000000000 : ℝ)*X 1 1+(4130741731/10000000000 : ℝ)*X 1 2+(4336932869/10000000000 : ℝ)*X 2 0+(4553006523/10000000000 : ℝ)*X 2 1+(4130741731/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6763237248273989897745820467/842750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (50001919/3125000000000 : ℝ)*(base19) + (1803780727/100000000000000 : ℝ)*(base23) + (61976719/100000000000000 : ℝ)*(lower2) + (11087049/2500000000000 : ℝ)*(upper3) + (58201477/50000000000000 : ℝ)*(lower4) + (3592133006592501/100000000000000 : ℝ)*(major0) + (3592133006592501/100000000000000 : ℝ)*(major1) + (3592133006592501/100000000000000 : ℝ)*(major2) + (4836407537405941/100000000000000 : ℝ)*(sp0) + (604553315451887/12500000000000 : ℝ)*(sp1) + (2418213159947889/50000000000000 : ℝ)*(sp2) + (1173909786683111/50000000000000 : ℝ)*(sp3) + (5146567641/25000000000000 : ℝ)*(sp4) + (4512158901/25000000000000 : ℝ)*(sp7) + (1173918811000913/50000000000000 : ℝ)*(f.failure) + (604553515459563/12500000000000 : ℝ)*(f.sum) + (111401722921067/16855000000000000000000000000 : ℝ)*base65 + (2211106317262447/500000000000000000000000000000 : ℝ)*base67 + (3858378258762447/500000000000000000000000000000 : ℝ)*base69 + (2104555823262447/500000000000000000000000000000 : ℝ)*base71 + (15269776433941/8427500000000000000000000000 : ℝ)*base73 + (6883623368262447/500000000000000000000000000000 : ℝ)*base75 + (1865048751262447/500000000000000000000000000000 : ℝ)*base77 + (4375460834262447/500000000000000000000000000000 : ℝ)*base79 + (18795771161299/8427500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (1361489/2500000000000000000000 : ℝ)*base89 + (1361489/2500000000000000000000 : ℝ)*base91 + (1361489/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1678437933264292952718258201/842750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (827426529/100000000000000 : ℝ)*(base19) + (893048861/100000000000000 : ℝ)*(base23) + (609473/25000000000000 : ℝ)*(upper2) + (1784229/2500000000000 : ℝ)*(upper3) + (83867613/100000000000000 : ℝ)*(upper5) + (3623259853176291/100000000000000 : ℝ)*(major0) + (3623259853176291/100000000000000 : ℝ)*(major1) + (3623259853176291/100000000000000 : ℝ)*(major2) + (699545523/5000000000000 : ℝ)*(sp1) + (13467451591/100000000000000 : ℝ)*(sp2) + (4878337342159483/100000000000000 : ℝ)*(sp4) + (2439161261911247/50000000000000 : ℝ)*(sp5) + (4878322981659031/100000000000000 : ℝ)*(sp6) + (9472729191223/400000000000 : ℝ)*(sp7) + (9472729191223/400000000000 : ℝ)*(f.failure) + (4878337342159483/100000000000000 : ℝ)*(f.sum) + (24929945629601/8427500000000000000000000000 : ℝ)*base65 + (3456129742328423/500000000000000000000000000000 : ℝ)*base68 + (391500441671577/500000000000000000000000000000 : ℝ)*base69 + (829732786328423/500000000000000000000000000000 : ℝ)*base72 + (21517186220961/8427500000000000000000000000 : ℝ)*base73 + (2230944316671577/500000000000000000000000000000 : ℝ)*base75 + (5423357731828423/500000000000000000000000000000 : ℝ)*base78 + (6548905405828423/500000000000000000000000000000 : ℝ)*base80 + (17339297628893/4213750000000000000000000000 : ℝ)*base81 + (155081/20000000000000000000 : ℝ)*base90 + (155081/20000000000000000000 : ℝ)*base92 + (155081/20000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1298_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76498753/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1629/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2387/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2671/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7529/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1298_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1298_s4_0 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2082190291/10000000000 : ℝ)*x 0 + (1354617183/2500000000 : ℝ)*x 1 + (5239931007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2082190291/10000000000 : ℝ)^2129 ≤ (12668920810229/100000000000000 : ℝ)^1617 := by
    have hnat : (2082190291 : ℕ)^2129*100000000000000^1617 ≤ 12668920810229^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082190291 10000000000 12668920810229 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1354617183/2500000000 : ℝ)^2129 ≤ (44628509390021/100000000000000 : ℝ)^1617 := by
    have hnat : (1354617183 : ℕ)^2129*100000000000000^1617 ≤ 44628509390021^1617*2500000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354617183 2500000000 44628509390021 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5239931007/10000000000 : ℝ)^2129 ≤ (8540513956613/20000000000000 : ℝ)^1617 := by
    have hnat : (5239931007 : ℕ)^2129*20000000000000^1617 ≤ 8540513956613^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239931007 10000000000 8540513956613 20000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2082190291/10000000000 : ℝ), (1354617183/2500000000 : ℝ), (5239931007/10000000000 : ℝ)] ![(12668920810229/100000000000000 : ℝ), (44628509390021/100000000000000 : ℝ), (8540513956613/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2082190291/10000000000 : ℝ)|^2129 ≤ (12668920810229/100000000000000 : ℝ)^1617
        have hw : |(-2082190291/10000000000 : ℝ)|=(2082190291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1354617183/2500000000 : ℝ)|^2129 ≤ (44628509390021/100000000000000 : ℝ)^1617
        have hw : |(1354617183/2500000000 : ℝ)|=(1354617183/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5239931007/10000000000 : ℝ)|^2129 ≤ (8540513956613/20000000000000 : ℝ)^1617
        have hw : |(5239931007/10000000000 : ℝ)|=(5239931007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s4_1 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5350595001/10000000000 : ℝ)*x 0 + (-2173262167/10000000000 : ℝ)*x 1 + (5239931279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350595001/10000000000 : ℝ)^2129 ≤ (43893930280259/100000000000000 : ℝ)^1617 := by
    have hnat : (5350595001 : ℕ)^2129*100000000000000^1617 ≤ 43893930280259^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350595001 10000000000 43893930280259 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2173262167/10000000000 : ℝ)^2129 ≤ (13403497007969/100000000000000 : ℝ)^1617 := by
    have hnat : (2173262167 : ℕ)^2129*100000000000000^1617 ≤ 13403497007969^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173262167 10000000000 13403497007969 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5239931279/10000000000 : ℝ)^2129 ≤ (42702572701587/100000000000000 : ℝ)^1617 := by
    have hnat : (5239931279 : ℕ)^2129*100000000000000^1617 ≤ 42702572701587^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239931279 10000000000 42702572701587 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350595001/10000000000 : ℝ), (-2173262167/10000000000 : ℝ), (5239931279/10000000000 : ℝ)] ![(43893930280259/100000000000000 : ℝ), (13403497007969/100000000000000 : ℝ), (42702572701587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350595001/10000000000 : ℝ)|^2129 ≤ (43893930280259/100000000000000 : ℝ)^1617
        have hw : |(5350595001/10000000000 : ℝ)|=(5350595001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2173262167/10000000000 : ℝ)|^2129 ≤ (13403497007969/100000000000000 : ℝ)^1617
        have hw : |(-2173262167/10000000000 : ℝ)|=(2173262167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5239931279/10000000000 : ℝ)|^2129 ≤ (42702572701587/100000000000000 : ℝ)^1617
        have hw : |(5239931279/10000000000 : ℝ)|=(5239931279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s4_2 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5350594931/10000000000 : ℝ)*x 0 + (2619965521/5000000000 : ℝ)*x 1 + (-543315643/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350594931/10000000000 : ℝ)^2129 ≤ (21946964762091/50000000000000 : ℝ)^1617 := by
    have hnat : (5350594931 : ℕ)^2129*50000000000000^1617 ≤ 21946964762091^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350594931 10000000000 21946964762091 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2619965521/5000000000 : ℝ)^2129 ≤ (4270257015861/10000000000000 : ℝ)^1617 := by
    have hnat : (2619965521 : ℕ)^2129*10000000000000^1617 ≤ 4270257015861^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619965521 5000000000 4270257015861 10000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543315643/2500000000 : ℝ)^2129 ≤ (837718768543/6250000000000 : ℝ)^1617 := by
    have hnat : (543315643 : ℕ)^2129*6250000000000^1617 ≤ 837718768543^1617*2500000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543315643 2500000000 837718768543 6250000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350594931/10000000000 : ℝ), (2619965521/5000000000 : ℝ), (-543315643/2500000000 : ℝ)] ![(21946964762091/50000000000000 : ℝ), (4270257015861/10000000000000 : ℝ), (837718768543/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350594931/10000000000 : ℝ)|^2129 ≤ (21946964762091/50000000000000 : ℝ)^1617
        have hw : |(5350594931/10000000000 : ℝ)|=(5350594931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2619965521/5000000000 : ℝ)|^2129 ≤ (4270257015861/10000000000000 : ℝ)^1617
        have hw : |(2619965521/5000000000 : ℝ)|=(2619965521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-543315643/2500000000 : ℝ)|^2129 ≤ (837718768543/6250000000000 : ℝ)^1617
        have hw : |(-543315643/2500000000 : ℝ)|=(543315643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s4_3 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2169006081/5000000000 : ℝ)*x 0 + (2078918933/5000000000 : ℝ)*x 1 + (4525616497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2169006081/5000000000 : ℝ)^2129 ≤ (33299986422351/100000000000000 : ℝ)^1617 := by
    have hnat : (2169006081 : ℕ)^2129*100000000000000^1617 ≤ 33299986422351^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169006081 5000000000 33299986422351 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2078918933/5000000000 : ℝ)^2129 ≤ (3936383528063/12500000000000 : ℝ)^1617 := by
    have hnat : (2078918933 : ℕ)^2129*12500000000000^1617 ≤ 3936383528063^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078918933 5000000000 3936383528063 12500000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4525616497/10000000000 : ℝ)^2129 ≤ (8802236334843/25000000000000 : ℝ)^1617 := by
    have hnat : (4525616497 : ℕ)^2129*25000000000000^1617 ≤ 8802236334843^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4525616497 10000000000 8802236334843 25000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2169006081/5000000000 : ℝ), (2078918933/5000000000 : ℝ), (4525616497/10000000000 : ℝ)] ![(33299986422351/100000000000000 : ℝ), (3936383528063/12500000000000 : ℝ), (8802236334843/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2169006081/5000000000 : ℝ)|^2129 ≤ (33299986422351/100000000000000 : ℝ)^1617
        have hw : |(2169006081/5000000000 : ℝ)|=(2169006081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2078918933/5000000000 : ℝ)|^2129 ≤ (3936383528063/12500000000000 : ℝ)^1617
        have hw : |(2078918933/5000000000 : ℝ)|=(2078918933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4525616497/10000000000 : ℝ)|^2129 ≤ (8802236334843/25000000000000 : ℝ)^1617
        have hw : |(4525616497/10000000000 : ℝ)|=(4525616497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s4_4 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2082204297/10000000000 : ℝ)*x 0 + (5240592989/10000000000 : ℝ)*x 1 + (1354450841/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2082204297/10000000000 : ℝ)^2129 ≤ (12669033011927/100000000000000 : ℝ)^1617 := by
    have hnat : (2082204297 : ℕ)^2129*100000000000000^1617 ≤ 12669033011927^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082204297 10000000000 12669033011927 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5240592989/10000000000 : ℝ)^2129 ≤ (42709672899773/100000000000000 : ℝ)^1617 := by
    have hnat : (5240592989 : ℕ)^2129*100000000000000^1617 ≤ 42709672899773^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240592989 10000000000 42709672899773 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1354450841/2500000000 : ℝ)^2129 ≤ (22310647040647/50000000000000 : ℝ)^1617 := by
    have hnat : (1354450841 : ℕ)^2129*50000000000000^1617 ≤ 22310647040647^1617*2500000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354450841 2500000000 22310647040647 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2082204297/10000000000 : ℝ), (5240592989/10000000000 : ℝ), (1354450841/2500000000 : ℝ)] ![(12669033011927/100000000000000 : ℝ), (42709672899773/100000000000000 : ℝ), (22310647040647/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2082204297/10000000000 : ℝ)|^2129 ≤ (12669033011927/100000000000000 : ℝ)^1617
        have hw : |(-2082204297/10000000000 : ℝ)|=(2082204297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5240592989/10000000000 : ℝ)|^2129 ≤ (42709672899773/100000000000000 : ℝ)^1617
        have hw : |(5240592989/10000000000 : ℝ)|=(5240592989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1354450841/2500000000 : ℝ)|^2129 ≤ (22310647040647/50000000000000 : ℝ)^1617
        have hw : |(1354450841/2500000000 : ℝ)|=(1354450841/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s4_5 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5304850309/10000000000 : ℝ)*x 0 + (-498847491/2500000000 : ℝ)*x 1 + (5417803237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304850309/10000000000 : ℝ)^2129 ≤ (43400507314651/100000000000000 : ℝ)^1617 := by
    have hnat : (5304850309 : ℕ)^2129*100000000000000^1617 ≤ 43400507314651^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304850309 10000000000 43400507314651 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (498847491/2500000000 : ℝ)^2129 ≤ (374318749107/3125000000000 : ℝ)^1617 := by
    have hnat : (498847491 : ℕ)^2129*3125000000000^1617 ≤ 374318749107^1617*2500000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      498847491 2500000000 374318749107 3125000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5417803237/10000000000 : ℝ)^2129 ≤ (22310646352061/50000000000000 : ℝ)^1617 := by
    have hnat : (5417803237 : ℕ)^2129*50000000000000^1617 ≤ 22310646352061^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417803237 10000000000 22310646352061 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304850309/10000000000 : ℝ), (-498847491/2500000000 : ℝ), (5417803237/10000000000 : ℝ)] ![(43400507314651/100000000000000 : ℝ), (374318749107/3125000000000 : ℝ), (22310646352061/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304850309/10000000000 : ℝ)|^2129 ≤ (43400507314651/100000000000000 : ℝ)^1617
        have hw : |(5304850309/10000000000 : ℝ)|=(5304850309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-498847491/2500000000 : ℝ)|^2129 ≤ (374318749107/3125000000000 : ℝ)^1617
        have hw : |(-498847491/2500000000 : ℝ)|=(498847491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5417803237/10000000000 : ℝ)|^2129 ≤ (22310646352061/50000000000000 : ℝ)^1617
        have hw : |(5417803237/10000000000 : ℝ)|=(5417803237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s4_6 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652424987/5000000000 : ℝ)*x 0 + (2708901803/5000000000 : ℝ)*x 1 + (-1995389913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652424987/5000000000 : ℝ)^2129 ≤ (21700251853053/50000000000000 : ℝ)^1617 := by
    have hnat : (2652424987 : ℕ)^2129*50000000000000^1617 ≤ 21700251853053^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652424987 5000000000 21700251853053 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2708901803/5000000000 : ℝ)^2129 ≤ (5577662088189/12500000000000 : ℝ)^1617 := by
    have hnat : (2708901803 : ℕ)^2129*12500000000000^1617 ≤ 5577662088189^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708901803 5000000000 5577662088189 12500000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1995389913/10000000000 : ℝ)^2129 ≤ (748637473021/6250000000000 : ℝ)^1617 := by
    have hnat : (1995389913 : ℕ)^2129*6250000000000^1617 ≤ 748637473021^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1995389913 10000000000 748637473021 6250000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652424987/5000000000 : ℝ), (2708901803/5000000000 : ℝ), (-1995389913/10000000000 : ℝ)] ![(21700251853053/50000000000000 : ℝ), (5577662088189/12500000000000 : ℝ), (748637473021/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652424987/5000000000 : ℝ)|^2129 ≤ (21700251853053/50000000000000 : ℝ)^1617
        have hw : |(2652424987/5000000000 : ℝ)|=(2652424987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2708901803/5000000000 : ℝ)|^2129 ≤ (5577662088189/12500000000000 : ℝ)^1617
        have hw : |(2708901803/5000000000 : ℝ)|=(2708901803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1995389913/10000000000 : ℝ)|^2129 ≤ (748637473021/6250000000000 : ℝ)^1617
        have hw : |(-1995389913/10000000000 : ℝ)|=(1995389913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s4_7 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (867608271/2000000000 : ℝ)*x 0 + (4524253383/10000000000 : ℝ)*x 1 + (1039802083/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (867608271/2000000000 : ℝ)^2129 ≤ (8325070368513/25000000000000 : ℝ)^1617 := by
    have hnat : (867608271 : ℕ)^2129*25000000000000^1617 ≤ 8325070368513^1617*2000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      867608271 2000000000 8325070368513 25000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4524253383/10000000000 : ℝ)^2129 ≤ (8798745796729/25000000000000 : ℝ)^1617 := by
    have hnat : (4524253383 : ℕ)^2129*25000000000000^1617 ≤ 8798745796729^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4524253383 10000000000 8798745796729 25000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1039802083/2500000000 : ℝ)^2129 ≤ (31504735325709/100000000000000 : ℝ)^1617 := by
    have hnat : (1039802083 : ℕ)^2129*100000000000000^1617 ≤ 31504735325709^1617*2500000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039802083 2500000000 31504735325709 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(867608271/2000000000 : ℝ), (4524253383/10000000000 : ℝ), (1039802083/2500000000 : ℝ)] ![(8325070368513/25000000000000 : ℝ), (8798745796729/25000000000000 : ℝ), (31504735325709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(867608271/2000000000 : ℝ)|^2129 ≤ (8325070368513/25000000000000 : ℝ)^1617
        have hw : |(867608271/2000000000 : ℝ)|=(867608271/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4524253383/10000000000 : ℝ)|^2129 ≤ (8798745796729/25000000000000 : ℝ)^1617
        have hw : |(4524253383/10000000000 : ℝ)|=(4524253383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1039802083/2500000000 : ℝ)|^2129 ≤ (31504735325709/100000000000000 : ℝ)^1617
        have hw : |(1039802083/2500000000 : ℝ)|=(1039802083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1298_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76498753/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7529/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2671/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10973/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14751/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7529/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2671/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7529/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2671/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7529/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2671/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7529/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2671/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7529/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2671/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7529/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2671/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2671/25000 : ℝ) ^ (4257/1024 : ℝ) ≤ (1833397689223807/20000000000000000000 : ℝ) := by
    have hpowers : (2671/25000 : ℝ)^4257 ≤ (1833397689223807/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2671 : ℕ)^4257*20000000000000000000^1024 ≤ 1833397689223807^1024*25000^4257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2671 25000 1833397689223807 20000000000000000000 4257 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2671/25000 : ℝ)) (X := (1833397689223807/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7529/50000 : ℝ) ^ (4257/1024 : ℝ) ≤ (38176169399271209/100000000000000000000 : ℝ) := by
    have hpowers : (7529/50000 : ℝ)^4257 ≤ (38176169399271209/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7529 : ℕ)^4257*100000000000000000000^1024 ≤ 38176169399271209^1024*50000^4257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7529 50000 38176169399271209 100000000000000000000 4257 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7529/50000 : ℝ)) (X := (38176169399271209/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001833397689223807/10000000000000000000 : ℝ) ≤ (10000440983919397/10000000000000000 : ℝ) ^ (4257/1024 : ℝ) := by
    have hpowers : (10001833397689223807/10000000000000000000 : ℝ)^1024 ≤ (10000440983919397/10000000000000000 : ℝ)^4257 := by
      have hnat : (10001833397689223807 : ℕ)^1024*10000000000000000^4257 ≤ 10000440983919397^4257*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001833397689223807 10000000000000000000 10000440983919397 10000000000000000 1024 4257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000440983919397/10000000000000000 : ℝ)) (X := (10001833397689223807/10000000000000000000 : ℝ)) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011835789461347561/25000000000000000000 : ℝ) ≤ (10001138611244307/10000000000000000 : ℝ) ^ (4257/1024 : ℝ) := by
    have hpowers : (25011835789461347561/25000000000000000000 : ℝ)^1024 ≤ (10001138611244307/10000000000000000 : ℝ)^4257 := by
      have hnat : (25011835789461347561 : ℕ)^1024*10000000000000000^4257 ≤ 10001138611244307^4257*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011835789461347561 25000000000000000000 10001138611244307 10000000000000000 1024 4257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001138611244307/10000000000000000 : ℝ)) (X := (25011835789461347561/25000000000000000000 : ℝ)) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50038176169399271209/50000000000000000000 : ℝ) ≤ (10001836238569217/10000000000000000 : ℝ) ^ (4257/1024 : ℝ) := by
    have hpowers : (50038176169399271209/50000000000000000000 : ℝ)^1024 ≤ (10001836238569217/10000000000000000 : ℝ)^4257 := by
      have hnat : (50038176169399271209 : ℕ)^1024*10000000000000000^4257 ≤ 10001836238569217^4257*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50038176169399271209 50000000000000000000 10001836238569217 10000000000000000 1024 4257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001836238569217/10000000000000000 : ℝ)) (X := (50038176169399271209/50000000000000000000 : ℝ)) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1833397689223807/20000000000000000000 : ℝ) ≤ ((21863510981492382799/21870000000000000000 : ℝ)+2*(69762732491/43740000000000 : ℝ)*(2671/25000 : ℝ))^(4257/1024 : ℝ) := by
    rw [show (21863510981492382799/21870000000000000000 : ℝ)+2*(69762732491/43740000000000 : ℝ)*(2671/25000 : ℝ)=(10000440983919397/10000000000000000 : ℝ) by norm_num, show 1+2*(1833397689223807/20000000000000000000 : ℝ)=(10001833397689223807/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38176169399271209/100000000000000000000 : ℝ)+(1833397689223807/20000000000000000000 : ℝ) ≤ ((21863510981492382799/21870000000000000000 : ℝ)+(69762732491/43740000000000 : ℝ)*((7529/50000 : ℝ)+(2671/25000 : ℝ)))^(4257/1024 : ℝ) := by
    rw [show (21863510981492382799/21870000000000000000 : ℝ)+(69762732491/43740000000000 : ℝ)*((7529/50000 : ℝ)+(2671/25000 : ℝ))=(10001138611244307/10000000000000000 : ℝ) by norm_num, show 1+(38176169399271209/100000000000000000000 : ℝ)+(1833397689223807/20000000000000000000 : ℝ)=(25011835789461347561/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38176169399271209/100000000000000000000 : ℝ) ≤ ((21863510981492382799/21870000000000000000 : ℝ)+2*(69762732491/43740000000000 : ℝ)*(7529/50000 : ℝ))^(4257/1024 : ℝ) := by
    rw [show (21863510981492382799/21870000000000000000 : ℝ)+2*(69762732491/43740000000000 : ℝ)*(7529/50000 : ℝ)=(10001836238569217/10000000000000000 : ℝ) by norm_num, show 1+2*(38176169399271209/100000000000000000000 : ℝ)=(50038176169399271209/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (21863510981492382799/21870000000000000000 : ℝ)*(X 1 0+X 2 0)+(69762732491/43740000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4257/1024 : ℝ)) (lo := (2671/25000 : ℝ)) (hi := (7529/50000 : ℝ)) (c := (21863510981492382799/21870000000000000000 : ℝ)) (alpha := (69762732491/43740000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (21863510981492382799/21870000000000000000 : ℝ)*(X 0 1+X 2 1)+(69762732491/43740000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4257/1024 : ℝ)) (lo := (2671/25000 : ℝ)) (hi := (7529/50000 : ℝ)) (c := (21863510981492382799/21870000000000000000 : ℝ)) (alpha := (69762732491/43740000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (21863510981492382799/21870000000000000000 : ℝ)*(X 0 2+X 1 2)+(69762732491/43740000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4257/1024 : ℝ)) (lo := (2671/25000 : ℝ)) (hi := (7529/50000 : ℝ)) (c := (21863510981492382799/21870000000000000000 : ℝ)) (alpha := (69762732491/43740000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2082190291/10000000000 : ℝ)*X 0 0+(1354617183/2500000000 : ℝ)*X 0 1+(5239931007/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350595001/10000000000 : ℝ)*X 1 0+(-2173262167/10000000000 : ℝ)*X 1 1+(5239931279/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350594931/10000000000 : ℝ)*X 2 0+(2619965521/5000000000 : ℝ)*X 2 1+(-543315643/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2169006081/5000000000 : ℝ)*X 0 0+(2078918933/5000000000 : ℝ)*X 0 1+(4525616497/10000000000 : ℝ)*X 0 2+(2169006081/5000000000 : ℝ)*X 1 0+(2078918933/5000000000 : ℝ)*X 1 1+(4525616497/10000000000 : ℝ)*X 1 2+(2169006081/5000000000 : ℝ)*X 2 0+(2078918933/5000000000 : ℝ)*X 2 1+(4525616497/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2082204297/10000000000 : ℝ)*X 0 0+(5240592989/10000000000 : ℝ)*X 0 1+(1354450841/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5304850309/10000000000 : ℝ)*X 1 0+(-498847491/2500000000 : ℝ)*X 1 1+(5417803237/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652424987/5000000000 : ℝ)*X 2 0+(2708901803/5000000000 : ℝ)*X 2 1+(-1995389913/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((867608271/2000000000 : ℝ)*X 0 0+(4524253383/10000000000 : ℝ)*X 0 1+(1039802083/2500000000 : ℝ)*X 0 2+(867608271/2000000000 : ℝ)*X 1 0+(4524253383/10000000000 : ℝ)*X 1 1+(1039802083/2500000000 : ℝ)*X 1 2+(867608271/2000000000 : ℝ)*X 2 0+(4524253383/10000000000 : ℝ)*X 2 1+(1039802083/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (140068123841766756599483/45000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (186263297/25000000000000 : ℝ)*(base19) + (49670977/6250000000000 : ℝ)*(base23) + (8335591/10000000000000 : ℝ)*(upper2) + (59186431/25000000000000 : ℝ)*(upper3) + (83201441877477/2000000000000 : ℝ)*(major0) + (83201441877477/2000000000000 : ℝ)*(major1) + (83201441877477/2000000000000 : ℝ)*(major2) + (5601083199489141/100000000000000 : ℝ)*(sp0) + (2800548824086713/50000000000000 : ℝ)*(sp1) + (5601093758687823/100000000000000 : ℝ)*(sp2) + (2719035058252453/100000000000000 : ℝ)*(sp3) + (15193737473/100000000000000 : ℝ)*(sp4) + (95995079/2500000000000 : ℝ)*(sp6) + (10632514461/100000000000000 : ℝ)*(sp7) + (1359522845383457/50000000000000 : ℝ)*(f.failure) + (2800549196613307/50000000000000 : ℝ)*(f.sum) + (94986878201/81000000000000000000000000 : ℝ)*base65 + (12510431992221551/1620000000000000000000000000000 : ℝ)*base68 + (343478286938449/1620000000000000000000000000000 : ℝ)*base69 + (9284750519361551/1620000000000000000000000000000 : ℝ)*base72 + (46979083189/81000000000000000000000000 : ℝ)*base74 + (3991702778961551/1620000000000000000000000000000 : ℝ)*base76 + (19830463915101551/1620000000000000000000000000000 : ℝ)*base78 + (13986058429761551/1620000000000000000000000000000 : ℝ)*base80 + (504166168133/81000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (17329121/2500000000000000000000 : ℝ)*base89 + (17329121/2500000000000000000000 : ℝ)*base91 + (17329121/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1090249896103862122518358489/182250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1471256653/100000000000000 : ℝ)*(base19) + (605340963/50000000000000 : ℝ)*(base23) + (42629613/25000000000000 : ℝ)*(upper3) + (29271623/100000000000000 : ℝ)*(lower4) + (46894639/100000000000000 : ℝ)*(upper5) + (2095597941597437/50000000000000 : ℝ)*(major0) + (2095597941597437/50000000000000 : ℝ)*(major1) + (2095597941597437/50000000000000 : ℝ)*(major2) + (4857136089/20000000000000 : ℝ)*(sp1) + (14496903831/50000000000000 : ℝ)*(sp2) + (5643003198656871/100000000000000 : ℝ)*(sp4) + (5642977441719773/100000000000000 : ℝ)*(sp5) + (5642972994167283/100000000000000 : ℝ)*(sp6) + (684847092081827/25000000000000 : ℝ)*(sp7) + (684847092081827/25000000000000 : ℝ)*(f.failure) + (5643003198656871/100000000000000 : ℝ)*(f.sum) + (5993295234023/2187000000000000000000000000 : ℝ)*base65 + (5181335484465713837/1093500000000000000000000000000000 : ℝ)*base68 + (9884789447705213837/1093500000000000000000000000000000 : ℝ)*base70 + (11570412417182213837/1093500000000000000000000000000000 : ℝ)*base72 + (1417160981587/437400000000000000000000000 : ℝ)*base73 + (25822475743877213837/1093500000000000000000000000000000 : ℝ)*base76 + (9240652342079213837/1093500000000000000000000000000000 : ℝ)*base78 + (20836525428026213837/1093500000000000000000000000000000 : ℝ)*base80 + (6160825083697/2187000000000000000000000000 : ℝ)*base82 + (14461731/1250000000000000000000 : ℝ)*base89 + (14461731/1250000000000000000000 : ℝ)*base91 + (14461731/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1298_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76498753/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7529/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2671/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10973/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14751/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1298_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1298_s5_0 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2082531151/10000000000 : ℝ)*x 0 + (5415547101/10000000000 : ℝ)*x 1 + (163832151/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2082531151/10000000000 : ℝ)^2129 ≤ (12671651498599/100000000000000 : ℝ)^1617 := by
    have hnat : (2082531151 : ℕ)^2129*100000000000000^1617 ≤ 12671651498599^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082531151 10000000000 12671651498599 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415547101/10000000000 : ℝ)^2129 ≤ (22298414528587/50000000000000 : ℝ)^1617 := by
    have hnat : (5415547101 : ℕ)^2129*50000000000000^1617 ≤ 22298414528587^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415547101 10000000000 22298414528587 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163832151/312500000 : ℝ)^2129 ≤ (42731519428767/100000000000000 : ℝ)^1617 := by
    have hnat : (163832151 : ℕ)^2129*100000000000000^1617 ≤ 42731519428767^1617*312500000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163832151 312500000 42731519428767 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2082531151/10000000000 : ℝ), (5415547101/10000000000 : ℝ), (163832151/312500000 : ℝ)] ![(12671651498599/100000000000000 : ℝ), (22298414528587/50000000000000 : ℝ), (42731519428767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2082531151/10000000000 : ℝ)|^2129 ≤ (12671651498599/100000000000000 : ℝ)^1617
        have hw : |(-2082531151/10000000000 : ℝ)|=(2082531151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415547101/10000000000 : ℝ)|^2129 ≤ (22298414528587/50000000000000 : ℝ)^1617
        have hw : |(5415547101/10000000000 : ℝ)|=(5415547101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163832151/312500000 : ℝ)|^2129 ≤ (42731519428767/100000000000000 : ℝ)^1617
        have hw : |(163832151/312500000 : ℝ)|=(163832151/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s5_1 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674927161/5000000000 : ℝ)*x 0 + (-2170682179/10000000000 : ℝ)*x 1 + (5242628791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674927161/5000000000 : ℝ)^2129 ≤ (1755437212273/4000000000000 : ℝ)^1617 := by
    have hnat : (2674927161 : ℕ)^2129*4000000000000^1617 ≤ 1755437212273^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674927161 5000000000 1755437212273 4000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2170682179/10000000000 : ℝ)^2129 ≤ (3345637672699/25000000000000 : ℝ)^1617 := by
    have hnat : (2170682179 : ℕ)^2129*25000000000000^1617 ≤ 3345637672699^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170682179 10000000000 3345637672699 25000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242628791/10000000000 : ℝ)^2129 ≤ (42731518988771/100000000000000 : ℝ)^1617 := by
    have hnat : (5242628791 : ℕ)^2129*100000000000000^1617 ≤ 42731518988771^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242628791 10000000000 42731518988771 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674927161/5000000000 : ℝ), (-2170682179/10000000000 : ℝ), (5242628791/10000000000 : ℝ)] ![(1755437212273/4000000000000 : ℝ), (3345637672699/25000000000000 : ℝ), (42731518988771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674927161/5000000000 : ℝ)|^2129 ≤ (1755437212273/4000000000000 : ℝ)^1617
        have hw : |(2674927161/5000000000 : ℝ)|=(2674927161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2170682179/10000000000 : ℝ)|^2129 ≤ (3345637672699/25000000000000 : ℝ)^1617
        have hw : |(-2170682179/10000000000 : ℝ)|=(2170682179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242628791/10000000000 : ℝ)|^2129 ≤ (42731518988771/100000000000000 : ℝ)^1617
        have hw : |(5242628791/10000000000 : ℝ)|=(5242628791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s5_2 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349854141/10000000000 : ℝ)*x 0 + (5242629001/10000000000 : ℝ)*x 1 + (-2170682143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349854141/10000000000 : ℝ)^2129 ≤ (5485741043989/12500000000000 : ℝ)^1617 := by
    have hnat : (5349854141 : ℕ)^2129*12500000000000^1617 ≤ 5485741043989^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349854141 10000000000 5485741043989 12500000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242629001/10000000000 : ℝ)^2129 ≤ (42731521242409/100000000000000 : ℝ)^1617 := by
    have hnat : (5242629001 : ℕ)^2129*100000000000000^1617 ≤ 42731521242409^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242629001 10000000000 42731521242409 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2170682143/10000000000 : ℝ)^2129 ≤ (836409399911/6250000000000 : ℝ)^1617 := by
    have hnat : (2170682143 : ℕ)^2129*6250000000000^1617 ≤ 836409399911^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170682143 10000000000 836409399911 6250000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349854141/10000000000 : ℝ), (5242629001/10000000000 : ℝ), (-2170682143/10000000000 : ℝ)] ![(5485741043989/12500000000000 : ℝ), (42731521242409/100000000000000 : ℝ), (836409399911/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349854141/10000000000 : ℝ)|^2129 ≤ (5485741043989/12500000000000 : ℝ)^1617
        have hw : |(5349854141/10000000000 : ℝ)|=(5349854141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242629001/10000000000 : ℝ)|^2129 ≤ (42731521242409/100000000000000 : ℝ)^1617
        have hw : |(5242629001/10000000000 : ℝ)|=(5242629001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2170682143/10000000000 : ℝ)|^2129 ≤ (836409399911/6250000000000 : ℝ)^1617
        have hw : |(-2170682143/10000000000 : ℝ)|=(2170682143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s5_3 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (542277023/1250000000 : ℝ)*x 0 + (208180013/500000000 : ℝ)*x 1 + (2259901487/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542277023/1250000000 : ℝ)^2129 ≤ (33302048472233/100000000000000 : ℝ)^1617 := by
    have hnat : (542277023 : ℕ)^2129*100000000000000^1617 ≤ 33302048472233^1617*1250000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542277023 1250000000 33302048472233 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208180013/500000000 : ℝ)^2129 ≤ (15774271923511/50000000000000 : ℝ)^1617 := by
    have hnat : (208180013 : ℕ)^2129*50000000000000^1617 ≤ 15774271923511^1617*500000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208180013 500000000 15774271923511 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2259901487/5000000000 : ℝ)^2129 ≤ (35149407654141/100000000000000 : ℝ)^1617 := by
    have hnat : (2259901487 : ℕ)^2129*100000000000000^1617 ≤ 35149407654141^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259901487 5000000000 35149407654141 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(542277023/1250000000 : ℝ), (208180013/500000000 : ℝ), (2259901487/5000000000 : ℝ)] ![(33302048472233/100000000000000 : ℝ), (15774271923511/50000000000000 : ℝ), (35149407654141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(542277023/1250000000 : ℝ)|^2129 ≤ (33302048472233/100000000000000 : ℝ)^1617
        have hw : |(542277023/1250000000 : ℝ)|=(542277023/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(208180013/500000000 : ℝ)|^2129 ≤ (15774271923511/50000000000000 : ℝ)^1617
        have hw : |(208180013/500000000 : ℝ)|=(208180013/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2259901487/5000000000 : ℝ)|^2129 ≤ (35149407654141/100000000000000 : ℝ)^1617
        have hw : |(2259901487/5000000000 : ℝ)|=(2259901487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s5_4 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2082544267/10000000000 : ℝ)*x 0 + (5243249717/10000000000 : ℝ)*x 1 + (5414922849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2082544267/10000000000 : ℝ)^2129 ≤ (12671756575969/100000000000000 : ℝ)^1617 := by
    have hnat : (2082544267 : ℕ)^2129*100000000000000^1617 ≤ 12671756575969^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082544267 10000000000 12671756575969 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243249717/10000000000 : ℝ)^2129 ≤ (42738182649123/100000000000000 : ℝ)^1617 := by
    have hnat : (5243249717 : ℕ)^2129*100000000000000^1617 ≤ 42738182649123^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243249717 10000000000 42738182649123 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414922849/10000000000 : ℝ)^2129 ≤ (11147515190459/25000000000000 : ℝ)^1617 := by
    have hnat : (5414922849 : ℕ)^2129*25000000000000^1617 ≤ 11147515190459^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414922849 10000000000 11147515190459 25000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2082544267/10000000000 : ℝ), (5243249717/10000000000 : ℝ), (5414922849/10000000000 : ℝ)] ![(12671756575969/100000000000000 : ℝ), (42738182649123/100000000000000 : ℝ), (11147515190459/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2082544267/10000000000 : ℝ)|^2129 ≤ (12671756575969/100000000000000 : ℝ)^1617
        have hw : |(-2082544267/10000000000 : ℝ)|=(2082544267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243249717/10000000000 : ℝ)|^2129 ≤ (42738182649123/100000000000000 : ℝ)^1617
        have hw : |(5243249717/10000000000 : ℝ)|=(5243249717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414922849/10000000000 : ℝ)|^2129 ≤ (11147515190459/25000000000000 : ℝ)^1617
        have hw : |(5414922849/10000000000 : ℝ)|=(5414922849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s5_5 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305549259/10000000000 : ℝ)*x 0 + (-1998388201/10000000000 : ℝ)*x 1 + (5414922859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305549259/10000000000 : ℝ)^2129 ≤ (21704018202269/50000000000000 : ℝ)^1617 := by
    have hnat : (5305549259 : ℕ)^2129*50000000000000^1617 ≤ 21704018202269^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305549259 10000000000 21704018202269 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1998388201/10000000000 : ℝ)^2129 ≤ (12001902716257/100000000000000 : ℝ)^1617 := by
    have hnat : (1998388201 : ℕ)^2129*100000000000000^1617 ≤ 12001902716257^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1998388201 10000000000 12001902716257 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414922859/10000000000 : ℝ)^2129 ≤ (2786878804391/6250000000000 : ℝ)^1617 := by
    have hnat : (5414922859 : ℕ)^2129*6250000000000^1617 ≤ 2786878804391^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414922859 10000000000 2786878804391 6250000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305549259/10000000000 : ℝ), (-1998388201/10000000000 : ℝ), (5414922859/10000000000 : ℝ)] ![(21704018202269/50000000000000 : ℝ), (12001902716257/100000000000000 : ℝ), (2786878804391/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305549259/10000000000 : ℝ)|^2129 ≤ (21704018202269/50000000000000 : ℝ)^1617
        have hw : |(5305549259/10000000000 : ℝ)|=(5305549259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1998388201/10000000000 : ℝ)|^2129 ≤ (12001902716257/100000000000000 : ℝ)^1617
        have hw : |(-1998388201/10000000000 : ℝ)|=(1998388201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414922859/10000000000 : ℝ)|^2129 ≤ (2786878804391/6250000000000 : ℝ)^1617
        have hw : |(5414922859/10000000000 : ℝ)|=(5414922859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s5_6 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (82899207/156250000 : ℝ)*x 0 + (270746143/500000000 : ℝ)*x 1 + (-999194107/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82899207/156250000 : ℝ)^2129 ≤ (43408036286043/100000000000000 : ℝ)^1617 := by
    have hnat : (82899207 : ℕ)^2129*100000000000000^1617 ≤ 43408036286043^1617*156250000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82899207 156250000 43408036286043 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270746143/500000000 : ℝ)^2129 ≤ (22295030440549/50000000000000 : ℝ)^1617 := by
    have hnat : (270746143 : ℕ)^2129*50000000000000^1617 ≤ 22295030440549^1617*500000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270746143 500000000 22295030440549 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (999194107/5000000000 : ℝ)^2129 ≤ (6000951409527/50000000000000 : ℝ)^1617 := by
    have hnat : (999194107 : ℕ)^2129*50000000000000^1617 ≤ 6000951409527^1617*5000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999194107 5000000000 6000951409527 50000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82899207/156250000 : ℝ), (270746143/500000000 : ℝ), (-999194107/5000000000 : ℝ)] ![(43408036286043/100000000000000 : ℝ), (22295030440549/50000000000000 : ℝ), (6000951409527/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82899207/156250000 : ℝ)|^2129 ≤ (43408036286043/100000000000000 : ℝ)^1617
        have hw : |(82899207/156250000 : ℝ)|=(82899207/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270746143/500000000 : ℝ)|^2129 ≤ (22295030440549/50000000000000 : ℝ)^1617
        have hw : |(270746143/500000000 : ℝ)|=(270746143/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-999194107/5000000000 : ℝ)|^2129 ≤ (6000951409527/50000000000000 : ℝ)^1617
        have hw : |(-999194107/5000000000 : ℝ)|=(999194107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1298_s5_7 (p : ℝ) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ)) (x : Fin 3 → ℝ) :
    (867648607/2000000000 : ℝ)*x 0 + (4518523839/10000000000 : ℝ)*x 1 + (832977151/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (867648607/2000000000 : ℝ)^2129 ≤ (6660463971503/20000000000000 : ℝ)^1617 := by
    have hnat : (867648607 : ℕ)^2129*20000000000000^1617 ≤ 6660463971503^1617*2000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      867648607 2000000000 6660463971503 20000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4518523839/10000000000 : ℝ)^2129 ≤ (8784077744633/25000000000000 : ℝ)^1617 := by
    have hnat : (4518523839 : ℕ)^2129*25000000000000^1617 ≤ 8784077744633^1617*10000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4518523839 10000000000 8784077744633 25000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (832977151/2000000000 : ℝ)^2129 ≤ (31561369147577/100000000000000 : ℝ)^1617 := by
    have hnat : (832977151 : ℕ)^2129*100000000000000^1617 ≤ 31561369147577^1617*2000000000^2129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      832977151 2000000000 31561369147577 100000000000000 2129 1617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2129/512 : ℝ)) 2129 1617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(867648607/2000000000 : ℝ), (4518523839/10000000000 : ℝ), (832977151/2000000000 : ℝ)] ![(6660463971503/20000000000000 : ℝ), (8784077744633/25000000000000 : ℝ), (31561369147577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(867648607/2000000000 : ℝ)|^2129 ≤ (6660463971503/20000000000000 : ℝ)^1617
        have hw : |(867648607/2000000000 : ℝ)|=(867648607/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4518523839/10000000000 : ℝ)|^2129 ≤ (8784077744633/25000000000000 : ℝ)^1617
        have hw : |(4518523839/10000000000 : ℝ)|=(4518523839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(832977151/2000000000 : ℝ)|^2129 ≤ (31561369147577/100000000000000 : ℝ)^1617
        have hw : |(832977151/2000000000 : ℝ)|=(832977151/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1298_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76498753/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14751/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10973/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1103/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1469/10000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (10973/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14751/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10973/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14751/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10973/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14751/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10973/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14751/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10973/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14751/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10973/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10973/100000 : ℝ) ^ (4257/1024 : ℝ) ≤ (10242717034429441/100000000000000000000 : ℝ) := by
    have hpowers : (10973/100000 : ℝ)^4257 ≤ (10242717034429441/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10973 : ℕ)^4257*100000000000000000000^1024 ≤ 10242717034429441^1024*100000^4257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10973 100000 10242717034429441 100000000000000000000 4257 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10973/100000 : ℝ)) (X := (10242717034429441/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14751/100000 : ℝ) ^ (4257/1024 : ℝ) ≤ (17521549591564351/50000000000000000000 : ℝ) := by
    have hpowers : (14751/100000 : ℝ)^4257 ≤ (17521549591564351/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14751 : ℕ)^4257*50000000000000000000^1024 ≤ 17521549591564351^1024*100000^4257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14751 100000 17521549591564351 50000000000000000000 4257 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14751/100000 : ℝ)) (X := (17521549591564351/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010242717034429441/50000000000000000000 : ℝ) ≤ (500024636425769/500000000000000 : ℝ) ^ (4257/1024 : ℝ) := by
    have hpowers : (50010242717034429441/50000000000000000000 : ℝ)^1024 ≤ (500024636425769/500000000000000 : ℝ)^4257 := by
      have hnat : (50010242717034429441 : ℕ)^1024*500000000000000^4257 ≤ 500024636425769^4257*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010242717034429441 50000000000000000000 500024636425769 500000000000000 1024 4257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500024636425769/500000000000000 : ℝ)) (X := (50010242717034429441/50000000000000000000 : ℝ)) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045285816217558143/100000000000000000000 : ℝ) ≤ (10001089140323079/10000000000000000 : ℝ) ^ (4257/1024 : ℝ) := by
    have hpowers : (100045285816217558143/100000000000000000000 : ℝ)^1024 ≤ (10001089140323079/10000000000000000 : ℝ)^4257 := by
      have hnat : (100045285816217558143 : ℕ)^1024*10000000000000000^4257 ≤ 10001089140323079^4257*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045285816217558143 100000000000000000000 10001089140323079 10000000000000000 1024 4257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001089140323079/10000000000000000 : ℝ)) (X := (100045285816217558143/100000000000000000000 : ℝ)) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017521549591564351/25000000000000000000 : ℝ) ≤ (5000842776065389/5000000000000000 : ℝ) ^ (4257/1024 : ℝ) := by
    have hpowers : (25017521549591564351/25000000000000000000 : ℝ)^1024 ≤ (5000842776065389/5000000000000000 : ℝ)^4257 := by
      have hnat : (25017521549591564351 : ℕ)^1024*5000000000000000^4257 ≤ 5000842776065389^4257*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017521549591564351 25000000000000000000 5000842776065389 5000000000000000 1024 4257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000842776065389/5000000000000000 : ℝ)) (X := (25017521549591564351/25000000000000000000 : ℝ)) (by norm_num) 4257 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10242717034429441/100000000000000000000 : ℝ) ≤ ((18884386337399671693/18890000000000000000 : ℝ)+2*(596411807699/377800000000000 : ℝ)*(10973/100000 : ℝ))^(4257/1024 : ℝ) := by
    rw [show (18884386337399671693/18890000000000000000 : ℝ)+2*(596411807699/377800000000000 : ℝ)*(10973/100000 : ℝ)=(500024636425769/500000000000000 : ℝ) by norm_num, show 1+2*(10242717034429441/100000000000000000000 : ℝ)=(50010242717034429441/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17521549591564351/50000000000000000000 : ℝ)+(10242717034429441/100000000000000000000 : ℝ) ≤ ((18884386337399671693/18890000000000000000 : ℝ)+(596411807699/377800000000000 : ℝ)*((14751/100000 : ℝ)+(10973/100000 : ℝ)))^(4257/1024 : ℝ) := by
    rw [show (18884386337399671693/18890000000000000000 : ℝ)+(596411807699/377800000000000 : ℝ)*((14751/100000 : ℝ)+(10973/100000 : ℝ))=(10001089140323079/10000000000000000 : ℝ) by norm_num, show 1+(17521549591564351/50000000000000000000 : ℝ)+(10242717034429441/100000000000000000000 : ℝ)=(100045285816217558143/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17521549591564351/50000000000000000000 : ℝ) ≤ ((18884386337399671693/18890000000000000000 : ℝ)+2*(596411807699/377800000000000 : ℝ)*(14751/100000 : ℝ))^(4257/1024 : ℝ) := by
    rw [show (18884386337399671693/18890000000000000000 : ℝ)+2*(596411807699/377800000000000 : ℝ)*(14751/100000 : ℝ)=(5000842776065389/5000000000000000 : ℝ) by norm_num, show 1+2*(17521549591564351/50000000000000000000 : ℝ)=(25017521549591564351/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18884386337399671693/18890000000000000000 : ℝ)*(X 1 0+X 2 0)+(596411807699/377800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4257/1024 : ℝ)) (lo := (10973/100000 : ℝ)) (hi := (14751/100000 : ℝ)) (c := (18884386337399671693/18890000000000000000 : ℝ)) (alpha := (596411807699/377800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18884386337399671693/18890000000000000000 : ℝ)*(X 0 1+X 2 1)+(596411807699/377800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4257/1024 : ℝ)) (lo := (10973/100000 : ℝ)) (hi := (14751/100000 : ℝ)) (c := (18884386337399671693/18890000000000000000 : ℝ)) (alpha := (596411807699/377800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18884386337399671693/18890000000000000000 : ℝ)*(X 0 2+X 1 2)+(596411807699/377800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4257/1024 : ℝ)) (lo := (10973/100000 : ℝ)) (hi := (14751/100000 : ℝ)) (c := (18884386337399671693/18890000000000000000 : ℝ)) (alpha := (596411807699/377800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2082531151/10000000000 : ℝ)*X 0 0+(5415547101/10000000000 : ℝ)*X 0 1+(163832151/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674927161/5000000000 : ℝ)*X 1 0+(-2170682179/10000000000 : ℝ)*X 1 1+(5242628791/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349854141/10000000000 : ℝ)*X 2 0+(5242629001/10000000000 : ℝ)*X 2 1+(-2170682143/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((542277023/1250000000 : ℝ)*X 0 0+(208180013/500000000 : ℝ)*X 0 1+(2259901487/5000000000 : ℝ)*X 0 2+(542277023/1250000000 : ℝ)*X 1 0+(208180013/500000000 : ℝ)*X 1 1+(2259901487/5000000000 : ℝ)*X 1 2+(542277023/1250000000 : ℝ)*X 2 0+(208180013/500000000 : ℝ)*X 2 1+(2259901487/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2082544267/10000000000 : ℝ)*X 0 0+(5243249717/10000000000 : ℝ)*X 0 1+(5414922849/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305549259/10000000000 : ℝ)*X 1 0+(-1998388201/10000000000 : ℝ)*X 1 1+(5414922859/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((82899207/156250000 : ℝ)*X 2 0+(270746143/500000000 : ℝ)*X 2 1+(-999194107/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((867648607/2000000000 : ℝ)*X 0 0+(4518523839/10000000000 : ℝ)*X 0 1+(832977151/2000000000 : ℝ)*X 0 2+(867648607/2000000000 : ℝ)*X 1 0+(4518523839/10000000000 : ℝ)*X 1 1+(832977151/2000000000 : ℝ)*X 1 2+(867648607/2000000000 : ℝ)*X 2 0+(4518523839/10000000000 : ℝ)*X 2 1+(832977151/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1298_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1190362867812340542135706971/118062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1653010323/100000000000000 : ℝ)*(base19) + (1241423919/100000000000000 : ℝ)*(base23) + (115517741/100000000000000 : ℝ)*(lower2) + (9431493/5000000000000 : ℝ)*(upper3) + (8972841/25000000000000 : ℝ)*(upper5) + (1073821581768949/25000000000000 : ℝ)*(major0) + (1073821581768949/25000000000000 : ℝ)*(major1) + (1073821581768949/25000000000000 : ℝ)*(major2) + (5783116552397811/100000000000000 : ℝ)*(sp0) + (5783148217874501/100000000000000 : ℝ)*(sp1) + (1156629725892181/20000000000000 : ℝ)*(sp2) + (70185126674197/2500000000000 : ℝ)*(sp3) + (33318487013/100000000000000 : ℝ)*(sp4) + (135782939/781250000000 : ℝ)*(sp7) + (350927805898009/12500000000000 : ℝ)*(f.failure) + (722893733860603/12500000000000 : ℝ)*(f.sum) + (29758516612321/4722500000000000000000000000 : ℝ)*base65 + (4828446897720789343/472250000000000000000000000000000 : ℝ)*base68 + (3391860390186039343/472250000000000000000000000000000 : ℝ)*base70 + (1915545069355289343/472250000000000000000000000000000 : ℝ)*base72 + (45819788537303/9445000000000000000000000000 : ℝ)*base74 + (6358351422005539343/472250000000000000000000000000000 : ℝ)*base76 + (2625887535497960657/472250000000000000000000000000000 : ℝ)*base77 + (10405003784545039343/472250000000000000000000000000000 : ℝ)*base80 + (1818069104223/9445000000000000000000000000 : ℝ)*base82 + (8682777/625000000000000000000 : ℝ)*base89 + (8682777/625000000000000000000 : ℝ)*base91 + (8682777/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (828145195135219965383632317/118062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (62954143/5000000000000 : ℝ)*(base19) + (1346592273/100000000000000 : ℝ)*(base23) + (73234319/50000000000000 : ℝ)*(upper3) + (5904669/12500000000000 : ℝ)*(lower4) + (74343171/50000000000000 : ℝ)*(upper5) + (1081596492187977/25000000000000 : ℝ)*(major0) + (1081596492187977/25000000000000 : ℝ)*(major1) + (1081596492187977/25000000000000 : ℝ)*(major2) + (25343622923/100000000000000 : ℝ)*(sp1) + (26607400199/100000000000000 : ℝ)*(sp2) + (2912511180987793/50000000000000 : ℝ)*(sp4) + (1456248939817451/25000000000000 : ℝ)*(sp5) + (2912497203991557/50000000000000 : ℝ)*(sp6) + (1413874670856369/50000000000000 : ℝ)*(sp7) + (1413874670856369/50000000000000 : ℝ)*(f.failure) + (2912511180987793/50000000000000 : ℝ)*(f.sum) + (923056517957/4722500000000000000000000000 : ℝ)*base66 + (7866571725833985061/472250000000000000000000000000000 : ℝ)*base67 + (6076441343573985061/472250000000000000000000000000000 : ℝ)*base69 + (2833578068164014939/472250000000000000000000000000000 : ℝ)*base72 + (39515667155201/9445000000000000000000000000 : ℝ)*base73 + (7123012884790235061/472250000000000000000000000000000 : ℝ)*base75 + (1510803687755735061/472250000000000000000000000000000 : ℝ)*base77 + (6861742696470735061/472250000000000000000000000000000 : ℝ)*base79 + (12655097996881/9445000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (29392143/2500000000000000000000 : ℝ)*base90 + (29392143/2500000000000000000000 : ℝ)*base92 + (29392143/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1298_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76498753/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14751/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10973/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1103/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1469/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1298_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1298_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76498753/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1629/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2387/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1103/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1469/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1298_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1298_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1298_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4257/1024 : ℝ) ≤ p) (hpb : p ≤ (2129/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76498753/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1629/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2387/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1103/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1469/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1298_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
