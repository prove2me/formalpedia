-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1630_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:59:56.019327+00:00
-- url     : https://prove2.me/submissions/489a7242-fc61-4ed1-aa43-d6746f7bcae0

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
theorem support_rectangle_w1630_s3_0 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1655142623/10000000000 : ℝ)*x 0 + (1090737619/2000000000 : ℝ)*x 1 + (2591149117/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1655142623/10000000000 : ℝ)^4839 ≤ (2553287985851/25000000000000 : ℝ)^3815 := by
    have hnat : (1655142623 : ℕ)^4839*25000000000000^3815 ≤ 2553287985851^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1655142623 10000000000 2553287985851 25000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1090737619/2000000000 : ℝ)^4839 ≤ (46346212099149/100000000000000 : ℝ)^3815 := by
    have hnat : (1090737619 : ℕ)^4839*100000000000000^3815 ≤ 46346212099149^3815*2000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090737619 2000000000 46346212099149 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2591149117/5000000000 : ℝ)^4839 ≤ (2172031796941/5000000000000 : ℝ)^3815 := by
    have hnat : (2591149117 : ℕ)^4839*5000000000000^3815 ≤ 2172031796941^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591149117 5000000000 2172031796941 5000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1655142623/10000000000 : ℝ), (1090737619/2000000000 : ℝ), (2591149117/5000000000 : ℝ)] ![(2553287985851/25000000000000 : ℝ), (46346212099149/100000000000000 : ℝ), (2172031796941/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1655142623/10000000000 : ℝ)|^4839 ≤ (2553287985851/25000000000000 : ℝ)^3815
        have hw : |(-1655142623/10000000000 : ℝ)|=(1655142623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1090737619/2000000000 : ℝ)|^4839 ≤ (46346212099149/100000000000000 : ℝ)^3815
        have hw : |(1090737619/2000000000 : ℝ)|=(1090737619/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2591149117/5000000000 : ℝ)|^4839 ≤ (2172031796941/5000000000000 : ℝ)^3815
        have hw : |(2591149117/5000000000 : ℝ)|=(2591149117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_s3_1 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675383141/5000000000 : ℝ)*x 0 + (-1794971827/10000000000 : ℝ)*x 1 + (5182298981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675383141/5000000000 : ℝ)^4839 ≤ (11309906007219/25000000000000 : ℝ)^3815 := by
    have hnat : (2675383141 : ℕ)^4839*25000000000000^3815 ≤ 11309906007219^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675383141 5000000000 11309906007219 25000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1794971827/10000000000 : ℝ)^4839 ≤ (2829933017769/25000000000000 : ℝ)^3815 := by
    have hnat : (1794971827 : ℕ)^4839*25000000000000^3815 ≤ 2829933017769^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1794971827 10000000000 2829933017769 25000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5182298981/10000000000 : ℝ)^4839 ≤ (5430080485161/12500000000000 : ℝ)^3815 := by
    have hnat : (5182298981 : ℕ)^4839*12500000000000^3815 ≤ 5430080485161^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182298981 10000000000 5430080485161 12500000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675383141/5000000000 : ℝ), (-1794971827/10000000000 : ℝ), (5182298981/10000000000 : ℝ)] ![(11309906007219/25000000000000 : ℝ), (2829933017769/25000000000000 : ℝ), (5430080485161/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675383141/5000000000 : ℝ)|^4839 ≤ (11309906007219/25000000000000 : ℝ)^3815
        have hw : |(2675383141/5000000000 : ℝ)|=(2675383141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1794971827/10000000000 : ℝ)|^4839 ≤ (2829933017769/25000000000000 : ℝ)^3815
        have hw : |(-1794971827/10000000000 : ℝ)|=(1794971827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5182298981/10000000000 : ℝ)|^4839 ≤ (5430080485161/12500000000000 : ℝ)^3815
        have hw : |(5182298981/10000000000 : ℝ)|=(5182298981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_s3_2 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350766929/10000000000 : ℝ)*x 0 + (1036459679/2000000000 : ℝ)*x 1 + (-89748587/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350766929/10000000000 : ℝ)^4839 ≤ (2261981548371/5000000000000 : ℝ)^3815 := by
    have hnat : (5350766929 : ℕ)^4839*5000000000000^3815 ≤ 2261981548371^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350766929 10000000000 2261981548371 5000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036459679/2000000000 : ℝ)^4839 ≤ (868812753013/2000000000000 : ℝ)^3815 := by
    have hnat : (1036459679 : ℕ)^4839*2000000000000^3815 ≤ 868812753013^3815*2000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036459679 2000000000 868812753013 2000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (89748587/500000000 : ℝ)^4839 ≤ (11319731375157/100000000000000 : ℝ)^3815 := by
    have hnat : (89748587 : ℕ)^4839*100000000000000^3815 ≤ 11319731375157^3815*500000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89748587 500000000 11319731375157 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350766929/10000000000 : ℝ), (1036459679/2000000000 : ℝ), (-89748587/500000000 : ℝ)] ![(2261981548371/5000000000000 : ℝ), (868812753013/2000000000000 : ℝ), (11319731375157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350766929/10000000000 : ℝ)|^4839 ≤ (2261981548371/5000000000000 : ℝ)^3815
        have hw : |(5350766929/10000000000 : ℝ)|=(5350766929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036459679/2000000000 : ℝ)|^4839 ≤ (868812753013/2000000000000 : ℝ)^3815
        have hw : |(1036459679/2000000000 : ℝ)|=(1036459679/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-89748587/500000000 : ℝ)|^4839 ≤ (11319731375157/100000000000000 : ℝ)^3815
        have hw : |(-89748587/500000000 : ℝ)|=(89748587/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_s3_3 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (83926247/200000000 : ℝ)*x 0 + (3864494281/10000000000 : ℝ)*x 1 + (142155773/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83926247/200000000 : ℝ)^4839 ≤ (33238406008279/100000000000000 : ℝ)^3815 := by
    have hnat : (83926247 : ℕ)^4839*100000000000000^3815 ≤ 33238406008279^3815*200000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83926247 200000000 33238406008279 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3864494281/10000000000 : ℝ)^4839 ≤ (29940737709111/100000000000000 : ℝ)^3815 := by
    have hnat : (3864494281 : ℕ)^4839*100000000000000^3815 ≤ 29940737709111^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3864494281 10000000000 29940737709111 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (142155773/312500000 : ℝ)^4839 ≤ (9205214066817/25000000000000 : ℝ)^3815 := by
    have hnat : (142155773 : ℕ)^4839*25000000000000^3815 ≤ 9205214066817^3815*312500000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142155773 312500000 9205214066817 25000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83926247/200000000 : ℝ), (3864494281/10000000000 : ℝ), (142155773/312500000 : ℝ)] ![(33238406008279/100000000000000 : ℝ), (29940737709111/100000000000000 : ℝ), (9205214066817/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83926247/200000000 : ℝ)|^4839 ≤ (33238406008279/100000000000000 : ℝ)^3815
        have hw : |(83926247/200000000 : ℝ)|=(83926247/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3864494281/10000000000 : ℝ)|^4839 ≤ (29940737709111/100000000000000 : ℝ)^3815
        have hw : |(3864494281/10000000000 : ℝ)|=(3864494281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(142155773/312500000 : ℝ)|^4839 ≤ (9205214066817/25000000000000 : ℝ)^3815
        have hw : |(142155773/312500000 : ℝ)|=(142155773/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_s3_4 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-827605333/5000000000 : ℝ)*x 0 + (5184337489/10000000000 : ℝ)*x 1 + (1362906743/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (827605333/5000000000 : ℝ)^4839 ≤ (10213684506783/100000000000000 : ℝ)^3815 := by
    have hnat : (827605333 : ℕ)^4839*100000000000000^3815 ≤ 10213684506783^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      827605333 5000000000 10213684506783 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184337489/10000000000 : ℝ)^4839 ≤ (69539711097/160000000000 : ℝ)^3815 := by
    have hnat : (5184337489 : ℕ)^4839*160000000000^3815 ≤ 69539711097^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184337489 10000000000 69539711097 160000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1362906743/2500000000 : ℝ)^4839 ≤ (9264799209183/20000000000000 : ℝ)^3815 := by
    have hnat : (1362906743 : ℕ)^4839*20000000000000^3815 ≤ 9264799209183^3815*2500000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362906743 2500000000 9264799209183 20000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-827605333/5000000000 : ℝ), (5184337489/10000000000 : ℝ), (1362906743/2500000000 : ℝ)] ![(10213684506783/100000000000000 : ℝ), (69539711097/160000000000 : ℝ), (9264799209183/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-827605333/5000000000 : ℝ)|^4839 ≤ (10213684506783/100000000000000 : ℝ)^3815
        have hw : |(-827605333/5000000000 : ℝ)|=(827605333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184337489/10000000000 : ℝ)|^4839 ≤ (69539711097/160000000000 : ℝ)^3815
        have hw : |(5184337489/10000000000 : ℝ)|=(5184337489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1362906743/2500000000 : ℝ)|^4839 ≤ (9264799209183/20000000000000 : ℝ)^3815
        have hw : |(1362906743/2500000000 : ℝ)|=(1362906743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_s3_5 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319614049/2500000000 : ℝ)*x 0 + (-61025709/400000000 : ℝ)*x 1 + (1362906803/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319614049/2500000000 : ℝ)^4839 ≤ (44465568770573/100000000000000 : ℝ)^3815 := by
    have hnat : (1319614049 : ℕ)^4839*100000000000000^3815 ≤ 44465568770573^3815*2500000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319614049 2500000000 44465568770573 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (61025709/400000000 : ℝ)^4839 ≤ (1842086514029/20000000000000 : ℝ)^3815 := by
    have hnat : (61025709 : ℕ)^4839*20000000000000^3815 ≤ 1842086514029^3815*400000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61025709 400000000 1842086514029 20000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1362906803/2500000000 : ℝ)^4839 ≤ (11580999658163/25000000000000 : ℝ)^3815 := by
    have hnat : (1362906803 : ℕ)^4839*25000000000000^3815 ≤ 11580999658163^3815*2500000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362906803 2500000000 11580999658163 25000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319614049/2500000000 : ℝ), (-61025709/400000000 : ℝ), (1362906803/2500000000 : ℝ)] ![(44465568770573/100000000000000 : ℝ), (1842086514029/20000000000000 : ℝ), (11580999658163/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319614049/2500000000 : ℝ)|^4839 ≤ (44465568770573/100000000000000 : ℝ)^3815
        have hw : |(1319614049/2500000000 : ℝ)|=(1319614049/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-61025709/400000000 : ℝ)|^4839 ≤ (1842086514029/20000000000000 : ℝ)^3815
        have hw : |(-61025709/400000000 : ℝ)|=(61025709/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1362906803/2500000000 : ℝ)|^4839 ≤ (11580999658163/25000000000000 : ℝ)^3815
        have hw : |(1362906803/2500000000 : ℝ)|=(1362906803/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_s3_6 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055691251/2000000000 : ℝ)*x 0 + (2725813593/5000000000 : ℝ)*x 1 + (-38141067/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055691251/2000000000 : ℝ)^4839 ≤ (44465569400993/100000000000000 : ℝ)^3815 := by
    have hnat : (1055691251 : ℕ)^4839*100000000000000^3815 ≤ 44465569400993^3815*2000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055691251 2000000000 44465569400993 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2725813593/5000000000 : ℝ)^4839 ≤ (23161999176211/50000000000000 : ℝ)^3815 := by
    have hnat : (2725813593 : ℕ)^4839*50000000000000^3815 ≤ 23161999176211^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725813593 5000000000 23161999176211 50000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (38141067/250000000 : ℝ)^4839 ≤ (9210432225557/100000000000000 : ℝ)^3815 := by
    have hnat : (38141067 : ℕ)^4839*100000000000000^3815 ≤ 9210432225557^3815*250000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38141067 250000000 9210432225557 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055691251/2000000000 : ℝ), (2725813593/5000000000 : ℝ), (-38141067/250000000 : ℝ)] ![(44465569400993/100000000000000 : ℝ), (23161999176211/50000000000000 : ℝ), (9210432225557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055691251/2000000000 : ℝ)|^4839 ≤ (44465569400993/100000000000000 : ℝ)^3815
        have hw : |(1055691251/2000000000 : ℝ)|=(1055691251/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2725813593/5000000000 : ℝ)|^4839 ≤ (23161999176211/50000000000000 : ℝ)^3815
        have hw : |(2725813593/5000000000 : ℝ)|=(2725813593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-38141067/250000000 : ℝ)|^4839 ≤ (9210432225557/100000000000000 : ℝ)^3815
        have hw : |(-38141067/250000000 : ℝ)|=(38141067/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_s3_7 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4196483421/10000000000 : ℝ)*x 0 + (4543842401/10000000000 : ℝ)*x 1 + (967422513/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4196483421/10000000000 : ℝ)^4839 ≤ (1662006237819/5000000000000 : ℝ)^3815 := by
    have hnat : (4196483421 : ℕ)^4839*5000000000000^3815 ≤ 1662006237819^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4196483421 10000000000 1662006237819 5000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4543842401/10000000000 : ℝ)^4839 ≤ (1470722732001/4000000000000 : ℝ)^3815 := by
    have hnat : (4543842401 : ℕ)^4839*4000000000000^3815 ≤ 1470722732001^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4543842401 10000000000 1470722732001 4000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (967422513/2500000000 : ℝ)^4839 ≤ (29991806930967/100000000000000 : ℝ)^3815 := by
    have hnat : (967422513 : ℕ)^4839*100000000000000^3815 ≤ 29991806930967^3815*2500000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      967422513 2500000000 29991806930967 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4196483421/10000000000 : ℝ), (4543842401/10000000000 : ℝ), (967422513/2500000000 : ℝ)] ![(1662006237819/5000000000000 : ℝ), (1470722732001/4000000000000 : ℝ), (29991806930967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4196483421/10000000000 : ℝ)|^4839 ≤ (1662006237819/5000000000000 : ℝ)^3815
        have hw : |(4196483421/10000000000 : ℝ)|=(4196483421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4543842401/10000000000 : ℝ)|^4839 ≤ (1470722732001/4000000000000 : ℝ)^3815
        have hw : |(4543842401/10000000000 : ℝ)|=(4543842401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(967422513/2500000000 : ℝ)|^4839 ≤ (29991806930967/100000000000000 : ℝ)^3815
        have hw : |(967422513/2500000000 : ℝ)|=(967422513/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1630_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35221777/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3283/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5231/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10553/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8157/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3283/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5231/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3283/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5231/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3283/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5231/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3283/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5231/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3283/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5231/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3283/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5231/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (5231/50000 : ℝ) ^ (4835/1024 : ℝ) ≤ (1174639826112719/50000000000000000000 : ℝ) := by
    have hpowers : (5231/50000 : ℝ)^4835 ≤ (1174639826112719/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5231 : ℕ)^4835*50000000000000000000^1024 ≤ 1174639826112719^1024*50000^4835 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5231 50000 1174639826112719 50000000000000000000 4835 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5231/50000 : ℝ)) (X := (1174639826112719/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4835 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3283/20000 : ℝ) ^ (4835/1024 : ℝ) ≤ (19706923779807027/100000000000000000000 : ℝ) := by
    have hpowers : (3283/20000 : ℝ)^4835 ≤ (19706923779807027/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3283 : ℕ)^4835*100000000000000000000^1024 ≤ 19706923779807027^1024*20000^4835 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3283 20000 19706923779807027 100000000000000000000 4835 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3283/20000 : ℝ)) (X := (19706923779807027/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4835 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001174639826112719/25000000000000000000 : ℝ) ≤ (5000049754246511/5000000000000000 : ℝ) ^ (4835/1024 : ℝ) := by
    have hpowers : (25001174639826112719/25000000000000000000 : ℝ)^1024 ≤ (5000049754246511/5000000000000000 : ℝ)^4835 := by
      have hnat : (25001174639826112719 : ℕ)^1024*5000000000000000^4835 ≤ 5000049754246511^4835*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001174639826112719 25000000000000000000 5000049754246511 5000000000000000 1024 4835 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000049754246511/5000000000000000 : ℝ)) (X := (25001174639826112719/25000000000000000000 : ℝ)) (by norm_num) 4835 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20004411240686406493/20000000000000000000 : ℝ) ≤ (10000467085611789/10000000000000000 : ℝ) ^ (4835/1024 : ℝ) := by
    have hpowers : (20004411240686406493/20000000000000000000 : ℝ)^1024 ≤ (10000467085611789/10000000000000000 : ℝ)^4835 := by
      have hnat : (20004411240686406493 : ℕ)^1024*10000000000000000^4835 ≤ 10000467085611789^4835*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20004411240686406493 20000000000000000000 10000467085611789 10000000000000000 1024 4835 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000467085611789/10000000000000000 : ℝ)) (X := (20004411240686406493/20000000000000000000 : ℝ)) (by norm_num) 4835 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50019706923779807027/50000000000000000000 : ℝ) ≤ (2500208665682639/2500000000000000 : ℝ) ^ (4835/1024 : ℝ) := by
    have hpowers : (50019706923779807027/50000000000000000000 : ℝ)^1024 ≤ (2500208665682639/2500000000000000 : ℝ)^4835 := by
      have hnat : (50019706923779807027 : ℕ)^1024*2500000000000000^4835 ≤ 2500208665682639^4835*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019706923779807027 50000000000000000000 2500208665682639 2500000000000000 1024 4835 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500208665682639/2500000000000000 : ℝ)) (X := (50019706923779807027/50000000000000000000 : ℝ)) (by norm_num) 4835 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1174639826112719/50000000000000000000 : ℝ) ≤ ((29761450595212939629/29765000000000000000 : ℝ)+2*(367577118767/595300000000000 : ℝ)*(5231/50000 : ℝ))^(4835/1024 : ℝ) := by
    rw [show (29761450595212939629/29765000000000000000 : ℝ)+2*(367577118767/595300000000000 : ℝ)*(5231/50000 : ℝ)=(5000049754246511/5000000000000000 : ℝ) by norm_num, show 1+2*(1174639826112719/50000000000000000000 : ℝ)=(25001174639826112719/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(19706923779807027/100000000000000000000 : ℝ)+(1174639826112719/50000000000000000000 : ℝ) ≤ ((29761450595212939629/29765000000000000000 : ℝ)+(367577118767/595300000000000 : ℝ)*((3283/20000 : ℝ)+(5231/50000 : ℝ)))^(4835/1024 : ℝ) := by
    rw [show (29761450595212939629/29765000000000000000 : ℝ)+(367577118767/595300000000000 : ℝ)*((3283/20000 : ℝ)+(5231/50000 : ℝ))=(10000467085611789/10000000000000000 : ℝ) by norm_num, show 1+(19706923779807027/100000000000000000000 : ℝ)+(1174639826112719/50000000000000000000 : ℝ)=(20004411240686406493/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(19706923779807027/100000000000000000000 : ℝ) ≤ ((29761450595212939629/29765000000000000000 : ℝ)+2*(367577118767/595300000000000 : ℝ)*(3283/20000 : ℝ))^(4835/1024 : ℝ) := by
    rw [show (29761450595212939629/29765000000000000000 : ℝ)+2*(367577118767/595300000000000 : ℝ)*(3283/20000 : ℝ)=(2500208665682639/2500000000000000 : ℝ) by norm_num, show 1+2*(19706923779807027/100000000000000000000 : ℝ)=(50019706923779807027/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (29761450595212939629/29765000000000000000 : ℝ)*(X 1 0+X 2 0)+(367577118767/595300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4835/1024 : ℝ)) (lo := (5231/50000 : ℝ)) (hi := (3283/20000 : ℝ)) (c := (29761450595212939629/29765000000000000000 : ℝ)) (alpha := (367577118767/595300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (29761450595212939629/29765000000000000000 : ℝ)*(X 0 1+X 2 1)+(367577118767/595300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4835/1024 : ℝ)) (lo := (5231/50000 : ℝ)) (hi := (3283/20000 : ℝ)) (c := (29761450595212939629/29765000000000000000 : ℝ)) (alpha := (367577118767/595300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (29761450595212939629/29765000000000000000 : ℝ)*(X 0 2+X 1 2)+(367577118767/595300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4835/1024 : ℝ)) (lo := (5231/50000 : ℝ)) (hi := (3283/20000 : ℝ)) (c := (29761450595212939629/29765000000000000000 : ℝ)) (alpha := (367577118767/595300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1655142623/10000000000 : ℝ)*X 0 0+(1090737619/2000000000 : ℝ)*X 0 1+(2591149117/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675383141/5000000000 : ℝ)*X 1 0+(-1794971827/10000000000 : ℝ)*X 1 1+(5182298981/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350766929/10000000000 : ℝ)*X 2 0+(1036459679/2000000000 : ℝ)*X 2 1+(-89748587/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((83926247/200000000 : ℝ)*X 0 0+(3864494281/10000000000 : ℝ)*X 0 1+(142155773/312500000 : ℝ)*X 0 2+(83926247/200000000 : ℝ)*X 1 0+(3864494281/10000000000 : ℝ)*X 1 1+(142155773/312500000 : ℝ)*X 1 2+(83926247/200000000 : ℝ)*X 2 0+(3864494281/10000000000 : ℝ)*X 2 1+(142155773/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-827605333/5000000000 : ℝ)*X 0 0+(5184337489/10000000000 : ℝ)*X 0 1+(1362906743/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1319614049/2500000000 : ℝ)*X 1 0+(-61025709/400000000 : ℝ)*X 1 1+(1362906803/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1055691251/2000000000 : ℝ)*X 2 0+(2725813593/5000000000 : ℝ)*X 2 1+(-38141067/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4196483421/10000000000 : ℝ)*X 0 0+(4543842401/10000000000 : ℝ)*X 0 1+(967422513/2500000000 : ℝ)*X 0 2+(4196483421/10000000000 : ℝ)*X 1 0+(4543842401/10000000000 : ℝ)*X 1 1+(967422513/2500000000 : ℝ)*X 1 2+(4196483421/10000000000 : ℝ)*X 2 0+(4543842401/10000000000 : ℝ)*X 2 1+(967422513/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2140814153200276850286481569/744125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (91885689/100000000000000 : ℝ)*(base8) + (151812053/100000000000000 : ℝ)*(base21) + (168148333/100000000000000 : ℝ)*(base29) + (33360571/25000000000000 : ℝ)*(lower2) + (149115551/100000000000000 : ℝ)*(upper4) + (32160528028489/1250000000000 : ℝ)*(major0) + (1286421205213727/50000000000000 : ℝ)*(major1) + (1286421205213727/50000000000000 : ℝ)*(major2) + (921184357313561/25000000000000 : ℝ)*(sp0) + (736949221861739/20000000000000 : ℝ)*(sp1) + (73694846059201/2000000000000 : ℝ)*(sp2) + (365234611874843/25000000000000 : ℝ)*(sp3) + (1094539637/12500000000000 : ℝ)*(sp4) + (228408537/6250000000000 : ℝ)*(sp6) + (365234611874843/25000000000000 : ℝ)*(f.failure) + (3684746277457029/100000000000000 : ℝ)*(f.sum) + (76858070044219/14882500000000000000000000000 : ℝ)*base65 + (3505251022331537283/1488250000000000000000000000000000 : ℝ)*base67 + (7249253556026462717/1488250000000000000000000000000000 : ℝ)*base70 + (249595921239335669/37206250000000000000000000000000 : ℝ)*base72 + (23539346783813/14882500000000000000000000000 : ℝ)*base74 + (4040477464833662717/1488250000000000000000000000000000 : ℝ)*base76 + (100084369934710669/37206250000000000000000000000000 : ℝ)*base78 + (2648927709601412717/1488250000000000000000000000000000 : ℝ)*base80 + (54451378848351/29765000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (7056011/500000000000000000000 : ℝ)*base89 + (2056011/500000000000000000000 : ℝ)*base91 + (2056011/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16686228752258029072383897279/1488250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (842705567/50000000000000 : ℝ)*(base19) + (227832501/12500000000000 : ℝ)*(base23) + (156710343/50000000000000 : ℝ)*(upper3) + (6705693/25000000000000 : ℝ)*(lower4) + (52108217/25000000000000 : ℝ)*(upper5) + (2612302430062617/100000000000000 : ℝ)*(major0) + (2612302430062617/100000000000000 : ℝ)*(major1) + (2612302430062617/100000000000000 : ℝ)*(major2) + (20159689621/100000000000000 : ℝ)*(sp1) + (11708154821/50000000000000 : ℝ)*(sp2) + (3741259435367681/100000000000000 : ℝ)*(sp4) + (1870618795133463/50000000000000 : ℝ)*(sp5) + (233827137274877/6250000000000 : ℝ)*(sp6) + (1483345051024891/100000000000000 : ℝ)*(sp7) + (1483345051024891/100000000000000 : ℝ)*(f.failure) + (3741259435367681/100000000000000 : ℝ)*(f.sum) + (27081329336993/14882500000000000000000000000 : ℝ)*base66 + (9786581001822699093/2976500000000000000000000000000000 : ℝ)*base67 + (24614853411023300907/2976500000000000000000000000000000 : ℝ)*base70 + (6108132677095800907/2976500000000000000000000000000000 : ℝ)*base72 + (57018188028871/29765000000000000000000000000 : ℝ)*base74 + (24117999901369800907/2976500000000000000000000000000000 : ℝ)*base76 + (896205936464199093/2976500000000000000000000000000000 : ℝ)*base77 + (13967167503151800907/2976500000000000000000000000000000 : ℝ)*base80 + (48906603976141/29765000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (7748693/2000000000000000000000 : ℝ)*base90 + (7748693/2000000000000000000000 : ℝ)*base92 + (7748693/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1630_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35221777/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3283/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5231/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10553/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8157/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1630_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1630_s4_0 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1655215329/10000000000 : ℝ)*x 0 + (340832603/625000000 : ℝ)*x 1 + (518261621/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1655215329/10000000000 : ℝ)^4839 ≤ (1021372100367/10000000000000 : ℝ)^3815 := by
    have hnat : (1655215329 : ℕ)^4839*10000000000000^3815 ≤ 1021372100367^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1655215329 10000000000 1021372100367 10000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (340832603/625000000 : ℝ)^4839 ≤ (1853690485717/4000000000000 : ℝ)^3815 := by
    have hnat : (340832603 : ℕ)^4839*4000000000000^3815 ≤ 1853690485717^3815*625000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340832603 625000000 1853690485717 4000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (518261621/1000000000 : ℝ)^4839 ≤ (1086100421057/2500000000000 : ℝ)^3815 := by
    have hnat : (518261621 : ℕ)^4839*2500000000000^3815 ≤ 1086100421057^3815*1000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518261621 1000000000 1086100421057 2500000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1655215329/10000000000 : ℝ), (340832603/625000000 : ℝ), (518261621/1000000000 : ℝ)] ![(1021372100367/10000000000000 : ℝ), (1853690485717/4000000000000 : ℝ), (1086100421057/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1655215329/10000000000 : ℝ)|^4839 ≤ (1021372100367/10000000000000 : ℝ)^3815
        have hw : |(-1655215329/10000000000 : ℝ)|=(1655215329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(340832603/625000000 : ℝ)|^4839 ≤ (1853690485717/4000000000000 : ℝ)^3815
        have hw : |(340832603/625000000 : ℝ)|=(340832603/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(518261621/1000000000 : ℝ)|^4839 ≤ (1086100421057/2500000000000 : ℝ)^3815
        have hw : |(518261621/1000000000 : ℝ)|=(518261621/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_s4_1 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675334363/5000000000 : ℝ)*x 0 + (-1794681121/10000000000 : ℝ)*x 1 + (1295654019/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675334363/5000000000 : ℝ)^4839 ≤ (9047715564671/20000000000000 : ℝ)^3815 := by
    have hnat : (2675334363 : ℕ)^4839*20000000000000^3815 ≤ 9047715564671^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675334363 5000000000 9047715564671 20000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1794681121/10000000000 : ℝ)^4839 ≤ (11317406743477/100000000000000 : ℝ)^3815 := by
    have hnat : (1794681121 : ℕ)^4839*100000000000000^3815 ≤ 11317406743477^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1794681121 10000000000 11317406743477 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1295654019/2500000000 : ℝ)^4839 ≤ (43444015417503/100000000000000 : ℝ)^3815 := by
    have hnat : (1295654019 : ℕ)^4839*100000000000000^3815 ≤ 43444015417503^3815*2500000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295654019 2500000000 43444015417503 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675334363/5000000000 : ℝ), (-1794681121/10000000000 : ℝ), (1295654019/2500000000 : ℝ)] ![(9047715564671/20000000000000 : ℝ), (11317406743477/100000000000000 : ℝ), (43444015417503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675334363/5000000000 : ℝ)|^4839 ≤ (9047715564671/20000000000000 : ℝ)^3815
        have hw : |(2675334363/5000000000 : ℝ)|=(2675334363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1794681121/10000000000 : ℝ)|^4839 ≤ (11317406743477/100000000000000 : ℝ)^3815
        have hw : |(-1794681121/10000000000 : ℝ)|=(1794681121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1295654019/2500000000 : ℝ)|^4839 ≤ (43444015417503/100000000000000 : ℝ)^3815
        have hw : |(1295654019/2500000000 : ℝ)|=(1295654019/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_s4_2 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334416787/625000000 : ℝ)*x 0 + (5182616219/10000000000 : ℝ)*x 1 + (-1794681111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334416787/625000000 : ℝ)^4839 ≤ (22619288193161/50000000000000 : ℝ)^3815 := by
    have hnat : (334416787 : ℕ)^4839*50000000000000^3815 ≤ 22619288193161^3815*625000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334416787 625000000 22619288193161 50000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5182616219/10000000000 : ℝ)^4839 ≤ (43444016937973/100000000000000 : ℝ)^3815 := by
    have hnat : (5182616219 : ℕ)^4839*100000000000000^3815 ≤ 43444016937973^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182616219 10000000000 43444016937973 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1794681111/10000000000 : ℝ)^4839 ≤ (1131740666349/10000000000000 : ℝ)^3815 := by
    have hnat : (1794681111 : ℕ)^4839*10000000000000^3815 ≤ 1131740666349^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1794681111 10000000000 1131740666349 10000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334416787/625000000 : ℝ), (5182616219/10000000000 : ℝ), (-1794681111/10000000000 : ℝ)] ![(22619288193161/50000000000000 : ℝ), (43444016937973/100000000000000 : ℝ), (1131740666349/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334416787/625000000 : ℝ)|^4839 ≤ (22619288193161/50000000000000 : ℝ)^3815
        have hw : |(334416787/625000000 : ℝ)|=(334416787/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5182616219/10000000000 : ℝ)|^4839 ≤ (43444016937973/100000000000000 : ℝ)^3815
        have hw : |(5182616219/10000000000 : ℝ)|=(5182616219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1794681111/10000000000 : ℝ)|^4839 ≤ (1131740666349/10000000000000 : ℝ)^3815
        have hw : |(-1794681111/10000000000 : ℝ)|=(1794681111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_s4_3 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4196360423/10000000000 : ℝ)*x 0 + (483168843/1250000000 : ℝ)*x 1 + (568514733/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4196360423/10000000000 : ℝ)^4839 ≤ (16619444497591/50000000000000 : ℝ)^3815 := by
    have hnat : (4196360423 : ℕ)^4839*50000000000000^3815 ≤ 16619444497591^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4196360423 10000000000 16619444497591 50000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (483168843/1250000000 : ℝ)^4839 ≤ (29949154614199/100000000000000 : ℝ)^3815 := by
    have hnat : (483168843 : ℕ)^4839*100000000000000^3815 ≤ 29949154614199^3815*1250000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      483168843 1250000000 29949154614199 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (568514733/1250000000 : ℝ)^4839 ≤ (18405978191577/50000000000000 : ℝ)^3815 := by
    have hnat : (568514733 : ℕ)^4839*50000000000000^3815 ≤ 18405978191577^3815*1250000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      568514733 1250000000 18405978191577 50000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4196360423/10000000000 : ℝ), (483168843/1250000000 : ℝ), (568514733/1250000000 : ℝ)] ![(16619444497591/50000000000000 : ℝ), (29949154614199/100000000000000 : ℝ), (18405978191577/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4196360423/10000000000 : ℝ)|^4839 ≤ (16619444497591/50000000000000 : ℝ)^3815
        have hw : |(4196360423/10000000000 : ℝ)|=(4196360423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(483168843/1250000000 : ℝ)|^4839 ≤ (29949154614199/100000000000000 : ℝ)^3815
        have hw : |(483168843/1250000000 : ℝ)|=(483168843/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(568514733/1250000000 : ℝ)|^4839 ≤ (18405978191577/50000000000000 : ℝ)^3815
        have hw : |(568514733/1250000000 : ℝ)|=(568514733/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_s4_4 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1655282401/10000000000 : ℝ)*x 0 + (129616123/250000000 : ℝ)*x 1 + (2725635781/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1655282401/10000000000 : ℝ)^4839 ≤ (159597593333/1562500000000 : ℝ)^3815 := by
    have hnat : (1655282401 : ℕ)^4839*1562500000000^3815 ≤ 159597593333^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1655282401 10000000000 159597593333 1562500000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129616123/250000000 : ℝ)^4839 ≤ (43465588562891/100000000000000 : ℝ)^3815 := by
    have hnat : (129616123 : ℕ)^4839*100000000000000^3815 ≤ 43465588562891^3815*250000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129616123 250000000 43465588562891 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2725635781/5000000000 : ℝ)^4839 ≤ (180938146273/390625000000 : ℝ)^3815 := by
    have hnat : (2725635781 : ℕ)^4839*390625000000^3815 ≤ 180938146273^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725635781 5000000000 180938146273 390625000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1655282401/10000000000 : ℝ), (129616123/250000000 : ℝ), (2725635781/5000000000 : ℝ)] ![(159597593333/1562500000000 : ℝ), (43465588562891/100000000000000 : ℝ), (180938146273/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1655282401/10000000000 : ℝ)|^4839 ≤ (159597593333/1562500000000 : ℝ)^3815
        have hw : |(-1655282401/10000000000 : ℝ)|=(1655282401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(129616123/250000000 : ℝ)|^4839 ≤ (43465588562891/100000000000000 : ℝ)^3815
        have hw : |(129616123/250000000 : ℝ)|=(129616123/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2725635781/5000000000 : ℝ)|^4839 ≤ (180938146273/390625000000 : ℝ)^3815
        have hw : |(2725635781/5000000000 : ℝ)|=(2725635781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_s4_5 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639270227/5000000000 : ℝ)*x 0 + (-1526025713/10000000000 : ℝ)*x 1 + (5451271567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639270227/5000000000 : ℝ)^4839 ≤ (44466469076453/100000000000000 : ℝ)^3815 := by
    have hnat : (2639270227 : ℕ)^4839*100000000000000^3815 ≤ 44466469076453^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639270227 5000000000 44466469076453 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1526025713/10000000000 : ℝ)^4839 ≤ (9213365408059/100000000000000 : ℝ)^3815 := by
    have hnat : (1526025713 : ℕ)^4839*100000000000000^3815 ≤ 9213365408059^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1526025713 10000000000 9213365408059 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5451271567/10000000000 : ℝ)^4839 ≤ (46320165499777/100000000000000 : ℝ)^3815 := by
    have hnat : (5451271567 : ℕ)^4839*100000000000000^3815 ≤ 46320165499777^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451271567 10000000000 46320165499777 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639270227/5000000000 : ℝ), (-1526025713/10000000000 : ℝ), (5451271567/10000000000 : ℝ)] ![(44466469076453/100000000000000 : ℝ), (9213365408059/100000000000000 : ℝ), (46320165499777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639270227/5000000000 : ℝ)|^4839 ≤ (44466469076453/100000000000000 : ℝ)^3815
        have hw : |(2639270227/5000000000 : ℝ)|=(2639270227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1526025713/10000000000 : ℝ)|^4839 ≤ (9213365408059/100000000000000 : ℝ)^3815
        have hw : |(-1526025713/10000000000 : ℝ)|=(1526025713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5451271567/10000000000 : ℝ)|^4839 ≤ (46320165499777/100000000000000 : ℝ)^3815
        have hw : |(5451271567/10000000000 : ℝ)|=(5451271567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_s4_6 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278540449/10000000000 : ℝ)*x 0 + (2725635797/5000000000 : ℝ)*x 1 + (-763012841/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278540449/10000000000 : ℝ)^4839 ≤ (44466469023027/100000000000000 : ℝ)^3815 := by
    have hnat : (5278540449 : ℕ)^4839*100000000000000^3815 ≤ 44466469023027^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278540449 10000000000 44466469023027 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2725635797/5000000000 : ℝ)^4839 ≤ (2316008289539/5000000000000 : ℝ)^3815 := by
    have hnat : (2725635797 : ℕ)^4839*5000000000000^3815 ≤ 2316008289539^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725635797 5000000000 2316008289539 5000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (763012841/5000000000 : ℝ)^4839 ≤ (9213365170659/100000000000000 : ℝ)^3815 := by
    have hnat : (763012841 : ℕ)^4839*100000000000000^3815 ≤ 9213365170659^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      763012841 5000000000 9213365170659 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278540449/10000000000 : ℝ), (2725635797/5000000000 : ℝ), (-763012841/5000000000 : ℝ)] ![(44466469023027/100000000000000 : ℝ), (2316008289539/5000000000000 : ℝ), (9213365170659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278540449/10000000000 : ℝ)|^4839 ≤ (44466469023027/100000000000000 : ℝ)^3815
        have hw : |(5278540449/10000000000 : ℝ)|=(5278540449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2725635797/5000000000 : ℝ)|^4839 ≤ (2316008289539/5000000000000 : ℝ)^3815
        have hw : |(2725635797/5000000000 : ℝ)|=(2725635797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-763012841/5000000000 : ℝ)|^4839 ≤ (9213365170659/100000000000000 : ℝ)^3815
        have hw : |(-763012841/5000000000 : ℝ)|=(763012841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_s4_7 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4196529587/10000000000 : ℝ)*x 0 + (1135750271/2500000000 : ℝ)*x 1 + (1935260601/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4196529587/10000000000 : ℝ)^4839 ≤ (33240588588801/100000000000000 : ℝ)^3815 := by
    have hnat : (4196529587 : ℕ)^4839*100000000000000^3815 ≤ 33240588588801^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4196529587 10000000000 33240588588801 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1135750271/2500000000 : ℝ)^4839 ≤ (36759433396181/100000000000000 : ℝ)^3815 := by
    have hnat : (1135750271 : ℕ)^4839*100000000000000^3815 ≤ 36759433396181^3815*2500000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135750271 2500000000 36759433396181 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1935260601/5000000000 : ℝ)^4839 ≤ (239999824087/800000000000 : ℝ)^3815 := by
    have hnat : (1935260601 : ℕ)^4839*800000000000^3815 ≤ 239999824087^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1935260601 5000000000 239999824087 800000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4196529587/10000000000 : ℝ), (1135750271/2500000000 : ℝ), (1935260601/5000000000 : ℝ)] ![(33240588588801/100000000000000 : ℝ), (36759433396181/100000000000000 : ℝ), (239999824087/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4196529587/10000000000 : ℝ)|^4839 ≤ (33240588588801/100000000000000 : ℝ)^3815
        have hw : |(4196529587/10000000000 : ℝ)|=(4196529587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1135750271/2500000000 : ℝ)|^4839 ≤ (36759433396181/100000000000000 : ℝ)^3815
        have hw : |(1135750271/2500000000 : ℝ)|=(1135750271/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1935260601/5000000000 : ℝ)|^4839 ≤ (239999824087/800000000000 : ℝ)^3815
        have hw : |(1935260601/5000000000 : ℝ)|=(1935260601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1630_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35221777/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8157/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10553/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10559/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8153/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8157/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10553/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8157/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10553/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8157/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10553/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8157/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10553/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8157/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10553/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8157/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10553/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10553/100000 : ℝ) ^ (4835/1024 : ℝ) ≤ (1223669144298883/50000000000000000000 : ℝ) := by
    have hpowers : (10553/100000 : ℝ)^4835 ≤ (1223669144298883/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10553 : ℕ)^4835*50000000000000000000^1024 ≤ 1223669144298883^1024*100000^4835 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10553 100000 1223669144298883 50000000000000000000 4835 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10553/100000 : ℝ)) (X := (1223669144298883/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4835 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8157/50000 : ℝ) ^ (4835/1024 : ℝ) ≤ (4785228910831907/25000000000000000000 : ℝ) := by
    have hpowers : (8157/50000 : ℝ)^4835 ≤ (4785228910831907/25000000000000000000 : ℝ)^1024 := by
      have hnat : (8157 : ℕ)^4835*25000000000000000000^1024 ≤ 4785228910831907^1024*50000^4835 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8157 50000 4785228910831907 25000000000000000000 4835 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8157/50000 : ℝ)) (X := (4785228910831907/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4835 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001223669144298883/25000000000000000000 : ℝ) ≤ (2500025915471213/2500000000000000 : ℝ) ^ (4835/1024 : ℝ) := by
    have hpowers : (25001223669144298883/25000000000000000000 : ℝ)^1024 ≤ (2500025915471213/2500000000000000 : ℝ)^4835 := by
      have hnat : (25001223669144298883 : ℕ)^1024*2500000000000000^4835 ≤ 2500025915471213^4835*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001223669144298883 25000000000000000000 2500025915471213 2500000000000000 1024 4835 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500025915471213/2500000000000000 : ℝ)) (X := (25001223669144298883/25000000000000000000 : ℝ)) (by norm_num) 4835 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50010794126965962697/50000000000000000000 : ℝ) ≤ (5000228588329341/5000000000000000 : ℝ) ^ (4835/1024 : ℝ) := by
    have hpowers : (50010794126965962697/50000000000000000000 : ℝ)^1024 ≤ (5000228588329341/5000000000000000 : ℝ)^4835 := by
      have hnat : (50010794126965962697 : ℕ)^1024*5000000000000000^4835 ≤ 5000228588329341^4835*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010794126965962697 50000000000000000000 5000228588329341 5000000000000000 1024 4835 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000228588329341/5000000000000000 : ℝ)) (X := (50010794126965962697/50000000000000000000 : ℝ)) (by norm_num) 4835 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12504785228910831907/12500000000000000000 : ℝ) ≤ (156262667053633/156250000000000 : ℝ) ^ (4835/1024 : ℝ) := by
    have hpowers : (12504785228910831907/12500000000000000000 : ℝ)^1024 ≤ (156262667053633/156250000000000 : ℝ)^4835 := by
      have hnat : (12504785228910831907 : ℕ)^1024*156250000000000^4835 ≤ 156262667053633^4835*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12504785228910831907 12500000000000000000 156262667053633 156250000000000 1024 4835 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156262667053633/156250000000000 : ℝ)) (X := (12504785228910831907/12500000000000000000 : ℝ)) (by norm_num) 4835 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1223669144298883/50000000000000000000 : ℝ) ≤ ((7200391989162772049/7201250000000000000 : ℝ)+2*(35351477383/57610000000000 : ℝ)*(10553/100000 : ℝ))^(4835/1024 : ℝ) := by
    rw [show (7200391989162772049/7201250000000000000 : ℝ)+2*(35351477383/57610000000000 : ℝ)*(10553/100000 : ℝ)=(2500025915471213/2500000000000000 : ℝ) by norm_num, show 1+2*(1223669144298883/50000000000000000000 : ℝ)=(25001223669144298883/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4785228910831907/25000000000000000000 : ℝ)+(1223669144298883/50000000000000000000 : ℝ) ≤ ((7200391989162772049/7201250000000000000 : ℝ)+(35351477383/57610000000000 : ℝ)*((8157/50000 : ℝ)+(10553/100000 : ℝ)))^(4835/1024 : ℝ) := by
    rw [show (7200391989162772049/7201250000000000000 : ℝ)+(35351477383/57610000000000 : ℝ)*((8157/50000 : ℝ)+(10553/100000 : ℝ))=(5000228588329341/5000000000000000 : ℝ) by norm_num, show 1+(4785228910831907/25000000000000000000 : ℝ)+(1223669144298883/50000000000000000000 : ℝ)=(50010794126965962697/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4785228910831907/25000000000000000000 : ℝ) ≤ ((7200391989162772049/7201250000000000000 : ℝ)+2*(35351477383/57610000000000 : ℝ)*(8157/50000 : ℝ))^(4835/1024 : ℝ) := by
    rw [show (7200391989162772049/7201250000000000000 : ℝ)+2*(35351477383/57610000000000 : ℝ)*(8157/50000 : ℝ)=(156262667053633/156250000000000 : ℝ) by norm_num, show 1+2*(4785228910831907/25000000000000000000 : ℝ)=(12504785228910831907/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7200391989162772049/7201250000000000000 : ℝ)*(X 1 0+X 2 0)+(35351477383/57610000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4835/1024 : ℝ)) (lo := (10553/100000 : ℝ)) (hi := (8157/50000 : ℝ)) (c := (7200391989162772049/7201250000000000000 : ℝ)) (alpha := (35351477383/57610000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7200391989162772049/7201250000000000000 : ℝ)*(X 0 1+X 2 1)+(35351477383/57610000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4835/1024 : ℝ)) (lo := (10553/100000 : ℝ)) (hi := (8157/50000 : ℝ)) (c := (7200391989162772049/7201250000000000000 : ℝ)) (alpha := (35351477383/57610000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7200391989162772049/7201250000000000000 : ℝ)*(X 0 2+X 1 2)+(35351477383/57610000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4835/1024 : ℝ)) (lo := (10553/100000 : ℝ)) (hi := (8157/50000 : ℝ)) (c := (7200391989162772049/7201250000000000000 : ℝ)) (alpha := (35351477383/57610000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1655215329/10000000000 : ℝ)*X 0 0+(340832603/625000000 : ℝ)*X 0 1+(518261621/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675334363/5000000000 : ℝ)*X 1 0+(-1794681121/10000000000 : ℝ)*X 1 1+(1295654019/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334416787/625000000 : ℝ)*X 2 0+(5182616219/10000000000 : ℝ)*X 2 1+(-1794681111/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4196360423/10000000000 : ℝ)*X 0 0+(483168843/1250000000 : ℝ)*X 0 1+(568514733/1250000000 : ℝ)*X 0 2+(4196360423/10000000000 : ℝ)*X 1 0+(483168843/1250000000 : ℝ)*X 1 1+(568514733/1250000000 : ℝ)*X 1 2+(4196360423/10000000000 : ℝ)*X 2 0+(483168843/1250000000 : ℝ)*X 2 1+(568514733/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1655282401/10000000000 : ℝ)*X 0 0+(129616123/250000000 : ℝ)*X 0 1+(2725635781/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2639270227/5000000000 : ℝ)*X 1 0+(-1526025713/10000000000 : ℝ)*X 1 1+(5451271567/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5278540449/10000000000 : ℝ)*X 2 0+(2725635797/5000000000 : ℝ)*X 2 1+(-763012841/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4196529587/10000000000 : ℝ)*X 0 0+(1135750271/2500000000 : ℝ)*X 0 1+(1935260601/5000000000 : ℝ)*X 0 2+(4196529587/10000000000 : ℝ)*X 1 0+(1135750271/2500000000 : ℝ)*X 1 1+(1935260601/5000000000 : ℝ)*X 1 2+(4196529587/10000000000 : ℝ)*X 2 0+(1135750271/2500000000 : ℝ)*X 2 1+(1935260601/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (268855408651770717015093723/22503906250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1904500657/100000000000000 : ℝ)*(base19) + (852907391/50000000000000 : ℝ)*(base23) + (56809347/100000000000000 : ℝ)*(lower2) + (68619557/25000000000000 : ℝ)*(upper3) + (48049319/25000000000000 : ℝ)*(upper5) + (80605374591083/3125000000000 : ℝ)*(major0) + (80605374591083/3125000000000 : ℝ)*(major1) + (80605374591083/3125000000000 : ℝ)*(major2) + (184703767203587/5000000000000 : ℝ)*(sp0) + (1847047765386293/50000000000000 : ℝ)*(sp1) + (1847047864729231/50000000000000 : ℝ)*(sp2) + (1464636747037841/100000000000000 : ℝ)*(sp3) + (4418240301/20000000000000 : ℝ)*(sp4) + (187865661/2000000000000 : ℝ)*(sp7) + (1464646140320891/100000000000000 : ℝ)*(f.failure) + (923524358818311/25000000000000 : ℝ)*(f.sum) + (777829937239/720125000000000000000000000 : ℝ)*base66 + (13564596777132817/22503906250000000000000000000000 : ℝ)*base67 + (572422663191906241/45007812500000000000000000000000 : ℝ)*base70 + (426126390869390643/90015625000000000000000000000000 : ℝ)*base71 + (5575318060509/2880500000000000000000000000 : ℝ)*base73 + (23888099975292971/11251953125000000000000000000000 : ℝ)*base75 + (47687060251671857/90015625000000000000000000000000 : ℝ)*base78 + (322094056232875009/45007812500000000000000000000000 : ℝ)*base79 + (8256916230933/2880500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base86 + (11243307/2000000000000000000000 : ℝ)*base89 + (11243307/2000000000000000000000 : ℝ)*base91 + (11243307/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (64886620035185689817861949/9001562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (218157757/20000000000000 : ℝ)*(base19) + (581834211/50000000000000 : ℝ)*(base23) + (334154867/100000000000000 : ℝ)*(lower1) + (10243163/6250000000000 : ℝ)*(upper3) + (14997451/50000000000000 : ℝ)*(lower4) + (73436021/50000000000000 : ℝ)*(upper5) + (130939455125867/5000000000000 : ℝ)*(major0) + (130939455125867/5000000000000 : ℝ)*(major1) + (130939455125867/5000000000000 : ℝ)*(major2) + (717485663/50000000000000 : ℝ)*(sp2) + (937637395782073/25000000000000 : ℝ)*(sp4) + (1875274246169753/50000000000000 : ℝ)*(sp5) + (117204593265267/3125000000000 : ℝ)*(sp6) + (371757095406819/25000000000000 : ℝ)*(sp7) + (371757095406819/25000000000000 : ℝ)*(f.failure) + (937637395782073/25000000000000 : ℝ)*(f.sum) + (855992747933/144025000000000000000000000 : ℝ)*base65 + (159429330755783517/36006250000000000000000000000000 : ℝ)*base68 + (284432013995483517/36006250000000000000000000000000 : ℝ)*base70 + (667904081130983517/36006250000000000000000000000000 : ℝ)*base72 + (6508378092763/2880500000000000000000000000 : ℝ)*base74 + (1400970363065278983/36006250000000000000000000000000 : ℝ)*base75 + (236064328829508517/36006250000000000000000000000000 : ℝ)*base78 + (506064340038846017/36006250000000000000000000000000 : ℝ)*base80 + (20073895166401/2880500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (3097363/500000000000000000000 : ℝ)*base89 + (3097363/500000000000000000000 : ℝ)*base91 + (3097363/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1630_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35221777/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8157/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10553/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10559/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8153/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1630_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1630_s5_0 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1655222017/10000000000 : ℝ)*x 0 + (5453294549/10000000000 : ℝ)*x 1 + (2591319379/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1655222017/10000000000 : ℝ)^4839 ≤ (10213773350101/100000000000000 : ℝ)^3815 := by
    have hnat : (1655222017 : ℕ)^4839*100000000000000^3815 ≤ 10213773350101^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1655222017 10000000000 10213773350101 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5453294549/10000000000 : ℝ)^4839 ≤ (23170985021929/50000000000000 : ℝ)^3815 := by
    have hnat : (5453294549 : ℕ)^4839*50000000000000^3815 ≤ 23170985021929^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453294549 10000000000 23170985021929 50000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2591319379/5000000000 : ℝ)^4839 ≤ (271526603673/625000000000 : ℝ)^3815 := by
    have hnat : (2591319379 : ℕ)^4839*625000000000^3815 ≤ 271526603673^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591319379 5000000000 271526603673 625000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1655222017/10000000000 : ℝ), (5453294549/10000000000 : ℝ), (2591319379/5000000000 : ℝ)] ![(10213773350101/100000000000000 : ℝ), (23170985021929/50000000000000 : ℝ), (271526603673/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1655222017/10000000000 : ℝ)|^4839 ≤ (10213773350101/100000000000000 : ℝ)^3815
        have hw : |(-1655222017/10000000000 : ℝ)|=(1655222017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5453294549/10000000000 : ℝ)|^4839 ≤ (23170985021929/50000000000000 : ℝ)^3815
        have hw : |(5453294549/10000000000 : ℝ)|=(5453294549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2591319379/5000000000 : ℝ)|^4839 ≤ (271526603673/625000000000 : ℝ)^3815
        have hw : |(2591319379/5000000000 : ℝ)|=(2591319379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_s5_1 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267533051/500000000 : ℝ)*x 0 + (-897330627/5000000000 : ℝ)*x 1 + (2591319397/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267533051/500000000 : ℝ)^4839 ≤ (22619247591623/50000000000000 : ℝ)^3815 := by
    have hnat : (267533051 : ℕ)^4839*50000000000000^3815 ≤ 22619247591623^3815*500000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267533051 500000000 22619247591623 50000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (897330627/5000000000 : ℝ)^4839 ≤ (1414655979133/12500000000000 : ℝ)^3815 := by
    have hnat : (897330627 : ℕ)^4839*12500000000000^3815 ≤ 1414655979133^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897330627 5000000000 1414655979133 12500000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2591319397/5000000000 : ℝ)^4839 ≤ (5430532121307/12500000000000 : ℝ)^3815 := by
    have hnat : (2591319397 : ℕ)^4839*12500000000000^3815 ≤ 5430532121307^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591319397 5000000000 5430532121307 12500000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267533051/500000000 : ℝ), (-897330627/5000000000 : ℝ), (2591319397/5000000000 : ℝ)] ![(22619247591623/50000000000000 : ℝ), (1414655979133/12500000000000 : ℝ), (5430532121307/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267533051/500000000 : ℝ)|^4839 ≤ (22619247591623/50000000000000 : ℝ)^3815
        have hw : |(267533051/500000000 : ℝ)|=(267533051/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-897330627/5000000000 : ℝ)|^4839 ≤ (1414655979133/12500000000000 : ℝ)^3815
        have hw : |(-897330627/5000000000 : ℝ)|=(897330627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2591319397/5000000000 : ℝ)|^4839 ≤ (5430532121307/12500000000000 : ℝ)^3815
        have hw : |(2591319397/5000000000 : ℝ)|=(2591319397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_s5_2 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (83604077/156250000 : ℝ)*x 0 + (1295659723/2500000000 : ℝ)*x 1 + (-14020791/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83604077/156250000 : ℝ)^4839 ≤ (45238494196627/100000000000000 : ℝ)^3815 := by
    have hnat : (83604077 : ℕ)^4839*100000000000000^3815 ≤ 45238494196627^3815*156250000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83604077 156250000 45238494196627 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1295659723/2500000000 : ℝ)^4839 ≤ (21722129006229/50000000000000 : ℝ)^3815 := by
    have hnat : (1295659723 : ℕ)^4839*50000000000000^3815 ≤ 21722129006229^3815*2500000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295659723 2500000000 21722129006229 50000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (14020791/78125000 : ℝ)^4839 ≤ (707327986567/6250000000000 : ℝ)^3815 := by
    have hnat : (14020791 : ℕ)^4839*6250000000000^3815 ≤ 707327986567^3815*78125000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14020791 78125000 707327986567 6250000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83604077/156250000 : ℝ), (1295659723/2500000000 : ℝ), (-14020791/78125000 : ℝ)] ![(45238494196627/100000000000000 : ℝ), (21722129006229/50000000000000 : ℝ), (707327986567/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83604077/156250000 : ℝ)|^4839 ≤ (45238494196627/100000000000000 : ℝ)^3815
        have hw : |(83604077/156250000 : ℝ)|=(83604077/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1295659723/2500000000 : ℝ)|^4839 ≤ (21722129006229/50000000000000 : ℝ)^3815
        have hw : |(1295659723/2500000000 : ℝ)|=(1295659723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-14020791/78125000 : ℝ)|^4839 ≤ (707327986567/6250000000000 : ℝ)^3815
        have hw : |(-14020791/78125000 : ℝ)|=(14020791/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_s5_3 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2098181977/5000000000 : ℝ)*x 0 + (386541283/1000000000 : ℝ)*x 1 + (2274027487/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2098181977/5000000000 : ℝ)^4839 ≤ (8309731117753/25000000000000 : ℝ)^3815 := by
    have hnat : (2098181977 : ℕ)^4839*25000000000000^3815 ≤ 8309731117753^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098181977 5000000000 8309731117753 25000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (386541283/1000000000 : ℝ)^4839 ≤ (29949764784909/100000000000000 : ℝ)^3815 := by
    have hnat : (386541283 : ℕ)^4839*100000000000000^3815 ≤ 29949764784909^3815*1000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      386541283 1000000000 29949764784909 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2274027487/5000000000 : ℝ)^4839 ≤ (36811310730327/100000000000000 : ℝ)^3815 := by
    have hnat : (2274027487 : ℕ)^4839*100000000000000^3815 ≤ 36811310730327^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2274027487 5000000000 36811310730327 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2098181977/5000000000 : ℝ), (386541283/1000000000 : ℝ), (2274027487/5000000000 : ℝ)] ![(8309731117753/25000000000000 : ℝ), (29949764784909/100000000000000 : ℝ), (36811310730327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2098181977/5000000000 : ℝ)|^4839 ≤ (8309731117753/25000000000000 : ℝ)^3815
        have hw : |(2098181977/5000000000 : ℝ)|=(2098181977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(386541283/1000000000 : ℝ)|^4839 ≤ (29949764784909/100000000000000 : ℝ)^3815
        have hw : |(386541283/1000000000 : ℝ)|=(386541283/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2274027487/5000000000 : ℝ)|^4839 ≤ (36811310730327/100000000000000 : ℝ)^3815
        have hw : |(2274027487/5000000000 : ℝ)|=(2274027487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_s5_4 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-41382221/250000000 : ℝ)*x 0 + (1296166823/2500000000 : ℝ)*x 1 + (2725622407/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41382221/250000000 : ℝ)^4839 ≤ (5107148185693/50000000000000 : ℝ)^3815 := by
    have hnat : (41382221 : ℕ)^4839*50000000000000^3815 ≤ 5107148185693^3815*250000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41382221 250000000 5107148185693 50000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1296166823/2500000000 : ℝ)^4839 ≤ (4346582646193/10000000000000 : ℝ)^3815 := by
    have hnat : (1296166823 : ℕ)^4839*10000000000000^3815 ≤ 4346582646193^3815*2500000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296166823 2500000000 4346582646193 10000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2725622407/5000000000 : ℝ)^4839 ≤ (4631987715933/10000000000000 : ℝ)^3815 := by
    have hnat : (2725622407 : ℕ)^4839*10000000000000^3815 ≤ 4631987715933^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725622407 5000000000 4631987715933 10000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-41382221/250000000 : ℝ), (1296166823/2500000000 : ℝ), (2725622407/5000000000 : ℝ)] ![(5107148185693/50000000000000 : ℝ), (4346582646193/10000000000000 : ℝ), (4631987715933/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-41382221/250000000 : ℝ)|^4839 ≤ (5107148185693/50000000000000 : ℝ)^3815
        have hw : |(-41382221/250000000 : ℝ)|=(41382221/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1296166823/2500000000 : ℝ)|^4839 ≤ (4346582646193/10000000000000 : ℝ)^3815
        have hw : |(1296166823/2500000000 : ℝ)|=(1296166823/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2725622407/5000000000 : ℝ)|^4839 ≤ (4631987715933/10000000000000 : ℝ)^3815
        have hw : |(2725622407/5000000000 : ℝ)|=(2725622407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_s5_5 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (659818277/1250000000 : ℝ)*x 0 + (-190756857/1250000000 : ℝ)*x 1 + (5451245147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (659818277/1250000000 : ℝ)^4839 ≤ (44466530644189/100000000000000 : ℝ)^3815 := by
    have hnat : (659818277 : ℕ)^4839*100000000000000^3815 ≤ 44466530644189^3815*1250000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659818277 1250000000 44466530644189 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (190756857/1250000000 : ℝ)^4839 ≤ (2303397146709/25000000000000 : ℝ)^3815 := by
    have hnat : (190756857 : ℕ)^4839*25000000000000^3815 ≤ 2303397146709^3815*1250000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190756857 1250000000 2303397146709 25000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5451245147/10000000000 : ℝ)^4839 ≤ (46319880748359/100000000000000 : ℝ)^3815 := by
    have hnat : (5451245147 : ℕ)^4839*100000000000000^3815 ≤ 46319880748359^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451245147 10000000000 46319880748359 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(659818277/1250000000 : ℝ), (-190756857/1250000000 : ℝ), (5451245147/10000000000 : ℝ)] ![(44466530644189/100000000000000 : ℝ), (2303397146709/25000000000000 : ℝ), (46319880748359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(659818277/1250000000 : ℝ)|^4839 ≤ (44466530644189/100000000000000 : ℝ)^3815
        have hw : |(659818277/1250000000 : ℝ)|=(659818277/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-190756857/1250000000 : ℝ)|^4839 ≤ (2303397146709/25000000000000 : ℝ)^3815
        have hw : |(-190756857/1250000000 : ℝ)|=(190756857/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5451245147/10000000000 : ℝ)|^4839 ≤ (46319880748359/100000000000000 : ℝ)^3815
        have hw : |(5451245147/10000000000 : ℝ)|=(5451245147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_s5_6 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278546493/10000000000 : ℝ)*x 0 + (5451244979/10000000000 : ℝ)*x 1 + (-763027353/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278546493/10000000000 : ℝ)^4839 ≤ (11116633400993/25000000000000 : ℝ)^3815 := by
    have hnat : (5278546493 : ℕ)^4839*25000000000000^3815 ≤ 11116633400993^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278546493 10000000000 11116633400993 25000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5451244979/10000000000 : ℝ)^4839 ≤ (23159939468839/50000000000000 : ℝ)^3815 := by
    have hnat : (5451244979 : ℕ)^4839*50000000000000^3815 ≤ 23159939468839^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451244979 10000000000 23159939468839 50000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (763027353/5000000000 : ℝ)^4839 ≤ (2303396859531/25000000000000 : ℝ)^3815 := by
    have hnat : (763027353 : ℕ)^4839*25000000000000^3815 ≤ 2303396859531^3815*5000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      763027353 5000000000 2303396859531 25000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278546493/10000000000 : ℝ), (5451244979/10000000000 : ℝ), (-763027353/5000000000 : ℝ)] ![(11116633400993/25000000000000 : ℝ), (23159939468839/50000000000000 : ℝ), (2303396859531/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278546493/10000000000 : ℝ)|^4839 ≤ (11116633400993/25000000000000 : ℝ)^3815
        have hw : |(5278546493/10000000000 : ℝ)|=(5278546493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5451244979/10000000000 : ℝ)|^4839 ≤ (23159939468839/50000000000000 : ℝ)^3815
        have hw : |(5451244979/10000000000 : ℝ)|=(5451244979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-763027353/5000000000 : ℝ)|^4839 ≤ (2303396859531/25000000000000 : ℝ)^3815
        have hw : |(-763027353/5000000000 : ℝ)|=(763027353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1630_s5_7 (p : ℝ) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (52456663/125000000 : ℝ)*x 0 + (4542939949/10000000000 : ℝ)*x 1 + (3870581493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52456663/125000000 : ℝ)^4839 ≤ (33240623281343/100000000000000 : ℝ)^3815 := by
    have hnat : (52456663 : ℕ)^4839*100000000000000^3815 ≤ 33240623281343^3815*125000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52456663 125000000 33240623281343 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4542939949/10000000000 : ℝ)^4839 ≤ (36758805950433/100000000000000 : ℝ)^3815 := by
    have hnat : (4542939949 : ℕ)^4839*100000000000000^3815 ≤ 36758805950433^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4542939949 10000000000 36758805950433 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3870581493/10000000000 : ℝ)^4839 ≤ (30000570753229/100000000000000 : ℝ)^3815 := by
    have hnat : (3870581493 : ℕ)^4839*100000000000000^3815 ≤ 30000570753229^3815*10000000000^4839 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3870581493 10000000000 30000570753229 100000000000000 4839 3815 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4839/1024 : ℝ)) 4839 3815 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(52456663/125000000 : ℝ), (4542939949/10000000000 : ℝ), (3870581493/10000000000 : ℝ)] ![(33240623281343/100000000000000 : ℝ), (36758805950433/100000000000000 : ℝ), (30000570753229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(52456663/125000000 : ℝ)|^4839 ≤ (33240623281343/100000000000000 : ℝ)^3815
        have hw : |(52456663/125000000 : ℝ)|=(52456663/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4542939949/10000000000 : ℝ)|^4839 ≤ (36758805950433/100000000000000 : ℝ)^3815
        have hw : |(4542939949/10000000000 : ℝ)|=(4542939949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3870581493/10000000000 : ℝ)|^4839 ≤ (30000570753229/100000000000000 : ℝ)^3815
        have hw : |(3870581493/10000000000 : ℝ)|=(3870581493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1630_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35221777/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8153/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10559/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (66/625 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3261/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8153/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10559/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8153/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10559/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8153/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10559/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8153/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10559/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8153/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10559/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8153/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10559/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10559/100000 : ℝ) ^ (4835/1024 : ℝ) ≤ (1226957625164347/50000000000000000000 : ℝ) := by
    have hpowers : (10559/100000 : ℝ)^4835 ≤ (1226957625164347/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10559 : ℕ)^4835*50000000000000000000^1024 ≤ 1226957625164347^1024*100000^4835 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10559 100000 1226957625164347 50000000000000000000 4835 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10559/100000 : ℝ)) (X := (1226957625164347/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4835 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8153/50000 : ℝ) ^ (4835/1024 : ℝ) ≤ (4774159297133179/25000000000000000000 : ℝ) := by
    have hpowers : (8153/50000 : ℝ)^4835 ≤ (4774159297133179/25000000000000000000 : ℝ)^1024 := by
      have hnat : (8153 : ℕ)^4835*25000000000000000000^1024 ≤ 4774159297133179^1024*50000^4835 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8153 50000 4774159297133179 25000000000000000000 4835 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8153/50000 : ℝ)) (X := (4774159297133179/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4835 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001226957625164347/25000000000000000000 : ℝ) ≤ (1000010394045977/1000000000000000 : ℝ) ^ (4835/1024 : ℝ) := by
    have hpowers : (25001226957625164347/25000000000000000000 : ℝ)^1024 ≤ (1000010394045977/1000000000000000 : ℝ)^4835 := by
      have hnat : (25001226957625164347 : ℕ)^1024*1000000000000000^4835 ≤ 1000010394045977^4835*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001226957625164347 25000000000000000000 1000010394045977 1000000000000000 1024 4835 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000010394045977/1000000000000000 : ℝ)) (X := (25001226957625164347/25000000000000000000 : ℝ)) (by norm_num) 4835 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10002155055243886141/10000000000000000000 : ℝ) ≤ (10000456378318111/10000000000000000 : ℝ) ^ (4835/1024 : ℝ) := by
    have hpowers : (10002155055243886141/10000000000000000000 : ℝ)^1024 ≤ (10000456378318111/10000000000000000 : ℝ)^4835 := by
      have hnat : (10002155055243886141 : ℕ)^1024*10000000000000000^4835 ≤ 10000456378318111^4835*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002155055243886141 10000000000000000000 10000456378318111 10000000000000000 1024 4835 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000456378318111/10000000000000000 : ℝ)) (X := (10002155055243886141/10000000000000000000 : ℝ)) (by norm_num) 4835 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12504774159297133179/12500000000000000000 : ℝ) ≤ (2500202204044113/2500000000000000 : ℝ) ^ (4835/1024 : ℝ) := by
    have hpowers : (12504774159297133179/12500000000000000000 : ℝ)^1024 ≤ (2500202204044113/2500000000000000 : ℝ)^4835 := by
      have hnat : (12504774159297133179 : ℕ)^1024*2500000000000000^4835 ≤ 2500202204044113^4835*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12504774159297133179 12500000000000000000 2500202204044113 2500000000000000 1024 4835 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500202204044113/2500000000000000 : ℝ)) (X := (12504774159297133179/12500000000000000000 : ℝ)) (by norm_num) 4835 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1226957625164347/50000000000000000000 : ℝ) ≤ ((7182894320391231619/7183750000000000000 : ℝ)+2*(352437858341/574700000000000 : ℝ)*(10559/100000 : ℝ))^(4835/1024 : ℝ) := by
    rw [show (7182894320391231619/7183750000000000000 : ℝ)+2*(352437858341/574700000000000 : ℝ)*(10559/100000 : ℝ)=(1000010394045977/1000000000000000 : ℝ) by norm_num, show 1+2*(1226957625164347/50000000000000000000 : ℝ)=(25001226957625164347/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4774159297133179/25000000000000000000 : ℝ)+(1226957625164347/50000000000000000000 : ℝ) ≤ ((7182894320391231619/7183750000000000000 : ℝ)+(352437858341/574700000000000 : ℝ)*((8153/50000 : ℝ)+(10559/100000 : ℝ)))^(4835/1024 : ℝ) := by
    rw [show (7182894320391231619/7183750000000000000 : ℝ)+(352437858341/574700000000000 : ℝ)*((8153/50000 : ℝ)+(10559/100000 : ℝ))=(10000456378318111/10000000000000000 : ℝ) by norm_num, show 1+(4774159297133179/25000000000000000000 : ℝ)+(1226957625164347/50000000000000000000 : ℝ)=(10002155055243886141/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4774159297133179/25000000000000000000 : ℝ) ≤ ((7182894320391231619/7183750000000000000 : ℝ)+2*(352437858341/574700000000000 : ℝ)*(8153/50000 : ℝ))^(4835/1024 : ℝ) := by
    rw [show (7182894320391231619/7183750000000000000 : ℝ)+2*(352437858341/574700000000000 : ℝ)*(8153/50000 : ℝ)=(2500202204044113/2500000000000000 : ℝ) by norm_num, show 1+2*(4774159297133179/25000000000000000000 : ℝ)=(12504774159297133179/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7182894320391231619/7183750000000000000 : ℝ)*(X 1 0+X 2 0)+(352437858341/574700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4835/1024 : ℝ)) (lo := (10559/100000 : ℝ)) (hi := (8153/50000 : ℝ)) (c := (7182894320391231619/7183750000000000000 : ℝ)) (alpha := (352437858341/574700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7182894320391231619/7183750000000000000 : ℝ)*(X 0 1+X 2 1)+(352437858341/574700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4835/1024 : ℝ)) (lo := (10559/100000 : ℝ)) (hi := (8153/50000 : ℝ)) (c := (7182894320391231619/7183750000000000000 : ℝ)) (alpha := (352437858341/574700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7182894320391231619/7183750000000000000 : ℝ)*(X 0 2+X 1 2)+(352437858341/574700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4835/1024 : ℝ)) (lo := (10559/100000 : ℝ)) (hi := (8153/50000 : ℝ)) (c := (7182894320391231619/7183750000000000000 : ℝ)) (alpha := (352437858341/574700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1655222017/10000000000 : ℝ)*X 0 0+(5453294549/10000000000 : ℝ)*X 0 1+(2591319379/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267533051/500000000 : ℝ)*X 1 0+(-897330627/5000000000 : ℝ)*X 1 1+(2591319397/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((83604077/156250000 : ℝ)*X 2 0+(1295659723/2500000000 : ℝ)*X 2 1+(-14020791/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2098181977/5000000000 : ℝ)*X 0 0+(386541283/1000000000 : ℝ)*X 0 1+(2274027487/5000000000 : ℝ)*X 0 2+(2098181977/5000000000 : ℝ)*X 1 0+(386541283/1000000000 : ℝ)*X 1 1+(2274027487/5000000000 : ℝ)*X 1 2+(2098181977/5000000000 : ℝ)*X 2 0+(386541283/1000000000 : ℝ)*X 2 1+(2274027487/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-41382221/250000000 : ℝ)*X 0 0+(1296166823/2500000000 : ℝ)*X 0 1+(2725622407/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((659818277/1250000000 : ℝ)*X 1 0+(-190756857/1250000000 : ℝ)*X 1 1+(5451245147/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5278546493/10000000000 : ℝ)*X 2 0+(5451244979/10000000000 : ℝ)*X 2 1+(-763027353/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((52456663/125000000 : ℝ)*X 0 0+(4542939949/10000000000 : ℝ)*X 0 1+(3870581493/10000000000 : ℝ)*X 0 2+(52456663/125000000 : ℝ)*X 1 0+(4542939949/10000000000 : ℝ)*X 1 1+(3870581493/10000000000 : ℝ)*X 1 2+(52456663/125000000 : ℝ)*X 2 0+(4542939949/10000000000 : ℝ)*X 2 1+(3870581493/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1630_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1103899559898985717250923221/179593750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (534848597/50000000000000 : ℝ)*(base19) + (956333387/100000000000000 : ℝ)*(base23) + (26665357/100000000000000 : ℝ)*(lower2) + (9042933/6250000000000 : ℝ)*(upper3) + (52201443/50000000000000 : ℝ)*(upper5) + (2579833726860703/100000000000000 : ℝ)*(major0) + (2579833726860703/100000000000000 : ℝ)*(major1) + (2579833726860703/100000000000000 : ℝ)*(major2) + (461843078150557/12500000000000 : ℝ)*(sp0) + (3694757848780717/100000000000000 : ℝ)*(sp1) + (923689490536131/25000000000000 : ℝ)*(sp2) + (1464902142198203/100000000000000 : ℝ)*(sp3) + (2858654691/20000000000000 : ℝ)*(sp4) + (3094078511/50000000000000 : ℝ)*(sp7) + (58596333214209/4000000000000 : ℝ)*(f.failure) + (3694758918477911/100000000000000 : ℝ)*(f.sum) + (36712534564927/28735000000000000000000000000 : ℝ)*base66 + (913741153366794343/718375000000000000000000000000000 : ℝ)*base68 + (8188841883549044343/718375000000000000000000000000000 : ℝ)*base70 + (2616557361563044343/718375000000000000000000000000000 : ℝ)*base72 + (102099191394973/28735000000000000000000000000 : ℝ)*base73 + (4978292747069044343/718375000000000000000000000000000 : ℝ)*base76 + (3102471191338544343/718375000000000000000000000000000 : ℝ)*base78 + (421299012459705657/718375000000000000000000000000000 : ℝ)*base79 + (159832470292037/28735000000000000000000000000 : ℝ)*base82 + (229393/80000000000000000000 : ℝ)*base89 + (229393/80000000000000000000 : ℝ)*base91 + (229393/80000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (601579395111017180630880363/359187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (325397981/100000000000000 : ℝ)*(base19) + (745577697/100000000000000 : ℝ)*(base23) + (124934849/50000000000000 : ℝ)*(lower1) + (23062287/100000000000000 : ℝ)*(upper3) + (20778341/25000000000000 : ℝ)*(lower4) + (1309636862939743/50000000000000 : ℝ)*(major0) + (1309636862939743/50000000000000 : ℝ)*(major1) + (2619273725879487/100000000000000 : ℝ)*(major2) + (964328613/20000000000000 : ℝ)*(sp2) + (643586603/25000000000000 : ℝ)*(sp3) + (1875621915183729/50000000000000 : ℝ)*(sp4) + (1875621752484739/50000000000000 : ℝ)*(sp5) + (468904782893337/12500000000000 : ℝ)*(sp6) + (297460198243459/20000000000000 : ℝ)*(sp7) + (743651782781853/50000000000000 : ℝ)*(f.failure) + (1875621915183729/50000000000000 : ℝ)*(f.sum) + (325648448482367/57470000000000000000000000000 : ℝ)*base66 + (4950833144196059833/359187500000000000000000000000000 : ℝ)*base68 + (6740739831648650547/718375000000000000000000000000000 : ℝ)*base70 + (11440448790846997333/359187500000000000000000000000000 : ℝ)*base72 + (37402354346297/57470000000000000000000000000 : ℝ)*base74 + (4006432497790900547/718375000000000000000000000000000 : ℝ)*base76 + (5940116766924128583/359187500000000000000000000000000 : ℝ)*base78 + (2613913358442941083/359187500000000000000000000000000 : ℝ)*base80 + (129529544460119/28735000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (6012781/1000000000000000000000 : ℝ)*base89 + (6012781/1000000000000000000000 : ℝ)*base91 + (3987219/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1630_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35221777/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8153/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10559/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (66/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3261/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1630_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1630_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35221777/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3283/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5231/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (66/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3261/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1630_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1630_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1630_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4835/1024 : ℝ) ≤ p) (hpb : p ≤ (4839/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35221777/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3283/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5231/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (66/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3261/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1630_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
