-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1688_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:37:55.984127+00:00
-- url     : https://prove2.me/submissions/788e064c-e387-4a11-b03e-fd280262bd8f

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
theorem support_rectangle_w1688_box_0 (p : ℝ) (hpa : (5119/1024 : ℝ) ≤ p) (hpb : p ≤ (5127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1159038757/10000000000 : ℝ)*x 0 + (5429176433/10000000000 : ℝ)*x 1 + (5429175871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1159038757/10000000000 : ℝ)^5127 ≤ (6768954993189/100000000000000 : ℝ)^4103 := by
    have hnat : (1159038757 : ℕ)^5127*100000000000000^4103 ≤ 6768954993189^4103*10000000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1159038757 10000000000 6768954993189 100000000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5429176433/10000000000 : ℝ)^5127 ≤ (23307762758403/50000000000000 : ℝ)^4103 := by
    have hnat : (5429176433 : ℕ)^5127*50000000000000^4103 ≤ 23307762758403^4103*10000000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429176433 10000000000 23307762758403 50000000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5429175871/10000000000 : ℝ)^5127 ≤ (46615519487119/100000000000000 : ℝ)^4103 := by
    have hnat : (5429175871 : ℕ)^5127*100000000000000^4103 ≤ 46615519487119^4103*10000000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429175871 10000000000 46615519487119 100000000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5127/1024 : ℝ)) 5127 4103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1159038757/10000000000 : ℝ), (5429176433/10000000000 : ℝ), (5429175871/10000000000 : ℝ)] ![(6768954993189/100000000000000 : ℝ), (23307762758403/50000000000000 : ℝ), (46615519487119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1159038757/10000000000 : ℝ)|^5127 ≤ (6768954993189/100000000000000 : ℝ)^4103
        have hw : |(-1159038757/10000000000 : ℝ)|=(1159038757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5429176433/10000000000 : ℝ)|^5127 ≤ (23307762758403/50000000000000 : ℝ)^4103
        have hw : |(5429176433/10000000000 : ℝ)|=(5429176433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5429175871/10000000000 : ℝ)|^5127 ≤ (46615519487119/100000000000000 : ℝ)^4103
        have hw : |(5429175871/10000000000 : ℝ)|=(5429175871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1688_box_1 (p : ℝ) (hpa : (5119/1024 : ℝ) ≤ p) (hpb : p ≤ (5127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5226067223/10000000000 : ℝ)*x 0 + (-90485611/625000000 : ℝ)*x 1 + (5429176263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5226067223/10000000000 : ℝ)^5127 ≤ (44446640758243/100000000000000 : ℝ)^4103 := by
    have hnat : (5226067223 : ℕ)^5127*100000000000000^4103 ≤ 44446640758243^4103*10000000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226067223 10000000000 44446640758243 100000000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (90485611/625000000 : ℝ)^5127 ≤ (27930736019/312500000000 : ℝ)^4103 := by
    have hnat : (90485611 : ℕ)^5127*312500000000^4103 ≤ 27930736019^4103*625000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90485611 625000000 27930736019 312500000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5429176263/10000000000 : ℝ)^5127 ≤ (46615523692879/100000000000000 : ℝ)^4103 := by
    have hnat : (5429176263 : ℕ)^5127*100000000000000^4103 ≤ 46615523692879^4103*10000000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429176263 10000000000 46615523692879 100000000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5127/1024 : ℝ)) 5127 4103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5226067223/10000000000 : ℝ), (-90485611/625000000 : ℝ), (5429176263/10000000000 : ℝ)] ![(44446640758243/100000000000000 : ℝ), (27930736019/312500000000 : ℝ), (46615523692879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5226067223/10000000000 : ℝ)|^5127 ≤ (44446640758243/100000000000000 : ℝ)^4103
        have hw : |(5226067223/10000000000 : ℝ)|=(5226067223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-90485611/625000000 : ℝ)|^5127 ≤ (27930736019/312500000000 : ℝ)^4103
        have hw : |(-90485611/625000000 : ℝ)|=(90485611/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5429176263/10000000000 : ℝ)|^5127 ≤ (46615523692879/100000000000000 : ℝ)^4103
        have hw : |(5429176263/10000000000 : ℝ)|=(5429176263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1688_box_2 (p : ℝ) (hpa : (5119/1024 : ℝ) ≤ p) (hpb : p ≤ (5127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2613033243/5000000000 : ℝ)*x 0 + (2714588641/5000000000 : ℝ)*x 1 + (-723884687/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2613033243/5000000000 : ℝ)^5127 ≤ (2777914557867/6250000000000 : ℝ)^4103 := by
    have hnat : (2613033243 : ℕ)^5127*6250000000000^4103 ≤ 2777914557867^4103*5000000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613033243 5000000000 2777914557867 6250000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2714588641/5000000000 : ℝ)^5127 ≤ (4661553462571/10000000000000 : ℝ)^4103 := by
    have hnat : (2714588641 : ℕ)^5127*10000000000000^4103 ≤ 4661553462571^4103*5000000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714588641 5000000000 4661553462571 10000000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (723884687/5000000000 : ℝ)^5127 ≤ (1787566484989/20000000000000 : ℝ)^4103 := by
    have hnat : (723884687 : ℕ)^5127*20000000000000^4103 ≤ 1787566484989^4103*5000000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      723884687 5000000000 1787566484989 20000000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5127/1024 : ℝ)) 5127 4103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2613033243/5000000000 : ℝ), (2714588641/5000000000 : ℝ), (-723884687/5000000000 : ℝ)] ![(2777914557867/6250000000000 : ℝ), (4661553462571/10000000000000 : ℝ), (1787566484989/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2613033243/5000000000 : ℝ)|^5127 ≤ (2777914557867/6250000000000 : ℝ)^4103
        have hw : |(2613033243/5000000000 : ℝ)|=(2613033243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2714588641/5000000000 : ℝ)|^5127 ≤ (4661553462571/10000000000000 : ℝ)^4103
        have hw : |(2714588641/5000000000 : ℝ)|=(2714588641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-723884687/5000000000 : ℝ)|^5127 ≤ (1787566484989/20000000000000 : ℝ)^4103
        have hw : |(-723884687/5000000000 : ℝ)|=(723884687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1688_box_3 (p : ℝ) (hpa : (5119/1024 : ℝ) ≤ p) (hpb : p ≤ (5127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (141205873/312500000 : ℝ)*x 0 + (1982223261/5000000000 : ℝ)*x 1 + (1982223323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (141205873/312500000 : ℝ)^5127 ≤ (9264896648073/25000000000000 : ℝ)^4103 := by
    have hnat : (141205873 : ℕ)^5127*25000000000000^4103 ≤ 9264896648073^4103*312500000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141205873 312500000 9264896648073 25000000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1982223261/5000000000 : ℝ)^5127 ≤ (31470206079757/100000000000000 : ℝ)^4103 := by
    have hnat : (1982223261 : ℕ)^5127*100000000000000^4103 ≤ 31470206079757^4103*5000000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1982223261 5000000000 31470206079757 100000000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1982223323/5000000000 : ℝ)^5127 ≤ (1966887956859/6250000000000 : ℝ)^4103 := by
    have hnat : (1982223323 : ℕ)^5127*6250000000000^4103 ≤ 1966887956859^4103*5000000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1982223323 5000000000 1966887956859 6250000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5127/1024 : ℝ)) 5127 4103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(141205873/312500000 : ℝ), (1982223261/5000000000 : ℝ), (1982223323/5000000000 : ℝ)] ![(9264896648073/25000000000000 : ℝ), (31470206079757/100000000000000 : ℝ), (1966887956859/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(141205873/312500000 : ℝ)|^5127 ≤ (9264896648073/25000000000000 : ℝ)^4103
        have hw : |(141205873/312500000 : ℝ)|=(141205873/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1982223261/5000000000 : ℝ)|^5127 ≤ (31470206079757/100000000000000 : ℝ)^4103
        have hw : |(1982223261/5000000000 : ℝ)|=(1982223261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1982223323/5000000000 : ℝ)|^5127 ≤ (1966887956859/6250000000000 : ℝ)^4103
        have hw : |(1982223323/5000000000 : ℝ)|=(1982223323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1688_box_4 (p : ℝ) (hpa : (5119/1024 : ℝ) ≤ p) (hpb : p ≤ (5127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1853393849/10000000000 : ℝ)*x 0 + (2588003151/5000000000 : ℝ)*x 1 + (5176006253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1853393849/10000000000 : ℝ)^5127 ≤ (12169475790023/100000000000000 : ℝ)^4103 := by
    have hnat : (1853393849 : ℕ)^5127*100000000000000^4103 ≤ 12169475790023^4103*10000000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1853393849 10000000000 12169475790023 100000000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2588003151/5000000000 : ℝ)^5127 ≤ (43915262360181/100000000000000 : ℝ)^4103 := by
    have hnat : (2588003151 : ℕ)^5127*100000000000000^4103 ≤ 43915262360181^4103*5000000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588003151 5000000000 43915262360181 100000000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5176006253/10000000000 : ℝ)^5127 ≤ (43915261840689/100000000000000 : ℝ)^4103 := by
    have hnat : (5176006253 : ℕ)^5127*100000000000000^4103 ≤ 43915261840689^4103*10000000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176006253 10000000000 43915261840689 100000000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5127/1024 : ℝ)) 5127 4103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1853393849/10000000000 : ℝ), (2588003151/5000000000 : ℝ), (5176006253/10000000000 : ℝ)] ![(12169475790023/100000000000000 : ℝ), (43915262360181/100000000000000 : ℝ), (43915261840689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1853393849/10000000000 : ℝ)|^5127 ≤ (12169475790023/100000000000000 : ℝ)^4103
        have hw : |(-1853393849/10000000000 : ℝ)|=(1853393849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2588003151/5000000000 : ℝ)|^5127 ≤ (43915262360181/100000000000000 : ℝ)^4103
        have hw : |(2588003151/5000000000 : ℝ)|=(2588003151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5176006253/10000000000 : ℝ)|^5127 ≤ (43915261840689/100000000000000 : ℝ)^4103
        have hw : |(5176006253/10000000000 : ℝ)|=(5176006253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1688_box_5 (p : ℝ) (hpa : (5119/1024 : ℝ) ≤ p) (hpb : p ≤ (5127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2699345611/5000000000 : ℝ)*x 0 + (-1557993343/10000000000 : ℝ)*x 1 + (5176006213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2699345611/5000000000 : ℝ)^5127 ≤ (11572169950497/25000000000000 : ℝ)^4103 := by
    have hnat : (2699345611 : ℕ)^5127*25000000000000^4103 ≤ 11572169950497^4103*5000000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699345611 5000000000 11572169950497 25000000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1557993343/10000000000 : ℝ)^5127 ≤ (4898029382827/50000000000000 : ℝ)^4103 := by
    have hnat : (1557993343 : ℕ)^5127*50000000000000^4103 ≤ 4898029382827^4103*10000000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1557993343 10000000000 4898029382827 50000000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5176006213/10000000000 : ℝ)^5127 ≤ (21957630708307/50000000000000 : ℝ)^4103 := by
    have hnat : (5176006213 : ℕ)^5127*50000000000000^4103 ≤ 21957630708307^4103*10000000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176006213 10000000000 21957630708307 50000000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5127/1024 : ℝ)) 5127 4103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2699345611/5000000000 : ℝ), (-1557993343/10000000000 : ℝ), (5176006213/10000000000 : ℝ)] ![(11572169950497/25000000000000 : ℝ), (4898029382827/50000000000000 : ℝ), (21957630708307/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2699345611/5000000000 : ℝ)|^5127 ≤ (11572169950497/25000000000000 : ℝ)^4103
        have hw : |(2699345611/5000000000 : ℝ)|=(2699345611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1557993343/10000000000 : ℝ)|^5127 ≤ (4898029382827/50000000000000 : ℝ)^4103
        have hw : |(-1557993343/10000000000 : ℝ)|=(1557993343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5176006213/10000000000 : ℝ)|^5127 ≤ (21957630708307/50000000000000 : ℝ)^4103
        have hw : |(5176006213/10000000000 : ℝ)|=(5176006213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1688_box_6 (p : ℝ) (hpa : (5119/1024 : ℝ) ≤ p) (hpb : p ≤ (5127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1687091/3125000 : ℝ)*x 0 + (1035201271/2000000000 : ℝ)*x 1 + (-1557993181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1687091/3125000 : ℝ)^5127 ≤ (23144339783141/50000000000000 : ℝ)^4103 := by
    have hnat : (1687091 : ℕ)^5127*50000000000000^4103 ≤ 23144339783141^4103*3125000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1687091 3125000 23144339783141 50000000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035201271/2000000000 : ℝ)^5127 ≤ (274470393263/625000000000 : ℝ)^4103 := by
    have hnat : (1035201271 : ℕ)^5127*625000000000^4103 ≤ 274470393263^4103*2000000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035201271 2000000000 274470393263 625000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1557993181/10000000000 : ℝ)^5127 ≤ (9796057492847/100000000000000 : ℝ)^4103 := by
    have hnat : (1557993181 : ℕ)^5127*100000000000000^4103 ≤ 9796057492847^4103*10000000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1557993181 10000000000 9796057492847 100000000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5127/1024 : ℝ)) 5127 4103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1687091/3125000 : ℝ), (1035201271/2000000000 : ℝ), (-1557993181/10000000000 : ℝ)] ![(23144339783141/50000000000000 : ℝ), (274470393263/625000000000 : ℝ), (9796057492847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1687091/3125000 : ℝ)|^5127 ≤ (23144339783141/50000000000000 : ℝ)^4103
        have hw : |(1687091/3125000 : ℝ)|=(1687091/3125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035201271/2000000000 : ℝ)|^5127 ≤ (274470393263/625000000000 : ℝ)^4103
        have hw : |(1035201271/2000000000 : ℝ)|=(1035201271/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1557993181/10000000000 : ℝ)|^5127 ≤ (9796057492847/100000000000000 : ℝ)^4103
        have hw : |(-1557993181/10000000000 : ℝ)|=(1557993181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1688_box_7 (p : ℝ) (hpa : (5119/1024 : ℝ) ≤ p) (hpb : p ≤ (5127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3734954017/10000000000 : ℝ)*x 0 + (871079687/2000000000 : ℝ)*x 1 + (4355398761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3734954017/10000000000 : ℝ)^5127 ≤ (29210500737569/100000000000000 : ℝ)^4103 := by
    have hnat : (3734954017 : ℕ)^5127*100000000000000^4103 ≤ 29210500737569^4103*10000000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3734954017 10000000000 29210500737569 100000000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (871079687/2000000000 : ℝ)^5127 ≤ (17697373983529/50000000000000 : ℝ)^4103 := by
    have hnat : (871079687 : ℕ)^5127*50000000000000^4103 ≤ 17697373983529^4103*2000000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871079687 2000000000 17697373983529 50000000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4355398761/10000000000 : ℝ)^5127 ≤ (35394751277533/100000000000000 : ℝ)^4103 := by
    have hnat : (4355398761 : ℕ)^5127*100000000000000^4103 ≤ 35394751277533^4103*10000000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355398761 10000000000 35394751277533 100000000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5127/1024 : ℝ)) 5127 4103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3734954017/10000000000 : ℝ), (871079687/2000000000 : ℝ), (4355398761/10000000000 : ℝ)] ![(29210500737569/100000000000000 : ℝ), (17697373983529/50000000000000 : ℝ), (35394751277533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3734954017/10000000000 : ℝ)|^5127 ≤ (29210500737569/100000000000000 : ℝ)^4103
        have hw : |(3734954017/10000000000 : ℝ)|=(3734954017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(871079687/2000000000 : ℝ)|^5127 ≤ (17697373983529/50000000000000 : ℝ)^4103
        have hw : |(871079687/2000000000 : ℝ)|=(871079687/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4355398761/10000000000 : ℝ)|^5127 ≤ (35394751277533/100000000000000 : ℝ)^4103
        have hw : |(4355398761/10000000000 : ℝ)|=(4355398761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1688_box_8 (p : ℝ) (hpa : (5119/1024 : ℝ) ≤ p) (hpb : p ≤ (5127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1704447319/10000000000 : ℝ)*x 0 + (2495167353/5000000000 : ℝ)*x 1 + (1368208509/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1704447319/10000000000 : ℝ)^5127 ≤ (10959915885697/100000000000000 : ℝ)^4103 := by
    have hnat : (1704447319 : ℕ)^5127*100000000000000^4103 ≤ 10959915885697^4103*10000000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1704447319 10000000000 10959915885697 100000000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2495167353/5000000000 : ℝ)^5127 ≤ (20977843980697/50000000000000 : ℝ)^4103 := by
    have hnat : (2495167353 : ℕ)^5127*50000000000000^4103 ≤ 20977843980697^4103*5000000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2495167353 5000000000 20977843980697 50000000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1368208509/2500000000 : ℝ)^5127 ≤ (11771099033453/25000000000000 : ℝ)^4103 := by
    have hnat : (1368208509 : ℕ)^5127*25000000000000^4103 ≤ 11771099033453^4103*2500000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368208509 2500000000 11771099033453 25000000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5127/1024 : ℝ)) 5127 4103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1704447319/10000000000 : ℝ), (2495167353/5000000000 : ℝ), (1368208509/2500000000 : ℝ)] ![(10959915885697/100000000000000 : ℝ), (20977843980697/50000000000000 : ℝ), (11771099033453/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1704447319/10000000000 : ℝ)|^5127 ≤ (10959915885697/100000000000000 : ℝ)^4103
        have hw : |(-1704447319/10000000000 : ℝ)|=(1704447319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2495167353/5000000000 : ℝ)|^5127 ≤ (20977843980697/50000000000000 : ℝ)^4103
        have hw : |(2495167353/5000000000 : ℝ)|=(2495167353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1368208509/2500000000 : ℝ)|^5127 ≤ (11771099033453/25000000000000 : ℝ)^4103
        have hw : |(1368208509/2500000000 : ℝ)|=(1368208509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1688_box_9 (p : ℝ) (hpa : (5119/1024 : ℝ) ≤ p) (hpb : p ≤ (5127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2598154401/5000000000 : ℝ)*x 0 + (-142792117/1000000000 : ℝ)*x 1 + (5472835043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2598154401/5000000000 : ℝ)^5127 ≤ (44130612083171/100000000000000 : ℝ)^4103 := by
    have hnat : (2598154401 : ℕ)^5127*100000000000000^4103 ≤ 44130612083171^4103*5000000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598154401 5000000000 44130612083171 100000000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (142792117/1000000000 : ℝ)^5127 ≤ (1756996188277/20000000000000 : ℝ)^4103 := by
    have hnat : (142792117 : ℕ)^5127*20000000000000^4103 ≤ 1756996188277^4103*1000000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142792117 1000000000 1756996188277 20000000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5472835043/10000000000 : ℝ)^5127 ≤ (5885550869939/12500000000000 : ℝ)^4103 := by
    have hnat : (5472835043 : ℕ)^5127*12500000000000^4103 ≤ 5885550869939^4103*10000000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5472835043 10000000000 5885550869939 12500000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5127/1024 : ℝ)) 5127 4103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2598154401/5000000000 : ℝ), (-142792117/1000000000 : ℝ), (5472835043/10000000000 : ℝ)] ![(44130612083171/100000000000000 : ℝ), (1756996188277/20000000000000 : ℝ), (5885550869939/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2598154401/5000000000 : ℝ)|^5127 ≤ (44130612083171/100000000000000 : ℝ)^4103
        have hw : |(2598154401/5000000000 : ℝ)|=(2598154401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-142792117/1000000000 : ℝ)|^5127 ≤ (1756996188277/20000000000000 : ℝ)^4103
        have hw : |(-142792117/1000000000 : ℝ)|=(142792117/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5472835043/10000000000 : ℝ)|^5127 ≤ (5885550869939/12500000000000 : ℝ)^4103
        have hw : |(5472835043/10000000000 : ℝ)|=(5472835043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1688_box_10 (p : ℝ) (hpa : (5119/1024 : ℝ) ≤ p) (hpb : p ≤ (5127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5196307789/10000000000 : ℝ)*x 0 + (684104427/1250000000 : ℝ)*x 1 + (-713961023/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5196307789/10000000000 : ℝ)^5127 ≤ (44130601332979/100000000000000 : ℝ)^4103 := by
    have hnat : (5196307789 : ℕ)^5127*100000000000000^4103 ≤ 44130601332979^4103*10000000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196307789 10000000000 44130601332979 100000000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (684104427/1250000000 : ℝ)^5127 ≤ (47084410969429/100000000000000 : ℝ)^4103 := by
    have hnat : (684104427 : ℕ)^5127*100000000000000^4103 ≤ 47084410969429^4103*1250000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684104427 1250000000 47084410969429 100000000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (713961023/5000000000 : ℝ)^5127 ≤ (8784987675841/100000000000000 : ℝ)^4103 := by
    have hnat : (713961023 : ℕ)^5127*100000000000000^4103 ≤ 8784987675841^4103*5000000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      713961023 5000000000 8784987675841 100000000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5127/1024 : ℝ)) 5127 4103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5196307789/10000000000 : ℝ), (684104427/1250000000 : ℝ), (-713961023/5000000000 : ℝ)] ![(44130601332979/100000000000000 : ℝ), (47084410969429/100000000000000 : ℝ), (8784987675841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5196307789/10000000000 : ℝ)|^5127 ≤ (44130601332979/100000000000000 : ℝ)^4103
        have hw : |(5196307789/10000000000 : ℝ)|=(5196307789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(684104427/1250000000 : ℝ)|^5127 ≤ (47084410969429/100000000000000 : ℝ)^4103
        have hw : |(684104427/1250000000 : ℝ)|=(684104427/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-713961023/5000000000 : ℝ)|^5127 ≤ (8784987675841/100000000000000 : ℝ)^4103
        have hw : |(-713961023/5000000000 : ℝ)|=(713961023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1688_box_11 (p : ℝ) (hpa : (5119/1024 : ℝ) ≤ p) (hpb : p ≤ (5127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (116217229/250000000 : ℝ)*x 0 + (487106583/1250000000 : ℝ)*x 1 + (974213161/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (116217229/250000000 : ℝ)^5127 ≤ (38397683425239/100000000000000 : ℝ)^4103 := by
    have hnat : (116217229 : ℕ)^5127*100000000000000^4103 ≤ 38397683425239^4103*250000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116217229 250000000 38397683425239 100000000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (487106583/1250000000 : ℝ)^5127 ≤ (30801158377497/100000000000000 : ℝ)^4103 := by
    have hnat : (487106583 : ℕ)^5127*100000000000000^4103 ≤ 30801158377497^4103*1250000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487106583 1250000000 30801158377497 100000000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (974213161/2500000000 : ℝ)^5127 ≤ (30801158179961/100000000000000 : ℝ)^4103 := by
    have hnat : (974213161 : ℕ)^5127*100000000000000^4103 ≤ 30801158179961^4103*2500000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      974213161 2500000000 30801158179961 100000000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5127/1024 : ℝ)) 5127 4103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(116217229/250000000 : ℝ), (487106583/1250000000 : ℝ), (974213161/2500000000 : ℝ)] ![(38397683425239/100000000000000 : ℝ), (30801158377497/100000000000000 : ℝ), (30801158179961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(116217229/250000000 : ℝ)|^5127 ≤ (38397683425239/100000000000000 : ℝ)^4103
        have hw : |(116217229/250000000 : ℝ)|=(116217229/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(487106583/1250000000 : ℝ)|^5127 ≤ (30801158377497/100000000000000 : ℝ)^4103
        have hw : |(487106583/1250000000 : ℝ)|=(487106583/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(974213161/2500000000 : ℝ)|^5127 ≤ (30801158179961/100000000000000 : ℝ)^4103
        have hw : |(974213161/2500000000 : ℝ)|=(974213161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1688_box_12 (p : ℝ) (hpa : (5119/1024 : ℝ) ≤ p) (hpb : p ≤ (5127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1303245211/10000000000 : ℝ)*x 0 + (1401396219/2500000000 : ℝ)*x 1 + (5150686921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1303245211/10000000000 : ℝ)^5127 ≤ (3918592771661/50000000000000 : ℝ)^4103 := by
    have hnat : (1303245211 : ℕ)^5127*50000000000000^4103 ≤ 3918592771661^4103*10000000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303245211 10000000000 3918592771661 50000000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1401396219/2500000000 : ℝ)^5127 ≤ (24257910409657/50000000000000 : ℝ)^4103 := by
    have hnat : (1401396219 : ℕ)^5127*50000000000000^4103 ≤ 24257910409657^4103*2500000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1401396219 2500000000 24257910409657 50000000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5150686921/10000000000 : ℝ)^5127 ≤ (43646993624383/100000000000000 : ℝ)^4103 := by
    have hnat : (5150686921 : ℕ)^5127*100000000000000^4103 ≤ 43646993624383^4103*10000000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5150686921 10000000000 43646993624383 100000000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5127/1024 : ℝ)) 5127 4103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1303245211/10000000000 : ℝ), (1401396219/2500000000 : ℝ), (5150686921/10000000000 : ℝ)] ![(3918592771661/50000000000000 : ℝ), (24257910409657/50000000000000 : ℝ), (43646993624383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1303245211/10000000000 : ℝ)|^5127 ≤ (3918592771661/50000000000000 : ℝ)^4103
        have hw : |(-1303245211/10000000000 : ℝ)|=(1303245211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1401396219/2500000000 : ℝ)|^5127 ≤ (24257910409657/50000000000000 : ℝ)^4103
        have hw : |(1401396219/2500000000 : ℝ)|=(1401396219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5150686921/10000000000 : ℝ)|^5127 ≤ (43646993624383/100000000000000 : ℝ)^4103
        have hw : |(5150686921/10000000000 : ℝ)|=(5150686921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1688_box_13 (p : ℝ) (hpa : (5119/1024 : ℝ) ≤ p) (hpb : p ≤ (5127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5415981647/10000000000 : ℝ)*x 0 + (-1568540921/10000000000 : ℝ)*x 1 + (5150687417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5415981647/10000000000 : ℝ)^5127 ≤ (23237000941697/50000000000000 : ℝ)^4103 := by
    have hnat : (5415981647 : ℕ)^5127*50000000000000^4103 ≤ 23237000941697^4103*10000000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415981647 10000000000 23237000941697 50000000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1568540921/10000000000 : ℝ)^5127 ≤ (9878999227583/100000000000000 : ℝ)^4103 := by
    have hnat : (1568540921 : ℕ)^5127*100000000000000^4103 ≤ 9878999227583^4103*10000000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1568540921 10000000000 9878999227583 100000000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5150687417/10000000000 : ℝ)^5127 ≤ (43646998876479/100000000000000 : ℝ)^4103 := by
    have hnat : (5150687417 : ℕ)^5127*100000000000000^4103 ≤ 43646998876479^4103*10000000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5150687417 10000000000 43646998876479 100000000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5127/1024 : ℝ)) 5127 4103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5415981647/10000000000 : ℝ), (-1568540921/10000000000 : ℝ), (5150687417/10000000000 : ℝ)] ![(23237000941697/50000000000000 : ℝ), (9878999227583/100000000000000 : ℝ), (43646998876479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5415981647/10000000000 : ℝ)|^5127 ≤ (23237000941697/50000000000000 : ℝ)^4103
        have hw : |(5415981647/10000000000 : ℝ)|=(5415981647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1568540921/10000000000 : ℝ)|^5127 ≤ (9878999227583/100000000000000 : ℝ)^4103
        have hw : |(-1568540921/10000000000 : ℝ)|=(1568540921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5150687417/10000000000 : ℝ)|^5127 ≤ (43646998876479/100000000000000 : ℝ)^4103
        have hw : |(5150687417/10000000000 : ℝ)|=(5150687417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1688_box_14 (p : ℝ) (hpa : (5119/1024 : ℝ) ≤ p) (hpb : p ≤ (5127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2707991333/5000000000 : ℝ)*x 0 + (128767141/250000000 : ℝ)*x 1 + (-1568541923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2707991333/5000000000 : ℝ)^5127 ≤ (46474012809587/100000000000000 : ℝ)^4103 := by
    have hnat : (2707991333 : ℕ)^5127*100000000000000^4103 ≤ 46474012809587^4103*5000000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707991333 5000000000 46474012809587 100000000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (128767141/250000000 : ℝ)^5127 ≤ (21823490029999/50000000000000 : ℝ)^4103 := by
    have hnat : (128767141 : ℕ)^5127*50000000000000^4103 ≤ 21823490029999^4103*250000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128767141 250000000 21823490029999 50000000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1568541923/10000000000 : ℝ)^5127 ≤ (9879007113399/100000000000000 : ℝ)^4103 := by
    have hnat : (1568541923 : ℕ)^5127*100000000000000^4103 ≤ 9879007113399^4103*10000000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1568541923 10000000000 9879007113399 100000000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5127/1024 : ℝ)) 5127 4103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2707991333/5000000000 : ℝ), (128767141/250000000 : ℝ), (-1568541923/10000000000 : ℝ)] ![(46474012809587/100000000000000 : ℝ), (21823490029999/50000000000000 : ℝ), (9879007113399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2707991333/5000000000 : ℝ)|^5127 ≤ (46474012809587/100000000000000 : ℝ)^4103
        have hw : |(2707991333/5000000000 : ℝ)|=(2707991333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(128767141/250000000 : ℝ)|^5127 ≤ (21823490029999/50000000000000 : ℝ)^4103
        have hw : |(128767141/250000000 : ℝ)|=(128767141/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1568541923/10000000000 : ℝ)|^5127 ≤ (9879007113399/100000000000000 : ℝ)^4103
        have hw : |(-1568541923/10000000000 : ℝ)|=(1568541923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1688_box_15 (p : ℝ) (hpa : (5119/1024 : ℝ) ≤ p) (hpb : p ≤ (5127/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (182680127/500000000 : ℝ)*x 0 + (4394394823/10000000000 : ℝ)*x 1 + (4394391823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (182680127/500000000 : ℝ)^5127 ≤ (28417648133491/100000000000000 : ℝ)^4103 := by
    have hnat : (182680127 : ℕ)^5127*100000000000000^4103 ≤ 28417648133491^4103*500000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182680127 500000000 28417648133491 100000000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4394394823/10000000000 : ℝ)^5127 ≤ (89477977971/250000000000 : ℝ)^4103 := by
    have hnat : (4394394823 : ℕ)^5127*250000000000^4103 ≤ 89477977971^4103*10000000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4394394823 10000000000 89477977971 250000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4394391823/10000000000 : ℝ)^5127 ≤ (35791160656059/100000000000000 : ℝ)^4103 := by
    have hnat : (4394391823 : ℕ)^5127*100000000000000^4103 ≤ 35791160656059^4103*10000000000^5127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4394391823 10000000000 35791160656059 100000000000000 5127 4103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5127/1024 : ℝ)) 5127 4103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(182680127/500000000 : ℝ), (4394394823/10000000000 : ℝ), (4394391823/10000000000 : ℝ)] ![(28417648133491/100000000000000 : ℝ), (89477977971/250000000000 : ℝ), (35791160656059/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(182680127/500000000 : ℝ)|^5127 ≤ (28417648133491/100000000000000 : ℝ)^4103
        have hw : |(182680127/500000000 : ℝ)|=(182680127/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4394394823/10000000000 : ℝ)|^5127 ≤ (89477977971/250000000000 : ℝ)^4103
        have hw : |(4394394823/10000000000 : ℝ)|=(4394394823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4394391823/10000000000 : ℝ)|^5127 ≤ (35791160656059/100000000000000 : ℝ)^4103
        have hw : |(4394391823/10000000000 : ℝ)|=(4394391823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1688_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5119/1024 : ℝ) ≤ p) (hpb : p ≤ (5127/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (46927187/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (539/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9811/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(66557/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(28941/50000 : ℝ) ∧ (40367/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (45051/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (539/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9811/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (539/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9811/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (539/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9811/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (539/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9811/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (539/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9811/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (539/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9811/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9811/100000 : ℝ) ^ (5119/1024 : ℝ) ≤ (36442740193977/4000000000000000000 : ℝ) := by
    have hpowers : (9811/100000 : ℝ)^5119 ≤ (36442740193977/4000000000000000000 : ℝ)^1024 := by
      have hnat : (9811 : ℕ)^5119*4000000000000000000^1024 ≤ 36442740193977^1024*100000^5119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9811 100000 36442740193977 4000000000000000000 5119 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9811/100000 : ℝ)) (X := (36442740193977/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5119 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (539/3125 : ℝ) ^ (5119/1024 : ℝ) ≤ (7645556361543809/50000000000000000000 : ℝ) := by
    have hpowers : (539/3125 : ℝ)^5119 ≤ (7645556361543809/50000000000000000000 : ℝ)^1024 := by
      have hnat : (539 : ℕ)^5119*50000000000000000000^1024 ≤ 7645556361543809^1024*3125^5119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        539 3125 7645556361543809 50000000000000000000 5119 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (539/3125 : ℝ)) (X := (7645556361543809/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5119 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000036442740193977/2000000000000000000 : ℝ) ≤ (10000036449593657/10000000000000000 : ℝ) ^ (5119/1024 : ℝ) := by
    have hpowers : (2000036442740193977/2000000000000000000 : ℝ)^1024 ≤ (10000036449593657/10000000000000000 : ℝ)^5119 := by
      have hnat : (2000036442740193977 : ℕ)^1024*10000000000000000^5119 ≤ 10000036449593657^5119*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000036442740193977 2000000000000000000 10000036449593657 10000000000000000 1024 5119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000036449593657/10000000000000000 : ℝ)) (X := (2000036442740193977/2000000000000000000 : ℝ)) (by norm_num) 5119 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100016202181227937043/100000000000000000000 : ℝ) ≤ (2500081021481201/2500000000000000 : ℝ) ^ (5119/1024 : ℝ) := by
    have hpowers : (100016202181227937043/100000000000000000000 : ℝ)^1024 ≤ (2500081021481201/2500000000000000 : ℝ)^5119 := by
      have hnat : (100016202181227937043 : ℕ)^1024*2500000000000000^5119 ≤ 2500081021481201^5119*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100016202181227937043 100000000000000000000 2500081021481201 2500000000000000 1024 5119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500081021481201/2500000000000000 : ℝ)) (X := (100016202181227937043/100000000000000000000 : ℝ)) (by norm_num) 5119 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25007645556361543809/25000000000000000000 : ℝ) ≤ (10000611722255951/10000000000000000 : ℝ) ^ (5119/1024 : ℝ) := by
    have hpowers : (25007645556361543809/25000000000000000000 : ℝ)^1024 ≤ (10000611722255951/10000000000000000 : ℝ)^5119 := by
      have hnat : (25007645556361543809 : ℕ)^1024*10000000000000000^5119 ≤ 10000611722255951^5119*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007645556361543809 25000000000000000000 10000611722255951 10000000000000000 1024 5119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000611722255951/10000000000000000 : ℝ)) (X := (25007645556361543809/25000000000000000000 : ℝ)) (by norm_num) 5119 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(36442740193977/4000000000000000000 : ℝ) ≤ ((991528361007176809/991600000000000000 : ℝ)+2*(95878777049/247900000000000 : ℝ)*(9811/100000 : ℝ))^(5119/1024 : ℝ) := by
    rw [show (991528361007176809/991600000000000000 : ℝ)+2*(95878777049/247900000000000 : ℝ)*(9811/100000 : ℝ)=(10000036449593657/10000000000000000 : ℝ) by norm_num, show 1+2*(36442740193977/4000000000000000000 : ℝ)=(2000036442740193977/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7645556361543809/50000000000000000000 : ℝ)+(36442740193977/4000000000000000000 : ℝ) ≤ ((991528361007176809/991600000000000000 : ℝ)+(95878777049/247900000000000 : ℝ)*((539/3125 : ℝ)+(9811/100000 : ℝ)))^(5119/1024 : ℝ) := by
    rw [show (991528361007176809/991600000000000000 : ℝ)+(95878777049/247900000000000 : ℝ)*((539/3125 : ℝ)+(9811/100000 : ℝ))=(2500081021481201/2500000000000000 : ℝ) by norm_num, show 1+(7645556361543809/50000000000000000000 : ℝ)+(36442740193977/4000000000000000000 : ℝ)=(100016202181227937043/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7645556361543809/50000000000000000000 : ℝ) ≤ ((991528361007176809/991600000000000000 : ℝ)+2*(95878777049/247900000000000 : ℝ)*(539/3125 : ℝ))^(5119/1024 : ℝ) := by
    rw [show (991528361007176809/991600000000000000 : ℝ)+2*(95878777049/247900000000000 : ℝ)*(539/3125 : ℝ)=(10000611722255951/10000000000000000 : ℝ) by norm_num, show 1+2*(7645556361543809/50000000000000000000 : ℝ)=(25007645556361543809/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (991528361007176809/991600000000000000 : ℝ)*(X 1 0+X 2 0)+(95878777049/247900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5119/1024 : ℝ)) (lo := (9811/100000 : ℝ)) (hi := (539/3125 : ℝ)) (c := (991528361007176809/991600000000000000 : ℝ)) (alpha := (95878777049/247900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (991528361007176809/991600000000000000 : ℝ)*(X 0 1+X 2 1)+(95878777049/247900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5119/1024 : ℝ)) (lo := (9811/100000 : ℝ)) (hi := (539/3125 : ℝ)) (c := (991528361007176809/991600000000000000 : ℝ)) (alpha := (95878777049/247900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (991528361007176809/991600000000000000 : ℝ)*(X 0 2+X 1 2)+(95878777049/247900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5119/1024 : ℝ)) (lo := (9811/100000 : ℝ)) (hi := (539/3125 : ℝ)) (c := (991528361007176809/991600000000000000 : ℝ)) (alpha := (95878777049/247900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1159038757/10000000000 : ℝ)*X 0 0+(5429176433/10000000000 : ℝ)*X 0 1+(5429175871/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1688_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5226067223/10000000000 : ℝ)*X 1 0+(-90485611/625000000 : ℝ)*X 1 1+(5429176263/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1688_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2613033243/5000000000 : ℝ)*X 2 0+(2714588641/5000000000 : ℝ)*X 2 1+(-723884687/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1688_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((141205873/312500000 : ℝ)*X 0 0+(1982223261/5000000000 : ℝ)*X 0 1+(1982223323/5000000000 : ℝ)*X 0 2+(141205873/312500000 : ℝ)*X 1 0+(1982223261/5000000000 : ℝ)*X 1 1+(1982223323/5000000000 : ℝ)*X 1 2+(141205873/312500000 : ℝ)*X 2 0+(1982223261/5000000000 : ℝ)*X 2 1+(1982223323/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1688_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1853393849/10000000000 : ℝ)*X 0 0+(2588003151/5000000000 : ℝ)*X 0 1+(5176006253/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1688_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2699345611/5000000000 : ℝ)*X 1 0+(-1557993343/10000000000 : ℝ)*X 1 1+(5176006213/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1688_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1687091/3125000 : ℝ)*X 2 0+(1035201271/2000000000 : ℝ)*X 2 1+(-1557993181/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1688_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3734954017/10000000000 : ℝ)*X 0 0+(871079687/2000000000 : ℝ)*X 0 1+(4355398761/10000000000 : ℝ)*X 0 2+(3734954017/10000000000 : ℝ)*X 1 0+(871079687/2000000000 : ℝ)*X 1 1+(4355398761/10000000000 : ℝ)*X 1 2+(3734954017/10000000000 : ℝ)*X 2 0+(871079687/2000000000 : ℝ)*X 2 1+(4355398761/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1688_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1704447319/10000000000 : ℝ)*X 0 0+(2495167353/5000000000 : ℝ)*X 0 1+(1368208509/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1688_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2598154401/5000000000 : ℝ)*X 1 0+(-142792117/1000000000 : ℝ)*X 1 1+(5472835043/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1688_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5196307789/10000000000 : ℝ)*X 2 0+(684104427/1250000000 : ℝ)*X 2 1+(-713961023/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1688_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((116217229/250000000 : ℝ)*X 0 0+(487106583/1250000000 : ℝ)*X 0 1+(974213161/2500000000 : ℝ)*X 0 2+(116217229/250000000 : ℝ)*X 1 0+(487106583/1250000000 : ℝ)*X 1 1+(974213161/2500000000 : ℝ)*X 1 2+(116217229/250000000 : ℝ)*X 2 0+(487106583/1250000000 : ℝ)*X 2 1+(974213161/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1688_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1303245211/10000000000 : ℝ)*X 0 0+(1401396219/2500000000 : ℝ)*X 0 1+(5150686921/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1688_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5415981647/10000000000 : ℝ)*X 1 0+(-1568540921/10000000000 : ℝ)*X 1 1+(5150687417/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1688_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2707991333/5000000000 : ℝ)*X 2 0+(128767141/250000000 : ℝ)*X 2 1+(-1568541923/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1688_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((182680127/500000000 : ℝ)*X 0 0+(4394394823/10000000000 : ℝ)*X 0 1+(4394391823/10000000000 : ℝ)*X 0 2+(182680127/500000000 : ℝ)*X 1 0+(4394394823/10000000000 : ℝ)*X 1 1+(4394391823/10000000000 : ℝ)*X 1 2+(182680127/500000000 : ℝ)*X 2 0+(4394394823/10000000000 : ℝ)*X 2 1+(4394391823/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1688_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-66557/100000 : ℝ) ≤ (-6599511353468029622163324153327/9916000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17344121/100000000000000 : ℝ)*(lower1) + (21424317/100000000000000 : ℝ)*(lower2) + (4393497/12500000000000 : ℝ)*(lower3) + (316247/4000000000000 : ℝ)*(lower4) + (4738153/50000000000000 : ℝ)*(lower5) + (260076443999299/20000000000000 : ℝ)*(major0) + (260076443999299/20000000000000 : ℝ)*(major1) + (260076443999299/20000000000000 : ℝ)*(major2) + (1930182911141533/100000000000000 : ℝ)*(sp4) + (120636453177347/6250000000000 : ℝ)*(sp5) + (482543244311617/25000000000000 : ℝ)*(sp6) + (692765912005601/100000000000000 : ℝ)*(sp7) + (16984801/5000000000000 : ℝ)*(sp8) + (2568397771/25000000000000 : ℝ)*(sp14) + (692765912005601/100000000000000 : ℝ)*(f.failure) + (120636453177347/6250000000000 : ℝ)*(f.sum) + (20853936303371/2479000000000000000000000000 : ℝ)*base65 + (96180049252811109/19832000000000000000000000000000 : ℝ)*base68 + (139182913388099109/19832000000000000000000000000000 : ℝ)*base70 + (35941285283508891/19832000000000000000000000000000 : ℝ)*base71 + (524837137877/247900000000000000000000000 : ℝ)*base74 + (105071238902923109/19832000000000000000000000000000 : ℝ)*base76 + (47672647067508891/19832000000000000000000000000000 : ℝ)*base77 + (45452308228059109/19832000000000000000000000000000 : ℝ)*base80 + (2669898795077/619750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (8174387/2500000000000000000000 : ℝ)*base89 + (8174387/2500000000000000000000 : ℝ)*base91 + (8174387/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (28941/50000 : ℝ) ≤ (5739863311614830315422174819911/9916000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16106273/100000000000000 : ℝ)*(lower0) + (8987499/10000000000000 : ℝ)*(lower1) + (30901591/100000000000000 : ℝ)*(lower2) + (49200769/50000000000000 : ℝ)*(lower5) + (279769944617769/20000000000000 : ℝ)*(major0) + (279769944617769/20000000000000 : ℝ)*(major1) + (279769944617769/20000000000000 : ℝ)*(major2) + (101659048971357/5000000000000 : ℝ)*(sp0) + (203317864901491/10000000000000 : ℝ)*(sp1) + (2033170910643457/100000000000000 : ℝ)*(sp2) + (745221454378099/100000000000000 : ℝ)*(sp3) + (10068783683/100000000000000 : ℝ)*(sp6) + (2057042287/100000000000000 : ℝ)*(sp7) + (233041223/10000000000000 : ℝ)*(sp9) + (745223511420387/100000000000000 : ℝ)*(f.failure) + (101659048971357/5000000000000 : ℝ)*(f.sum) + (1885976013251/619750000000000000000000000 : ℝ)*base65 + (116667147716867121/19832000000000000000000000000000 : ℝ)*base67 + (146369193839411121/19832000000000000000000000000000 : ℝ)*base69 + (175989820201587121/19832000000000000000000000000000 : ℝ)*base71 + (251609501103/77468750000000000000000000 : ℝ)*base74 + (170280273710451121/19832000000000000000000000000000 : ℝ)*base75 + (175755241118003121/19832000000000000000000000000000 : ℝ)*base77 + (62207331033659121/19832000000000000000000000000000 : ℝ)*base79 + (14017080610901/2479000000000000000000000000 : ℝ)*base81 + (11361369/2500000000000000000000 : ℝ)*base89 + (11361369/2500000000000000000000 : ℝ)*base91 + (11361369/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (40367/50000 : ℝ) ≤ (4002919630821611060584288673457/4958000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (34478487/100000000000000 : ℝ)*(upper0) + (169794013/100000000000000 : ℝ)*(upper1) + (35193099/12500000000000 : ℝ)*(upper2) + (143086663258703/10000000000000 : ℝ)*(major0) + (143086663258703/10000000000000 : ℝ)*(major1) + (143086663258703/10000000000000 : ℝ)*(major2) + (87386984181/100000000000000 : ℝ)*(sp1) + (63327189483/100000000000000 : ℝ)*(sp2) + (1596952097/12500000000000 : ℝ)*(sp3) + (4072441/4000000000000 : ℝ)*(sp4) + (64766898849587/3125000000000 : ℝ)*(sp8) + (518113369503407/25000000000000 : ℝ)*(sp9) + (2072477537808327/100000000000000 : ℝ)*(sp10) + (152453486252727/20000000000000 : ℝ)*(sp11) + (762280206880411/100000000000000 : ℝ)*(f.failure) + (207254086499781/10000000000000 : ℝ)*(f.sum) + (414721256691/2479000000000000000000000000 : ℝ)*base66 + (54128935867150727/9916000000000000000000000000000 : ℝ)*base67 + (56618625126746727/9916000000000000000000000000000 : ℝ)*base69 + (75605681081026727/9916000000000000000000000000000 : ℝ)*base71 + (3378701325331/247900000000000000000000000 : ℝ)*base73 + (10343210879618727/9916000000000000000000000000000 : ℝ)*base75 + (1620692369674727/9916000000000000000000000000000 : ℝ)*base77 + (126818876078606727/9916000000000000000000000000000 : ℝ)*base79 + (378746215257/1239500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (16366143/2500000000000000000000 : ℝ)*base90 + (16366143/2500000000000000000000 : ℝ)*base92 + (16366143/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-45051/50000 : ℝ) ≤ (-22335660607840009743243903664827/24790000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5950593/5000000000000 : ℝ)*(upper1) + (13535027/100000000000000 : ℝ)*(lower2) + (218664161/100000000000000 : ℝ)*(upper3) + (1926829/20000000000000 : ℝ)*(upper5) + (1477765536205201/100000000000000 : ℝ)*(major0) + (1477765536205201/100000000000000 : ℝ)*(major1) + (1477765536205201/100000000000000 : ℝ)*(major2) + (3705996139/100000000000000 : ℝ)*(sp4) + (121719957291/100000000000000 : ℝ)*(sp6) + (24028403421/100000000000000 : ℝ)*(sp7) + (137393461661121/6250000000000 : ℝ)*(sp12) + (87931963702963/4000000000000 : ℝ)*(sp13) + (137386085788549/6250000000000 : ℝ)*(sp14) + (12300642355967/1562500000000 : ℝ)*(sp15) + (787265139185309/100000000000000 : ℝ)*(f.failure) + (87931963702963/4000000000000 : ℝ)*(f.sum) + (33803303105301/12395000000000000000000000000 : ℝ)*base66 + (7495049673099609/99160000000000000000000000000000 : ℝ)*base67 + (166882894599299609/99160000000000000000000000000000 : ℝ)*base69 + (93128303969459609/99160000000000000000000000000000 : ℝ)*base71 + (34888047985331/12395000000000000000000000000 : ℝ)*base74 + (832972142322979609/99160000000000000000000000000000 : ℝ)*base75 + (136348146722580391/99160000000000000000000000000000 : ℝ)*base78 + (500538188379939609/99160000000000000000000000000000 : ℝ)*base79 + (16323059421559/12395000000000000000000000000 : ℝ)*base81 + (1904217/2500000000000000000000 : ℝ)*base90 + (1904217/2500000000000000000000 : ℝ)*base92 + (1904217/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1688_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5119/1024 : ℝ) ≤ p) (hpb : p ≤ (5127/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (46927187/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (539/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9811/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66557/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(28941/50000 : ℝ) else (40367/50000 : ℝ) ≤ X j i ∧ X j i ≤ (45051/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1688_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1688_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5119/1024 : ℝ) ≤ p) (hpb : p ≤ (5127/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (46927187/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (539/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9811/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66557/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(28941/50000 : ℝ) else (40367/50000 : ℝ) ≤ X j i ∧ X j i ≤ (45051/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1688_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5119/1024 : ℝ) ≤ p) (hpb : p ≤ (5127/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (46927187/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (539/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9811/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66557/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(28941/50000 : ℝ) else (40367/50000 : ℝ) ≤ X j i ∧ X j i ≤ (45051/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1688_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
