-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1148_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:34:31.540637+00:00
-- url     : https://prove2.me/submissions/329af879-aed7-4374-92aa-abb48786d173

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
theorem support_rectangle_w1148_s6_0 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-432798323/2000000000 : ℝ)*x 0 + (53932593/100000000 : ℝ)*x 1 + (2632760383/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (432798323/2000000000 : ℝ)^8341 ≤ (6574920555297/50000000000000 : ℝ)^6293 := by
    have hnat : (432798323 : ℕ)^8341*50000000000000^6293 ≤ 6574920555297^6293*2000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432798323 2000000000 6574920555297 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (53932593/100000000 : ℝ)^8341 ≤ (2205742106369/5000000000000 : ℝ)^6293 := by
    have hnat : (53932593 : ℕ)^8341*5000000000000^6293 ≤ 2205742106369^6293*100000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53932593 100000000 2205742106369 5000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632760383/5000000000 : ℝ)^8341 ≤ (42735316737197/100000000000000 : ℝ)^6293 := by
    have hnat : (2632760383 : ℕ)^8341*100000000000000^6293 ≤ 42735316737197^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632760383 5000000000 42735316737197 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-432798323/2000000000 : ℝ), (53932593/100000000 : ℝ), (2632760383/5000000000 : ℝ)] ![(6574920555297/50000000000000 : ℝ), (2205742106369/5000000000000 : ℝ), (42735316737197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-432798323/2000000000 : ℝ)|^8341 ≤ (6574920555297/50000000000000 : ℝ)^6293
        have hw : |(-432798323/2000000000 : ℝ)|=(432798323/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(53932593/100000000 : ℝ)|^8341 ≤ (2205742106369/5000000000000 : ℝ)^6293
        have hw : |(53932593/100000000 : ℝ)|=(53932593/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632760383/5000000000 : ℝ)|^8341 ≤ (42735316737197/100000000000000 : ℝ)^6293
        have hw : |(2632760383/5000000000 : ℝ)|=(2632760383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s6_1 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344819573/10000000000 : ℝ)*x 0 + (-222878593/1000000000 : ℝ)*x 1 + (5265520767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344819573/10000000000 : ℝ)^8341 ≤ (21795223263401/50000000000000 : ℝ)^6293 := by
    have hnat : (5344819573 : ℕ)^8341*50000000000000^6293 ≤ 21795223263401^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344819573 10000000000 21795223263401 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (222878593/1000000000 : ℝ)^8341 ≤ (3418559179727/25000000000000 : ℝ)^6293 := by
    have hnat : (222878593 : ℕ)^8341*25000000000000^6293 ≤ 3418559179727^6293*1000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222878593 1000000000 3418559179727 25000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265520767/10000000000 : ℝ)^8341 ≤ (21367658373977/50000000000000 : ℝ)^6293 := by
    have hnat : (5265520767 : ℕ)^8341*50000000000000^6293 ≤ 21367658373977^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265520767 10000000000 21367658373977 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344819573/10000000000 : ℝ), (-222878593/1000000000 : ℝ), (5265520767/10000000000 : ℝ)] ![(21795223263401/50000000000000 : ℝ), (3418559179727/25000000000000 : ℝ), (21367658373977/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344819573/10000000000 : ℝ)|^8341 ≤ (21795223263401/50000000000000 : ℝ)^6293
        have hw : |(5344819573/10000000000 : ℝ)|=(5344819573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-222878593/1000000000 : ℝ)|^8341 ≤ (3418559179727/25000000000000 : ℝ)^6293
        have hw : |(-222878593/1000000000 : ℝ)|=(222878593/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265520767/10000000000 : ℝ)|^8341 ≤ (21367658373977/50000000000000 : ℝ)^6293
        have hw : |(5265520767/10000000000 : ℝ)|=(5265520767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s6_2 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (267240977/500000000 : ℝ)*x 0 + (5265520793/10000000000 : ℝ)*x 1 + (-2228785939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267240977/500000000 : ℝ)^8341 ≤ (43590446170077/100000000000000 : ℝ)^6293 := by
    have hnat : (267240977 : ℕ)^8341*100000000000000^6293 ≤ 43590446170077^6293*500000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267240977 500000000 43590446170077 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265520793/10000000000 : ℝ)^8341 ≤ (21367658513823/50000000000000 : ℝ)^6293 := by
    have hnat : (5265520793 : ℕ)^8341*50000000000000^6293 ≤ 21367658513823^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265520793 10000000000 21367658513823 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2228785939/10000000000 : ℝ)^8341 ≤ (2734847358419/20000000000000 : ℝ)^6293 := by
    have hnat : (2228785939 : ℕ)^8341*20000000000000^6293 ≤ 2734847358419^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2228785939 10000000000 2734847358419 20000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267240977/500000000 : ℝ), (5265520793/10000000000 : ℝ), (-2228785939/10000000000 : ℝ)] ![(43590446170077/100000000000000 : ℝ), (21367658513823/50000000000000 : ℝ), (2734847358419/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267240977/500000000 : ℝ)|^8341 ≤ (43590446170077/100000000000000 : ℝ)^6293
        have hw : |(267240977/500000000 : ℝ)|=(267240977/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265520793/10000000000 : ℝ)|^8341 ≤ (21367658513823/50000000000000 : ℝ)^6293
        have hw : |(5265520793/10000000000 : ℝ)|=(5265520793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2228785939/10000000000 : ℝ)|^8341 ≤ (2734847358419/20000000000000 : ℝ)^6293
        have hw : |(-2228785939/10000000000 : ℝ)|=(2228785939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s6_3 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (872762407/2000000000 : ℝ)*x 0 + (4238438831/10000000000 : ℝ)*x 1 + (449287043/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872762407/2000000000 : ℝ)^8341 ≤ (2082301959287/6250000000000 : ℝ)^6293 := by
    have hnat : (872762407 : ℕ)^8341*6250000000000^6293 ≤ 2082301959287^6293*2000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872762407 2000000000 2082301959287 6250000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4238438831/10000000000 : ℝ)^8341 ≤ (32054090162281/100000000000000 : ℝ)^6293 := by
    have hnat : (4238438831 : ℕ)^8341*100000000000000^6293 ≤ 32054090162281^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238438831 10000000000 32054090162281 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (449287043/1000000000 : ℝ)^8341 ≤ (6925815694679/20000000000000 : ℝ)^6293 := by
    have hnat : (449287043 : ℕ)^8341*20000000000000^6293 ≤ 6925815694679^6293*1000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449287043 1000000000 6925815694679 20000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(872762407/2000000000 : ℝ), (4238438831/10000000000 : ℝ), (449287043/1000000000 : ℝ)] ![(2082301959287/6250000000000 : ℝ), (32054090162281/100000000000000 : ℝ), (6925815694679/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(872762407/2000000000 : ℝ)|^8341 ≤ (2082301959287/6250000000000 : ℝ)^6293
        have hw : |(872762407/2000000000 : ℝ)|=(872762407/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4238438831/10000000000 : ℝ)|^8341 ≤ (32054090162281/100000000000000 : ℝ)^6293
        have hw : |(4238438831/10000000000 : ℝ)|=(4238438831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(449287043/1000000000 : ℝ)|^8341 ≤ (6925815694679/20000000000000 : ℝ)^6293
        have hw : |(449287043/1000000000 : ℝ)|=(449287043/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s6_4 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2163996583/10000000000 : ℝ)*x 0 + (1053168681/2000000000 : ℝ)*x 1 + (337058467/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163996583/10000000000 : ℝ)^8341 ≤ (13149881124143/100000000000000 : ℝ)^6293 := by
    have hnat : (2163996583 : ℕ)^8341*100000000000000^6293 ≤ 13149881124143^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163996583 10000000000 13149881124143 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053168681/2000000000 : ℝ)^8341 ≤ (5342348439743/12500000000000 : ℝ)^6293 := by
    have hnat : (1053168681 : ℕ)^8341*12500000000000^6293 ≤ 5342348439743^6293*2000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053168681 2000000000 5342348439743 12500000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337058467/625000000 : ℝ)^8341 ≤ (22055665672249/50000000000000 : ℝ)^6293 := by
    have hnat : (337058467 : ℕ)^8341*50000000000000^6293 ≤ 22055665672249^6293*625000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337058467 625000000 22055665672249 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2163996583/10000000000 : ℝ), (1053168681/2000000000 : ℝ), (337058467/625000000 : ℝ)] ![(13149881124143/100000000000000 : ℝ), (5342348439743/12500000000000 : ℝ), (22055665672249/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2163996583/10000000000 : ℝ)|^8341 ≤ (13149881124143/100000000000000 : ℝ)^6293
        have hw : |(-2163996583/10000000000 : ℝ)|=(2163996583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053168681/2000000000 : ℝ)|^8341 ≤ (5342348439743/12500000000000 : ℝ)^6293
        have hw : |(1053168681/2000000000 : ℝ)|=(1053168681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337058467/625000000 : ℝ)|^8341 ≤ (22055665672249/50000000000000 : ℝ)^6293
        have hw : |(337058467/625000000 : ℝ)|=(337058467/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s6_5 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312442097/10000000000 : ℝ)*x 0 + (-2101371289/10000000000 : ℝ)*x 1 + (5392935459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312442097/10000000000 : ℝ)^8341 ≤ (8648159429669/20000000000000 : ℝ)^6293 := by
    have hnat : (5312442097 : ℕ)^8341*20000000000000^6293 ≤ 8648159429669^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312442097 10000000000 8648159429669 20000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2101371289/10000000000 : ℝ)^8341 ≤ (6323935813891/50000000000000 : ℝ)^6293 := by
    have hnat : (2101371289 : ℕ)^8341*50000000000000^6293 ≤ 6323935813891^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101371289 10000000000 6323935813891 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392935459/10000000000 : ℝ)^8341 ≤ (1102783280089/2500000000000 : ℝ)^6293 := by
    have hnat : (5392935459 : ℕ)^8341*2500000000000^6293 ≤ 1102783280089^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392935459 10000000000 1102783280089 2500000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312442097/10000000000 : ℝ), (-2101371289/10000000000 : ℝ), (5392935459/10000000000 : ℝ)] ![(8648159429669/20000000000000 : ℝ), (6323935813891/50000000000000 : ℝ), (1102783280089/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312442097/10000000000 : ℝ)|^8341 ≤ (8648159429669/20000000000000 : ℝ)^6293
        have hw : |(5312442097/10000000000 : ℝ)|=(5312442097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2101371289/10000000000 : ℝ)|^8341 ≤ (6323935813891/50000000000000 : ℝ)^6293
        have hw : |(-2101371289/10000000000 : ℝ)|=(2101371289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392935459/10000000000 : ℝ)|^8341 ≤ (1102783280089/2500000000000 : ℝ)^6293
        have hw : |(5392935459/10000000000 : ℝ)|=(5392935459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s6_6 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (53124421/100000000 : ℝ)*x 0 + (1348233863/2500000000 : ℝ)*x 1 + (-420274259/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53124421/100000000 : ℝ)^8341 ≤ (43240797180711/100000000000000 : ℝ)^6293 := by
    have hnat : (53124421 : ℕ)^8341*100000000000000^6293 ≤ 43240797180711^6293*100000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53124421 100000000 43240797180711 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348233863/2500000000 : ℝ)^8341 ≤ (4411133112767/10000000000000 : ℝ)^6293 := by
    have hnat : (1348233863 : ℕ)^8341*10000000000000^6293 ≤ 4411133112767^6293*2500000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348233863 2500000000 4411133112767 10000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (420274259/2000000000 : ℝ)^8341 ≤ (49405748733/390625000000 : ℝ)^6293 := by
    have hnat : (420274259 : ℕ)^8341*390625000000^6293 ≤ 49405748733^6293*2000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420274259 2000000000 49405748733 390625000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53124421/100000000 : ℝ), (1348233863/2500000000 : ℝ), (-420274259/2000000000 : ℝ)] ![(43240797180711/100000000000000 : ℝ), (4411133112767/10000000000000 : ℝ), (49405748733/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53124421/100000000 : ℝ)|^8341 ≤ (43240797180711/100000000000000 : ℝ)^6293
        have hw : |(53124421/100000000 : ℝ)|=(53124421/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348233863/2500000000 : ℝ)|^8341 ≤ (4411133112767/10000000000000 : ℝ)^6293
        have hw : |(1348233863/2500000000 : ℝ)|=(1348233863/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-420274259/2000000000 : ℝ)|^8341 ≤ (49405748733/390625000000 : ℝ)^6293
        have hw : |(-420274259/2000000000 : ℝ)|=(420274259/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s6_7 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (545477733/1250000000 : ℝ)*x 0 + (4492227777/10000000000 : ℝ)*x 1 + (4239083839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545477733/1250000000 : ℝ)^8341 ≤ (33316930812963/100000000000000 : ℝ)^6293 := by
    have hnat : (545477733 : ℕ)^8341*100000000000000^6293 ≤ 33316930812963^6293*1250000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545477733 1250000000 33316930812963 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4492227777/10000000000 : ℝ)^8341 ≤ (17311256667691/50000000000000 : ℝ)^6293 := by
    have hnat : (4492227777 : ℕ)^8341*50000000000000^6293 ≤ 17311256667691^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492227777 10000000000 17311256667691 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4239083839/10000000000 : ℝ)^8341 ≤ (32060555835913/100000000000000 : ℝ)^6293 := by
    have hnat : (4239083839 : ℕ)^8341*100000000000000^6293 ≤ 32060555835913^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239083839 10000000000 32060555835913 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(545477733/1250000000 : ℝ), (4492227777/10000000000 : ℝ), (4239083839/10000000000 : ℝ)] ![(33316930812963/100000000000000 : ℝ), (17311256667691/50000000000000 : ℝ), (32060555835913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(545477733/1250000000 : ℝ)|^8341 ≤ (33316930812963/100000000000000 : ℝ)^6293
        have hw : |(545477733/1250000000 : ℝ)|=(545477733/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4492227777/10000000000 : ℝ)|^8341 ≤ (17311256667691/50000000000000 : ℝ)^6293
        have hw : |(4492227777/10000000000 : ℝ)|=(4492227777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4239083839/10000000000 : ℝ)|^8341 ≤ (32060555835913/100000000000000 : ℝ)^6293
        have hw : |(4239083839/10000000000 : ℝ)|=(4239083839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1148_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149590789/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14091/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2831/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5677/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (703/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14091/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2831/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14091/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2831/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14091/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2831/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14091/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2831/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14091/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2831/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14091/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2831/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2831/25000 : ℝ) ^ (2085/512 : ℝ) ≤ (14048700417431849/100000000000000000000 : ℝ) := by
    have hpowers : (2831/25000 : ℝ)^2085 ≤ (14048700417431849/100000000000000000000 : ℝ)^512 := by
      have hnat : (2831 : ℕ)^2085*100000000000000000000^512 ≤ 14048700417431849^512*25000^2085 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2831 25000 14048700417431849 100000000000000000000 2085 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2831/25000 : ℝ)) (X := (14048700417431849/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14091/100000 : ℝ) ^ (2085/512 : ℝ) ≤ (34218818320093387/100000000000000000000 : ℝ) := by
    have hpowers : (14091/100000 : ℝ)^2085 ≤ (34218818320093387/100000000000000000000 : ℝ)^512 := by
      have hnat : (14091 : ℕ)^2085*100000000000000000000^512 ≤ 34218818320093387^512*100000^2085 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14091 100000 34218818320093387 100000000000000000000 2085 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14091/100000 : ℝ)) (X := (34218818320093387/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014048700417431849/50000000000000000000 : ℝ) ≤ (1250086237078783/1250000000000000 : ℝ) ^ (2085/512 : ℝ) := by
    have hpowers : (50014048700417431849/50000000000000000000 : ℝ)^512 ≤ (1250086237078783/1250000000000000 : ℝ)^2085 := by
      have hnat : (50014048700417431849 : ℕ)^512*1250000000000000^2085 ≤ 1250086237078783^2085*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014048700417431849 50000000000000000000 1250086237078783 1250000000000000 512 2085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250086237078783/1250000000000000 : ℝ)) (X := (50014048700417431849/50000000000000000000 : ℝ)) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012066879684381309/25000000000000000000 : ℝ) ≤ (5000592529287221/5000000000000000 : ℝ) ^ (2085/512 : ℝ) := by
    have hpowers : (25012066879684381309/25000000000000000000 : ℝ)^512 ≤ (5000592529287221/5000000000000000 : ℝ)^2085 := by
      have hnat : (25012066879684381309 : ℕ)^512*5000000000000000^2085 ≤ 5000592529287221^2085*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012066879684381309 25000000000000000000 5000592529287221 5000000000000000 512 2085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000592529287221/5000000000000000 : ℝ)) (X := (25012066879684381309/25000000000000000000 : ℝ)) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034218818320093387/50000000000000000000 : ℝ) ≤ (500084011025931/500000000000000 : ℝ) ^ (2085/512 : ℝ) := by
    have hpowers : (50034218818320093387/50000000000000000000 : ℝ)^512 ≤ (500084011025931/500000000000000 : ℝ)^2085 := by
      have hnat : (50034218818320093387 : ℕ)^512*500000000000000^2085 ≤ 500084011025931^2085*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034218818320093387 50000000000000000000 500084011025931 500000000000000 512 2085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500084011025931/500000000000000 : ℝ)) (X := (50034218818320093387/50000000000000000000 : ℝ)) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14048700417431849/100000000000000000000 : ℝ) ≤ ((3457586814533024643/3458750000000000000 : ℝ)+2*(247580972089/138350000000000 : ℝ)*(2831/25000 : ℝ))^(2085/512 : ℝ) := by
    rw [show (3457586814533024643/3458750000000000000 : ℝ)+2*(247580972089/138350000000000 : ℝ)*(2831/25000 : ℝ)=(1250086237078783/1250000000000000 : ℝ) by norm_num, show 1+2*(14048700417431849/100000000000000000000 : ℝ)=(50014048700417431849/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34218818320093387/100000000000000000000 : ℝ)+(14048700417431849/100000000000000000000 : ℝ) ≤ ((3457586814533024643/3458750000000000000 : ℝ)+(247580972089/138350000000000 : ℝ)*((14091/100000 : ℝ)+(2831/25000 : ℝ)))^(2085/512 : ℝ) := by
    rw [show (3457586814533024643/3458750000000000000 : ℝ)+(247580972089/138350000000000 : ℝ)*((14091/100000 : ℝ)+(2831/25000 : ℝ))=(5000592529287221/5000000000000000 : ℝ) by norm_num, show 1+(34218818320093387/100000000000000000000 : ℝ)+(14048700417431849/100000000000000000000 : ℝ)=(25012066879684381309/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34218818320093387/100000000000000000000 : ℝ) ≤ ((3457586814533024643/3458750000000000000 : ℝ)+2*(247580972089/138350000000000 : ℝ)*(14091/100000 : ℝ))^(2085/512 : ℝ) := by
    rw [show (3457586814533024643/3458750000000000000 : ℝ)+2*(247580972089/138350000000000 : ℝ)*(14091/100000 : ℝ)=(500084011025931/500000000000000 : ℝ) by norm_num, show 1+2*(34218818320093387/100000000000000000000 : ℝ)=(50034218818320093387/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3457586814533024643/3458750000000000000 : ℝ)*(X 1 0+X 2 0)+(247580972089/138350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2085/512 : ℝ)) (lo := (2831/25000 : ℝ)) (hi := (14091/100000 : ℝ)) (c := (3457586814533024643/3458750000000000000 : ℝ)) (alpha := (247580972089/138350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3457586814533024643/3458750000000000000 : ℝ)*(X 0 1+X 2 1)+(247580972089/138350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2085/512 : ℝ)) (lo := (2831/25000 : ℝ)) (hi := (14091/100000 : ℝ)) (c := (3457586814533024643/3458750000000000000 : ℝ)) (alpha := (247580972089/138350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3457586814533024643/3458750000000000000 : ℝ)*(X 0 2+X 1 2)+(247580972089/138350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2085/512 : ℝ)) (lo := (2831/25000 : ℝ)) (hi := (14091/100000 : ℝ)) (c := (3457586814533024643/3458750000000000000 : ℝ)) (alpha := (247580972089/138350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-432798323/2000000000 : ℝ)*X 0 0+(53932593/100000000 : ℝ)*X 0 1+(2632760383/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344819573/10000000000 : ℝ)*X 1 0+(-222878593/1000000000 : ℝ)*X 1 1+(5265520767/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267240977/500000000 : ℝ)*X 2 0+(5265520793/10000000000 : ℝ)*X 2 1+(-2228785939/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((872762407/2000000000 : ℝ)*X 0 0+(4238438831/10000000000 : ℝ)*X 0 1+(449287043/1000000000 : ℝ)*X 0 2+(872762407/2000000000 : ℝ)*X 1 0+(4238438831/10000000000 : ℝ)*X 1 1+(449287043/1000000000 : ℝ)*X 1 2+(872762407/2000000000 : ℝ)*X 2 0+(4238438831/10000000000 : ℝ)*X 2 1+(449287043/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2163996583/10000000000 : ℝ)*X 0 0+(1053168681/2000000000 : ℝ)*X 0 1+(337058467/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312442097/10000000000 : ℝ)*X 1 0+(-2101371289/10000000000 : ℝ)*X 1 1+(5392935459/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((53124421/100000000 : ℝ)*X 2 0+(1348233863/2500000000 : ℝ)*X 2 1+(-420274259/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((545477733/1250000000 : ℝ)*X 0 0+(4492227777/10000000000 : ℝ)*X 0 1+(4239083839/10000000000 : ℝ)*X 0 2+(545477733/1250000000 : ℝ)*X 1 0+(4492227777/10000000000 : ℝ)*X 1 1+(4239083839/10000000000 : ℝ)*X 1 2+(545477733/1250000000 : ℝ)*X 2 0+(4492227777/10000000000 : ℝ)*X 2 1+(4239083839/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (588765198609990245521924731/86468750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (753226473/50000000000000 : ℝ)*(base19) + (1324753133/100000000000000 : ℝ)*(base23) + (35640487/50000000000000 : ℝ)*(lower2) + (196324051/100000000000000 : ℝ)*(upper3) + (1478729/2000000000000 : ℝ)*(upper5) + (5879474511052079/100000000000000 : ℝ)*(major0) + (5879474511052079/100000000000000 : ℝ)*(major1) + (73493431388151/1250000000000 : ℝ)*(major2) + (1957134037005659/25000000000000 : ℝ)*(sp0) + (3914287635780007/50000000000000 : ℝ)*(sp1) + (1957143863314957/25000000000000 : ℝ)*(sp2) + (491293649010883/12500000000000 : ℝ)*(sp3) + (1625199613/4000000000000 : ℝ)*(sp4) + (11412518827/50000000000000 : ℝ)*(sp7) + (3930372017124717/100000000000000 : ℝ)*(f.failure) + (48928604862581/625000000000 : ℝ)*(f.sum) + (29347690619621/3458750000000000000000000000 : ℝ)*base66 + (4350961047444742203/345875000000000000000000000000000 : ℝ)*base68 + (57121040985760811/8646875000000000000000000000000 : ℝ)*base69 + (7631470436646867203/345875000000000000000000000000000 : ℝ)*base72 + (89223652126719/13835000000000000000000000000 : ℝ)*base74 + (249095127769342061/8646875000000000000000000000000 : ℝ)*base75 + (4981369394219842203/345875000000000000000000000000000 : ℝ)*base78 + (3538475576658592203/345875000000000000000000000000000 : ℝ)*base80 + (5429404757207/3458750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (27431713/10000000000000000000000 : ℝ)*base89 + (27431713/10000000000000000000000 : ℝ)*base91 + (72568287/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (669816824706929772979964121/86468750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (731045249/50000000000000 : ℝ)*(base19) + (1574757877/100000000000000 : ℝ)*(base23) + (1870409/1250000000000 : ℝ)*(upper3) + (12986501/25000000000000 : ℝ)*(lower4) + (84017237/50000000000000 : ℝ)*(upper5) + (2954658095932051/50000000000000 : ℝ)*(major0) + (2954658095932051/50000000000000 : ℝ)*(major1) + (2954658095932051/50000000000000 : ℝ)*(major2) + (8063952391/20000000000000 : ℝ)*(sp1) + (8406631787/20000000000000 : ℝ)*(sp2) + (3934155616260491/50000000000000 : ℝ)*(sp4) + (7868269450668529/100000000000000 : ℝ)*(sp5) + (7868267624604169/100000000000000 : ℝ)*(sp6) + (987580223248923/25000000000000 : ℝ)*(sp7) + (987580223248923/25000000000000 : ℝ)*(f.failure) + (3934155616260491/50000000000000 : ℝ)*(f.sum) + (1840197180907/6917500000000000000000000000 : ℝ)*base66 + (600260380212632793/172937500000000000000000000000000 : ℝ)*base67 + (524098776622742207/172937500000000000000000000000000 : ℝ)*base70 + (935022412658007793/172937500000000000000000000000000 : ℝ)*base71 + (55666577598901/13835000000000000000000000000 : ℝ)*base73 + (853103567348257793/172937500000000000000000000000000 : ℝ)*base75 + (2161617209494007793/172937500000000000000000000000000 : ℝ)*base77 + (1750740388850554707/172937500000000000000000000000000 : ℝ)*base80 + (7893188955531/3458750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (15029753/2500000000000000000000 : ℝ)*base90 + (15029753/2500000000000000000000 : ℝ)*base92 + (15029753/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1148_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149590789/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14091/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2831/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5677/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (703/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1148_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1148_s7_0 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1082008557/5000000000 : ℝ)*x 0 + (1078590043/2000000000 : ℝ)*x 1 + (210632527/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082008557/5000000000 : ℝ)^8341 ≤ (1315004648641/10000000000000 : ℝ)^6293 := by
    have hnat : (1082008557 : ℕ)^8341*10000000000000^6293 ≤ 1315004648641^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082008557 5000000000 1315004648641 10000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078590043/2000000000 : ℝ)^8341 ≤ (8822298235863/20000000000000 : ℝ)^6293 := by
    have hnat : (1078590043 : ℕ)^8341*20000000000000^6293 ≤ 8822298235863^6293*2000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078590043 2000000000 8822298235863 20000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210632527/400000000 : ℝ)^8341 ≤ (21369231158279/50000000000000 : ℝ)^6293 := by
    have hnat : (210632527 : ℕ)^8341*50000000000000^6293 ≤ 21369231158279^6293*400000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210632527 400000000 21369231158279 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1082008557/5000000000 : ℝ), (1078590043/2000000000 : ℝ), (210632527/400000000 : ℝ)] ![(1315004648641/10000000000000 : ℝ), (8822298235863/20000000000000 : ℝ), (21369231158279/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1082008557/5000000000 : ℝ)|^8341 ≤ (1315004648641/10000000000000 : ℝ)^6293
        have hw : |(-1082008557/5000000000 : ℝ)|=(1082008557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078590043/2000000000 : ℝ)|^8341 ≤ (8822298235863/20000000000000 : ℝ)^6293
        have hw : |(1078590043/2000000000 : ℝ)|=(1078590043/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210632527/400000000 : ℝ)|^8341 ≤ (21369231158279/50000000000000 : ℝ)^6293
        have hw : |(210632527/400000000 : ℝ)|=(210632527/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s7_1 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672371067/5000000000 : ℝ)*x 0 + (-2228502049/10000000000 : ℝ)*x 1 + (2632906587/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672371067/5000000000 : ℝ)^8341 ≤ (43589609426747/100000000000000 : ℝ)^6293 := by
    have hnat : (2672371067 : ℕ)^8341*100000000000000^6293 ≤ 43589609426747^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672371067 5000000000 43589609426747 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2228502049/10000000000 : ℝ)^8341 ≤ (1708991032299/12500000000000 : ℝ)^6293 := by
    have hnat : (2228502049 : ℕ)^8341*12500000000000^6293 ≤ 1708991032299^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2228502049 10000000000 1708991032299 12500000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632906587/5000000000 : ℝ)^8341 ≤ (213692311529/500000000000 : ℝ)^6293 := by
    have hnat : (2632906587 : ℕ)^8341*500000000000^6293 ≤ 213692311529^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632906587 5000000000 213692311529 500000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672371067/5000000000 : ℝ), (-2228502049/10000000000 : ℝ), (2632906587/5000000000 : ℝ)] ![(43589609426747/100000000000000 : ℝ), (1708991032299/12500000000000 : ℝ), (213692311529/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672371067/5000000000 : ℝ)|^8341 ≤ (43589609426747/100000000000000 : ℝ)^6293
        have hw : |(2672371067/5000000000 : ℝ)|=(2672371067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2228502049/10000000000 : ℝ)|^8341 ≤ (1708991032299/12500000000000 : ℝ)^6293
        have hw : |(-2228502049/10000000000 : ℝ)|=(2228502049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632906587/5000000000 : ℝ)|^8341 ≤ (213692311529/500000000000 : ℝ)^6293
        have hw : |(2632906587/5000000000 : ℝ)|=(2632906587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s7_2 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672371067/5000000000 : ℝ)*x 0 + (2632906587/5000000000 : ℝ)*x 1 + (-2228502049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672371067/5000000000 : ℝ)^8341 ≤ (43589609426747/100000000000000 : ℝ)^6293 := by
    have hnat : (2672371067 : ℕ)^8341*100000000000000^6293 ≤ 43589609426747^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672371067 5000000000 43589609426747 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632906587/5000000000 : ℝ)^8341 ≤ (213692311529/500000000000 : ℝ)^6293 := by
    have hnat : (2632906587 : ℕ)^8341*500000000000^6293 ≤ 213692311529^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632906587 5000000000 213692311529 500000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2228502049/10000000000 : ℝ)^8341 ≤ (1708991032299/12500000000000 : ℝ)^6293 := by
    have hnat : (2228502049 : ℕ)^8341*12500000000000^6293 ≤ 1708991032299^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2228502049 10000000000 1708991032299 12500000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672371067/5000000000 : ℝ), (2632906587/5000000000 : ℝ), (-2228502049/10000000000 : ℝ)] ![(43589609426747/100000000000000 : ℝ), (213692311529/500000000000 : ℝ), (1708991032299/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672371067/5000000000 : ℝ)|^8341 ≤ (43589609426747/100000000000000 : ℝ)^6293
        have hw : |(2672371067/5000000000 : ℝ)|=(2672371067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632906587/5000000000 : ℝ)|^8341 ≤ (213692311529/500000000000 : ℝ)^6293
        have hw : |(2632906587/5000000000 : ℝ)|=(2632906587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2228502049/10000000000 : ℝ)|^8341 ≤ (1708991032299/12500000000000 : ℝ)^6293
        have hw : |(-2228502049/10000000000 : ℝ)|=(2228502049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s7_3 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2181913663/5000000000 : ℝ)*x 0 + (4239035873/10000000000 : ℝ)*x 1 + (898453887/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2181913663/5000000000 : ℝ)^8341 ≤ (6663397217119/20000000000000 : ℝ)^6293 := by
    have hnat : (2181913663 : ℕ)^8341*20000000000000^6293 ≤ 6663397217119^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181913663 5000000000 6663397217119 20000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4239035873/10000000000 : ℝ)^8341 ≤ (32060075005273/100000000000000 : ℝ)^6293 := by
    have hnat : (4239035873 : ℕ)^8341*100000000000000^6293 ≤ 32060075005273^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239035873 10000000000 32060075005273 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (898453887/2000000000 : ℝ)^8341 ≤ (6924587778191/20000000000000 : ℝ)^6293 := by
    have hnat : (898453887 : ℕ)^8341*20000000000000^6293 ≤ 6924587778191^6293*2000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898453887 2000000000 6924587778191 20000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2181913663/5000000000 : ℝ), (4239035873/10000000000 : ℝ), (898453887/2000000000 : ℝ)] ![(6663397217119/20000000000000 : ℝ), (32060075005273/100000000000000 : ℝ), (6924587778191/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2181913663/5000000000 : ℝ)|^8341 ≤ (6663397217119/20000000000000 : ℝ)^6293
        have hw : |(2181913663/5000000000 : ℝ)|=(2181913663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4239035873/10000000000 : ℝ)|^8341 ≤ (32060075005273/100000000000000 : ℝ)^6293
        have hw : |(4239035873/10000000000 : ℝ)|=(4239035873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(898453887/2000000000 : ℝ)|^8341 ≤ (6924587778191/20000000000000 : ℝ)^6293
        have hw : |(898453887/2000000000 : ℝ)|=(898453887/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s7_4 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1082010933/5000000000 : ℝ)*x 0 + (52661331/100000000 : ℝ)*x 1 + (1348157307/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082010933/5000000000 : ℝ)^8341 ≤ (6575042380193/50000000000000 : ℝ)^6293 := by
    have hnat : (1082010933 : ℕ)^8341*50000000000000^6293 ≤ 6575042380193^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082010933 5000000000 6575042380193 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52661331/100000000 : ℝ)^8341 ≤ (42741903963427/100000000000000 : ℝ)^6293 := by
    have hnat : (52661331 : ℕ)^8341*100000000000000^6293 ≤ 42741903963427^6293*100000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52661331 100000000 42741903963427 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348157307/2500000000 : ℝ)^8341 ≤ (44108011261759/100000000000000 : ℝ)^6293 := by
    have hnat : (1348157307 : ℕ)^8341*100000000000000^6293 ≤ 44108011261759^6293*2500000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348157307 2500000000 44108011261759 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1082010933/5000000000 : ℝ), (52661331/100000000 : ℝ), (1348157307/2500000000 : ℝ)] ![(6575042380193/50000000000000 : ℝ), (42741903963427/100000000000000 : ℝ), (44108011261759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1082010933/5000000000 : ℝ)|^8341 ≤ (6575042380193/50000000000000 : ℝ)^6293
        have hw : |(-1082010933/5000000000 : ℝ)|=(1082010933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(52661331/100000000 : ℝ)|^8341 ≤ (42741903963427/100000000000000 : ℝ)^6293
        have hw : |(52661331/100000000 : ℝ)|=(52661331/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348157307/2500000000 : ℝ)|^8341 ≤ (44108011261759/100000000000000 : ℝ)^6293
        have hw : |(1348157307/2500000000 : ℝ)|=(1348157307/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s7_5 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656258317/5000000000 : ℝ)*x 0 + (-1050842931/5000000000 : ℝ)*x 1 + (26963149/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656258317/5000000000 : ℝ)^8341 ≤ (21620800645197/50000000000000 : ℝ)^6293 := by
    have hnat : (2656258317 : ℕ)^8341*50000000000000^6293 ≤ 21620800645197^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656258317 5000000000 21620800645197 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1050842931/5000000000 : ℝ)^8341 ≤ (6325190621291/50000000000000 : ℝ)^6293 := by
    have hnat : (1050842931 : ℕ)^8341*50000000000000^6293 ≤ 6325190621291^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050842931 5000000000 6325190621291 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26963149/50000000 : ℝ)^8341 ≤ (11027004365731/25000000000000 : ℝ)^6293 := by
    have hnat : (26963149 : ℕ)^8341*25000000000000^6293 ≤ 11027004365731^6293*50000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26963149 50000000 11027004365731 25000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656258317/5000000000 : ℝ), (-1050842931/5000000000 : ℝ), (26963149/50000000 : ℝ)] ![(21620800645197/50000000000000 : ℝ), (6325190621291/50000000000000 : ℝ), (11027004365731/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656258317/5000000000 : ℝ)|^8341 ≤ (21620800645197/50000000000000 : ℝ)^6293
        have hw : |(2656258317/5000000000 : ℝ)|=(2656258317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1050842931/5000000000 : ℝ)|^8341 ≤ (6325190621291/50000000000000 : ℝ)^6293
        have hw : |(-1050842931/5000000000 : ℝ)|=(1050842931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(26963149/50000000 : ℝ)|^8341 ≤ (11027004365731/25000000000000 : ℝ)^6293
        have hw : |(26963149/50000000 : ℝ)|=(26963149/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s7_6 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656258503/5000000000 : ℝ)*x 0 + (5392629383/10000000000 : ℝ)*x 1 + (-525421481/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656258503/5000000000 : ℝ)^8341 ≤ (10810401325931/25000000000000 : ℝ)^6293 := by
    have hnat : (2656258503 : ℕ)^8341*25000000000000^6293 ≤ 10810401325931^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656258503 5000000000 10810401325931 25000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392629383/10000000000 : ℝ)^8341 ≤ (8821602588429/20000000000000 : ℝ)^6293 := by
    have hnat : (5392629383 : ℕ)^8341*20000000000000^6293 ≤ 8821602588429^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392629383 10000000000 8821602588429 20000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (525421481/2500000000 : ℝ)^8341 ≤ (632519086861/5000000000000 : ℝ)^6293 := by
    have hnat : (525421481 : ℕ)^8341*5000000000000^6293 ≤ 632519086861^6293*2500000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525421481 2500000000 632519086861 5000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656258503/5000000000 : ℝ), (5392629383/10000000000 : ℝ), (-525421481/2500000000 : ℝ)] ![(10810401325931/25000000000000 : ℝ), (8821602588429/20000000000000 : ℝ), (632519086861/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656258503/5000000000 : ℝ)|^8341 ≤ (10810401325931/25000000000000 : ℝ)^6293
        have hw : |(2656258503/5000000000 : ℝ)|=(2656258503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392629383/10000000000 : ℝ)|^8341 ≤ (8821602588429/20000000000000 : ℝ)^6293
        have hw : |(5392629383/10000000000 : ℝ)|=(5392629383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-525421481/2500000000 : ℝ)|^8341 ≤ (632519086861/5000000000000 : ℝ)^6293
        have hw : |(-525421481/2500000000 : ℝ)|=(525421481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s7_7 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4363836967/10000000000 : ℝ)*x 0 + (4491633013/10000000000 : ℝ)*x 1 + (4239674663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4363836967/10000000000 : ℝ)^8341 ≤ (16658541823807/50000000000000 : ℝ)^6293 := by
    have hnat : (4363836967 : ℕ)^8341*50000000000000^6293 ≤ 16658541823807^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363836967 10000000000 16658541823807 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4491633013/10000000000 : ℝ)^8341 ≤ (6923287537689/20000000000000 : ℝ)^6293 := by
    have hnat : (4491633013 : ℕ)^8341*20000000000000^6293 ≤ 6923287537689^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491633013 10000000000 6923287537689 20000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4239674663/10000000000 : ℝ)^8341 ≤ (32066478640561/100000000000000 : ℝ)^6293 := by
    have hnat : (4239674663 : ℕ)^8341*100000000000000^6293 ≤ 32066478640561^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239674663 10000000000 32066478640561 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4363836967/10000000000 : ℝ), (4491633013/10000000000 : ℝ), (4239674663/10000000000 : ℝ)] ![(16658541823807/50000000000000 : ℝ), (6923287537689/20000000000000 : ℝ), (32066478640561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4363836967/10000000000 : ℝ)|^8341 ≤ (16658541823807/50000000000000 : ℝ)^6293
        have hw : |(4363836967/10000000000 : ℝ)|=(4363836967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4491633013/10000000000 : ℝ)|^8341 ≤ (6923287537689/20000000000000 : ℝ)^6293
        have hw : |(4491633013/10000000000 : ℝ)|=(4491633013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4239674663/10000000000 : ℝ)|^8341 ≤ (32066478640561/100000000000000 : ℝ)^6293
        have hw : |(4239674663/10000000000 : ℝ)|=(4239674663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1148_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149590789/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (703/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5677/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (71/625 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14053/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (703/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5677/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (703/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5677/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (703/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5677/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (703/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5677/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (703/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5677/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (703/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5677/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (5677/50000 : ℝ) ^ (2085/512 : ℝ) ≤ (7100440751745969/50000000000000000000 : ℝ) := by
    have hpowers : (5677/50000 : ℝ)^2085 ≤ (7100440751745969/50000000000000000000 : ℝ)^512 := by
      have hnat : (5677 : ℕ)^2085*50000000000000000000^512 ≤ 7100440751745969^512*50000^2085 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5677 50000 7100440751745969 50000000000000000000 2085 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5677/50000 : ℝ)) (X := (7100440751745969/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have hpowhi : (703/5000 : ℝ) ^ (2085/512 : ℝ) ≤ (1059790277792311/3125000000000000000 : ℝ) := by
    have hpowers : (703/5000 : ℝ)^2085 ≤ (1059790277792311/3125000000000000000 : ℝ)^512 := by
      have hnat : (703 : ℕ)^2085*3125000000000000000^512 ≤ 1059790277792311^512*5000^2085 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        703 5000 1059790277792311 3125000000000000000 2085 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (703/5000 : ℝ)) (X := (1059790277792311/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007100440751745969/25000000000000000000 : ℝ) ≤ (5000348684531639/5000000000000000 : ℝ) ^ (2085/512 : ℝ) := by
    have hpowers : (25007100440751745969/25000000000000000000 : ℝ)^512 ≤ (5000348684531639/5000000000000000 : ℝ)^2085 := by
      have hnat : (25007100440751745969 : ℕ)^512*5000000000000000^2085 ≤ 5000348684531639^2085*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007100440751745969 25000000000000000000 5000348684531639 5000000000000000 512 2085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000348684531639/5000000000000000 : ℝ)) (X := (25007100440751745969/25000000000000000000 : ℝ)) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004811417039284589/10000000000000000000 : ℝ) ≤ (1000118129426657/1000000000000000 : ℝ) ^ (2085/512 : ℝ) := by
    have hpowers : (10004811417039284589/10000000000000000000 : ℝ)^512 ≤ (1000118129426657/1000000000000000 : ℝ)^2085 := by
      have hnat : (10004811417039284589 : ℕ)^512*1000000000000000^2085 ≤ 1000118129426657^2085*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004811417039284589 10000000000000000000 1000118129426657 1000000000000000 512 2085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000118129426657/1000000000000000 : ℝ)) (X := (10004811417039284589/10000000000000000000 : ℝ)) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (1563559790277792311/1562500000000000000 : ℝ) ≤ (5000832609734931/5000000000000000 : ℝ) ^ (2085/512 : ℝ) := by
    have hpowers : (1563559790277792311/1562500000000000000 : ℝ)^512 ≤ (5000832609734931/5000000000000000 : ℝ)^2085 := by
      have hnat : (1563559790277792311 : ℕ)^512*5000000000000000^2085 ≤ 5000832609734931^2085*1562500000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563559790277792311 1562500000000000000 5000832609734931 5000000000000000 512 2085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000832609734931/5000000000000000 : ℝ)) (X := (1563559790277792311/1562500000000000000 : ℝ)) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7100440751745969/50000000000000000000 : ℝ) ≤ ((6762724526792218883/6765000000000000000 : ℝ)+2*(120981300823/67650000000000 : ℝ)*(5677/50000 : ℝ))^(2085/512 : ℝ) := by
    rw [show (6762724526792218883/6765000000000000000 : ℝ)+2*(120981300823/67650000000000 : ℝ)*(5677/50000 : ℝ)=(5000348684531639/5000000000000000 : ℝ) by norm_num, show 1+2*(7100440751745969/50000000000000000000 : ℝ)=(25007100440751745969/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1059790277792311/3125000000000000000 : ℝ)+(7100440751745969/50000000000000000000 : ℝ) ≤ ((6762724526792218883/6765000000000000000 : ℝ)+(120981300823/67650000000000 : ℝ)*((703/5000 : ℝ)+(5677/50000 : ℝ)))^(2085/512 : ℝ) := by
    rw [show (6762724526792218883/6765000000000000000 : ℝ)+(120981300823/67650000000000 : ℝ)*((703/5000 : ℝ)+(5677/50000 : ℝ))=(1000118129426657/1000000000000000 : ℝ) by norm_num, show 1+(1059790277792311/3125000000000000000 : ℝ)+(7100440751745969/50000000000000000000 : ℝ)=(10004811417039284589/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1059790277792311/3125000000000000000 : ℝ) ≤ ((6762724526792218883/6765000000000000000 : ℝ)+2*(120981300823/67650000000000 : ℝ)*(703/5000 : ℝ))^(2085/512 : ℝ) := by
    rw [show (6762724526792218883/6765000000000000000 : ℝ)+2*(120981300823/67650000000000 : ℝ)*(703/5000 : ℝ)=(5000832609734931/5000000000000000 : ℝ) by norm_num, show 1+2*(1059790277792311/3125000000000000000 : ℝ)=(1563559790277792311/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6762724526792218883/6765000000000000000 : ℝ)*(X 1 0+X 2 0)+(120981300823/67650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2085/512 : ℝ)) (lo := (5677/50000 : ℝ)) (hi := (703/5000 : ℝ)) (c := (6762724526792218883/6765000000000000000 : ℝ)) (alpha := (120981300823/67650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6762724526792218883/6765000000000000000 : ℝ)*(X 0 1+X 2 1)+(120981300823/67650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2085/512 : ℝ)) (lo := (5677/50000 : ℝ)) (hi := (703/5000 : ℝ)) (c := (6762724526792218883/6765000000000000000 : ℝ)) (alpha := (120981300823/67650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6762724526792218883/6765000000000000000 : ℝ)*(X 0 2+X 1 2)+(120981300823/67650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2085/512 : ℝ)) (lo := (5677/50000 : ℝ)) (hi := (703/5000 : ℝ)) (c := (6762724526792218883/6765000000000000000 : ℝ)) (alpha := (120981300823/67650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1082008557/5000000000 : ℝ)*X 0 0+(1078590043/2000000000 : ℝ)*X 0 1+(210632527/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672371067/5000000000 : ℝ)*X 1 0+(-2228502049/10000000000 : ℝ)*X 1 1+(2632906587/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672371067/5000000000 : ℝ)*X 2 0+(2632906587/5000000000 : ℝ)*X 2 1+(-2228502049/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2181913663/5000000000 : ℝ)*X 0 0+(4239035873/10000000000 : ℝ)*X 0 1+(898453887/2000000000 : ℝ)*X 0 2+(2181913663/5000000000 : ℝ)*X 1 0+(4239035873/10000000000 : ℝ)*X 1 1+(898453887/2000000000 : ℝ)*X 1 2+(2181913663/5000000000 : ℝ)*X 2 0+(4239035873/10000000000 : ℝ)*X 2 1+(898453887/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1082010933/5000000000 : ℝ)*X 0 0+(52661331/100000000 : ℝ)*X 0 1+(1348157307/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656258317/5000000000 : ℝ)*X 1 0+(-1050842931/5000000000 : ℝ)*X 1 1+(26963149/50000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656258503/5000000000 : ℝ)*X 2 0+(5392629383/10000000000 : ℝ)*X 2 1+(-525421481/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4363836967/10000000000 : ℝ)*X 0 0+(4491633013/10000000000 : ℝ)*X 0 1+(4239674663/10000000000 : ℝ)*X 0 2+(4363836967/10000000000 : ℝ)*X 1 0+(4491633013/10000000000 : ℝ)*X 1 1+(4239674663/10000000000 : ℝ)*X 1 2+(4363836967/10000000000 : ℝ)*X 2 0+(4491633013/10000000000 : ℝ)*X 2 1+(4239674663/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (103791376443849510675821841/11275000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1819313337/100000000000000 : ℝ)*(base19) + (1689396967/100000000000000 : ℝ)*(base23) + (69436951/100000000000000 : ℝ)*(lower2) + (233076033/100000000000000 : ℝ)*(upper3) + (136994051/100000000000000 : ℝ)*(upper5) + (1181460484639027/20000000000000 : ℝ)*(major0) + (1181460484639027/20000000000000 : ℝ)*(major1) + (11537700045303/195312500000 : ℝ)*(major2) + (1573116071108981/20000000000000 : ℝ)*(sp0) + (7865628012170319/100000000000000 : ℝ)*(sp1) + (7865628142086689/100000000000000 : ℝ)*(sp2) + (987236945478467/25000000000000 : ℝ)*(sp3) + (39580751/80000000000 : ℝ)*(sp4) + (26926144617/100000000000000 : ℝ)*(sp7) + (1974487354029243/50000000000000 : ℝ)*(f.failure) + (983203728935457/12500000000000 : ℝ)*(f.sum) + (9388410097307/1691250000000000000000000000 : ℝ)*base65 + (445761112241293159/135300000000000000000000000000000 : ℝ)*base68 + (32049726998576659/21140625000000000000000000000000 : ℝ)*base69 + (2177381519394193159/135300000000000000000000000000000 : ℝ)*base72 + (40043551291223/6765000000000000000000000000 : ℝ)*base73 + (7353037862630951/1321289062500000000000000000000 : ℝ)*base76 + (123853926261551053/45100000000000000000000000000000 : ℝ)*base78 + (779743259545351053/45100000000000000000000000000000 : ℝ)*base80 + (716218496659/169125000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (39442727/5000000000000000000000 : ℝ)*base89 + (39442727/5000000000000000000000 : ℝ)*base91 + (10557273/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (515563208274553390609238217/112750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (83019963/50000000000000 : ℝ)*(base15) + (9064573/6250000000000 : ℝ)*(lower2) + (29132119/50000000000000 : ℝ)*(upper3) + (9800253/25000000000000 : ℝ)*(upper4) + (5937159318216849/100000000000000 : ℝ)*(major0) + (5937159318216849/100000000000000 : ℝ)*(major1) + (118743186364337/2000000000000 : ℝ)*(major2) + (24001946169/100000000000000 : ℝ)*(sp1) + (14067370793/100000000000000 : ℝ)*(sp2) + (9890554157/100000000000000 : ℝ)*(sp3) + (7905384729530991/100000000000000 : ℝ)*(sp4) + (123521258774139/1562500000000 : ℝ)*(sp5) + (3952685331080099/50000000000000 : ℝ)*(sp6) + (1984461931963889/50000000000000 : ℝ)*(sp7) + (1984466877240967/50000000000000 : ℝ)*(f.failure) + (7905384729530991/100000000000000 : ℝ)*(f.sum) + (16499014118753/6765000000000000000000000000 : ℝ)*base66 + (9900003363115940333/676500000000000000000000000000000 : ℝ)*base68 + (13466866690780039/1230000000000000000000000000000 : ℝ)*base70 + (3047437494944559667/676500000000000000000000000000000 : ℝ)*base71 + (29174826252353/6765000000000000000000000000 : ℝ)*base74 + (15641661988120039/1230000000000000000000000000000 : ℝ)*base76 + (7180056745582580111/225500000000000000000000000000000 : ℝ)*base78 + (2431173553524080111/225500000000000000000000000000000 : ℝ)*base80 + (1364026870659/1127500000000000000000000000 : ℝ)*base81 + (53347037/5000000000000000000000 : ℝ)*base90 + (53347037/5000000000000000000000 : ℝ)*base92 + (103347037/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1148_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149590789/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (703/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5677/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (71/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14053/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1148_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1148_s8_0 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-86561001/400000000 : ℝ)*x 0 + (5392883841/10000000000 : ℝ)*x 1 + (5265874143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86561001/400000000 : ℝ)^8341 ≤ (1643763775487/12500000000000 : ℝ)^6293 := by
    have hnat : (86561001 : ℕ)^8341*12500000000000^6293 ≤ 1643763775487^6293*400000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86561001 400000000 1643763775487 12500000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392883841/10000000000 : ℝ)^8341 ≤ (22055385796547/50000000000000 : ℝ)^6293 := by
    have hnat : (5392883841 : ℕ)^8341*50000000000000^6293 ≤ 22055385796547^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392883841 10000000000 22055385796547 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265874143/10000000000 : ℝ)^8341 ≤ (53423897731/125000000000 : ℝ)^6293 := by
    have hnat : (5265874143 : ℕ)^8341*125000000000^6293 ≤ 53423897731^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265874143 10000000000 53423897731 125000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-86561001/400000000 : ℝ), (5392883841/10000000000 : ℝ), (5265874143/10000000000 : ℝ)] ![(1643763775487/12500000000000 : ℝ), (22055385796547/50000000000000 : ℝ), (53423897731/125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-86561001/400000000 : ℝ)|^8341 ≤ (1643763775487/12500000000000 : ℝ)^6293
        have hw : |(-86561001/400000000 : ℝ)|=(86561001/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392883841/10000000000 : ℝ)|^8341 ≤ (22055385796547/50000000000000 : ℝ)^6293
        have hw : |(5392883841/10000000000 : ℝ)|=(5392883841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265874143/10000000000 : ℝ)|^8341 ≤ (53423897731/125000000000 : ℝ)^6293
        have hw : |(5265874143/10000000000 : ℝ)|=(5265874143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s8_1 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068944957/2000000000 : ℝ)*x 0 + (-2228444457/10000000000 : ℝ)*x 1 + (263293707/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068944957/2000000000 : ℝ)^8341 ≤ (21794710944039/50000000000000 : ℝ)^6293 := by
    have hnat : (1068944957 : ℕ)^8341*50000000000000^6293 ≤ 21794710944039^6293*2000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068944957 2000000000 21794710944039 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2228444457/10000000000 : ℝ)^8341 ≤ (13671459944051/100000000000000 : ℝ)^6293 := by
    have hnat : (2228444457 : ℕ)^8341*100000000000000^6293 ≤ 13671459944051^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2228444457 10000000000 13671459944051 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263293707/500000000 : ℝ)^8341 ≤ (42739118152527/100000000000000 : ℝ)^6293 := by
    have hnat : (263293707 : ℕ)^8341*100000000000000^6293 ≤ 42739118152527^6293*500000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263293707 500000000 42739118152527 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068944957/2000000000 : ℝ), (-2228444457/10000000000 : ℝ), (263293707/500000000 : ℝ)] ![(21794710944039/50000000000000 : ℝ), (13671459944051/100000000000000 : ℝ), (42739118152527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068944957/2000000000 : ℝ)|^8341 ≤ (21794710944039/50000000000000 : ℝ)^6293
        have hw : |(1068944957/2000000000 : ℝ)|=(1068944957/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2228444457/10000000000 : ℝ)|^8341 ≤ (13671459944051/100000000000000 : ℝ)^6293
        have hw : |(-2228444457/10000000000 : ℝ)|=(2228444457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263293707/500000000 : ℝ)|^8341 ≤ (42739118152527/100000000000000 : ℝ)^6293
        have hw : |(263293707/500000000 : ℝ)|=(263293707/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s8_2 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344724783/10000000000 : ℝ)*x 0 + (2632937071/5000000000 : ℝ)*x 1 + (-2228444457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344724783/10000000000 : ℝ)^8341 ≤ (43589421866459/100000000000000 : ℝ)^6293 := by
    have hnat : (5344724783 : ℕ)^8341*100000000000000^6293 ≤ 43589421866459^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344724783 10000000000 43589421866459 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632937071/5000000000 : ℝ)^8341 ≤ (21369559087021/50000000000000 : ℝ)^6293 := by
    have hnat : (2632937071 : ℕ)^8341*50000000000000^6293 ≤ 21369559087021^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632937071 5000000000 21369559087021 50000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2228444457/10000000000 : ℝ)^8341 ≤ (13671459944051/100000000000000 : ℝ)^6293 := by
    have hnat : (2228444457 : ℕ)^8341*100000000000000^6293 ≤ 13671459944051^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2228444457 10000000000 13671459944051 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344724783/10000000000 : ℝ), (2632937071/5000000000 : ℝ), (-2228444457/10000000000 : ℝ)] ![(43589421866459/100000000000000 : ℝ), (21369559087021/50000000000000 : ℝ), (13671459944051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344724783/10000000000 : ℝ)|^8341 ≤ (43589421866459/100000000000000 : ℝ)^6293
        have hw : |(5344724783/10000000000 : ℝ)|=(5344724783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632937071/5000000000 : ℝ)|^8341 ≤ (21369559087021/50000000000000 : ℝ)^6293
        have hw : |(2632937071/5000000000 : ℝ)|=(2632937071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2228444457/10000000000 : ℝ)|^8341 ≤ (13671459944051/100000000000000 : ℝ)^6293
        have hw : |(-2228444457/10000000000 : ℝ)|=(2228444457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s8_3 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1090957639/2500000000 : ℝ)*x 0 + (132473821/312500000 : ℝ)*x 1 + (4492142199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090957639/2500000000 : ℝ)^8341 ≤ (6663403754309/20000000000000 : ℝ)^6293 := by
    have hnat : (1090957639 : ℕ)^8341*20000000000000^6293 ≤ 6663403754309^6293*2500000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090957639 2500000000 6663403754309 20000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (132473821/312500000 : ℝ)^8341 ≤ (32061342083933/100000000000000 : ℝ)^6293 := by
    have hnat : (132473821 : ℕ)^8341*100000000000000^6293 ≤ 32061342083933^6293*312500000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132473821 312500000 32061342083933 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4492142199/10000000000 : ℝ)^8341 ≤ (34621639120897/100000000000000 : ℝ)^6293 := by
    have hnat : (4492142199 : ℕ)^8341*100000000000000^6293 ≤ 34621639120897^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492142199 10000000000 34621639120897 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1090957639/2500000000 : ℝ), (132473821/312500000 : ℝ), (4492142199/10000000000 : ℝ)] ![(6663403754309/20000000000000 : ℝ), (32061342083933/100000000000000 : ℝ), (34621639120897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1090957639/2500000000 : ℝ)|^8341 ≤ (6663403754309/20000000000000 : ℝ)^6293
        have hw : |(1090957639/2500000000 : ℝ)|=(1090957639/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(132473821/312500000 : ℝ)|^8341 ≤ (32061342083933/100000000000000 : ℝ)^6293
        have hw : |(132473821/312500000 : ℝ)|=(132473821/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4492142199/10000000000 : ℝ)|^8341 ≤ (34621639120897/100000000000000 : ℝ)^6293
        have hw : |(4492142199/10000000000 : ℝ)|=(4492142199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s8_4 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-54100747/250000000 : ℝ)*x 0 + (2633096553/5000000000 : ℝ)*x 1 + (539256373/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (54100747/250000000 : ℝ)^8341 ≤ (1315014930751/10000000000000 : ℝ)^6293 := by
    have hnat : (54100747 : ℕ)^8341*10000000000000^6293 ≤ 1315014930751^6293*250000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54100747 250000000 1315014930751 10000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633096553/5000000000 : ℝ)^8341 ≤ (42742549495619/100000000000000 : ℝ)^6293 := by
    have hnat : (2633096553 : ℕ)^8341*100000000000000^6293 ≤ 42742549495619^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633096553 5000000000 42742549495619 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539256373/1000000000 : ℝ)^8341 ≤ (44107301186329/100000000000000 : ℝ)^6293 := by
    have hnat : (539256373 : ℕ)^8341*100000000000000^6293 ≤ 44107301186329^6293*1000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539256373 1000000000 44107301186329 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-54100747/250000000 : ℝ), (2633096553/5000000000 : ℝ), (539256373/1000000000 : ℝ)] ![(1315014930751/10000000000000 : ℝ), (42742549495619/100000000000000 : ℝ), (44107301186329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-54100747/250000000 : ℝ)|^8341 ≤ (1315014930751/10000000000000 : ℝ)^6293
        have hw : |(-54100747/250000000 : ℝ)|=(54100747/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633096553/5000000000 : ℝ)|^8341 ≤ (42742549495619/100000000000000 : ℝ)^6293
        have hw : |(2633096553/5000000000 : ℝ)|=(2633096553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539256373/1000000000 : ℝ)|^8341 ≤ (44107301186329/100000000000000 : ℝ)^6293
        have hw : |(539256373/1000000000 : ℝ)|=(539256373/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s8_5 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656265997/5000000000 : ℝ)*x 0 + (-525438719/2500000000 : ℝ)*x 1 + (2696281863/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656265997/5000000000 : ℝ)^8341 ≤ (43241767002133/100000000000000 : ℝ)^6293 := by
    have hnat : (2656265997 : ℕ)^8341*100000000000000^6293 ≤ 43241767002133^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656265997 5000000000 43241767002133 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (525438719/2500000000 : ℝ)^8341 ≤ (2530186368393/20000000000000 : ℝ)^6293 := by
    have hnat : (525438719 : ℕ)^8341*20000000000000^6293 ≤ 2530186368393^6293*2500000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525438719 2500000000 2530186368393 20000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696281863/5000000000 : ℝ)^8341 ≤ (11026825285741/25000000000000 : ℝ)^6293 := by
    have hnat : (2696281863 : ℕ)^8341*25000000000000^6293 ≤ 11026825285741^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696281863 5000000000 11026825285741 25000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656265997/5000000000 : ℝ), (-525438719/2500000000 : ℝ), (2696281863/5000000000 : ℝ)] ![(43241767002133/100000000000000 : ℝ), (2530186368393/20000000000000 : ℝ), (11026825285741/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656265997/5000000000 : ℝ)|^8341 ≤ (43241767002133/100000000000000 : ℝ)^6293
        have hw : |(2656265997/5000000000 : ℝ)|=(2656265997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-525438719/2500000000 : ℝ)|^8341 ≤ (2530186368393/20000000000000 : ℝ)^6293
        have hw : |(-525438719/2500000000 : ℝ)|=(525438719/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696281863/5000000000 : ℝ)|^8341 ≤ (11026825285741/25000000000000 : ℝ)^6293
        have hw : |(2696281863/5000000000 : ℝ)|=(2696281863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s8_6 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312531999/10000000000 : ℝ)*x 0 + (134814093/250000000 : ℝ)*x 1 + (-1050877439/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312531999/10000000000 : ℝ)^8341 ≤ (10810441764019/25000000000000 : ℝ)^6293 := by
    have hnat : (5312531999 : ℕ)^8341*25000000000000^6293 ≤ 10810441764019^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312531999 10000000000 10810441764019 25000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134814093/250000000 : ℝ)^8341 ≤ (44107301077917/100000000000000 : ℝ)^6293 := by
    have hnat : (134814093 : ℕ)^8341*100000000000000^6293 ≤ 44107301077917^6293*250000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134814093 250000000 44107301077917 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1050877439/5000000000 : ℝ)^8341 ≤ (12650931857921/100000000000000 : ℝ)^6293 := by
    have hnat : (1050877439 : ℕ)^8341*100000000000000^6293 ≤ 12650931857921^6293*5000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050877439 5000000000 12650931857921 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312531999/10000000000 : ℝ), (134814093/250000000 : ℝ), (-1050877439/5000000000 : ℝ)] ![(10810441764019/25000000000000 : ℝ), (44107301077917/100000000000000 : ℝ), (12650931857921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312531999/10000000000 : ℝ)|^8341 ≤ (10810441764019/25000000000000 : ℝ)^6293
        have hw : |(5312531999/10000000000 : ℝ)|=(5312531999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(134814093/250000000 : ℝ)|^8341 ≤ (44107301077917/100000000000000 : ℝ)^6293
        have hw : |(134814093/250000000 : ℝ)|=(134814093/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1050877439/5000000000 : ℝ)|^8341 ≤ (12650931857921/100000000000000 : ℝ)^6293
        have hw : |(-1050877439/5000000000 : ℝ)|=(1050877439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1148_s8_7 (p : ℝ) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (872768047/2000000000 : ℝ)*x 0 + (4491506873/10000000000 : ℝ)*x 1 + (529974987/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872768047/2000000000 : ℝ)^8341 ≤ (2082319794883/6250000000000 : ℝ)^6293 := by
    have hnat : (872768047 : ℕ)^8341*6250000000000^6293 ≤ 2082319794883^6293*2000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872768047 2000000000 2082319794883 6250000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4491506873/10000000000 : ℝ)^8341 ≤ (34615149173857/100000000000000 : ℝ)^6293 := by
    have hnat : (4491506873 : ℕ)^8341*100000000000000^6293 ≤ 34615149173857^6293*10000000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491506873 10000000000 34615149173857 100000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (529974987/1250000000 : ℝ)^8341 ≤ (8016933523059/25000000000000 : ℝ)^6293 := by
    have hnat : (529974987 : ℕ)^8341*25000000000000^6293 ≤ 8016933523059^6293*1250000000^8341 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529974987 1250000000 8016933523059 25000000000000 8341 6293 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8341/2048 : ℝ)) 8341 6293 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(872768047/2000000000 : ℝ), (4491506873/10000000000 : ℝ), (529974987/1250000000 : ℝ)] ![(2082319794883/6250000000000 : ℝ), (34615149173857/100000000000000 : ℝ), (8016933523059/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(872768047/2000000000 : ℝ)|^8341 ≤ (2082319794883/6250000000000 : ℝ)^6293
        have hw : |(872768047/2000000000 : ℝ)|=(872768047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4491506873/10000000000 : ℝ)|^8341 ≤ (34615149173857/100000000000000 : ℝ)^6293
        have hw : |(4491506873/10000000000 : ℝ)|=(4491506873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(529974987/1250000000 : ℝ)|^8341 ≤ (8016933523059/25000000000000 : ℝ)^6293
        have hw : |(529974987/1250000000 : ℝ)|=(529974987/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1148_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149590789/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14053/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (71/625 : ℝ)*pair X i i ≤ pair X i h) :
    (5681/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3513/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14053/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (71/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14053/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (71/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14053/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (71/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14053/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (71/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14053/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (71/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14053/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (71/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (71/625 : ℝ) ^ (2085/512 : ℝ) ≤ (1778933293647681/12500000000000000000 : ℝ) := by
    have hpowers : (71/625 : ℝ)^2085 ≤ (1778933293647681/12500000000000000000 : ℝ)^512 := by
      have hnat : (71 : ℕ)^2085*12500000000000000000^512 ≤ 1778933293647681^512*625^2085 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        71 625 1778933293647681 12500000000000000000 2085 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (71/625 : ℝ)) (X := (1778933293647681/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14053/100000 : ℝ) ^ (2085/512 : ℝ) ≤ (33844584169866879/100000000000000000000 : ℝ) := by
    have hpowers : (14053/100000 : ℝ)^2085 ≤ (33844584169866879/100000000000000000000 : ℝ)^512 := by
      have hnat : (14053 : ℕ)^2085*100000000000000000000^512 ≤ 33844584169866879^512*100000^2085 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14053 100000 33844584169866879 100000000000000000000 2085 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14053/100000 : ℝ)) (X := (33844584169866879/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251778933293647681/6250000000000000000 : ℝ) ≤ (5000349435422901/5000000000000000 : ℝ) ^ (2085/512 : ℝ) := by
    have hpowers : (6251778933293647681/6250000000000000000 : ℝ)^512 ≤ (5000349435422901/5000000000000000 : ℝ)^2085 := by
      have hnat : (6251778933293647681 : ℕ)^512*5000000000000000^2085 ≤ 5000349435422901^2085*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251778933293647681 6250000000000000000 5000349435422901 5000000000000000 512 2085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000349435422901/5000000000000000 : ℝ)) (X := (6251778933293647681/6250000000000000000 : ℝ)) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048076050519048327/100000000000000000000 : ℝ) ≤ (2500295089630233/2500000000000000 : ℝ) ^ (2085/512 : ℝ) := by
    have hpowers : (100048076050519048327/100000000000000000000 : ℝ)^512 ≤ (2500295089630233/2500000000000000 : ℝ)^2085 := by
      have hnat : (100048076050519048327 : ℕ)^512*2500000000000000^2085 ≤ 2500295089630233^2085*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048076050519048327 100000000000000000000 2500295089630233 2500000000000000 512 2085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500295089630233/2500000000000000 : ℝ)) (X := (100048076050519048327/100000000000000000000 : ℝ)) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033844584169866879/50000000000000000000 : ℝ) ≤ (5000830923098031/5000000000000000 : ℝ) ^ (2085/512 : ℝ) := by
    have hpowers : (50033844584169866879/50000000000000000000 : ℝ)^512 ≤ (5000830923098031/5000000000000000 : ℝ)^2085 := by
      have hnat : (50033844584169866879 : ℕ)^512*5000000000000000^2085 ≤ 5000830923098031^2085*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033844584169866879 50000000000000000000 5000830923098031 5000000000000000 512 2085 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000830923098031/5000000000000000 : ℝ)) (X := (50033844584169866879/50000000000000000000 : ℝ)) (by norm_num) 2085 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1778933293647681/12500000000000000000 : ℝ) ≤ ((13460471329604395593/13465000000000000000 : ℝ)+2*(48148767513/26930000000000 : ℝ)*(71/625 : ℝ))^(2085/512 : ℝ) := by
    rw [show (13460471329604395593/13465000000000000000 : ℝ)+2*(48148767513/26930000000000 : ℝ)*(71/625 : ℝ)=(5000349435422901/5000000000000000 : ℝ) by norm_num, show 1+2*(1778933293647681/12500000000000000000 : ℝ)=(6251778933293647681/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33844584169866879/100000000000000000000 : ℝ)+(1778933293647681/12500000000000000000 : ℝ) ≤ ((13460471329604395593/13465000000000000000 : ℝ)+(48148767513/26930000000000 : ℝ)*((14053/100000 : ℝ)+(71/625 : ℝ)))^(2085/512 : ℝ) := by
    rw [show (13460471329604395593/13465000000000000000 : ℝ)+(48148767513/26930000000000 : ℝ)*((14053/100000 : ℝ)+(71/625 : ℝ))=(2500295089630233/2500000000000000 : ℝ) by norm_num, show 1+(33844584169866879/100000000000000000000 : ℝ)+(1778933293647681/12500000000000000000 : ℝ)=(100048076050519048327/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33844584169866879/100000000000000000000 : ℝ) ≤ ((13460471329604395593/13465000000000000000 : ℝ)+2*(48148767513/26930000000000 : ℝ)*(14053/100000 : ℝ))^(2085/512 : ℝ) := by
    rw [show (13460471329604395593/13465000000000000000 : ℝ)+2*(48148767513/26930000000000 : ℝ)*(14053/100000 : ℝ)=(5000830923098031/5000000000000000 : ℝ) by norm_num, show 1+2*(33844584169866879/100000000000000000000 : ℝ)=(50033844584169866879/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13460471329604395593/13465000000000000000 : ℝ)*(X 1 0+X 2 0)+(48148767513/26930000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2085/512 : ℝ)) (lo := (71/625 : ℝ)) (hi := (14053/100000 : ℝ)) (c := (13460471329604395593/13465000000000000000 : ℝ)) (alpha := (48148767513/26930000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13460471329604395593/13465000000000000000 : ℝ)*(X 0 1+X 2 1)+(48148767513/26930000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2085/512 : ℝ)) (lo := (71/625 : ℝ)) (hi := (14053/100000 : ℝ)) (c := (13460471329604395593/13465000000000000000 : ℝ)) (alpha := (48148767513/26930000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13460471329604395593/13465000000000000000 : ℝ)*(X 0 2+X 1 2)+(48148767513/26930000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2085/512 : ℝ)) (lo := (71/625 : ℝ)) (hi := (14053/100000 : ℝ)) (c := (13460471329604395593/13465000000000000000 : ℝ)) (alpha := (48148767513/26930000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-86561001/400000000 : ℝ)*X 0 0+(5392883841/10000000000 : ℝ)*X 0 1+(5265874143/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068944957/2000000000 : ℝ)*X 1 0+(-2228444457/10000000000 : ℝ)*X 1 1+(263293707/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344724783/10000000000 : ℝ)*X 2 0+(2632937071/5000000000 : ℝ)*X 2 1+(-2228444457/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1090957639/2500000000 : ℝ)*X 0 0+(132473821/312500000 : ℝ)*X 0 1+(4492142199/10000000000 : ℝ)*X 0 2+(1090957639/2500000000 : ℝ)*X 1 0+(132473821/312500000 : ℝ)*X 1 1+(4492142199/10000000000 : ℝ)*X 1 2+(1090957639/2500000000 : ℝ)*X 2 0+(132473821/312500000 : ℝ)*X 2 1+(4492142199/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-54100747/250000000 : ℝ)*X 0 0+(2633096553/5000000000 : ℝ)*X 0 1+(539256373/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656265997/5000000000 : ℝ)*X 1 0+(-525438719/2500000000 : ℝ)*X 1 1+(2696281863/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312531999/10000000000 : ℝ)*X 2 0+(134814093/250000000 : ℝ)*X 2 1+(-1050877439/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((872768047/2000000000 : ℝ)*X 0 0+(4491506873/10000000000 : ℝ)*X 0 1+(529974987/1250000000 : ℝ)*X 0 2+(872768047/2000000000 : ℝ)*X 1 0+(4491506873/10000000000 : ℝ)*X 1 1+(529974987/1250000000 : ℝ)*X 1 2+(872768047/2000000000 : ℝ)*X 2 0+(4491506873/10000000000 : ℝ)*X 2 1+(529974987/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1148_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1811859721159669488865101873/673250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (533567101/100000000000000 : ℝ)*(base19) + (98978819/20000000000000 : ℝ)*(base23) + (19094967/100000000000000 : ℝ)*(lower2) + (3391993/5000000000000 : ℝ)*(upper3) + (40866873/100000000000000 : ℝ)*(upper5) + (5913170946930013/100000000000000 : ℝ)*(major0) + (5913170946930013/100000000000000 : ℝ)*(major1) + (5913170946930013/100000000000000 : ℝ)*(major2) + (3936714823763437/50000000000000 : ℝ)*(sp0) + (7873443510998457/100000000000000 : ℝ)*(sp1) + (3936721774835731/50000000000000 : ℝ)*(sp2) + (24705561830699/625000000000 : ℝ)*(sp3) + (3599259671/25000000000000 : ℝ)*(sp4) + (1966668873/25000000000000 : ℝ)*(sp7) + (988224439896833/25000000000000 : ℝ)*(f.failure) + (3936722022282779/50000000000000 : ℝ)*(f.sum) + (924906765027/168312500000000000000000000 : ℝ)*base66 + (14243228520540132709/1346500000000000000000000000000000 : ℝ)*base67 + (14873518125799867291/1346500000000000000000000000000000 : ℝ)*base70 + (17445006412238632709/1346500000000000000000000000000000 : ℝ)*base71 + (14247117182533/2693000000000000000000000000 : ℝ)*base74 + (6601499610226867291/1346500000000000000000000000000000 : ℝ)*base76 + (2317636361892132709/1346500000000000000000000000000000 : ℝ)*base77 + (20387065561671132709/1346500000000000000000000000000000 : ℝ)*base79 + (123887863843/336625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (2071237/2500000000000000000000 : ℝ)*base89 + (2071237/2500000000000000000000 : ℝ)*base91 + (2071237/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (281080025942413593438480189/42078125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (149131333/12500000000000 : ℝ)*(base19) + (13106899/1000000000000 : ℝ)*(base23) + (420345337/100000000000000 : ℝ)*(lower1) + (12617989/10000000000000 : ℝ)*(upper3) + (12833839/25000000000000 : ℝ)*(lower4) + (137886659/100000000000000 : ℝ)*(upper5) + (742878369327209/12500000000000 : ℝ)*(major0) + (742878369327209/12500000000000 : ℝ)*(major1) + (742878369327209/12500000000000 : ℝ)*(major2) + (447570573/20000000000000 : ℝ)*(sp2) + (494574842108349/6250000000000 : ℝ)*(sp4) + (7913196280682919/100000000000000 : ℝ)*(sp5) + (3956596962595409/50000000000000 : ℝ)*(sp6) + (3972856212836521/100000000000000 : ℝ)*(sp7) + (3972856212836521/100000000000000 : ℝ)*(f.failure) + (494574842108349/6250000000000 : ℝ)*(f.sum) + (8881352916577/2693000000000000000000000000 : ℝ)*base65 + (8944943412193222563/168312500000000000000000000000000 : ℝ)*base68 + (1277679639587589937/168312500000000000000000000000000 : ℝ)*base69 + (8494814817087277437/168312500000000000000000000000000 : ℝ)*base71 + (485239233939/538600000000000000000000000 : ℝ)*base73 + (28082137386794964937/168312500000000000000000000000000 : ℝ)*base75 + (125942318352089937/168312500000000000000000000000000 : ℝ)*base77 + (3091661130494402437/168312500000000000000000000000000 : ℝ)*base79 + (5337527056721/2693000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (95594931/10000000000000000000000 : ℝ)*base90 + (95594931/10000000000000000000000 : ℝ)*base92 + (95594931/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1148_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149590789/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14053/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (71/625 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5681/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3513/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1148_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1148_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149590789/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14091/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2831/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5681/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3513/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1148_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1148_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1148_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2085/512 : ℝ) ≤ p) (hpb : p ≤ (8341/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149590789/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14091/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2831/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5681/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3513/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1148_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
