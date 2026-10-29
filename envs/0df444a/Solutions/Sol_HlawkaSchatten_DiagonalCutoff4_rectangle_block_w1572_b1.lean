-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1572_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:27:55.378085+00:00
-- url     : https://prove2.me/submissions/ca71c41c-7582-4b3b-aac2-36e7fff415d2

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
theorem support_rectangle_w1572_s3_0 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-891321421/5000000000 : ℝ)*x 0 + (1356792111/2500000000 : ℝ)*x 1 + (260932951/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (891321421/5000000000 : ℝ)^4641 ≤ (1094044535993/10000000000000 : ℝ)^3617 := by
    have hnat : (891321421 : ℕ)^4641*10000000000000^3617 ≤ 1094044535993^3617*5000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      891321421 5000000000 1094044535993 10000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356792111/2500000000 : ℝ)^4641 ≤ (45648761508737/100000000000000 : ℝ)^3617 := by
    have hnat : (1356792111 : ℕ)^4641*100000000000000^3617 ≤ 45648761508737^3617*2500000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356792111 2500000000 45648761508737 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (260932951/500000000 : ℝ)^4641 ≤ (8682158623597/20000000000000 : ℝ)^3617 := by
    have hnat : (260932951 : ℕ)^4641*20000000000000^3617 ≤ 8682158623597^3617*500000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260932951 500000000 8682158623597 20000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-891321421/5000000000 : ℝ), (1356792111/2500000000 : ℝ), (260932951/500000000 : ℝ)] ![(1094044535993/10000000000000 : ℝ), (45648761508737/100000000000000 : ℝ), (8682158623597/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-891321421/5000000000 : ℝ)|^4641 ≤ (1094044535993/10000000000000 : ℝ)^3617
        have hw : |(-891321421/5000000000 : ℝ)|=(891321421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356792111/2500000000 : ℝ)|^4641 ≤ (45648761508737/100000000000000 : ℝ)^3617
        have hw : |(1356792111/2500000000 : ℝ)|=(1356792111/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(260932951/500000000 : ℝ)|^4641 ≤ (8682158623597/20000000000000 : ℝ)^3617
        have hw : |(260932951/500000000 : ℝ)|=(260932951/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s3_1 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337125047/2500000000 : ℝ)*x 0 + (-472336423/2500000000 : ℝ)*x 1 + (5218659029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337125047/2500000000 : ℝ)^4641 ≤ (44801488949737/100000000000000 : ℝ)^3617 := by
    have hnat : (1337125047 : ℕ)^4641*100000000000000^3617 ≤ 44801488949737^3617*2500000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337125047 2500000000 44801488949737 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (472336423/2500000000 : ℝ)^4641 ≤ (589385890643/5000000000000 : ℝ)^3617 := by
    have hnat : (472336423 : ℕ)^4641*5000000000000^3617 ≤ 589385890643^3617*2500000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      472336423 2500000000 589385890643 5000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218659029/10000000000 : ℝ)^4641 ≤ (21705396607023/50000000000000 : ℝ)^3617 := by
    have hnat : (5218659029 : ℕ)^4641*50000000000000^3617 ≤ 21705396607023^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218659029 10000000000 21705396607023 50000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337125047/2500000000 : ℝ), (-472336423/2500000000 : ℝ), (5218659029/10000000000 : ℝ)] ![(44801488949737/100000000000000 : ℝ), (589385890643/5000000000000 : ℝ), (21705396607023/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337125047/2500000000 : ℝ)|^4641 ≤ (44801488949737/100000000000000 : ℝ)^3617
        have hw : |(1337125047/2500000000 : ℝ)|=(1337125047/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-472336423/2500000000 : ℝ)|^4641 ≤ (589385890643/5000000000000 : ℝ)^3617
        have hw : |(-472336423/2500000000 : ℝ)|=(472336423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218659029/10000000000 : ℝ)|^4641 ≤ (21705396607023/50000000000000 : ℝ)^3617
        have hw : |(5218659029/10000000000 : ℝ)|=(5218659029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s3_2 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348500147/10000000000 : ℝ)*x 0 + (20385387/39062500 : ℝ)*x 1 + (-1889345691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348500147/10000000000 : ℝ)^4641 ≤ (44801488509073/100000000000000 : ℝ)^3617 := by
    have hnat : (5348500147 : ℕ)^4641*100000000000000^3617 ≤ 44801488509073^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348500147 10000000000 44801488509073 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20385387/39062500 : ℝ)^4641 ≤ (43410793673001/100000000000000 : ℝ)^3617 := by
    have hnat : (20385387 : ℕ)^4641*100000000000000^3617 ≤ 43410793673001^3617*39062500^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20385387 39062500 43410793673001 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1889345691/10000000000 : ℝ)^4641 ≤ (2357543560971/20000000000000 : ℝ)^3617 := by
    have hnat : (1889345691 : ℕ)^4641*20000000000000^3617 ≤ 2357543560971^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1889345691 10000000000 2357543560971 20000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348500147/10000000000 : ℝ), (20385387/39062500 : ℝ), (-1889345691/10000000000 : ℝ)] ![(44801488509073/100000000000000 : ℝ), (43410793673001/100000000000000 : ℝ), (2357543560971/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348500147/10000000000 : ℝ)|^4641 ≤ (44801488509073/100000000000000 : ℝ)^3617
        have hw : |(5348500147/10000000000 : ℝ)|=(5348500147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(20385387/39062500 : ℝ)|^4641 ≤ (43410793673001/100000000000000 : ℝ)^3617
        have hw : |(20385387/39062500 : ℝ)|=(20385387/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1889345691/10000000000 : ℝ)|^4641 ≤ (2357543560971/20000000000000 : ℝ)^3617
        have hw : |(-1889345691/10000000000 : ℝ)|=(1889345691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s3_3 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2121236027/5000000000 : ℝ)*x 0 + (1000455993/2500000000 : ℝ)*x 1 + (561836763/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2121236027/5000000000 : ℝ)^4641 ≤ (33280904101839/100000000000000 : ℝ)^3617 := by
    have hnat : (2121236027 : ℕ)^4641*100000000000000^3617 ≤ 33280904101839^3617*5000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121236027 5000000000 33280904101839 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1000455993/2500000000 : ℝ)^4641 ≤ (30878359129391/100000000000000 : ℝ)^3617 := by
    have hnat : (1000455993 : ℕ)^4641*100000000000000^3617 ≤ 30878359129391^3617*2500000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000455993 2500000000 30878359129391 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (561836763/1250000000 : ℝ)^4641 ≤ (7168147351521/20000000000000 : ℝ)^3617 := by
    have hnat : (561836763 : ℕ)^4641*20000000000000^3617 ≤ 7168147351521^3617*1250000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561836763 1250000000 7168147351521 20000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2121236027/5000000000 : ℝ), (1000455993/2500000000 : ℝ), (561836763/1250000000 : ℝ)] ![(33280904101839/100000000000000 : ℝ), (30878359129391/100000000000000 : ℝ), (7168147351521/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2121236027/5000000000 : ℝ)|^4641 ≤ (33280904101839/100000000000000 : ℝ)^3617
        have hw : |(2121236027/5000000000 : ℝ)|=(2121236027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1000455993/2500000000 : ℝ)|^4641 ≤ (30878359129391/100000000000000 : ℝ)^3617
        have hw : |(1000455993/2500000000 : ℝ)|=(1000455993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(561836763/1250000000 : ℝ)|^4641 ≤ (7168147351521/20000000000000 : ℝ)^3617
        have hw : |(561836763/1250000000 : ℝ)|=(561836763/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s3_4 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1782670449/10000000000 : ℝ)*x 0 + (2609881039/5000000000 : ℝ)*x 1 + (42391073/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1782670449/10000000000 : ℝ)^4641 ≤ (10940662757101/100000000000000 : ℝ)^3617 := by
    have hnat : (1782670449 : ℕ)^4641*100000000000000^3617 ≤ 10940662757101^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1782670449 10000000000 10940662757101 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609881039/5000000000 : ℝ)^4641 ≤ (8684513364871/20000000000000 : ℝ)^3617 := by
    have hnat : (2609881039 : ℕ)^4641*20000000000000^3617 ≤ 8684513364871^3617*5000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609881039 5000000000 8684513364871 20000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42391073/78125000 : ℝ)^4641 ≤ (45636770400623/100000000000000 : ℝ)^3617 := by
    have hnat : (42391073 : ℕ)^4641*100000000000000^3617 ≤ 45636770400623^3617*78125000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42391073 78125000 45636770400623 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1782670449/10000000000 : ℝ), (2609881039/5000000000 : ℝ), (42391073/78125000 : ℝ)] ![(10940662757101/100000000000000 : ℝ), (8684513364871/20000000000000 : ℝ), (45636770400623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1782670449/10000000000 : ℝ)|^4641 ≤ (10940662757101/100000000000000 : ℝ)^3617
        have hw : |(-1782670449/10000000000 : ℝ)|=(1782670449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609881039/5000000000 : ℝ)|^4641 ≤ (8684513364871/20000000000000 : ℝ)^3617
        have hw : |(2609881039/5000000000 : ℝ)|=(2609881039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42391073/78125000 : ℝ)|^4641 ≤ (45636770400623/100000000000000 : ℝ)^3617
        have hw : |(42391073/78125000 : ℝ)|=(42391073/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s3_5 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529332129/1000000000 : ℝ)*x 0 + (-672779/4000000 : ℝ)*x 1 + (1085211491/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529332129/1000000000 : ℝ)^4641 ≤ (22104650034641/50000000000000 : ℝ)^3617 := by
    have hnat : (529332129 : ℕ)^4641*50000000000000^3617 ≤ 22104650034641^3617*1000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529332129 1000000000 22104650034641 50000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (672779/4000000 : ℝ)^4641 ≤ (1269241038979/12500000000000 : ℝ)^3617 := by
    have hnat : (672779 : ℕ)^4641*12500000000000^3617 ≤ 1269241038979^3617*4000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672779 4000000 1269241038979 12500000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1085211491/2000000000 : ℝ)^4641 ≤ (2852298224907/6250000000000 : ℝ)^3617 := by
    have hnat : (1085211491 : ℕ)^4641*6250000000000^3617 ≤ 2852298224907^3617*2000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085211491 2000000000 2852298224907 6250000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529332129/1000000000 : ℝ), (-672779/4000000 : ℝ), (1085211491/2000000000 : ℝ)] ![(22104650034641/50000000000000 : ℝ), (1269241038979/12500000000000 : ℝ), (2852298224907/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529332129/1000000000 : ℝ)|^4641 ≤ (22104650034641/50000000000000 : ℝ)^3617
        have hw : |(529332129/1000000000 : ℝ)|=(529332129/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-672779/4000000 : ℝ)|^4641 ≤ (1269241038979/12500000000000 : ℝ)^3617
        have hw : |(-672779/4000000 : ℝ)|=(672779/4000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1085211491/2000000000 : ℝ)|^4641 ≤ (2852298224907/6250000000000 : ℝ)^3617
        have hw : |(1085211491/2000000000 : ℝ)|=(1085211491/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s3_6 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058664379/2000000000 : ℝ)*x 0 + (5426056971/10000000000 : ℝ)*x 1 + (-840973669/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058664379/2000000000 : ℝ)^4641 ≤ (44209306552697/100000000000000 : ℝ)^3617 := by
    have hnat : (1058664379 : ℕ)^4641*100000000000000^3617 ≤ 44209306552697^3617*2000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058664379 2000000000 44209306552697 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5426056971/10000000000 : ℝ)^4641 ≤ (11409191593821/25000000000000 : ℝ)^3617 := by
    have hnat : (5426056971 : ℕ)^4641*25000000000000^3617 ≤ 11409191593821^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426056971 10000000000 11409191593821 25000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (840973669/5000000000 : ℝ)^4641 ≤ (10153927056959/100000000000000 : ℝ)^3617 := by
    have hnat : (840973669 : ℕ)^4641*100000000000000^3617 ≤ 10153927056959^3617*5000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      840973669 5000000000 10153927056959 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058664379/2000000000 : ℝ), (5426056971/10000000000 : ℝ), (-840973669/5000000000 : ℝ)] ![(44209306552697/100000000000000 : ℝ), (11409191593821/25000000000000 : ℝ), (10153927056959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058664379/2000000000 : ℝ)|^4641 ≤ (44209306552697/100000000000000 : ℝ)^3617
        have hw : |(1058664379/2000000000 : ℝ)|=(1058664379/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5426056971/10000000000 : ℝ)|^4641 ≤ (11409191593821/25000000000000 : ℝ)^3617
        have hw : |(5426056971/10000000000 : ℝ)|=(5426056971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-840973669/5000000000 : ℝ)|^4641 ≤ (10153927056959/100000000000000 : ℝ)^3617
        have hw : |(-840973669/5000000000 : ℝ)|=(840973669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s3_7 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4242538577/10000000000 : ℝ)*x 0 + (2246043691/5000000000 : ℝ)*x 1 + (500556217/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4242538577/10000000000 : ℝ)^4641 ≤ (3328157369649/10000000000000 : ℝ)^3617 := by
    have hnat : (4242538577 : ℕ)^4641*10000000000000^3617 ≤ 3328157369649^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242538577 10000000000 3328157369649 10000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2246043691/5000000000 : ℝ)^4641 ≤ (7162813647633/20000000000000 : ℝ)^3617 := by
    have hnat : (2246043691 : ℕ)^4641*20000000000000^3617 ≤ 7162813647633^3617*5000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246043691 5000000000 7162813647633 20000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (500556217/1250000000 : ℝ)^4641 ≤ (30904358049571/100000000000000 : ℝ)^3617 := by
    have hnat : (500556217 : ℕ)^4641*100000000000000^3617 ≤ 30904358049571^3617*1250000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500556217 1250000000 30904358049571 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4242538577/10000000000 : ℝ), (2246043691/5000000000 : ℝ), (500556217/1250000000 : ℝ)] ![(3328157369649/10000000000000 : ℝ), (7162813647633/20000000000000 : ℝ), (30904358049571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4242538577/10000000000 : ℝ)|^4641 ≤ (3328157369649/10000000000000 : ℝ)^3617
        have hw : |(4242538577/10000000000 : ℝ)|=(4242538577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2246043691/5000000000 : ℝ)|^4641 ≤ (7162813647633/20000000000000 : ℝ)^3617
        have hw : |(2246043691/5000000000 : ℝ)|=(2246043691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(500556217/1250000000 : ℝ)|^4641 ≤ (30904358049571/100000000000000 : ℝ)^3617
        have hw : |(500556217/1250000000 : ℝ)|=(500556217/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1572_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84094463/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7903/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10831/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1387/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15519/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7903/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10831/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7903/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10831/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7903/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10831/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7903/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10831/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7903/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10831/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7903/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10831/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10831/100000 : ℝ) ^ (4639/1024 : ℝ) ≤ (423432901162127/10000000000000000000 : ℝ) := by
    have hpowers : (10831/100000 : ℝ)^4639 ≤ (423432901162127/10000000000000000000 : ℝ)^1024 := by
      have hnat : (10831 : ℕ)^4639*10000000000000000000^1024 ≤ 423432901162127^1024*100000^4639 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10831 100000 423432901162127 10000000000000000000 4639 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10831/100000 : ℝ)) (X := (423432901162127/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4639 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7903/50000 : ℝ) ^ (4639/1024 : ℝ) ≤ (11733146431350413/50000000000000000000 : ℝ) := by
    have hpowers : (7903/50000 : ℝ)^4639 ≤ (11733146431350413/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7903 : ℕ)^4639*50000000000000000000^1024 ≤ 11733146431350413^1024*50000^4639 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7903 50000 11733146431350413 50000000000000000000 4639 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7903/50000 : ℝ)) (X := (11733146431350413/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4639 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000423432901162127/5000000000000000000 : ℝ) ≤ (10000186928641673/10000000000000000 : ℝ) ^ (4639/1024 : ℝ) := by
    have hpowers : (5000423432901162127/5000000000000000000 : ℝ)^1024 ≤ (10000186928641673/10000000000000000 : ℝ)^4639 := by
      have hnat : (5000423432901162127 : ℕ)^1024*10000000000000000^4639 ≤ 10000186928641673^4639*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000423432901162127 5000000000000000000 10000186928641673 10000000000000000 1024 4639 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000186928641673/10000000000000000 : ℝ)) (X := (5000423432901162127/5000000000000000000 : ℝ)) (by norm_num) 4639 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6251731288867145131/6250000000000000000 : ℝ) ≤ (2000122277972889/2000000000000000 : ℝ) ^ (4639/1024 : ℝ) := by
    have hpowers : (6251731288867145131/6250000000000000000 : ℝ)^1024 ≤ (2000122277972889/2000000000000000 : ℝ)^4639 := by
      have hnat : (6251731288867145131 : ℕ)^1024*2000000000000000^4639 ≤ 2000122277972889^4639*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251731288867145131 6250000000000000000 2000122277972889 2000000000000000 1024 4639 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000122277972889/2000000000000000 : ℝ)) (X := (6251731288867145131/6250000000000000000 : ℝ)) (by norm_num) 4639 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25011733146431350413/25000000000000000000 : ℝ) ≤ (10001035851087217/10000000000000000 : ℝ) ^ (4639/1024 : ℝ) := by
    have hpowers : (25011733146431350413/25000000000000000000 : ℝ)^1024 ≤ (10001035851087217/10000000000000000 : ℝ)^4639 := by
      have hnat : (25011733146431350413 : ℕ)^1024*10000000000000000^4639 ≤ 10001035851087217^4639*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011733146431350413 25000000000000000000 10001035851087217 10000000000000000 1024 4639 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001035851087217/10000000000000000 : ℝ)) (X := (25011733146431350413/25000000000000000000 : ℝ)) (by norm_num) 4639 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(423432901162127/10000000000000000000 : ℝ) ≤ ((49741735290984636111/49750000000000000000 : ℝ)+2*(106115305693/124375000000000 : ℝ)*(10831/100000 : ℝ))^(4639/1024 : ℝ) := by
    rw [show (49741735290984636111/49750000000000000000 : ℝ)+2*(106115305693/124375000000000 : ℝ)*(10831/100000 : ℝ)=(10000186928641673/10000000000000000 : ℝ) by norm_num, show 1+2*(423432901162127/10000000000000000000 : ℝ)=(5000423432901162127/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11733146431350413/50000000000000000000 : ℝ)+(423432901162127/10000000000000000000 : ℝ) ≤ ((49741735290984636111/49750000000000000000 : ℝ)+(106115305693/124375000000000 : ℝ)*((7903/50000 : ℝ)+(10831/100000 : ℝ)))^(4639/1024 : ℝ) := by
    rw [show (49741735290984636111/49750000000000000000 : ℝ)+(106115305693/124375000000000 : ℝ)*((7903/50000 : ℝ)+(10831/100000 : ℝ))=(2000122277972889/2000000000000000 : ℝ) by norm_num, show 1+(11733146431350413/50000000000000000000 : ℝ)+(423432901162127/10000000000000000000 : ℝ)=(6251731288867145131/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11733146431350413/50000000000000000000 : ℝ) ≤ ((49741735290984636111/49750000000000000000 : ℝ)+2*(106115305693/124375000000000 : ℝ)*(7903/50000 : ℝ))^(4639/1024 : ℝ) := by
    rw [show (49741735290984636111/49750000000000000000 : ℝ)+2*(106115305693/124375000000000 : ℝ)*(7903/50000 : ℝ)=(10001035851087217/10000000000000000 : ℝ) by norm_num, show 1+2*(11733146431350413/50000000000000000000 : ℝ)=(25011733146431350413/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (49741735290984636111/49750000000000000000 : ℝ)*(X 1 0+X 2 0)+(106115305693/124375000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4639/1024 : ℝ)) (lo := (10831/100000 : ℝ)) (hi := (7903/50000 : ℝ)) (c := (49741735290984636111/49750000000000000000 : ℝ)) (alpha := (106115305693/124375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (49741735290984636111/49750000000000000000 : ℝ)*(X 0 1+X 2 1)+(106115305693/124375000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4639/1024 : ℝ)) (lo := (10831/100000 : ℝ)) (hi := (7903/50000 : ℝ)) (c := (49741735290984636111/49750000000000000000 : ℝ)) (alpha := (106115305693/124375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (49741735290984636111/49750000000000000000 : ℝ)*(X 0 2+X 1 2)+(106115305693/124375000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4639/1024 : ℝ)) (lo := (10831/100000 : ℝ)) (hi := (7903/50000 : ℝ)) (c := (49741735290984636111/49750000000000000000 : ℝ)) (alpha := (106115305693/124375000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-891321421/5000000000 : ℝ)*X 0 0+(1356792111/2500000000 : ℝ)*X 0 1+(260932951/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337125047/2500000000 : ℝ)*X 1 0+(-472336423/2500000000 : ℝ)*X 1 1+(5218659029/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348500147/10000000000 : ℝ)*X 2 0+(20385387/39062500 : ℝ)*X 2 1+(-1889345691/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2121236027/5000000000 : ℝ)*X 0 0+(1000455993/2500000000 : ℝ)*X 0 1+(561836763/1250000000 : ℝ)*X 0 2+(2121236027/5000000000 : ℝ)*X 1 0+(1000455993/2500000000 : ℝ)*X 1 1+(561836763/1250000000 : ℝ)*X 1 2+(2121236027/5000000000 : ℝ)*X 2 0+(1000455993/2500000000 : ℝ)*X 2 1+(561836763/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1782670449/10000000000 : ℝ)*X 0 0+(2609881039/5000000000 : ℝ)*X 0 1+(42391073/78125000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((529332129/1000000000 : ℝ)*X 1 0+(-672779/4000000 : ℝ)*X 1 1+(1085211491/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1058664379/2000000000 : ℝ)*X 2 0+(5426056971/10000000000 : ℝ)*X 2 1+(-840973669/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4242538577/10000000000 : ℝ)*X 0 0+(2246043691/5000000000 : ℝ)*X 0 1+(500556217/1250000000 : ℝ)*X 0 2+(4242538577/10000000000 : ℝ)*X 1 0+(2246043691/5000000000 : ℝ)*X 1 1+(500556217/1250000000 : ℝ)*X 1 2+(4242538577/10000000000 : ℝ)*X 2 0+(2246043691/5000000000 : ℝ)*X 2 1+(500556217/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (25021189883607166773575527371/2487500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1734318723/100000000000000 : ℝ)*(base19) + (1651216589/100000000000000 : ℝ)*(base23) + (24783569/100000000000000 : ℝ)*(lower2) + (122674311/50000000000000 : ℝ)*(upper3) + (207759113/100000000000000 : ℝ)*(upper5) + (3412480251107113/100000000000000 : ℝ)*(major0) + (3412480251107113/100000000000000 : ℝ)*(major1) + (3412480251107113/100000000000000 : ℝ)*(major2) + (1198993810882343/25000000000000 : ℝ)*(sp0) + (959200374064413/20000000000000 : ℝ)*(sp1) + (4796001953424199/100000000000000 : ℝ)*(sp2) + (1014472002579349/50000000000000 : ℝ)*(sp3) + (3545138927/12500000000000 : ℝ)*(sp4) + (12557122407/100000000000000 : ℝ)*(sp7) + (1014478281140553/50000000000000 : ℝ)*(f.failure) + (1199000901160197/25000000000000 : ℝ)*(f.sum) + (62132278642611/24875000000000000000000000000 : ℝ)*base65 + (28234542042562357543/4975000000000000000000000000000000 : ℝ)*base67 + (8538869561112357543/4975000000000000000000000000000000 : ℝ)*base69 + (26140702822687357543/4975000000000000000000000000000000 : ℝ)*base71 + (32580237947993/12437500000000000000000000000 : ℝ)*base73 + (16527172135362642457/4975000000000000000000000000000000 : ℝ)*base76 + (19787547116487642457/4975000000000000000000000000000000 : ℝ)*base78 + (50619735075362357543/4975000000000000000000000000000000 : ℝ)*base79 + (110796357731611/24875000000000000000000000000 : ℝ)*base81 + (7058039/2500000000000000000000 : ℝ)*base89 + (7058039/2500000000000000000000 : ℝ)*base91 + (7058039/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6236965328328766666145574489/497500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1489449299/100000000000000 : ℝ)*(base19) + (2814251519/100000000000000 : ℝ)*(base23) + (72929571/20000000000000 : ℝ)*(upper3) + (149390751/50000000000000 : ℝ)*(lower4) + (150081287/100000000000000 : ℝ)*(upper5) + (689811808801533/20000000000000 : ℝ)*(major0) + (689811808801533/20000000000000 : ℝ)*(major1) + (689811808801533/20000000000000 : ℝ)*(major2) + (17860500771/100000000000000 : ℝ)*(sp1) + (9413258841/25000000000000 : ℝ)*(sp2) + (4847412474467657/100000000000000 : ℝ)*(sp4) + (1211848281129397/25000000000000 : ℝ)*(sp5) + (2423686003590387/50000000000000 : ℝ)*(sp6) + (2050705195660543/100000000000000 : ℝ)*(sp7) + (2050705195660543/100000000000000 : ℝ)*(f.failure) + (4847412474467657/100000000000000 : ℝ)*(f.sum) + (15606547998787/2487500000000000000000000000 : ℝ)*base66 + (2092841675668441837/995000000000000000000000000000000 : ℝ)*base68 + (8750061390251558163/995000000000000000000000000000000 : ℝ)*base69 + (13717507377133441837/995000000000000000000000000000000 : ℝ)*base72 + (1520608056587/2487500000000000000000000000 : ℝ)*base74 + (1131588966293441837/995000000000000000000000000000000 : ℝ)*base76 + (364559388283441837/995000000000000000000000000000000 : ℝ)*base78 + (5619217740911558163/995000000000000000000000000000000 : ℝ)*base79 + (925051921931/1243750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (43873409/5000000000000000000000 : ℝ)*base89 + (43873409/5000000000000000000000 : ℝ)*base91 + (43873409/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1572_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84094463/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7903/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10831/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1387/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15519/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1572_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1572_s4_0 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1782861629/10000000000 : ℝ)*x 0 + (5425696127/10000000000 : ℝ)*x 1 + (652498279/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1782861629/10000000000 : ℝ)^4641 ≤ (437686730827/4000000000000 : ℝ)^3617 := by
    have hnat : (1782861629 : ℕ)^4641*4000000000000^3617 ≤ 437686730827^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1782861629 10000000000 437686730827 4000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5425696127/10000000000 : ℝ)^4641 ≤ (5704109032309/12500000000000 : ℝ)^3617 := by
    have hnat : (5425696127 : ℕ)^4641*12500000000000^3617 ≤ 5704109032309^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425696127 10000000000 5704109032309 12500000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (652498279/1250000000 : ℝ)^4641 ≤ (43424959462251/100000000000000 : ℝ)^3617 := by
    have hnat : (652498279 : ℕ)^4641*100000000000000^3617 ≤ 43424959462251^3617*1250000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652498279 1250000000 43424959462251 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1782861629/10000000000 : ℝ), (5425696127/10000000000 : ℝ), (652498279/1250000000 : ℝ)] ![(437686730827/4000000000000 : ℝ), (5704109032309/12500000000000 : ℝ), (43424959462251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1782861629/10000000000 : ℝ)|^4641 ≤ (437686730827/4000000000000 : ℝ)^3617
        have hw : |(-1782861629/10000000000 : ℝ)|=(1782861629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5425696127/10000000000 : ℝ)|^4641 ≤ (5704109032309/12500000000000 : ℝ)^3617
        have hw : |(5425696127/10000000000 : ℝ)|=(5425696127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(652498279/1250000000 : ℝ)|^4641 ≤ (43424959462251/100000000000000 : ℝ)^3617
        have hw : |(652498279/1250000000 : ℝ)|=(652498279/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s4_1 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348110219/10000000000 : ℝ)*x 0 + (-1888099547/10000000000 : ℝ)*x 1 + (5219986231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348110219/10000000000 : ℝ)^4641 ≤ (11199324411597/25000000000000 : ℝ)^3617 := by
    have hnat : (5348110219 : ℕ)^4641*25000000000000^3617 ≤ 11199324411597^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348110219 10000000000 11199324411597 25000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1888099547/10000000000 : ℝ)^4641 ≤ (2355548578733/20000000000000 : ℝ)^3617 := by
    have hnat : (1888099547 : ℕ)^4641*20000000000000^3617 ≤ 2355548578733^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1888099547 10000000000 2355548578733 20000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219986231/10000000000 : ℝ)^4641 ≤ (43424959451577/100000000000000 : ℝ)^3617 := by
    have hnat : (5219986231 : ℕ)^4641*100000000000000^3617 ≤ 43424959451577^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219986231 10000000000 43424959451577 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348110219/10000000000 : ℝ), (-1888099547/10000000000 : ℝ), (5219986231/10000000000 : ℝ)] ![(11199324411597/25000000000000 : ℝ), (2355548578733/20000000000000 : ℝ), (43424959451577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348110219/10000000000 : ℝ)|^4641 ≤ (11199324411597/25000000000000 : ℝ)^3617
        have hw : |(5348110219/10000000000 : ℝ)|=(5348110219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1888099547/10000000000 : ℝ)|^4641 ≤ (2355548578733/20000000000000 : ℝ)^3617
        have hw : |(-1888099547/10000000000 : ℝ)|=(1888099547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219986231/10000000000 : ℝ)|^4641 ≤ (43424959451577/100000000000000 : ℝ)^3617
        have hw : |(5219986231/10000000000 : ℝ)|=(5219986231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s4_2 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348110221/10000000000 : ℝ)*x 0 + (5219986229/10000000000 : ℝ)*x 1 + (-1888099547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348110221/10000000000 : ℝ)^4641 ≤ (44797297667883/100000000000000 : ℝ)^3617 := by
    have hnat : (5348110221 : ℕ)^4641*100000000000000^3617 ≤ 44797297667883^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348110221 10000000000 44797297667883 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219986229/10000000000 : ℝ)^4641 ≤ (43424959430229/100000000000000 : ℝ)^3617 := by
    have hnat : (5219986229 : ℕ)^4641*100000000000000^3617 ≤ 43424959430229^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219986229 10000000000 43424959430229 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1888099547/10000000000 : ℝ)^4641 ≤ (2355548578733/20000000000000 : ℝ)^3617 := by
    have hnat : (1888099547 : ℕ)^4641*20000000000000^3617 ≤ 2355548578733^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1888099547 10000000000 2355548578733 20000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348110221/10000000000 : ℝ), (5219986229/10000000000 : ℝ), (-1888099547/10000000000 : ℝ)] ![(44797297667883/100000000000000 : ℝ), (43424959430229/100000000000000 : ℝ), (2355548578733/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348110221/10000000000 : ℝ)|^4641 ≤ (44797297667883/100000000000000 : ℝ)^3617
        have hw : |(5348110221/10000000000 : ℝ)|=(5348110221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219986229/10000000000 : ℝ)|^4641 ≤ (43424959430229/100000000000000 : ℝ)^3617
        have hw : |(5219986229/10000000000 : ℝ)|=(5219986229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1888099547/10000000000 : ℝ)|^4641 ≤ (2355548578733/20000000000000 : ℝ)^3617
        have hw : |(-1888099547/10000000000 : ℝ)|=(1888099547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s4_3 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4242610857/10000000000 : ℝ)*x 0 + (4005117351/10000000000 : ℝ)*x 1 + (898273997/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4242610857/10000000000 : ℝ)^4641 ≤ (16641150621117/50000000000000 : ℝ)^3617 := by
    have hnat : (4242610857 : ℕ)^4641*50000000000000^3617 ≤ 16641150621117^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242610857 10000000000 16641150621117 50000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4005117351/10000000000 : ℝ)^4641 ≤ (7727742297089/25000000000000 : ℝ)^3617 := by
    have hnat : (4005117351 : ℕ)^4641*25000000000000^3617 ≤ 7727742297089^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4005117351 10000000000 7727742297089 25000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (898273997/2000000000 : ℝ)^4641 ≤ (35806729552967/100000000000000 : ℝ)^3617 := by
    have hnat : (898273997 : ℕ)^4641*100000000000000^3617 ≤ 35806729552967^3617*2000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898273997 2000000000 35806729552967 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4242610857/10000000000 : ℝ), (4005117351/10000000000 : ℝ), (898273997/2000000000 : ℝ)] ![(16641150621117/50000000000000 : ℝ), (7727742297089/25000000000000 : ℝ), (35806729552967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4242610857/10000000000 : ℝ)|^4641 ≤ (16641150621117/50000000000000 : ℝ)^3617
        have hw : |(4242610857/10000000000 : ℝ)|=(4242610857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4005117351/10000000000 : ℝ)|^4641 ≤ (7727742297089/25000000000000 : ℝ)^3617
        have hw : |(4005117351/10000000000 : ℝ)|=(4005117351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(898273997/2000000000 : ℝ)|^4641 ≤ (35806729552967/100000000000000 : ℝ)^3617
        have hw : |(898273997/2000000000 : ℝ)|=(898273997/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s4_4 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-11143053/62500000 : ℝ)*x 0 + (5221059707/10000000000 : ℝ)*x 1 + (5424614679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (11143053/62500000 : ℝ)^4641 ≤ (5471189860949/50000000000000 : ℝ)^3617 := by
    have hnat : (11143053 : ℕ)^4641*50000000000000^3617 ≤ 5471189860949^3617*62500000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11143053 62500000 5471189860949 50000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5221059707/10000000000 : ℝ)^4641 ≤ (1737456728971/4000000000000 : ℝ)^3617 := by
    have hnat : (5221059707 : ℕ)^4641*4000000000000^3617 ≤ 1737456728971^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221059707 10000000000 1737456728971 4000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5424614679/10000000000 : ℝ)^4641 ≤ (4562120204539/10000000000000 : ℝ)^3617 := by
    have hnat : (5424614679 : ℕ)^4641*10000000000000^3617 ≤ 4562120204539^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424614679 10000000000 4562120204539 10000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-11143053/62500000 : ℝ), (5221059707/10000000000 : ℝ), (5424614679/10000000000 : ℝ)] ![(5471189860949/50000000000000 : ℝ), (1737456728971/4000000000000 : ℝ), (4562120204539/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-11143053/62500000 : ℝ)|^4641 ≤ (5471189860949/50000000000000 : ℝ)^3617
        have hw : |(-11143053/62500000 : ℝ)|=(11143053/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5221059707/10000000000 : ℝ)|^4641 ≤ (1737456728971/4000000000000 : ℝ)^3617
        have hw : |(5221059707/10000000000 : ℝ)|=(5221059707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5424614679/10000000000 : ℝ)|^4641 ≤ (4562120204539/10000000000000 : ℝ)^3617
        have hw : |(5424614679/10000000000 : ℝ)|=(5424614679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s4_5 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323418177/2500000000 : ℝ)*x 0 + (-1683471129/10000000000 : ℝ)*x 1 + (1084922933/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323418177/2500000000 : ℝ)^4641 ≤ (44213066036433/100000000000000 : ℝ)^3617 := by
    have hnat : (1323418177 : ℕ)^4641*100000000000000^3617 ≤ 44213066036433^3617*2500000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323418177 2500000000 44213066036433 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1683471129/10000000000 : ℝ)^4641 ≤ (5082866025727/50000000000000 : ℝ)^3617 := by
    have hnat : (1683471129 : ℕ)^4641*50000000000000^3617 ≤ 5082866025727^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1683471129 10000000000 5082866025727 50000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1084922933/2000000000 : ℝ)^4641 ≤ (11405300473579/25000000000000 : ℝ)^3617 := by
    have hnat : (1084922933 : ℕ)^4641*25000000000000^3617 ≤ 11405300473579^3617*2000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084922933 2000000000 11405300473579 25000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323418177/2500000000 : ℝ), (-1683471129/10000000000 : ℝ), (1084922933/2000000000 : ℝ)] ![(44213066036433/100000000000000 : ℝ), (5082866025727/50000000000000 : ℝ), (11405300473579/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323418177/2500000000 : ℝ)|^4641 ≤ (44213066036433/100000000000000 : ℝ)^3617
        have hw : |(1323418177/2500000000 : ℝ)|=(1323418177/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1683471129/10000000000 : ℝ)|^4641 ≤ (5082866025727/50000000000000 : ℝ)^3617
        have hw : |(-1683471129/10000000000 : ℝ)|=(1683471129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1084922933/2000000000 : ℝ)|^4641 ≤ (11405300473579/25000000000000 : ℝ)^3617
        have hw : |(1084922933/2000000000 : ℝ)|=(1084922933/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s4_6 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293672683/10000000000 : ℝ)*x 0 + (5424614673/10000000000 : ℝ)*x 1 + (-105216947/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293672683/10000000000 : ℝ)^4641 ≤ (22106532884259/50000000000000 : ℝ)^3617 := by
    have hnat : (5293672683 : ℕ)^4641*50000000000000^3617 ≤ 22106532884259^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293672683 10000000000 22106532884259 50000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5424614673/10000000000 : ℝ)^4641 ≤ (11405300495161/25000000000000 : ℝ)^3617 := by
    have hnat : (5424614673 : ℕ)^4641*25000000000000^3617 ≤ 11405300495161^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424614673 10000000000 11405300495161 25000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105216947/625000000 : ℝ)^4641 ≤ (10165732229661/100000000000000 : ℝ)^3617 := by
    have hnat : (105216947 : ℕ)^4641*100000000000000^3617 ≤ 10165732229661^3617*625000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105216947 625000000 10165732229661 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293672683/10000000000 : ℝ), (5424614673/10000000000 : ℝ), (-105216947/625000000 : ℝ)] ![(22106532884259/50000000000000 : ℝ), (11405300495161/25000000000000 : ℝ), (10165732229661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293672683/10000000000 : ℝ)|^4641 ≤ (22106532884259/50000000000000 : ℝ)^3617
        have hw : |(5293672683/10000000000 : ℝ)|=(5293672683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5424614673/10000000000 : ℝ)|^4641 ≤ (11405300495161/25000000000000 : ℝ)^3617
        have hw : |(5424614673/10000000000 : ℝ)|=(5424614673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-105216947/625000000 : ℝ)|^4641 ≤ (10165732229661/100000000000000 : ℝ)^3617
        have hw : |(-105216947/625000000 : ℝ)|=(105216947/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s4_7 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1060668561/2500000000 : ℝ)*x 0 + (4488832463/10000000000 : ℝ)*x 1 + (400767367/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060668561/2500000000 : ℝ)^4641 ≤ (33282939276971/100000000000000 : ℝ)^3617 := by
    have hnat : (1060668561 : ℕ)^4641*100000000000000^3617 ≤ 33282939276971^3617*2500000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060668561 2500000000 33282939276971 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4488832463/10000000000 : ℝ)^4641 ≤ (7156154875599/20000000000000 : ℝ)^3617 := by
    have hnat : (4488832463 : ℕ)^4641*20000000000000^3617 ≤ 7156154875599^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488832463 10000000000 7156154875599 20000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (400767367/1000000000 : ℝ)^4641 ≤ (7734071583127/25000000000000 : ℝ)^3617 := by
    have hnat : (400767367 : ℕ)^4641*25000000000000^3617 ≤ 7734071583127^3617*1000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400767367 1000000000 7734071583127 25000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060668561/2500000000 : ℝ), (4488832463/10000000000 : ℝ), (400767367/1000000000 : ℝ)] ![(33282939276971/100000000000000 : ℝ), (7156154875599/20000000000000 : ℝ), (7734071583127/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060668561/2500000000 : ℝ)|^4641 ≤ (33282939276971/100000000000000 : ℝ)^3617
        have hw : |(1060668561/2500000000 : ℝ)|=(1060668561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4488832463/10000000000 : ℝ)|^4641 ≤ (7156154875599/20000000000000 : ℝ)^3617
        have hw : |(4488832463/10000000000 : ℝ)|=(4488832463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(400767367/1000000000 : ℝ)|^4641 ≤ (7734071583127/25000000000000 : ℝ)^3617
        have hw : |(400767367/1000000000 : ℝ)|=(400767367/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1572_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84094463/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15519/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1387/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (89/800 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (484/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15519/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1387/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15519/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1387/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15519/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1387/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15519/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1387/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15519/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1387/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15519/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1387/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1387/12500 : ℝ) ^ (4639/1024 : ℝ) ≤ (4724359332596113/100000000000000000000 : ℝ) := by
    have hpowers : (1387/12500 : ℝ)^4639 ≤ (4724359332596113/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1387 : ℕ)^4639*100000000000000000000^1024 ≤ 4724359332596113^1024*12500^4639 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1387 12500 4724359332596113 100000000000000000000 4639 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1387/12500 : ℝ)) (X := (4724359332596113/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4639 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15519/100000 : ℝ) ^ (4639/1024 : ℝ) ≤ (10798451131280427/50000000000000000000 : ℝ) := by
    have hpowers : (15519/100000 : ℝ)^4639 ≤ (10798451131280427/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15519 : ℕ)^4639*50000000000000000000^1024 ≤ 10798451131280427^1024*100000^4639 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15519 100000 10798451131280427 50000000000000000000 4639 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15519/100000 : ℝ)) (X := (10798451131280427/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4639 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004724359332596113/50000000000000000000 : ℝ) ≤ (10000208560718439/10000000000000000 : ℝ) ^ (4639/1024 : ℝ) := by
    have hpowers : (50004724359332596113/50000000000000000000 : ℝ)^1024 ≤ (10000208560718439/10000000000000000 : ℝ)^4639 := by
      have hnat : (50004724359332596113 : ℕ)^1024*10000000000000000^4639 ≤ 10000208560718439^4639*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004724359332596113 50000000000000000000 10000208560718439 10000000000000000 1024 4639 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000208560718439/10000000000000000 : ℝ)) (X := (50004724359332596113/50000000000000000000 : ℝ)) (by norm_num) 4639 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100026321261595156967/100000000000000000000 : ℝ) ≤ (5000290474327643/5000000000000000 : ℝ) ^ (4639/1024 : ℝ) := by
    have hpowers : (100026321261595156967/100000000000000000000 : ℝ)^1024 ≤ (5000290474327643/5000000000000000 : ℝ)^4639 := by
      have hnat : (100026321261595156967 : ℕ)^1024*5000000000000000^4639 ≤ 5000290474327643^4639*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100026321261595156967 100000000000000000000 5000290474327643 5000000000000000 1024 4639 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000290474327643/5000000000000000 : ℝ)) (X := (100026321261595156967/100000000000000000000 : ℝ)) (by norm_num) 4639 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25010798451131280427/25000000000000000000 : ℝ) ≤ (10000953336592133/10000000000000000 : ℝ) ^ (4639/1024 : ℝ) := by
    have hpowers : (25010798451131280427/25000000000000000000 : ℝ)^1024 ≤ (10000953336592133/10000000000000000 : ℝ)^4639 := by
      have hnat : (25010798451131280427 : ℕ)^1024*10000000000000000^4639 ≤ 10000953336592133^4639*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010798451131280427 25000000000000000000 10000953336592133 10000000000000000 1024 4639 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000953336592133/10000000000000000 : ℝ)) (X := (25010798451131280427/25000000000000000000 : ℝ)) (by norm_num) 4639 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4724359332596113/100000000000000000000 : ℝ) ≤ ((44222658430963147073/44230000000000000000 : ℝ)+2*(372387936847/442300000000000 : ℝ)*(1387/12500 : ℝ))^(4639/1024 : ℝ) := by
    rw [show (44222658430963147073/44230000000000000000 : ℝ)+2*(372387936847/442300000000000 : ℝ)*(1387/12500 : ℝ)=(10000208560718439/10000000000000000 : ℝ) by norm_num, show 1+2*(4724359332596113/100000000000000000000 : ℝ)=(50004724359332596113/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10798451131280427/50000000000000000000 : ℝ)+(4724359332596113/100000000000000000000 : ℝ) ≤ ((44222658430963147073/44230000000000000000 : ℝ)+(372387936847/442300000000000 : ℝ)*((15519/100000 : ℝ)+(1387/12500 : ℝ)))^(4639/1024 : ℝ) := by
    rw [show (44222658430963147073/44230000000000000000 : ℝ)+(372387936847/442300000000000 : ℝ)*((15519/100000 : ℝ)+(1387/12500 : ℝ))=(5000290474327643/5000000000000000 : ℝ) by norm_num, show 1+(10798451131280427/50000000000000000000 : ℝ)+(4724359332596113/100000000000000000000 : ℝ)=(100026321261595156967/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10798451131280427/50000000000000000000 : ℝ) ≤ ((44222658430963147073/44230000000000000000 : ℝ)+2*(372387936847/442300000000000 : ℝ)*(15519/100000 : ℝ))^(4639/1024 : ℝ) := by
    rw [show (44222658430963147073/44230000000000000000 : ℝ)+2*(372387936847/442300000000000 : ℝ)*(15519/100000 : ℝ)=(10000953336592133/10000000000000000 : ℝ) by norm_num, show 1+2*(10798451131280427/50000000000000000000 : ℝ)=(25010798451131280427/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (44222658430963147073/44230000000000000000 : ℝ)*(X 1 0+X 2 0)+(372387936847/442300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4639/1024 : ℝ)) (lo := (1387/12500 : ℝ)) (hi := (15519/100000 : ℝ)) (c := (44222658430963147073/44230000000000000000 : ℝ)) (alpha := (372387936847/442300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (44222658430963147073/44230000000000000000 : ℝ)*(X 0 1+X 2 1)+(372387936847/442300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4639/1024 : ℝ)) (lo := (1387/12500 : ℝ)) (hi := (15519/100000 : ℝ)) (c := (44222658430963147073/44230000000000000000 : ℝ)) (alpha := (372387936847/442300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (44222658430963147073/44230000000000000000 : ℝ)*(X 0 2+X 1 2)+(372387936847/442300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4639/1024 : ℝ)) (lo := (1387/12500 : ℝ)) (hi := (15519/100000 : ℝ)) (c := (44222658430963147073/44230000000000000000 : ℝ)) (alpha := (372387936847/442300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1782861629/10000000000 : ℝ)*X 0 0+(5425696127/10000000000 : ℝ)*X 0 1+(652498279/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348110219/10000000000 : ℝ)*X 1 0+(-1888099547/10000000000 : ℝ)*X 1 1+(5219986231/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348110221/10000000000 : ℝ)*X 2 0+(5219986229/10000000000 : ℝ)*X 2 1+(-1888099547/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4242610857/10000000000 : ℝ)*X 0 0+(4005117351/10000000000 : ℝ)*X 0 1+(898273997/2000000000 : ℝ)*X 0 2+(4242610857/10000000000 : ℝ)*X 1 0+(4005117351/10000000000 : ℝ)*X 1 1+(898273997/2000000000 : ℝ)*X 1 2+(4242610857/10000000000 : ℝ)*X 2 0+(4005117351/10000000000 : ℝ)*X 2 1+(898273997/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-11143053/62500000 : ℝ)*X 0 0+(5221059707/10000000000 : ℝ)*X 0 1+(5424614679/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323418177/2500000000 : ℝ)*X 1 0+(-1683471129/10000000000 : ℝ)*X 1 1+(1084922933/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293672683/10000000000 : ℝ)*X 2 0+(5424614673/10000000000 : ℝ)*X 2 1+(-105216947/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1060668561/2500000000 : ℝ)*X 0 0+(4488832463/10000000000 : ℝ)*X 0 1+(400767367/1000000000 : ℝ)*X 0 2+(1060668561/2500000000 : ℝ)*X 1 0+(4488832463/10000000000 : ℝ)*X 1 1+(400767367/1000000000 : ℝ)*X 1 2+(1060668561/2500000000 : ℝ)*X 2 0+(4488832463/10000000000 : ℝ)*X 2 1+(400767367/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (238456802199682408840708863/55287500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (727198441/100000000000000 : ℝ)*(base19) + (340736863/50000000000000 : ℝ)*(base23) + (3178291/12500000000000 : ℝ)*(lower2) + (26484411/25000000000000 : ℝ)*(upper3) + (36017851/50000000000000 : ℝ)*(upper5) + (172944833722423/5000000000000 : ℝ)*(major0) + (172944833722423/5000000000000 : ℝ)*(major1) + (172944833722423/5000000000000 : ℝ)*(major2) + (2430613534319631/50000000000000 : ℝ)*(sp0) + (4861238127587537/100000000000000 : ℝ)*(sp1) + (1215309543328063/25000000000000 : ℝ)*(sp2) + (1028274475955413/50000000000000 : ℝ)*(sp3) + (2946536679/25000000000000 : ℝ)*(sp4) + (2699216173/50000000000000 : ℝ)*(sp7) + (2056554350343173/100000000000000 : ℝ)*(f.failure) + (2430619427392989/50000000000000 : ℝ)*(f.sum) + (16714315833/6910937500000000000000000 : ℝ)*base66 + (1131965845533517879/221150000000000000000000000000000 : ℝ)*base67 + (820703464040317879/221150000000000000000000000000000 : ℝ)*base69 + (1637785809309667879/221150000000000000000000000000000 : ℝ)*base71 + (12526601433731/4423000000000000000000000000 : ℝ)*base74 + (4511405466446467879/221150000000000000000000000000000 : ℝ)*base75 + (993675185422682121/221150000000000000000000000000000 : ℝ)*base78 + (4655887769388217879/221150000000000000000000000000000 : ℝ)*base79 + (8987439469123/2211500000000000000000000000 : ℝ)*base81 + (848901/5000000000000000000000 : ℝ)*base90 + (848901/5000000000000000000000 : ℝ)*base92 + (848901/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11643918392145895743947834103/1105750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1661949593/100000000000000 : ℝ)*(base19) + (34578223/2000000000000 : ℝ)*(base23) + (109151007/50000000000000 : ℝ)*(upper3) + (45159137/100000000000000 : ℝ)*(lower4) + (230389191/100000000000000 : ℝ)*(upper5) + (1747748267588963/50000000000000 : ℝ)*(major0) + (1747748267588963/50000000000000 : ℝ)*(major1) + (1747748267588963/50000000000000 : ℝ)*(major2) + (13078002113/50000000000000 : ℝ)*(sp1) + (26628056747/100000000000000 : ℝ)*(sp2) + (4912677209334259/100000000000000 : ℝ)*(sp4) + (122816234784511/2500000000000 : ℝ)*(sp5) + (2456324426183181/50000000000000 : ℝ)*(sp6) + (2078315510010407/100000000000000 : ℝ)*(sp7) + (2078315510010407/100000000000000 : ℝ)*(f.failure) + (4912677209334259/100000000000000 : ℝ)*(f.sum) + (35077881855149/11057500000000000000000000000 : ℝ)*base66 + (16602170911275655299/2211500000000000000000000000000000 : ℝ)*base67 + (5967671157410155299/2211500000000000000000000000000000 : ℝ)*base69 + (1220815720656344701/2211500000000000000000000000000000 : ℝ)*base72 + (47871569534537/22115000000000000000000000000 : ℝ)*base73 + (28244161643542655299/2211500000000000000000000000000000 : ℝ)*base75 + (60625930624844701/2211500000000000000000000000000000 : ℝ)*base78 + (42061479551451655299/2211500000000000000000000000000000 : ℝ)*base79 + (105236347436233/22115000000000000000000000000 : ℝ)*base82 + (1076441/5000000000000000000000 : ℝ)*base89 + (1076441/5000000000000000000000 : ℝ)*base91 + (1076441/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1572_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84094463/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15519/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1387/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (89/800 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (484/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1572_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1572_s5_0 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1782883451/10000000000 : ℝ)*x 0 + (5425546237/10000000000 : ℝ)*x 1 + (522012167/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1782883451/10000000000 : ℝ)^4641 ≤ (1094234011853/10000000000000 : ℝ)^3617 := by
    have hnat : (1782883451 : ℕ)^4641*10000000000000^3617 ≤ 1094234011853^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1782883451 10000000000 1094234011853 10000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5425546237/10000000000 : ℝ)^4641 ≤ (22815627356759/50000000000000 : ℝ)^3617 := by
    have hnat : (5425546237 : ℕ)^4641*50000000000000^3617 ≤ 22815627356759^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425546237 10000000000 22815627356759 50000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (522012167/1000000000 : ℝ)^4641 ≤ (43426405152497/100000000000000 : ℝ)^3617 := by
    have hnat : (522012167 : ℕ)^4641*100000000000000^3617 ≤ 43426405152497^3617*1000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522012167 1000000000 43426405152497 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1782883451/10000000000 : ℝ), (5425546237/10000000000 : ℝ), (522012167/1000000000 : ℝ)] ![(1094234011853/10000000000000 : ℝ), (22815627356759/50000000000000 : ℝ), (43426405152497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1782883451/10000000000 : ℝ)|^4641 ≤ (1094234011853/10000000000000 : ℝ)^3617
        have hw : |(-1782883451/10000000000 : ℝ)|=(1782883451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5425546237/10000000000 : ℝ)|^4641 ≤ (22815627356759/50000000000000 : ℝ)^3617
        have hw : |(5425546237/10000000000 : ℝ)|=(5425546237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(522012167/1000000000 : ℝ)|^4641 ≤ (43426405152497/100000000000000 : ℝ)^3617
        have hw : |(522012167/1000000000 : ℝ)|=(522012167/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s5_1 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337017653/2500000000 : ℝ)*x 0 + (-235996513/1250000000 : ℝ)*x 1 + (522012167/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337017653/2500000000 : ℝ)^4641 ≤ (44796871963669/100000000000000 : ℝ)^3617 := by
    have hnat : (1337017653 : ℕ)^4641*100000000000000^3617 ≤ 44796871963669^3617*2500000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337017653 2500000000 44796871963669 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (235996513/1250000000 : ℝ)^4641 ≤ (5888361432851/50000000000000 : ℝ)^3617 := by
    have hnat : (235996513 : ℕ)^4641*50000000000000^3617 ≤ 5888361432851^3617*1250000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235996513 1250000000 5888361432851 50000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (522012167/1000000000 : ℝ)^4641 ≤ (43426405152497/100000000000000 : ℝ)^3617 := by
    have hnat : (522012167 : ℕ)^4641*100000000000000^3617 ≤ 43426405152497^3617*1000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522012167 1000000000 43426405152497 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337017653/2500000000 : ℝ), (-235996513/1250000000 : ℝ), (522012167/1000000000 : ℝ)] ![(44796871963669/100000000000000 : ℝ), (5888361432851/50000000000000 : ℝ), (43426405152497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337017653/2500000000 : ℝ)|^4641 ≤ (44796871963669/100000000000000 : ℝ)^3617
        have hw : |(1337017653/2500000000 : ℝ)|=(1337017653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-235996513/1250000000 : ℝ)|^4641 ≤ (5888361432851/50000000000000 : ℝ)^3617
        have hw : |(-235996513/1250000000 : ℝ)|=(235996513/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(522012167/1000000000 : ℝ)|^4641 ≤ (43426405152497/100000000000000 : ℝ)^3617
        have hw : |(522012167/1000000000 : ℝ)|=(522012167/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s5_2 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337017653/2500000000 : ℝ)*x 0 + (522012167/1000000000 : ℝ)*x 1 + (-235996513/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337017653/2500000000 : ℝ)^4641 ≤ (44796871963669/100000000000000 : ℝ)^3617 := by
    have hnat : (1337017653 : ℕ)^4641*100000000000000^3617 ≤ 44796871963669^3617*2500000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337017653 2500000000 44796871963669 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (522012167/1000000000 : ℝ)^4641 ≤ (43426405152497/100000000000000 : ℝ)^3617 := by
    have hnat : (522012167 : ℕ)^4641*100000000000000^3617 ≤ 43426405152497^3617*1000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522012167 1000000000 43426405152497 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (235996513/1250000000 : ℝ)^4641 ≤ (5888361432851/50000000000000 : ℝ)^3617 := by
    have hnat : (235996513 : ℕ)^4641*50000000000000^3617 ≤ 5888361432851^3617*1250000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235996513 1250000000 5888361432851 50000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337017653/2500000000 : ℝ), (522012167/1000000000 : ℝ), (-235996513/1250000000 : ℝ)] ![(44796871963669/100000000000000 : ℝ), (43426405152497/100000000000000 : ℝ), (5888361432851/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337017653/2500000000 : ℝ)|^4641 ≤ (44796871963669/100000000000000 : ℝ)^3617
        have hw : |(1337017653/2500000000 : ℝ)|=(1337017653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(522012167/1000000000 : ℝ)|^4641 ≤ (43426405152497/100000000000000 : ℝ)^3617
        have hw : |(522012167/1000000000 : ℝ)|=(522012167/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-235996513/1250000000 : ℝ)|^4641 ≤ (5888361432851/50000000000000 : ℝ)^3617
        have hw : |(-235996513/1250000000 : ℝ)|=(235996513/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s5_3 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42426249/100000000 : ℝ)*x 0 + (125170407/312500000 : ℝ)*x 1 + (4491031201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42426249/100000000 : ℝ)^4641 ≤ (33282442594673/100000000000000 : ℝ)^3617 := by
    have hnat : (42426249 : ℕ)^4641*100000000000000^3617 ≤ 33282442594673^3617*100000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42426249 100000000 33282442594673 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (125170407/312500000 : ℝ)^4641 ≤ (15457146674481/50000000000000 : ℝ)^3617 := by
    have hnat : (125170407 : ℕ)^4641*50000000000000^3617 ≤ 15457146674481^3617*312500000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125170407 312500000 15457146674481 50000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4491031201/10000000000 : ℝ)^4641 ≤ (35803264043117/100000000000000 : ℝ)^3617 := by
    have hnat : (4491031201 : ℕ)^4641*100000000000000^3617 ≤ 35803264043117^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491031201 10000000000 35803264043117 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42426249/100000000 : ℝ), (125170407/312500000 : ℝ), (4491031201/10000000000 : ℝ)] ![(33282442594673/100000000000000 : ℝ), (15457146674481/50000000000000 : ℝ), (35803264043117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42426249/100000000 : ℝ)|^4641 ≤ (33282442594673/100000000000000 : ℝ)^3617
        have hw : |(42426249/100000000 : ℝ)|=(42426249/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(125170407/312500000 : ℝ)|^4641 ≤ (15457146674481/50000000000000 : ℝ)^3617
        have hw : |(125170407/312500000 : ℝ)|=(125170407/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4491031201/10000000000 : ℝ)|^4641 ≤ (35803264043117/100000000000000 : ℝ)^3617
        have hw : |(4491031201/10000000000 : ℝ)|=(4491031201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s5_4 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1782910159/10000000000 : ℝ)*x 0 + (652649027/1250000000 : ℝ)*x 1 + (216978711/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1782910159/10000000000 : ℝ)^4641 ≤ (2735637611089/25000000000000 : ℝ)^3617 := by
    have hnat : (1782910159 : ℕ)^4641*25000000000000^3617 ≤ 2735637611089^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1782910159 10000000000 2735637611089 25000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (652649027/1250000000 : ℝ)^4641 ≤ (21718916366031/50000000000000 : ℝ)^3617 := by
    have hnat : (652649027 : ℕ)^4641*50000000000000^3617 ≤ 21718916366031^3617*1250000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652649027 1250000000 21718916366031 50000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216978711/400000000 : ℝ)^4641 ≤ (5702452101667/12500000000000 : ℝ)^3617 := by
    have hnat : (216978711 : ℕ)^4641*12500000000000^3617 ≤ 5702452101667^3617*400000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216978711 400000000 5702452101667 12500000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1782910159/10000000000 : ℝ), (652649027/1250000000 : ℝ), (216978711/400000000 : ℝ)] ![(2735637611089/25000000000000 : ℝ), (21718916366031/50000000000000 : ℝ), (5702452101667/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1782910159/10000000000 : ℝ)|^4641 ≤ (2735637611089/25000000000000 : ℝ)^3617
        have hw : |(-1782910159/10000000000 : ℝ)|=(1782910159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(652649027/1250000000 : ℝ)|^4641 ≤ (21718916366031/50000000000000 : ℝ)^3617
        have hw : |(652649027/1250000000 : ℝ)|=(652649027/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216978711/400000000 : ℝ)|^4641 ≤ (5702452101667/12500000000000 : ℝ)^3617
        have hw : |(216978711/400000000 : ℝ)|=(216978711/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s5_5 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058741729/2000000000 : ℝ)*x 0 + (-841813/5000000 : ℝ)*x 1 + (2712233887/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058741729/2000000000 : ℝ)^4641 ≤ (44213451158889/100000000000000 : ℝ)^3617 := by
    have hnat : (1058741729 : ℕ)^4641*100000000000000^3617 ≤ 44213451158889^3617*2000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058741729 2000000000 44213451158889 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (841813/5000000 : ℝ)^4641 ≤ (10166932025363/100000000000000 : ℝ)^3617 := by
    have hnat : (841813 : ℕ)^4641*100000000000000^3617 ≤ 10166932025363^3617*5000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      841813 5000000 10166932025363 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712233887/5000000000 : ℝ)^4641 ≤ (9123923360509/20000000000000 : ℝ)^3617 := by
    have hnat : (2712233887 : ℕ)^4641*20000000000000^3617 ≤ 9123923360509^3617*5000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712233887 5000000000 9123923360509 20000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058741729/2000000000 : ℝ), (-841813/5000000 : ℝ), (2712233887/5000000000 : ℝ)] ![(44213451158889/100000000000000 : ℝ), (10166932025363/100000000000000 : ℝ), (9123923360509/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058741729/2000000000 : ℝ)|^4641 ≤ (44213451158889/100000000000000 : ℝ)^3617
        have hw : |(1058741729/2000000000 : ℝ)|=(1058741729/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-841813/5000000 : ℝ)|^4641 ≤ (10166932025363/100000000000000 : ℝ)^3617
        have hw : |(-841813/5000000 : ℝ)|=(841813/5000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712233887/5000000000 : ℝ)|^4641 ≤ (9123923360509/20000000000000 : ℝ)^3617
        have hw : |(2712233887/5000000000 : ℝ)|=(2712233887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s5_6 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058741729/2000000000 : ℝ)*x 0 + (2712233887/5000000000 : ℝ)*x 1 + (-841813/5000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058741729/2000000000 : ℝ)^4641 ≤ (44213451158889/100000000000000 : ℝ)^3617 := by
    have hnat : (1058741729 : ℕ)^4641*100000000000000^3617 ≤ 44213451158889^3617*2000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058741729 2000000000 44213451158889 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2712233887/5000000000 : ℝ)^4641 ≤ (9123923360509/20000000000000 : ℝ)^3617 := by
    have hnat : (2712233887 : ℕ)^4641*20000000000000^3617 ≤ 9123923360509^3617*5000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712233887 5000000000 9123923360509 20000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (841813/5000000 : ℝ)^4641 ≤ (10166932025363/100000000000000 : ℝ)^3617 := by
    have hnat : (841813 : ℕ)^4641*100000000000000^3617 ≤ 10166932025363^3617*5000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      841813 5000000 10166932025363 100000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058741729/2000000000 : ℝ), (2712233887/5000000000 : ℝ), (-841813/5000000 : ℝ)] ![(44213451158889/100000000000000 : ℝ), (9123923360509/20000000000000 : ℝ), (10166932025363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058741729/2000000000 : ℝ)|^4641 ≤ (44213451158889/100000000000000 : ℝ)^3617
        have hw : |(1058741729/2000000000 : ℝ)|=(1058741729/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2712233887/5000000000 : ℝ)|^4641 ≤ (9123923360509/20000000000000 : ℝ)^3617
        have hw : |(2712233887/5000000000 : ℝ)|=(2712233887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-841813/5000000 : ℝ)|^4641 ≤ (10166932025363/100000000000000 : ℝ)^3617
        have hw : |(-841813/5000000 : ℝ)|=(841813/5000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1572_s5_7 (p : ℝ) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4242688031/10000000000 : ℝ)*x 0 + (1122125167/2500000000 : ℝ)*x 1 + (4008002269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4242688031/10000000000 : ℝ)^4641 ≤ (1664153902659/5000000000000 : ℝ)^3617 := by
    have hnat : (4242688031 : ℕ)^4641*5000000000000^3617 ≤ 1664153902659^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242688031 10000000000 1664153902659 5000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1122125167/2500000000 : ℝ)^4641 ≤ (17888690451351/50000000000000 : ℝ)^3617 := by
    have hnat : (1122125167 : ℕ)^4641*50000000000000^3617 ≤ 17888690451351^3617*2500000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122125167 2500000000 17888690451351 50000000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4008002269/10000000000 : ℝ)^4641 ≤ (773488525663/2500000000000 : ℝ)^3617 := by
    have hnat : (4008002269 : ℕ)^4641*2500000000000^3617 ≤ 773488525663^3617*10000000000^4641 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4008002269 10000000000 773488525663 2500000000000 4641 3617 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4641/1024 : ℝ)) 4641 3617 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4242688031/10000000000 : ℝ), (1122125167/2500000000 : ℝ), (4008002269/10000000000 : ℝ)] ![(1664153902659/5000000000000 : ℝ), (17888690451351/50000000000000 : ℝ), (773488525663/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4242688031/10000000000 : ℝ)|^4641 ≤ (1664153902659/5000000000000 : ℝ)^3617
        have hw : |(4242688031/10000000000 : ℝ)|=(4242688031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1122125167/2500000000 : ℝ)|^4641 ≤ (17888690451351/50000000000000 : ℝ)^3617
        have hw : |(1122125167/2500000000 : ℝ)|=(1122125167/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4008002269/10000000000 : ℝ)|^4641 ≤ (773488525663/2500000000000 : ℝ)^3617
        have hw : |(4008002269/10000000000 : ℝ)|=(4008002269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1572_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84094463/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (484/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (89/800 : ℝ)*pair X i i ≤ pair X i h) :
    (1391/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (484/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (89/800 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (484/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (89/800 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (484/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (89/800 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (484/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (89/800 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (484/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (89/800 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (484/3125 : ℝ)*(X 0 2+X 1 2) := by
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
  have hpowlo : (89/800 : ℝ) ^ (4639/1024 : ℝ) ≤ (956110983707203/20000000000000000000 : ℝ) := by
    have hpowers : (89/800 : ℝ)^4639 ≤ (956110983707203/20000000000000000000 : ℝ)^1024 := by
      have hnat : (89 : ℕ)^4639*20000000000000000000^1024 ≤ 956110983707203^1024*800^4639 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        89 800 956110983707203 20000000000000000000 4639 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (89/800 : ℝ)) (X := (956110983707203/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4639 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (484/3125 : ℝ) ^ (4639/1024 : ℝ) ≤ (10701075020748803/50000000000000000000 : ℝ) := by
    have hpowers : (484/3125 : ℝ)^4639 ≤ (10701075020748803/50000000000000000000 : ℝ)^1024 := by
      have hnat : (484 : ℕ)^4639*50000000000000000000^1024 ≤ 10701075020748803^1024*3125^4639 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        484 3125 10701075020748803 50000000000000000000 4639 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (484/3125 : ℝ)) (X := (10701075020748803/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4639 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000956110983707203/10000000000000000000 : ℝ) ≤ (10000211041426271/10000000000000000 : ℝ) ^ (4639/1024 : ℝ) := by
    have hpowers : (10000956110983707203/10000000000000000000 : ℝ)^1024 ≤ (10000211041426271/10000000000000000 : ℝ)^4639 := by
      have hnat : (10000956110983707203 : ℕ)^1024*10000000000000000^4639 ≤ 10000211041426271^4639*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000956110983707203 10000000000000000000 10000211041426271 10000000000000000 1024 4639 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000211041426271/10000000000000000 : ℝ)) (X := (10000956110983707203/10000000000000000000 : ℝ)) (by norm_num) 4639 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100026182704960033621/100000000000000000000 : ℝ) ≤ (10000577890820061/10000000000000000 : ℝ) ^ (4639/1024 : ℝ) := by
    have hpowers : (100026182704960033621/100000000000000000000 : ℝ)^1024 ≤ (10000577890820061/10000000000000000 : ℝ)^4639 := by
      have hnat : (100026182704960033621 : ℕ)^1024*10000000000000000^4639 ≤ 10000577890820061^4639*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100026182704960033621 100000000000000000000 10000577890820061 10000000000000000 1024 4639 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000577890820061/10000000000000000 : ℝ)) (X := (100026182704960033621/100000000000000000000 : ℝ)) (by norm_num) 4639 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25010701075020748803/25000000000000000000 : ℝ) ≤ (10000944740213851/10000000000000000 : ℝ) ^ (4639/1024 : ℝ) := by
    have hpowers : (25010701075020748803/25000000000000000000 : ℝ)^1024 ≤ (10000944740213851/10000000000000000 : ℝ)^4639 := by
      have hnat : (25010701075020748803 : ℕ)^1024*10000000000000000^4639 ≤ 10000944740213851^4639*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010701075020748803 25000000000000000000 10000944740213851 10000000000000000 1024 4639 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000944740213851/10000000000000000 : ℝ)) (X := (25010701075020748803/25000000000000000000 : ℝ)) (by norm_num) 4639 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(956110983707203/20000000000000000000 : ℝ) ≤ ((43622758374730992873/43630000000000000000 : ℝ)+2*(36684939379/43630000000000 : ℝ)*(89/800 : ℝ))^(4639/1024 : ℝ) := by
    rw [show (43622758374730992873/43630000000000000000 : ℝ)+2*(36684939379/43630000000000 : ℝ)*(89/800 : ℝ)=(10000211041426271/10000000000000000 : ℝ) by norm_num, show 1+2*(956110983707203/20000000000000000000 : ℝ)=(10000956110983707203/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10701075020748803/50000000000000000000 : ℝ)+(956110983707203/20000000000000000000 : ℝ) ≤ ((43622758374730992873/43630000000000000000 : ℝ)+(36684939379/43630000000000 : ℝ)*((484/3125 : ℝ)+(89/800 : ℝ)))^(4639/1024 : ℝ) := by
    rw [show (43622758374730992873/43630000000000000000 : ℝ)+(36684939379/43630000000000 : ℝ)*((484/3125 : ℝ)+(89/800 : ℝ))=(10000577890820061/10000000000000000 : ℝ) by norm_num, show 1+(10701075020748803/50000000000000000000 : ℝ)+(956110983707203/20000000000000000000 : ℝ)=(100026182704960033621/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10701075020748803/50000000000000000000 : ℝ) ≤ ((43622758374730992873/43630000000000000000 : ℝ)+2*(36684939379/43630000000000 : ℝ)*(484/3125 : ℝ))^(4639/1024 : ℝ) := by
    rw [show (43622758374730992873/43630000000000000000 : ℝ)+2*(36684939379/43630000000000 : ℝ)*(484/3125 : ℝ)=(10000944740213851/10000000000000000 : ℝ) by norm_num, show 1+2*(10701075020748803/50000000000000000000 : ℝ)=(25010701075020748803/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (43622758374730992873/43630000000000000000 : ℝ)*(X 1 0+X 2 0)+(36684939379/43630000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4639/1024 : ℝ)) (lo := (89/800 : ℝ)) (hi := (484/3125 : ℝ)) (c := (43622758374730992873/43630000000000000000 : ℝ)) (alpha := (36684939379/43630000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (43622758374730992873/43630000000000000000 : ℝ)*(X 0 1+X 2 1)+(36684939379/43630000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4639/1024 : ℝ)) (lo := (89/800 : ℝ)) (hi := (484/3125 : ℝ)) (c := (43622758374730992873/43630000000000000000 : ℝ)) (alpha := (36684939379/43630000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (43622758374730992873/43630000000000000000 : ℝ)*(X 0 2+X 1 2)+(36684939379/43630000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4639/1024 : ℝ)) (lo := (89/800 : ℝ)) (hi := (484/3125 : ℝ)) (c := (43622758374730992873/43630000000000000000 : ℝ)) (alpha := (36684939379/43630000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1782883451/10000000000 : ℝ)*X 0 0+(5425546237/10000000000 : ℝ)*X 0 1+(522012167/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337017653/2500000000 : ℝ)*X 1 0+(-235996513/1250000000 : ℝ)*X 1 1+(522012167/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337017653/2500000000 : ℝ)*X 2 0+(522012167/1000000000 : ℝ)*X 2 1+(-235996513/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((42426249/100000000 : ℝ)*X 0 0+(125170407/312500000 : ℝ)*X 0 1+(4491031201/10000000000 : ℝ)*X 0 2+(42426249/100000000 : ℝ)*X 1 0+(125170407/312500000 : ℝ)*X 1 1+(4491031201/10000000000 : ℝ)*X 1 2+(42426249/100000000 : ℝ)*X 2 0+(125170407/312500000 : ℝ)*X 2 1+(4491031201/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1782910159/10000000000 : ℝ)*X 0 0+(652649027/1250000000 : ℝ)*X 0 1+(216978711/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1058741729/2000000000 : ℝ)*X 1 0+(-841813/5000000 : ℝ)*X 1 1+(2712233887/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1058741729/2000000000 : ℝ)*X 2 0+(2712233887/5000000000 : ℝ)*X 2 1+(-841813/5000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4242688031/10000000000 : ℝ)*X 0 0+(1122125167/2500000000 : ℝ)*X 0 1+(4008002269/10000000000 : ℝ)*X 0 2+(4242688031/10000000000 : ℝ)*X 1 0+(1122125167/2500000000 : ℝ)*X 1 1+(4008002269/10000000000 : ℝ)*X 1 2+(4242688031/10000000000 : ℝ)*X 2 0+(1122125167/2500000000 : ℝ)*X 2 1+(4008002269/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1572_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3560139650685331971586159233/1090750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (277316367/50000000000000 : ℝ)*(base19) + (51797121/10000000000000 : ℝ)*(base23) + (19606841/100000000000000 : ℝ)*(lower2) + (20191859/25000000000000 : ℝ)*(upper3) + (54423137/100000000000000 : ℝ)*(upper5) + (1731848464113107/50000000000000 : ℝ)*(major0) + (1731848464113107/50000000000000 : ℝ)*(major1) + (1731848464113107/50000000000000 : ℝ)*(major2) + (2433988146000621/50000000000000 : ℝ)*(sp0) + (4867984758350983/100000000000000 : ℝ)*(sp1) + (2433992397506253/50000000000000 : ℝ)*(sp2) + (514851076753401/25000000000000 : ℝ)*(sp3) + (4510491237/50000000000000 : ℝ)*(sp4) + (4127657187/100000000000000 : ℝ)*(sp7) + (205940843467079/10000000000000 : ℝ)*(f.failure) + (1216996328245929/25000000000000 : ℝ)*(f.sum) + (4447820020099/872600000000000000000000000 : ℝ)*base66 + (9377249686810886411/2181500000000000000000000000000000 : ℝ)*base67 + (8683644151219613589/2181500000000000000000000000000000 : ℝ)*base70 + (14671588518693613589/2181500000000000000000000000000000 : ℝ)*base72 + (1251989047883/272687500000000000000000000 : ℝ)*base74 + (8116916890999613589/2181500000000000000000000000000000 : ℝ)*base76 + (22846677037487613589/2181500000000000000000000000000000 : ℝ)*base78 + (20638248057627886411/2181500000000000000000000000000000 : ℝ)*base79 + (26384448328917/4363000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (3316423/500000000000000000000 : ℝ)*base90 + (3316423/500000000000000000000 : ℝ)*base92 + (3316423/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26010644390238173707097997633/2181500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (374003809/20000000000000 : ℝ)*(base19) + (202660049/10000000000000 : ℝ)*(base23) + (304584561/50000000000000 : ℝ)*(lower1) + (122986093/50000000000000 : ℝ)*(upper3) + (35452171/50000000000000 : ℝ)*(lower4) + (61497/25000000000 : ℝ)*(upper5) + (3500279508393293/100000000000000 : ℝ)*(major0) + (3500279508393293/100000000000000 : ℝ)*(major1) + (3500279508393293/100000000000000 : ℝ)*(major2) + (2204723313/100000000000000 : ℝ)*(sp2) + (2459699649750249/50000000000000 : ℝ)*(sp4) + (1229849357370363/25000000000000 : ℝ)*(sp5) + (2459697534088347/50000000000000 : ℝ)*(sp6) + (1040579659921633/50000000000000 : ℝ)*(sp7) + (1040579659921633/50000000000000 : ℝ)*(f.failure) + (2459699649750249/50000000000000 : ℝ)*(f.sum) + (9299291739569/2181500000000000000000000000 : ℝ)*base66 + (12265546415983000789/4363000000000000000000000000000000 : ℝ)*base67 + (5024723622959000789/4363000000000000000000000000000000 : ℝ)*base69 + (152365611684406999211/4363000000000000000000000000000000 : ℝ)*base72 + (550589366373/87260000000000000000000000 : ℝ)*base74 + (358832278879985000789/4363000000000000000000000000000000 : ℝ)*base75 + (8135061374904999211/4363000000000000000000000000000000 : ℝ)*base78 + (15578685151809000789/4363000000000000000000000000000000 : ℝ)*base79 + (314066724579/545375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (24218079/2500000000000000000000 : ℝ)*base89 + (24218079/2500000000000000000000 : ℝ)*base91 + (24218079/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1572_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84094463/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (484/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (89/800 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1391/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1572_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1572_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84094463/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7903/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10831/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1391/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1572_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1572_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1572_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4639/1024 : ℝ) ≤ p) (hpb : p ≤ (4641/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (84094463/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7903/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10831/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1391/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1572_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
