-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1678_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:27:57.635627+00:00
-- url     : https://prove2.me/submissions/4dd747ad-ed5d-48af-92fa-6077b61bc3ec

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
theorem support_rectangle_w1678_s0_0 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-287275359/2000000000 : ℝ)*x 0 + (720838441/1250000000 : ℝ)*x 1 + (153851799/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (287275359/2000000000 : ℝ)^5047 ≤ (4382606706127/50000000000000 : ℝ)^4023 := by
    have hnat : (287275359 : ℕ)^5047*50000000000000^4023 ≤ 4382606706127^4023*2000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287275359 2000000000 4382606706127 50000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (720838441/1250000000 : ℝ)^5047 ≤ (2005096912171/4000000000000 : ℝ)^4023 := by
    have hnat : (720838441 : ℕ)^5047*4000000000000^4023 ≤ 2005096912171^4023*1250000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      720838441 1250000000 2005096912171 4000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (153851799/312500000 : ℝ)^5047 ≤ (10276840941213/25000000000000 : ℝ)^4023 := by
    have hnat : (153851799 : ℕ)^5047*25000000000000^4023 ≤ 10276840941213^4023*312500000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153851799 312500000 10276840941213 25000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-287275359/2000000000 : ℝ), (720838441/1250000000 : ℝ), (153851799/312500000 : ℝ)] ![(4382606706127/50000000000000 : ℝ), (2005096912171/4000000000000 : ℝ), (10276840941213/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-287275359/2000000000 : ℝ)|^5047 ≤ (4382606706127/50000000000000 : ℝ)^4023
        have hw : |(-287275359/2000000000 : ℝ)|=(287275359/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(720838441/1250000000 : ℝ)|^5047 ≤ (2005096912171/4000000000000 : ℝ)^4023
        have hw : |(720838441/1250000000 : ℝ)|=(720838441/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(153851799/312500000 : ℝ)|^5047 ≤ (10276840941213/25000000000000 : ℝ)^4023
        have hw : |(153851799/312500000 : ℝ)|=(153851799/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_s0_1 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5427530493/10000000000 : ℝ)*x 0 + (-1898278291/10000000000 : ℝ)*x 1 + (4923258439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5427530493/10000000000 : ℝ)^5047 ≤ (4645675656419/10000000000000 : ℝ)^4023 := by
    have hnat : (5427530493 : ℕ)^5047*10000000000000^4023 ≤ 4645675656419^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427530493 10000000000 4645675656419 10000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1898278291/10000000000 : ℝ)^5047 ≤ (248717410563/2000000000000 : ℝ)^4023 := by
    have hnat : (1898278291 : ℕ)^5047*2000000000000^4023 ≤ 248717410563^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1898278291 10000000000 248717410563 2000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4923258439/10000000000 : ℝ)^5047 ≤ (82214745777/200000000000 : ℝ)^4023 := by
    have hnat : (4923258439 : ℕ)^5047*200000000000^4023 ≤ 82214745777^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4923258439 10000000000 82214745777 200000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5427530493/10000000000 : ℝ), (-1898278291/10000000000 : ℝ), (4923258439/10000000000 : ℝ)] ![(4645675656419/10000000000000 : ℝ), (248717410563/2000000000000 : ℝ), (82214745777/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5427530493/10000000000 : ℝ)|^5047 ≤ (4645675656419/10000000000000 : ℝ)^4023
        have hw : |(5427530493/10000000000 : ℝ)|=(5427530493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1898278291/10000000000 : ℝ)|^5047 ≤ (248717410563/2000000000000 : ℝ)^4023
        have hw : |(-1898278291/10000000000 : ℝ)|=(1898278291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4923258439/10000000000 : ℝ)|^5047 ≤ (82214745777/200000000000 : ℝ)^4023
        have hw : |(4923258439/10000000000 : ℝ)|=(4923258439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_s0_2 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (54275319/100000000 : ℝ)*x 0 + (4923257493/10000000000 : ℝ)*x 1 + (-949138829/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (54275319/100000000 : ℝ)^5047 ≤ (23228385836391/50000000000000 : ℝ)^4023 := by
    have hnat : (54275319 : ℕ)^5047*50000000000000^4023 ≤ 23228385836391^4023*100000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54275319 100000000 23228385836391 50000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4923257493/10000000000 : ℝ)^5047 ≤ (20553681489617/50000000000000 : ℝ)^4023 := by
    have hnat : (4923257493 : ℕ)^5047*50000000000000^4023 ≤ 20553681489617^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4923257493 10000000000 20553681489617 50000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (949138829/5000000000 : ℝ)^5047 ≤ (2487173065151/20000000000000 : ℝ)^4023 := by
    have hnat : (949138829 : ℕ)^5047*20000000000000^4023 ≤ 2487173065151^4023*5000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      949138829 5000000000 2487173065151 20000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(54275319/100000000 : ℝ), (4923257493/10000000000 : ℝ), (-949138829/5000000000 : ℝ)] ![(23228385836391/50000000000000 : ℝ), (20553681489617/50000000000000 : ℝ), (2487173065151/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(54275319/100000000 : ℝ)|^5047 ≤ (23228385836391/50000000000000 : ℝ)^4023
        have hw : |(54275319/100000000 : ℝ)|=(54275319/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4923257493/10000000000 : ℝ)|^5047 ≤ (20553681489617/50000000000000 : ℝ)^4023
        have hw : |(4923257493/10000000000 : ℝ)|=(4923257493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-949138829/5000000000 : ℝ)|^5047 ≤ (2487173065151/20000000000000 : ℝ)^4023
        have hw : |(-949138829/5000000000 : ℝ)|=(949138829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_s0_3 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2033593419/5000000000 : ℝ)*x 0 + (3041376147/10000000000 : ℝ)*x 1 + (5309033759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2033593419/5000000000 : ℝ)^5047 ≤ (8086959324753/25000000000000 : ℝ)^4023 := by
    have hnat : (2033593419 : ℕ)^5047*25000000000000^4023 ≤ 8086959324753^4023*5000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2033593419 5000000000 8086959324753 25000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3041376147/10000000000 : ℝ)^5047 ≤ (22464288124347/100000000000000 : ℝ)^4023 := by
    have hnat : (3041376147 : ℕ)^5047*100000000000000^4023 ≤ 22464288124347^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3041376147 10000000000 22464288124347 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5309033759/10000000000 : ℝ)^5047 ≤ (2259393728689/5000000000000 : ℝ)^4023 := by
    have hnat : (5309033759 : ℕ)^5047*5000000000000^4023 ≤ 2259393728689^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309033759 10000000000 2259393728689 5000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2033593419/5000000000 : ℝ), (3041376147/10000000000 : ℝ), (5309033759/10000000000 : ℝ)] ![(8086959324753/25000000000000 : ℝ), (22464288124347/100000000000000 : ℝ), (2259393728689/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2033593419/5000000000 : ℝ)|^5047 ≤ (8086959324753/25000000000000 : ℝ)^4023
        have hw : |(2033593419/5000000000 : ℝ)|=(2033593419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3041376147/10000000000 : ℝ)|^5047 ≤ (22464288124347/100000000000000 : ℝ)^4023
        have hw : |(3041376147/10000000000 : ℝ)|=(3041376147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5309033759/10000000000 : ℝ)|^5047 ≤ (2259393728689/5000000000000 : ℝ)^4023
        have hw : |(5309033759/10000000000 : ℝ)|=(5309033759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_s0_4 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-359656073/2500000000 : ℝ)*x 0 + (494468463/1000000000 : ℝ)*x 1 + (718065679/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (359656073/2500000000 : ℝ)^5047 ≤ (8782422702081/100000000000000 : ℝ)^4023 := by
    have hnat : (359656073 : ℕ)^5047*100000000000000^4023 ≤ 8782422702081^4023*2500000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      359656073 2500000000 8782422702081 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (494468463/1000000000 : ℝ)^5047 ≤ (41331934518391/100000000000000 : ℝ)^4023 := by
    have hnat : (494468463 : ℕ)^5047*100000000000000^4023 ≤ 41331934518391^4023*1000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      494468463 1000000000 41331934518391 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (718065679/1250000000 : ℝ)^5047 ≤ (12471410691717/25000000000000 : ℝ)^4023 := by
    have hnat : (718065679 : ℕ)^5047*25000000000000^4023 ≤ 12471410691717^4023*1250000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      718065679 1250000000 12471410691717 25000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-359656073/2500000000 : ℝ), (494468463/1000000000 : ℝ), (718065679/1250000000 : ℝ)] ![(8782422702081/100000000000000 : ℝ), (41331934518391/100000000000000 : ℝ), (12471410691717/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-359656073/2500000000 : ℝ)|^5047 ≤ (8782422702081/100000000000000 : ℝ)^4023
        have hw : |(-359656073/2500000000 : ℝ)|=(359656073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(494468463/1000000000 : ℝ)|^5047 ≤ (41331934518391/100000000000000 : ℝ)^4023
        have hw : |(494468463/1000000000 : ℝ)|=(494468463/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(718065679/1250000000 : ℝ)|^5047 ≤ (12471410691717/25000000000000 : ℝ)^4023
        have hw : |(718065679/1250000000 : ℝ)|=(718065679/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_s0_5 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5198108281/10000000000 : ℝ)*x 0 + (-134626489/1250000000 : ℝ)*x 1 + (5744522687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5198108281/10000000000 : ℝ)^5047 ≤ (11001644755883/25000000000000 : ℝ)^4023 := by
    have hnat : (5198108281 : ℕ)^5047*25000000000000^4023 ≤ 11001644755883^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5198108281 10000000000 11001644755883 25000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134626489/1250000000 : ℝ)^5047 ≤ (3053904048693/50000000000000 : ℝ)^4023 := by
    have hnat : (134626489 : ℕ)^5047*50000000000000^4023 ≤ 3053904048693^4023*1250000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134626489 1250000000 3053904048693 50000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5744522687/10000000000 : ℝ)^5047 ≤ (49885612861647/100000000000000 : ℝ)^4023 := by
    have hnat : (5744522687 : ℕ)^5047*100000000000000^4023 ≤ 49885612861647^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5744522687 10000000000 49885612861647 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5198108281/10000000000 : ℝ), (-134626489/1250000000 : ℝ), (5744522687/10000000000 : ℝ)] ![(11001644755883/25000000000000 : ℝ), (3053904048693/50000000000000 : ℝ), (49885612861647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5198108281/10000000000 : ℝ)|^5047 ≤ (11001644755883/25000000000000 : ℝ)^4023
        have hw : |(5198108281/10000000000 : ℝ)|=(5198108281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-134626489/1250000000 : ℝ)|^5047 ≤ (3053904048693/50000000000000 : ℝ)^4023
        have hw : |(-134626489/1250000000 : ℝ)|=(134626489/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5744522687/10000000000 : ℝ)|^5047 ≤ (49885612861647/100000000000000 : ℝ)^4023
        have hw : |(5744522687/10000000000 : ℝ)|=(5744522687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_s0_6 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5198108193/10000000000 : ℝ)*x 0 + (2872260871/5000000000 : ℝ)*x 1 + (-269253373/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5198108193/10000000000 : ℝ)^5047 ≤ (8801315617781/20000000000000 : ℝ)^4023 := by
    have hnat : (5198108193 : ℕ)^5047*20000000000000^4023 ≤ 8801315617781^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5198108193 10000000000 8801315617781 20000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2872260871/5000000000 : ℝ)^5047 ≤ (6235700320801/12500000000000 : ℝ)^4023 := by
    have hnat : (2872260871 : ℕ)^5047*12500000000000^4023 ≤ 6235700320801^4023*5000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2872260871 5000000000 6235700320801 12500000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269253373/2500000000 : ℝ)^5047 ≤ (1526954834599/25000000000000 : ℝ)^4023 := by
    have hnat : (269253373 : ℕ)^5047*25000000000000^4023 ≤ 1526954834599^4023*2500000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269253373 2500000000 1526954834599 25000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5198108193/10000000000 : ℝ), (2872260871/5000000000 : ℝ), (-269253373/2500000000 : ℝ)] ![(8801315617781/20000000000000 : ℝ), (6235700320801/12500000000000 : ℝ), (1526954834599/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5198108193/10000000000 : ℝ)|^5047 ≤ (8801315617781/20000000000000 : ℝ)^4023
        have hw : |(5198108193/10000000000 : ℝ)|=(5198108193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2872260871/5000000000 : ℝ)|^5047 ≤ (6235700320801/12500000000000 : ℝ)^4023
        have hw : |(2872260871/5000000000 : ℝ)|=(2872260871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-269253373/2500000000 : ℝ)|^5047 ≤ (1526954834599/25000000000000 : ℝ)^4023
        have hw : |(-269253373/2500000000 : ℝ)|=(269253373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_s0_7 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (32585819/80000000 : ℝ)*x 0 + (5251424677/10000000000 : ℝ)*x 1 + (3101016261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (32585819/80000000 : ℝ)^5047 ≤ (506376873473/1562500000000 : ℝ)^4023 := by
    have hnat : (32585819 : ℕ)^5047*1562500000000^4023 ≤ 506376873473^4023*80000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32585819 80000000 506376873473 1562500000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5251424677/10000000000 : ℝ)^5047 ≤ (44573576929403/100000000000000 : ℝ)^4023 := by
    have hnat : (5251424677 : ℕ)^5047*100000000000000^4023 ≤ 44573576929403^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251424677 10000000000 44573576929403 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3101016261/10000000000 : ℝ)^5047 ≤ (23018303154177/100000000000000 : ℝ)^4023 := by
    have hnat : (3101016261 : ℕ)^5047*100000000000000^4023 ≤ 23018303154177^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3101016261 10000000000 23018303154177 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(32585819/80000000 : ℝ), (5251424677/10000000000 : ℝ), (3101016261/10000000000 : ℝ)] ![(506376873473/1562500000000 : ℝ), (44573576929403/100000000000000 : ℝ), (23018303154177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(32585819/80000000 : ℝ)|^5047 ≤ (506376873473/1562500000000 : ℝ)^4023
        have hw : |(32585819/80000000 : ℝ)|=(32585819/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5251424677/10000000000 : ℝ)|^5047 ≤ (44573576929403/100000000000000 : ℝ)^4023
        have hw : |(5251424677/10000000000 : ℝ)|=(5251424677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3101016261/10000000000 : ℝ)|^5047 ≤ (23018303154177/100000000000000 : ℝ)^4023
        have hw : |(3101016261/10000000000 : ℝ)|=(3101016261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1678_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (46106879/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (5023/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (11553/50000 : ℝ)*pair X 0 0 := by
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
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (5039/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5039 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5039*1^1024 ≤ 0^1024*1^5039 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5039 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5039 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5039/1024 : ℝ) ≤ (1100975445190806547/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5039 ≤ (1100975445190806547/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5039*100000000000000000000^1024 ≤ 1100975445190806547^1024*5^5039 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1100975445190806547 100000000000000000000 5039 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1100975445190806547/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5039 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5039/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5039 := by
      have hnat : (1 : ℕ)^1024*1^5039 ≤ 1^5039*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5039 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101100975445190806547/100000000000000000000 : ℝ) ≤ (2004455194336793/2000000000000000 : ℝ) ^ (5039/1024 : ℝ) := by
    have hpowers : (101100975445190806547/100000000000000000000 : ℝ)^1024 ≤ (2004455194336793/2000000000000000 : ℝ)^5039 := by
      have hnat : (101100975445190806547 : ℕ)^1024*2000000000000000^5039 ≤ 2004455194336793^5039*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101100975445190806547 100000000000000000000 2004455194336793 2000000000000000 1024 5039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2004455194336793/2000000000000000 : ℝ)) (X := (101100975445190806547/100000000000000000000 : ℝ)) (by norm_num) 5039 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51100975445190806547/50000000000000000000 : ℝ) ≤ (1004455194336793/1000000000000000 : ℝ) ^ (5039/1024 : ℝ) := by
    have hpowers : (51100975445190806547/50000000000000000000 : ℝ)^1024 ≤ (1004455194336793/1000000000000000 : ℝ)^5039 := by
      have hnat : (51100975445190806547 : ℕ)^1024*1000000000000000^5039 ≤ 1004455194336793^5039*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51100975445190806547 50000000000000000000 1004455194336793 1000000000000000 1024 5039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1004455194336793/1000000000000000 : ℝ)) (X := (51100975445190806547/50000000000000000000 : ℝ)) (by norm_num) 5039 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(4455194336793/800000000000000 : ℝ)*(0 : ℝ))^(5039/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(4455194336793/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1100975445190806547/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(4455194336793/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5039/1024 : ℝ) := by
    rw [show (1 : ℝ)+(4455194336793/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2004455194336793/2000000000000000 : ℝ) by norm_num, show 1+(1100975445190806547/100000000000000000000 : ℝ)+(0 : ℝ)=(101100975445190806547/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1100975445190806547/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(4455194336793/800000000000000 : ℝ)*(2/5 : ℝ))^(5039/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(4455194336793/800000000000000 : ℝ)*(2/5 : ℝ)=(1004455194336793/1000000000000000 : ℝ) by norm_num, show 1+2*(1100975445190806547/100000000000000000000 : ℝ)=(51100975445190806547/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(4455194336793/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5039/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4455194336793/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(4455194336793/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5039/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4455194336793/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(4455194336793/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5039/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (4455194336793/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-287275359/2000000000 : ℝ)*X 0 0+(720838441/1250000000 : ℝ)*X 0 1+(153851799/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5427530493/10000000000 : ℝ)*X 1 0+(-1898278291/10000000000 : ℝ)*X 1 1+(4923258439/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((54275319/100000000 : ℝ)*X 2 0+(4923257493/10000000000 : ℝ)*X 2 1+(-949138829/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2033593419/5000000000 : ℝ)*X 0 0+(3041376147/10000000000 : ℝ)*X 0 1+(5309033759/10000000000 : ℝ)*X 0 2+(2033593419/5000000000 : ℝ)*X 1 0+(3041376147/10000000000 : ℝ)*X 1 1+(5309033759/10000000000 : ℝ)*X 1 2+(2033593419/5000000000 : ℝ)*X 2 0+(3041376147/10000000000 : ℝ)*X 2 1+(5309033759/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-359656073/2500000000 : ℝ)*X 0 0+(494468463/1000000000 : ℝ)*X 0 1+(718065679/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5198108281/10000000000 : ℝ)*X 1 0+(-134626489/1250000000 : ℝ)*X 1 1+(5744522687/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5198108193/10000000000 : ℝ)*X 2 0+(2872260871/5000000000 : ℝ)*X 2 1+(-269253373/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((32585819/80000000 : ℝ)*X 0 0+(5251424677/10000000000 : ℝ)*X 0 1+(3101016261/10000000000 : ℝ)*X 0 2+(32585819/80000000 : ℝ)*X 1 0+(5251424677/10000000000 : ℝ)*X 1 1+(3101016261/10000000000 : ℝ)*X 1 2+(32585819/80000000 : ℝ)*X 2 0+(5251424677/10000000000 : ℝ)*X 2 1+(3101016261/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12025605418700578975251/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (76351417/100000000000000 : ℝ)*(base1) + (33613763/4000000000000 : ℝ)*(base19) + (1120920213/100000000000000 : ℝ)*(base23) + (5355097/20000000000000 : ℝ)*(base24) + (103098039/50000000000000 : ℝ)*(upper5) + (203325440482031/25000000000000 : ℝ)*(major0) + (203325440482031/25000000000000 : ℝ)*(major1) + (203325440482031/25000000000000 : ℝ)*(major2) + (592805116488033/50000000000000 : ℝ)*(sp0) + (592807655325421/50000000000000 : ℝ)*(sp1) + (1185615003299219/100000000000000 : ℝ)*(sp2) + (11024639697547/2500000000000 : ℝ)*(sp3) + (5994370269/100000000000000 : ℝ)*(sp4) + (1548266619/100000000000000 : ℝ)*(sp7) + (440987212519917/100000000000000 : ℝ)*(f.failure) + (592808075497459/50000000000000 : ℝ)*(f.sum) + (32073403196583/10000000000000000000000000000 : ℝ)*base65 + (116701203846583/20000000000000000000000000000 : ℝ)*base67 + (47203135166583/20000000000000000000000000000 : ℝ)*base69 + (140453765246583/20000000000000000000000000000 : ℝ)*base71 + (39185854656583/10000000000000000000000000000 : ℝ)*base73 + (141874996326583/20000000000000000000000000000 : ℝ)*base75 + (65724545366583/20000000000000000000000000000 : ℝ)*base77 + (109431050866583/20000000000000000000000000000 : ℝ)*base79 + (23959815103417/10000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1790957/2500000000000000000000 : ℝ)*base90 + (1790957/2500000000000000000000 : ℝ)*base92 + (1790957/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (222899286391217966491347/40000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (56970047/4000000000000 : ℝ)*(base19) + (182042973/12500000000000 : ℝ)*(base23) + (154804677/100000000000000 : ℝ)*(base39) + (10689473/50000000000000 : ℝ)*(upper2) + (61869/12500000000000 : ℝ)*(upper3) + (44852613/20000000000000 : ℝ)*(upper5) + (214409499602171/25000000000000 : ℝ)*(major0) + (214409499602171/25000000000000 : ℝ)*(major1) + (857637843604007/100000000000000 : ℝ)*(major2) + (639011589/20000000000000 : ℝ)*(sp1) + (625124259383937/50000000000000 : ℝ)*(sp4) + (250048779891751/20000000000000 : ℝ)*(sp5) + (1250247217228767/100000000000000 : ℝ)*(sp6) + (465027137495407/100000000000000 : ℝ)*(sp7) + (465027137495407/100000000000000 : ℝ)*(f.failure) + (1250248673572551/100000000000000 : ℝ)*(f.sum) + (42840320879963/80000000000000000000000000000 : ℝ)*base65 + (460660469609551/80000000000000000000000000000 : ℝ)*base67 + (15122007922397/20000000000000000000000000000 : ℝ)*base70 + (59539410870449/80000000000000000000000000000 : ℝ)*base72 + (199470275519963/80000000000000000000000000000 : ℝ)*base73 + (103841027362397/20000000000000000000000000000 : ℝ)*base76 + (108682594857603/20000000000000000000000000000 : ℝ)*base77 + (26959474917603/20000000000000000000000000000 : ℝ)*base79 + (16877200652397/10000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (6395247/2500000000000000000000 : ℝ)*base90 + (6395247/2500000000000000000000 : ℝ)*base92 + (6395247/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1678_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (46106879/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5023/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (11553/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1678_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1678_s1_0 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-382350869/2500000000 : ℝ)*x 0 + (5520068473/10000000000 : ℝ)*x 1 + (510918819/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (382350869/2500000000 : ℝ)^5047 ≤ (4741581815609/50000000000000 : ℝ)^4023 := by
    have hnat : (382350869 : ℕ)^5047*50000000000000^4023 ≤ 4741581815609^4023*2500000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      382350869 2500000000 4741581815609 50000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5520068473/10000000000 : ℝ)^5047 ≤ (47452591358983/100000000000000 : ℝ)^4023 := by
    have hnat : (5520068473 : ℕ)^5047*100000000000000^4023 ≤ 47452591358983^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5520068473 10000000000 47452591358983 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (510918819/1000000000 : ℝ)^5047 ≤ (8612848998861/20000000000000 : ℝ)^4023 := by
    have hnat : (510918819 : ℕ)^5047*20000000000000^4023 ≤ 8612848998861^4023*1000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      510918819 1000000000 8612848998861 20000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-382350869/2500000000 : ℝ), (5520068473/10000000000 : ℝ), (510918819/1000000000 : ℝ)] ![(4741581815609/50000000000000 : ℝ), (47452591358983/100000000000000 : ℝ), (8612848998861/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-382350869/2500000000 : ℝ)|^5047 ≤ (4741581815609/50000000000000 : ℝ)^4023
        have hw : |(-382350869/2500000000 : ℝ)|=(382350869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5520068473/10000000000 : ℝ)|^5047 ≤ (47452591358983/100000000000000 : ℝ)^4023
        have hw : |(5520068473/10000000000 : ℝ)|=(5520068473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(510918819/1000000000 : ℝ)|^5047 ≤ (8612848998861/20000000000000 : ℝ)^4023
        have hw : |(510918819/1000000000 : ℝ)|=(510918819/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_s1_1 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5361814389/10000000000 : ℝ)*x 0 + (-4360707/25000000 : ℝ)*x 1 + (319324259/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5361814389/10000000000 : ℝ)^5047 ≤ (45752177194003/100000000000000 : ℝ)^4023 := by
    have hnat : (5361814389 : ℕ)^5047*100000000000000^4023 ≤ 45752177194003^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361814389 10000000000 45752177194003 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4360707/25000000 : ℝ)^5047 ≤ (11183578280213/100000000000000 : ℝ)^4023 := by
    have hnat : (4360707 : ℕ)^5047*100000000000000^4023 ≤ 11183578280213^4023*25000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360707 25000000 11183578280213 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (319324259/625000000 : ℝ)^5047 ≤ (43064244507891/100000000000000 : ℝ)^4023 := by
    have hnat : (319324259 : ℕ)^5047*100000000000000^4023 ≤ 43064244507891^4023*625000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319324259 625000000 43064244507891 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5361814389/10000000000 : ℝ), (-4360707/25000000 : ℝ), (319324259/625000000 : ℝ)] ![(45752177194003/100000000000000 : ℝ), (11183578280213/100000000000000 : ℝ), (43064244507891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5361814389/10000000000 : ℝ)|^5047 ≤ (45752177194003/100000000000000 : ℝ)^4023
        have hw : |(5361814389/10000000000 : ℝ)|=(5361814389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4360707/25000000 : ℝ)|^5047 ≤ (11183578280213/100000000000000 : ℝ)^4023
        have hw : |(-4360707/25000000 : ℝ)|=(4360707/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(319324259/625000000 : ℝ)|^5047 ≤ (43064244507891/100000000000000 : ℝ)^4023
        have hw : |(319324259/625000000 : ℝ)|=(319324259/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_s1_2 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (536181393/1000000000 : ℝ)*x 0 + (5109188579/10000000000 : ℝ)*x 1 + (-1744282839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536181393/1000000000 : ℝ)^5047 ≤ (45752172280447/100000000000000 : ℝ)^4023 := by
    have hnat : (536181393 : ℕ)^5047*100000000000000^4023 ≤ 45752172280447^4023*1000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536181393 1000000000 45752172280447 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5109188579/10000000000 : ℝ)^5047 ≤ (1722569964307/4000000000000 : ℝ)^4023 := by
    have hnat : (5109188579 : ℕ)^5047*4000000000000^4023 ≤ 1722569964307^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5109188579 10000000000 1722569964307 4000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1744282839/10000000000 : ℝ)^5047 ≤ (11183578593911/100000000000000 : ℝ)^4023 := by
    have hnat : (1744282839 : ℕ)^5047*100000000000000^4023 ≤ 11183578593911^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1744282839 10000000000 11183578593911 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536181393/1000000000 : ℝ), (5109188579/10000000000 : ℝ), (-1744282839/10000000000 : ℝ)] ![(45752172280447/100000000000000 : ℝ), (1722569964307/4000000000000 : ℝ), (11183578593911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536181393/1000000000 : ℝ)|^5047 ≤ (45752172280447/100000000000000 : ℝ)^4023
        have hw : |(536181393/1000000000 : ℝ)|=(536181393/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5109188579/10000000000 : ℝ)|^5047 ≤ (1722569964307/4000000000000 : ℝ)^4023
        have hw : |(5109188579/10000000000 : ℝ)|=(5109188579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1744282839/10000000000 : ℝ)|^5047 ≤ (11183578593911/100000000000000 : ℝ)^4023
        have hw : |(-1744282839/10000000000 : ℝ)|=(1744282839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_s1_3 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (828501257/2000000000 : ℝ)*x 0 + (3615549147/10000000000 : ℝ)*x 1 + (944044211/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (828501257/2000000000 : ℝ)^5047 ≤ (33101122135033/100000000000000 : ℝ)^4023 := by
    have hnat : (828501257 : ℕ)^5047*100000000000000^4023 ≤ 33101122135033^4023*2000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      828501257 2000000000 33101122135033 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3615549147/10000000000 : ℝ)^5047 ≤ (13953512183319/50000000000000 : ℝ)^4023 := by
    have hnat : (3615549147 : ℕ)^5047*50000000000000^4023 ≤ 13953512183319^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3615549147 10000000000 13953512183319 50000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (944044211/2000000000 : ℝ)^5047 ≤ (38991853478153/100000000000000 : ℝ)^4023 := by
    have hnat : (944044211 : ℕ)^5047*100000000000000^4023 ≤ 38991853478153^4023*2000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      944044211 2000000000 38991853478153 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(828501257/2000000000 : ℝ), (3615549147/10000000000 : ℝ), (944044211/2000000000 : ℝ)] ![(33101122135033/100000000000000 : ℝ), (13953512183319/50000000000000 : ℝ), (38991853478153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(828501257/2000000000 : ℝ)|^5047 ≤ (33101122135033/100000000000000 : ℝ)^4023
        have hw : |(828501257/2000000000 : ℝ)|=(828501257/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3615549147/10000000000 : ℝ)|^5047 ≤ (13953512183319/50000000000000 : ℝ)^4023
        have hw : |(3615549147/10000000000 : ℝ)|=(3615549147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(944044211/2000000000 : ℝ)|^5047 ≤ (38991853478153/100000000000000 : ℝ)^4023
        have hw : |(944044211/2000000000 : ℝ)|=(944044211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_s1_4 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1529659759/10000000000 : ℝ)*x 0 + (1022850557/2000000000 : ℝ)*x 1 + (2757458259/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1529659759/10000000000 : ℝ)^5047 ≤ (948515725637/10000000000000 : ℝ)^4023 := by
    have hnat : (1529659759 : ℕ)^5047*10000000000000^4023 ≤ 948515725637^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1529659759 10000000000 948515725637 10000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1022850557/2000000000 : ℝ)^5047 ≤ (10779451468597/25000000000000 : ℝ)^4023 := by
    have hnat : (1022850557 : ℕ)^5047*25000000000000^4023 ≤ 10779451468597^4023*2000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1022850557 2000000000 10779451468597 25000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2757458259/5000000000 : ℝ)^5047 ≤ (47397036864359/100000000000000 : ℝ)^4023 := by
    have hnat : (2757458259 : ℕ)^5047*100000000000000^4023 ≤ 47397036864359^4023*5000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757458259 5000000000 47397036864359 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1529659759/10000000000 : ℝ), (1022850557/2000000000 : ℝ), (2757458259/5000000000 : ℝ)] ![(948515725637/10000000000000 : ℝ), (10779451468597/25000000000000 : ℝ), (47397036864359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1529659759/10000000000 : ℝ)|^5047 ≤ (948515725637/10000000000000 : ℝ)^4023
        have hw : |(-1529659759/10000000000 : ℝ)|=(1529659759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1022850557/2000000000 : ℝ)|^5047 ≤ (10779451468597/25000000000000 : ℝ)^4023
        have hw : |(1022850557/2000000000 : ℝ)|=(1022850557/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2757458259/5000000000 : ℝ)|^5047 ≤ (47397036864359/100000000000000 : ℝ)^4023
        have hw : |(2757458259/5000000000 : ℝ)|=(2757458259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_s1_5 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5252028893/10000000000 : ℝ)*x 0 + (-334638999/2500000000 : ℝ)*x 1 + (5514917311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5252028893/10000000000 : ℝ)^5047 ≤ (22290005473163/50000000000000 : ℝ)^4023 := by
    have hnat : (5252028893 : ℕ)^5047*50000000000000^4023 ≤ 22290005473163^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252028893 10000000000 22290005473163 50000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (334638999/2500000000 : ℝ)^5047 ≤ (802294361749/10000000000000 : ℝ)^4023 := by
    have hnat : (334638999 : ℕ)^5047*10000000000000^4023 ≤ 802294361749^4023*2500000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334638999 2500000000 802294361749 10000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5514917311/10000000000 : ℝ)^5047 ≤ (4739704541441/10000000000000 : ℝ)^4023 := by
    have hnat : (5514917311 : ℕ)^5047*10000000000000^4023 ≤ 4739704541441^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5514917311 10000000000 4739704541441 10000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5252028893/10000000000 : ℝ), (-334638999/2500000000 : ℝ), (5514917311/10000000000 : ℝ)] ![(22290005473163/50000000000000 : ℝ), (802294361749/10000000000000 : ℝ), (4739704541441/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5252028893/10000000000 : ℝ)|^5047 ≤ (22290005473163/50000000000000 : ℝ)^4023
        have hw : |(5252028893/10000000000 : ℝ)|=(5252028893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-334638999/2500000000 : ℝ)|^5047 ≤ (802294361749/10000000000000 : ℝ)^4023
        have hw : |(-334638999/2500000000 : ℝ)|=(334638999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5514917311/10000000000 : ℝ)|^5047 ≤ (4739704541441/10000000000000 : ℝ)^4023
        have hw : |(5514917311/10000000000 : ℝ)|=(5514917311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_s1_6 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (262601493/500000000 : ℝ)*x 0 + (5514917017/10000000000 : ℝ)*x 1 + (-26771101/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262601493/500000000 : ℝ)^5047 ≤ (44580021243613/100000000000000 : ℝ)^4023 := by
    have hnat : (262601493 : ℕ)^5047*100000000000000^4023 ≤ 44580021243613^4023*500000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262601493 500000000 44580021243613 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5514917017/10000000000 : ℝ)^5047 ≤ (47397042244529/100000000000000 : ℝ)^4023 := by
    have hnat : (5514917017 : ℕ)^5047*100000000000000^4023 ≤ 47397042244529^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5514917017 10000000000 47397042244529 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26771101/200000000 : ℝ)^5047 ≤ (8022936504183/100000000000000 : ℝ)^4023 := by
    have hnat : (26771101 : ℕ)^5047*100000000000000^4023 ≤ 8022936504183^4023*200000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26771101 200000000 8022936504183 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262601493/500000000 : ℝ), (5514917017/10000000000 : ℝ), (-26771101/200000000 : ℝ)] ![(44580021243613/100000000000000 : ℝ), (47397042244529/100000000000000 : ℝ), (8022936504183/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262601493/500000000 : ℝ)|^5047 ≤ (44580021243613/100000000000000 : ℝ)^4023
        have hw : |(262601493/500000000 : ℝ)|=(262601493/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5514917017/10000000000 : ℝ)|^5047 ≤ (47397042244529/100000000000000 : ℝ)^4023
        have hw : |(5514917017/10000000000 : ℝ)|=(5514917017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-26771101/200000000 : ℝ)|^5047 ≤ (8022936504183/100000000000000 : ℝ)^4023
        have hw : |(-26771101/200000000 : ℝ)|=(26771101/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_s1_7 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (414319429/1000000000 : ℝ)*x 0 + (4706602487/10000000000 : ℝ)*x 1 + (3629399619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (414319429/1000000000 : ℝ)^5047 ≤ (33108019188403/100000000000000 : ℝ)^4023 := by
    have hnat : (414319429 : ℕ)^5047*100000000000000^4023 ≤ 33108019188403^4023*1000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414319429 1000000000 33108019188403 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4706602487/10000000000 : ℝ)^5047 ≤ (1214086659059/3125000000000 : ℝ)^4023 := by
    have hnat : (4706602487 : ℕ)^5047*3125000000000^4023 ≤ 1214086659059^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4706602487 10000000000 1214086659059 3125000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3629399619/10000000000 : ℝ)^5047 ≤ (5608241540919/20000000000000 : ℝ)^4023 := by
    have hnat : (3629399619 : ℕ)^5047*20000000000000^4023 ≤ 5608241540919^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3629399619 10000000000 5608241540919 20000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(414319429/1000000000 : ℝ), (4706602487/10000000000 : ℝ), (3629399619/10000000000 : ℝ)] ![(33108019188403/100000000000000 : ℝ), (1214086659059/3125000000000 : ℝ), (5608241540919/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(414319429/1000000000 : ℝ)|^5047 ≤ (33108019188403/100000000000000 : ℝ)^4023
        have hw : |(414319429/1000000000 : ℝ)|=(414319429/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4706602487/10000000000 : ℝ)|^5047 ≤ (1214086659059/3125000000000 : ℝ)^4023
        have hw : |(4706602487/10000000000 : ℝ)|=(4706602487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3629399619/10000000000 : ℝ)|^5047 ≤ (5608241540919/20000000000000 : ℝ)^4023
        have hw : |(3629399619/10000000000 : ℝ)|=(3629399619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1678_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (46106879/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (11553/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5023/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4593/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4479/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (11553/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5023/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (11553/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5023/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (11553/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5023/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (11553/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5023/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (11553/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5023/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (11553/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5023/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5023/100000 : ℝ) ^ (5039/1024 : ℝ) ≤ (10127721303039/25000000000000000000 : ℝ) := by
    have hpowers : (5023/100000 : ℝ)^5039 ≤ (10127721303039/25000000000000000000 : ℝ)^1024 := by
      have hnat : (5023 : ℕ)^5039*25000000000000000000^1024 ≤ 10127721303039^1024*100000^5039 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5023 100000 10127721303039 25000000000000000000 5039 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5023/100000 : ℝ)) (X := (10127721303039/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5039 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (11553/50000 : ℝ) ^ (5039/1024 : ℝ) ≤ (73952729858411041/100000000000000000000 : ℝ) := by
    have hpowers : (11553/50000 : ℝ)^5039 ≤ (73952729858411041/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11553 : ℕ)^5039*100000000000000000000^1024 ≤ 73952729858411041^1024*50000^5039 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11553 50000 73952729858411041 100000000000000000000 5039 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11553/50000 : ℝ)) (X := (73952729858411041/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5039 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500010127721303039/12500000000000000000 : ℝ) ≤ (5000000823241379/5000000000000000 : ℝ) ^ (5039/1024 : ℝ) := by
    have hpowers : (12500010127721303039/12500000000000000000 : ℝ)^1024 ≤ (5000000823241379/5000000000000000 : ℝ)^5039 := by
      have hnat : (12500010127721303039 : ℕ)^1024*5000000000000000^5039 ≤ 5000000823241379^5039*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500010127721303039 12500000000000000000 5000000823241379 5000000000000000 1024 5039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000823241379/5000000000000000 : ℝ)) (X := (12500010127721303039/12500000000000000000 : ℝ)) (by norm_num) 5039 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100073993240743623197/100000000000000000000 : ℝ) ≤ (400060128400823/400000000000000 : ℝ) ^ (5039/1024 : ℝ) := by
    have hpowers : (100073993240743623197/100000000000000000000 : ℝ)^1024 ≤ (400060128400823/400000000000000 : ℝ)^5039 := by
      have hnat : (100073993240743623197 : ℕ)^1024*400000000000000^5039 ≤ 400060128400823^5039*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100073993240743623197 100000000000000000000 400060128400823 400000000000000 1024 5039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400060128400823/400000000000000 : ℝ)) (X := (100073993240743623197/100000000000000000000 : ℝ)) (by norm_num) 5039 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50073952729858411041/50000000000000000000 : ℝ) ≤ (1250375596694799/1250000000000000 : ℝ) ^ (5039/1024 : ℝ) := by
    have hpowers : (50073952729858411041/50000000000000000000 : ℝ)^1024 ≤ (1250375596694799/1250000000000000 : ℝ)^5039 := by
      have hnat : (50073952729858411041 : ℕ)^1024*1250000000000000^5039 ≤ 1250375596694799^5039*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50073952729858411041 50000000000000000000 1250375596694799 1250000000000000 1024 5039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250375596694799/1250000000000000 : ℝ)) (X := (50073952729858411041/50000000000000000000 : ℝ)) (by norm_num) 5039 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10127721303039/25000000000000000000 : ℝ) ≤ ((45203736266511700833/45207500000000000000 : ℝ)+2*(1501563537817/1808300000000000 : ℝ)*(5023/100000 : ℝ))^(5039/1024 : ℝ) := by
    rw [show (45203736266511700833/45207500000000000000 : ℝ)+2*(1501563537817/1808300000000000 : ℝ)*(5023/100000 : ℝ)=(5000000823241379/5000000000000000 : ℝ) by norm_num, show 1+2*(10127721303039/25000000000000000000 : ℝ)=(12500010127721303039/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(73952729858411041/100000000000000000000 : ℝ)+(10127721303039/25000000000000000000 : ℝ) ≤ ((45203736266511700833/45207500000000000000 : ℝ)+(1501563537817/1808300000000000 : ℝ)*((11553/50000 : ℝ)+(5023/100000 : ℝ)))^(5039/1024 : ℝ) := by
    rw [show (45203736266511700833/45207500000000000000 : ℝ)+(1501563537817/1808300000000000 : ℝ)*((11553/50000 : ℝ)+(5023/100000 : ℝ))=(400060128400823/400000000000000 : ℝ) by norm_num, show 1+(73952729858411041/100000000000000000000 : ℝ)+(10127721303039/25000000000000000000 : ℝ)=(100073993240743623197/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(73952729858411041/100000000000000000000 : ℝ) ≤ ((45203736266511700833/45207500000000000000 : ℝ)+2*(1501563537817/1808300000000000 : ℝ)*(11553/50000 : ℝ))^(5039/1024 : ℝ) := by
    rw [show (45203736266511700833/45207500000000000000 : ℝ)+2*(1501563537817/1808300000000000 : ℝ)*(11553/50000 : ℝ)=(1250375596694799/1250000000000000 : ℝ) by norm_num, show 1+2*(73952729858411041/100000000000000000000 : ℝ)=(50073952729858411041/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (45203736266511700833/45207500000000000000 : ℝ)*(X 1 0+X 2 0)+(1501563537817/1808300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5039/1024 : ℝ)) (lo := (5023/100000 : ℝ)) (hi := (11553/50000 : ℝ)) (c := (45203736266511700833/45207500000000000000 : ℝ)) (alpha := (1501563537817/1808300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (45203736266511700833/45207500000000000000 : ℝ)*(X 0 1+X 2 1)+(1501563537817/1808300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5039/1024 : ℝ)) (lo := (5023/100000 : ℝ)) (hi := (11553/50000 : ℝ)) (c := (45203736266511700833/45207500000000000000 : ℝ)) (alpha := (1501563537817/1808300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (45203736266511700833/45207500000000000000 : ℝ)*(X 0 2+X 1 2)+(1501563537817/1808300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5039/1024 : ℝ)) (lo := (5023/100000 : ℝ)) (hi := (11553/50000 : ℝ)) (c := (45203736266511700833/45207500000000000000 : ℝ)) (alpha := (1501563537817/1808300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-382350869/2500000000 : ℝ)*X 0 0+(5520068473/10000000000 : ℝ)*X 0 1+(510918819/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5361814389/10000000000 : ℝ)*X 1 0+(-4360707/25000000 : ℝ)*X 1 1+(319324259/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((536181393/1000000000 : ℝ)*X 2 0+(5109188579/10000000000 : ℝ)*X 2 1+(-1744282839/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((828501257/2000000000 : ℝ)*X 0 0+(3615549147/10000000000 : ℝ)*X 0 1+(944044211/2000000000 : ℝ)*X 0 2+(828501257/2000000000 : ℝ)*X 1 0+(3615549147/10000000000 : ℝ)*X 1 1+(944044211/2000000000 : ℝ)*X 1 2+(828501257/2000000000 : ℝ)*X 2 0+(3615549147/10000000000 : ℝ)*X 2 1+(944044211/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1529659759/10000000000 : ℝ)*X 0 0+(1022850557/2000000000 : ℝ)*X 0 1+(2757458259/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5252028893/10000000000 : ℝ)*X 1 0+(-334638999/2500000000 : ℝ)*X 1 1+(5514917311/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((262601493/500000000 : ℝ)*X 2 0+(5514917017/10000000000 : ℝ)*X 2 1+(-26771101/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((414319429/1000000000 : ℝ)*X 0 0+(4706602487/10000000000 : ℝ)*X 0 1+(3629399619/10000000000 : ℝ)*X 0 2+(414319429/1000000000 : ℝ)*X 1 0+(4706602487/10000000000 : ℝ)*X 1 1+(3629399619/10000000000 : ℝ)*X 1 2+(414319429/1000000000 : ℝ)*X 2 0+(4706602487/10000000000 : ℝ)*X 2 1+(3629399619/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9771521264506730926949409243/1130187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (654417801/50000000000000 : ℝ)*(base19) + (536779381/50000000000000 : ℝ)*(base23) + (102336409/50000000000000 : ℝ)*(upper3) + (14438733/100000000000000 : ℝ)*(upper4) + (131334297/100000000000000 : ℝ)*(upper5) + (834768910518081/50000000000000 : ℝ)*(major0) + (834768910518081/50000000000000 : ℝ)*(major1) + (834768910518081/50000000000000 : ℝ)*(major2) + (486762140897327/20000000000000 : ℝ)*(sp0) + (2433819852364171/100000000000000 : ℝ)*(sp1) + (2433820087641011/100000000000000 : ℝ)*(sp2) + (905250019967939/100000000000000 : ℝ)*(sp3) + (5228356569/50000000000000 : ℝ)*(sp4) + (834541391/20000000000000 : ℝ)*(sp7) + (452627096337447/50000000000000 : ℝ)*(f.failure) + (608455290299943/25000000000000 : ℝ)*(f.sum) + (134968722655291/90415000000000000000000000000 : ℝ)*base66 + (20001099131407561473/2260375000000000000000000000000000 : ℝ)*base67 + (8699411469027186473/2260375000000000000000000000000000 : ℝ)*base69 + (7813163277367186473/2260375000000000000000000000000000 : ℝ)*base71 + (1188511365399/5650937500000000000000000000 : ℝ)*base73 + (34592155171193436473/2260375000000000000000000000000000 : ℝ)*base75 + (17118614700490561473/2260375000000000000000000000000000 : ℝ)*base77 + (17792112210936061473/2260375000000000000000000000000000 : ℝ)*base79 + (284421914609461/90415000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (13002087/1250000000000000000000 : ℝ)*base90 + (13002087/1250000000000000000000 : ℝ)*base92 + (13002087/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9807616598755521015781309539/2260375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27956021/12500000000000 : ℝ)*(base23) + (2605547/25000000000000 : ℝ)*(lower2) + (98961009/50000000000000 : ℝ)*(upper3) + (28693999/20000000000000 : ℝ)*(upper4) + (167162871/50000000000000 : ℝ)*(upper5) + (1712097514132039/100000000000000 : ℝ)*(major0) + (1712097514132039/100000000000000 : ℝ)*(major1) + (1712097514132039/100000000000000 : ℝ)*(major2) + (683223351/25000000000000 : ℝ)*(sp2) + (52592489/25000000000000 : ℝ)*(sp3) + (2495864040565033/100000000000000 : ℝ)*(sp4) + (2495864040565033/100000000000000 : ℝ)*(sp5) + (2495861084023461/100000000000000 : ℝ)*(sp6) + (928330632697973/100000000000000 : ℝ)*(sp7) + (928330843067929/100000000000000 : ℝ)*(f.failure) + (2495864040565033/100000000000000 : ℝ)*(f.sum) + (98352000996541/45207500000000000000000000000 : ℝ)*base66 + (6213735286373863487/4520750000000000000000000000000000 : ℝ)*base67 + (10805652411159113487/4520750000000000000000000000000000 : ℝ)*base69 + (6903182161045613487/4520750000000000000000000000000000 : ℝ)*base71 + (49428697542569/45207500000000000000000000000 : ℝ)*base73 + (8037155326097636513/4520750000000000000000000000000000 : ℝ)*base76 + (16431143792363487/4520750000000000000000000000000000 : ℝ)*base77 + (22011575692972136513/4520750000000000000000000000000000 : ℝ)*base80 + (63511982544137/22603750000000000000000000000 : ℝ)*base81 + (16183591/2500000000000000000000 : ℝ)*base89 + (16183591/2500000000000000000000 : ℝ)*base91 + (16183591/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1678_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (46106879/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (11553/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5023/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4593/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4479/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1678_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1678_s2_0 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-76811997/500000000 : ℝ)*x 0 + (5493134951/10000000000 : ℝ)*x 1 + (2565797813/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (76811997/500000000 : ℝ)^5047 ≤ (9536373562397/100000000000000 : ℝ)^4023 := by
    have hnat : (76811997 : ℕ)^5047*100000000000000^4023 ≤ 9536373562397^4023*500000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76811997 500000000 9536373562397 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5493134951/10000000000 : ℝ)^5047 ≤ (47162308230317/100000000000000 : ℝ)^4023 := by
    have hnat : (5493134951 : ℕ)^5047*100000000000000^4023 ≤ 47162308230317^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5493134951 10000000000 47162308230317 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2565797813/5000000000 : ℝ)^5047 ≤ (1732052727519/4000000000000 : ℝ)^4023 := by
    have hnat : (2565797813 : ℕ)^5047*4000000000000^4023 ≤ 1732052727519^4023*5000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2565797813 5000000000 1732052727519 4000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-76811997/500000000 : ℝ), (5493134951/10000000000 : ℝ), (2565797813/5000000000 : ℝ)] ![(9536373562397/100000000000000 : ℝ), (47162308230317/100000000000000 : ℝ), (1732052727519/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-76811997/500000000 : ℝ)|^5047 ≤ (9536373562397/100000000000000 : ℝ)^4023
        have hw : |(-76811997/500000000 : ℝ)|=(76811997/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5493134951/10000000000 : ℝ)|^5047 ≤ (47162308230317/100000000000000 : ℝ)^4023
        have hw : |(5493134951/10000000000 : ℝ)|=(5493134951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2565797813/5000000000 : ℝ)|^5047 ≤ (1732052727519/4000000000000 : ℝ)^4023
        have hw : |(2565797813/5000000000 : ℝ)|=(2565797813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_s2_1 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354647233/10000000000 : ℝ)*x 0 + (-1724316743/10000000000 : ℝ)*x 1 + (1026319129/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354647233/10000000000 : ℝ)^5047 ≤ (4567546644799/10000000000000 : ℝ)^4023 := by
    have hnat : (5354647233 : ℕ)^5047*10000000000000^4023 ≤ 4567546644799^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354647233 10000000000 4567546644799 10000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1724316743/10000000000 : ℝ)^5047 ≤ (1377901894141/12500000000000 : ℝ)^4023 := by
    have hnat : (1724316743 : ℕ)^5047*12500000000000^4023 ≤ 1377901894141^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1724316743 10000000000 1377901894141 12500000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1026319129/2000000000 : ℝ)^5047 ≤ (43301318389109/100000000000000 : ℝ)^4023 := by
    have hnat : (1026319129 : ℕ)^5047*100000000000000^4023 ≤ 43301318389109^4023*2000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026319129 2000000000 43301318389109 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354647233/10000000000 : ℝ), (-1724316743/10000000000 : ℝ), (1026319129/2000000000 : ℝ)] ![(4567546644799/10000000000000 : ℝ), (1377901894141/12500000000000 : ℝ), (43301318389109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354647233/10000000000 : ℝ)|^5047 ≤ (4567546644799/10000000000000 : ℝ)^4023
        have hw : |(5354647233/10000000000 : ℝ)|=(5354647233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1724316743/10000000000 : ℝ)|^5047 ≤ (1377901894141/12500000000000 : ℝ)^4023
        have hw : |(-1724316743/10000000000 : ℝ)|=(1724316743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1026319129/2000000000 : ℝ)|^5047 ≤ (43301318389109/100000000000000 : ℝ)^4023
        have hw : |(1026319129/2000000000 : ℝ)|=(1026319129/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_s2_2 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354646957/10000000000 : ℝ)*x 0 + (1282898967/2500000000 : ℝ)*x 1 + (-107769801/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354646957/10000000000 : ℝ)^5047 ≤ (45675463494439/100000000000000 : ℝ)^4023 := by
    have hnat : (5354646957 : ℕ)^5047*100000000000000^4023 ≤ 45675463494439^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354646957 10000000000 45675463494439 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1282898967/2500000000 : ℝ)^5047 ≤ (43301320749787/100000000000000 : ℝ)^4023 := by
    have hnat : (1282898967 : ℕ)^5047*100000000000000^4023 ≤ 43301320749787^4023*2500000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1282898967 2500000000 43301320749787 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (107769801/625000000 : ℝ)^5047 ≤ (2755803934647/25000000000000 : ℝ)^4023 := by
    have hnat : (107769801 : ℕ)^5047*25000000000000^4023 ≤ 2755803934647^4023*625000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107769801 625000000 2755803934647 25000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354646957/10000000000 : ℝ), (1282898967/2500000000 : ℝ), (-107769801/625000000 : ℝ)] ![(45675463494439/100000000000000 : ℝ), (43301320749787/100000000000000 : ℝ), (2755803934647/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354646957/10000000000 : ℝ)|^5047 ≤ (45675463494439/100000000000000 : ℝ)^4023
        have hw : |(5354646957/10000000000 : ℝ)|=(5354646957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1282898967/2500000000 : ℝ)|^5047 ≤ (43301320749787/100000000000000 : ℝ)^4023
        have hw : |(1282898967/2500000000 : ℝ)|=(1282898967/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-107769801/625000000 : ℝ)|^5047 ≤ (2755803934647/25000000000000 : ℝ)^4023
        have hw : |(-107769801/625000000 : ℝ)|=(107769801/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_s2_3 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2073868201/5000000000 : ℝ)*x 0 + (920344009/2500000000 : ℝ)*x 1 + (4653390419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2073868201/5000000000 : ℝ)^5047 ≤ (4144194984489/12500000000000 : ℝ)^4023 := by
    have hnat : (2073868201 : ℕ)^5047*12500000000000^4023 ≤ 4144194984489^4023*5000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073868201 5000000000 4144194984489 12500000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (920344009/2500000000 : ℝ)^5047 ≤ (1784119686299/6250000000000 : ℝ)^4023 := by
    have hnat : (920344009 : ℕ)^5047*6250000000000^4023 ≤ 1784119686299^4023*2500000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      920344009 2500000000 1784119686299 6250000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4653390419/10000000000 : ℝ)^5047 ≤ (19150262563567/50000000000000 : ℝ)^4023 := by
    have hnat : (4653390419 : ℕ)^5047*50000000000000^4023 ≤ 19150262563567^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4653390419 10000000000 19150262563567 50000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2073868201/5000000000 : ℝ), (920344009/2500000000 : ℝ), (4653390419/10000000000 : ℝ)] ![(4144194984489/12500000000000 : ℝ), (1784119686299/6250000000000 : ℝ), (19150262563567/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2073868201/5000000000 : ℝ)|^5047 ≤ (4144194984489/12500000000000 : ℝ)^4023
        have hw : |(2073868201/5000000000 : ℝ)|=(2073868201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(920344009/2500000000 : ℝ)|^5047 ≤ (1784119686299/6250000000000 : ℝ)^4023
        have hw : |(920344009/2500000000 : ℝ)|=(920344009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4653390419/10000000000 : ℝ)|^5047 ≤ (19150262563567/50000000000000 : ℝ)^4023
        have hw : |(4653390419/10000000000 : ℝ)|=(4653390419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_s2_4 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1536414077/10000000000 : ℝ)*x 0 + (1283880489/2500000000 : ℝ)*x 1 + (2744574713/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1536414077/10000000000 : ℝ)^5047 ≤ (596108106453/6250000000000 : ℝ)^4023 := by
    have hnat : (1536414077 : ℕ)^5047*6250000000000^4023 ≤ 596108106453^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1536414077 10000000000 596108106453 6250000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1283880489/2500000000 : ℝ)^5047 ≤ (43342886371007/100000000000000 : ℝ)^4023 := by
    have hnat : (1283880489 : ℕ)^5047*100000000000000^4023 ≤ 43342886371007^4023*2500000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1283880489 2500000000 43342886371007 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2744574713/5000000000 : ℝ)^5047 ≤ (23559691952277/50000000000000 : ℝ)^4023 := by
    have hnat : (2744574713 : ℕ)^5047*50000000000000^4023 ≤ 23559691952277^4023*5000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2744574713 5000000000 23559691952277 50000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1536414077/10000000000 : ℝ), (1283880489/2500000000 : ℝ), (2744574713/5000000000 : ℝ)] ![(596108106453/6250000000000 : ℝ), (43342886371007/100000000000000 : ℝ), (23559691952277/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1536414077/10000000000 : ℝ)|^5047 ≤ (596108106453/6250000000000 : ℝ)^4023
        have hw : |(-1536414077/10000000000 : ℝ)|=(1536414077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1283880489/2500000000 : ℝ)|^5047 ≤ (43342886371007/100000000000000 : ℝ)^4023
        have hw : |(1283880489/2500000000 : ℝ)|=(1283880489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2744574713/5000000000 : ℝ)|^5047 ≤ (23559691952277/50000000000000 : ℝ)^4023
        have hw : |(2744574713/5000000000 : ℝ)|=(2744574713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_s2_5 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5258131597/10000000000 : ℝ)*x 0 + (-1366763249/10000000000 : ℝ)*x 1 + (2744574709/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5258131597/10000000000 : ℝ)^5047 ≤ (44645006379601/100000000000000 : ℝ)^4023 := by
    have hnat : (5258131597 : ℕ)^5047*100000000000000^4023 ≤ 44645006379601^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258131597 10000000000 44645006379601 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1366763249/10000000000 : ℝ)^5047 ≤ (102945122373/1250000000000 : ℝ)^4023 := by
    have hnat : (1366763249 : ℕ)^5047*1250000000000^4023 ≤ 102945122373^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366763249 10000000000 102945122373 1250000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2744574709/5000000000 : ℝ)^5047 ≤ (47119383818401/100000000000000 : ℝ)^4023 := by
    have hnat : (2744574709 : ℕ)^5047*100000000000000^4023 ≤ 47119383818401^4023*5000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2744574709 5000000000 47119383818401 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5258131597/10000000000 : ℝ), (-1366763249/10000000000 : ℝ), (2744574709/5000000000 : ℝ)] ![(44645006379601/100000000000000 : ℝ), (102945122373/1250000000000 : ℝ), (47119383818401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5258131597/10000000000 : ℝ)|^5047 ≤ (44645006379601/100000000000000 : ℝ)^4023
        have hw : |(5258131597/10000000000 : ℝ)|=(5258131597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1366763249/10000000000 : ℝ)|^5047 ≤ (102945122373/1250000000000 : ℝ)^4023
        have hw : |(-1366763249/10000000000 : ℝ)|=(1366763249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2744574709/5000000000 : ℝ)|^5047 ≤ (47119383818401/100000000000000 : ℝ)^4023
        have hw : |(2744574709/5000000000 : ℝ)|=(2744574709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_s2_6 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (262906579/500000000 : ℝ)*x 0 + (1372287361/2500000000 : ℝ)*x 1 + (-273352647/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262906579/500000000 : ℝ)^5047 ≤ (1116125154963/2500000000000 : ℝ)^4023 := by
    have hnat : (262906579 : ℕ)^5047*2500000000000^4023 ≤ 1116125154963^4023*500000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262906579 500000000 1116125154963 2500000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1372287361/2500000000 : ℝ)^5047 ≤ (47119384098397/100000000000000 : ℝ)^4023 := by
    have hnat : (1372287361 : ℕ)^5047*100000000000000^4023 ≤ 47119384098397^4023*2500000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372287361 2500000000 47119384098397 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (273352647/2000000000 : ℝ)^5047 ≤ (8235609684009/100000000000000 : ℝ)^4023 := by
    have hnat : (273352647 : ℕ)^5047*100000000000000^4023 ≤ 8235609684009^4023*2000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273352647 2000000000 8235609684009 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262906579/500000000 : ℝ), (1372287361/2500000000 : ℝ), (-273352647/2000000000 : ℝ)] ![(1116125154963/2500000000000 : ℝ), (47119384098397/100000000000000 : ℝ), (8235609684009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262906579/500000000 : ℝ)|^5047 ≤ (1116125154963/2500000000000 : ℝ)^4023
        have hw : |(262906579/500000000 : ℝ)|=(262906579/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1372287361/2500000000 : ℝ)|^5047 ≤ (47119384098397/100000000000000 : ℝ)^4023
        have hw : |(1372287361/2500000000 : ℝ)|=(1372287361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-273352647/2000000000 : ℝ)|^5047 ≤ (8235609684009/100000000000000 : ℝ)^4023
        have hw : |(-273352647/2000000000 : ℝ)|=(273352647/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1678_s2_7 (p : ℝ) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165928191/400000000 : ℝ)*x 0 + (4642835163/10000000000 : ℝ)*x 1 + (1846044971/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165928191/400000000 : ℝ)^5047 ≤ (16579128328857/50000000000000 : ℝ)^4023 := by
    have hnat : (165928191 : ℕ)^5047*50000000000000^4023 ≤ 16579128328857^4023*400000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165928191 400000000 16579128328857 50000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4642835163/10000000000 : ℝ)^5047 ≤ (9547891612711/25000000000000 : ℝ)^4023 := by
    have hnat : (4642835163 : ℕ)^5047*25000000000000^4023 ≤ 9547891612711^4023*10000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4642835163 10000000000 9547891612711 25000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1846044971/5000000000 : ℝ)^5047 ≤ (28650176873041/100000000000000 : ℝ)^4023 := by
    have hnat : (1846044971 : ℕ)^5047*100000000000000^4023 ≤ 28650176873041^4023*5000000000^5047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1846044971 5000000000 28650176873041 100000000000000 5047 4023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5047/1024 : ℝ)) 5047 4023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165928191/400000000 : ℝ), (4642835163/10000000000 : ℝ), (1846044971/5000000000 : ℝ)] ![(16579128328857/50000000000000 : ℝ), (9547891612711/25000000000000 : ℝ), (28650176873041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165928191/400000000 : ℝ)|^5047 ≤ (16579128328857/50000000000000 : ℝ)^4023
        have hw : |(165928191/400000000 : ℝ)|=(165928191/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4642835163/10000000000 : ℝ)|^5047 ≤ (9547891612711/25000000000000 : ℝ)^4023
        have hw : |(4642835163/10000000000 : ℝ)|=(4642835163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1846044971/5000000000 : ℝ)|^5047 ≤ (28650176873041/100000000000000 : ℝ)^4023
        have hw : |(1846044971/5000000000 : ℝ)|=(1846044971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1678_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (46106879/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4479/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4593/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (9673/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8677/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4479/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4593/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4479/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4593/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4479/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4593/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4479/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4593/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4479/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4593/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4479/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4593/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4593/50000 : ℝ) ^ (5039/1024 : ℝ) ≤ (395021313150753/50000000000000000000 : ℝ) := by
    have hpowers : (4593/50000 : ℝ)^5039 ≤ (395021313150753/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4593 : ℕ)^5039*50000000000000000000^1024 ≤ 395021313150753^1024*50000^5039 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4593 50000 395021313150753 50000000000000000000 5039 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4593/50000 : ℝ)) (X := (395021313150753/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5039 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4479/25000 : ℝ) ^ (5039/1024 : ℝ) ≤ (21148280806249197/100000000000000000000 : ℝ) := by
    have hpowers : (4479/25000 : ℝ)^5039 ≤ (21148280806249197/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4479 : ℕ)^5039*100000000000000000000^1024 ≤ 21148280806249197^1024*25000^5039 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4479 25000 21148280806249197 100000000000000000000 5039 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4479/25000 : ℝ)) (X := (21148280806249197/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5039 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000395021313150753/25000000000000000000 : ℝ) ≤ (5000016054744131/5000000000000000 : ℝ) ^ (5039/1024 : ℝ) := by
    have hpowers : (25000395021313150753/25000000000000000000 : ℝ)^1024 ≤ (5000016054744131/5000000000000000 : ℝ)^5039 := by
      have hnat : (25000395021313150753 : ℕ)^1024*5000000000000000^5039 ≤ 5000016054744131^5039*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000395021313150753 25000000000000000000 5000016054744131 5000000000000000 1024 5039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000016054744131/5000000000000000 : ℝ)) (X := (25000395021313150753/25000000000000000000 : ℝ)) (by norm_num) 5039 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100021938323432550703/100000000000000000000 : ℝ) ≤ (2500111445128057/2500000000000000 : ℝ) ^ (5039/1024 : ℝ) := by
    have hpowers : (100021938323432550703/100000000000000000000 : ℝ)^1024 ≤ (2500111445128057/2500000000000000 : ℝ)^5039 := by
      have hnat : (100021938323432550703 : ℕ)^1024*2500000000000000^5039 ≤ 2500111445128057^5039*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100021938323432550703 100000000000000000000 2500111445128057 2500000000000000 1024 5039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500111445128057/2500000000000000 : ℝ)) (X := (100021938323432550703/100000000000000000000 : ℝ)) (by norm_num) 5039 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50021148280806249197/50000000000000000000 : ℝ) ≤ (5000429725768097/5000000000000000 : ℝ) ^ (5039/1024 : ℝ) := by
    have hpowers : (50021148280806249197/50000000000000000000 : ℝ)^1024 ≤ (5000429725768097/5000000000000000 : ℝ)^5039 := by
      have hnat : (50021148280806249197 : ℕ)^1024*5000000000000000^5039 ≤ 5000429725768097^5039*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021148280806249197 50000000000000000000 5000429725768097 5000000000000000 1024 5039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000429725768097/5000000000000000 : ℝ)) (X := (50021148280806249197/50000000000000000000 : ℝ)) (by norm_num) 5039 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(395021313150753/50000000000000000000 : ℝ) ≤ ((2424796676438339553/2425000000000000000 : ℝ)+2*(68945170661/145500000000000 : ℝ)*(4593/50000 : ℝ))^(5039/1024 : ℝ) := by
    rw [show (2424796676438339553/2425000000000000000 : ℝ)+2*(68945170661/145500000000000 : ℝ)*(4593/50000 : ℝ)=(5000016054744131/5000000000000000 : ℝ) by norm_num, show 1+2*(395021313150753/50000000000000000000 : ℝ)=(25000395021313150753/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21148280806249197/100000000000000000000 : ℝ)+(395021313150753/50000000000000000000 : ℝ) ≤ ((2424796676438339553/2425000000000000000 : ℝ)+(68945170661/145500000000000 : ℝ)*((4479/25000 : ℝ)+(4593/50000 : ℝ)))^(5039/1024 : ℝ) := by
    rw [show (2424796676438339553/2425000000000000000 : ℝ)+(68945170661/145500000000000 : ℝ)*((4479/25000 : ℝ)+(4593/50000 : ℝ))=(2500111445128057/2500000000000000 : ℝ) by norm_num, show 1+(21148280806249197/100000000000000000000 : ℝ)+(395021313150753/50000000000000000000 : ℝ)=(100021938323432550703/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21148280806249197/100000000000000000000 : ℝ) ≤ ((2424796676438339553/2425000000000000000 : ℝ)+2*(68945170661/145500000000000 : ℝ)*(4479/25000 : ℝ))^(5039/1024 : ℝ) := by
    rw [show (2424796676438339553/2425000000000000000 : ℝ)+2*(68945170661/145500000000000 : ℝ)*(4479/25000 : ℝ)=(5000429725768097/5000000000000000 : ℝ) by norm_num, show 1+2*(21148280806249197/100000000000000000000 : ℝ)=(50021148280806249197/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2424796676438339553/2425000000000000000 : ℝ)*(X 1 0+X 2 0)+(68945170661/145500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5039/1024 : ℝ)) (lo := (4593/50000 : ℝ)) (hi := (4479/25000 : ℝ)) (c := (2424796676438339553/2425000000000000000 : ℝ)) (alpha := (68945170661/145500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2424796676438339553/2425000000000000000 : ℝ)*(X 0 1+X 2 1)+(68945170661/145500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5039/1024 : ℝ)) (lo := (4593/50000 : ℝ)) (hi := (4479/25000 : ℝ)) (c := (2424796676438339553/2425000000000000000 : ℝ)) (alpha := (68945170661/145500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2424796676438339553/2425000000000000000 : ℝ)*(X 0 2+X 1 2)+(68945170661/145500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5039/1024 : ℝ)) (lo := (4593/50000 : ℝ)) (hi := (4479/25000 : ℝ)) (c := (2424796676438339553/2425000000000000000 : ℝ)) (alpha := (68945170661/145500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-76811997/500000000 : ℝ)*X 0 0+(5493134951/10000000000 : ℝ)*X 0 1+(2565797813/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5354647233/10000000000 : ℝ)*X 1 0+(-1724316743/10000000000 : ℝ)*X 1 1+(1026319129/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354646957/10000000000 : ℝ)*X 2 0+(1282898967/2500000000 : ℝ)*X 2 1+(-107769801/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2073868201/5000000000 : ℝ)*X 0 0+(920344009/2500000000 : ℝ)*X 0 1+(4653390419/10000000000 : ℝ)*X 0 2+(2073868201/5000000000 : ℝ)*X 1 0+(920344009/2500000000 : ℝ)*X 1 1+(4653390419/10000000000 : ℝ)*X 1 2+(2073868201/5000000000 : ℝ)*X 2 0+(920344009/2500000000 : ℝ)*X 2 1+(4653390419/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1536414077/10000000000 : ℝ)*X 0 0+(1283880489/2500000000 : ℝ)*X 0 1+(2744574713/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5258131597/10000000000 : ℝ)*X 1 0+(-1366763249/10000000000 : ℝ)*X 1 1+(2744574709/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((262906579/500000000 : ℝ)*X 2 0+(1372287361/2500000000 : ℝ)*X 2 1+(-273352647/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((165928191/400000000 : ℝ)*X 0 0+(4642835163/10000000000 : ℝ)*X 0 1+(1846044971/5000000000 : ℝ)*X 0 2+(165928191/400000000 : ℝ)*X 1 0+(4642835163/10000000000 : ℝ)*X 1 1+(1846044971/5000000000 : ℝ)*X 1 2+(165928191/400000000 : ℝ)*X 2 0+(4642835163/10000000000 : ℝ)*X 2 1+(1846044971/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1678_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1547857151726468779714327/189453125000000000000000000000 : ℝ) := by norm_num
    linear_combination (664396877/50000000000000 : ℝ)*(base19) + (1141741267/100000000000000 : ℝ)*(base23) + (11909521/50000000000000 : ℝ)*(lower2) + (191505107/100000000000000 : ℝ)*(upper3) + (5905097/6250000000000 : ℝ)*(upper5) + (11858680276763/625000000000 : ℝ)*(major0) + (11858680276763/625000000000 : ℝ)*(major1) + (11858680276763/625000000000 : ℝ)*(major2) + (1382982656760133/50000000000000 : ℝ)*(sp0) + (2765976868403917/100000000000000 : ℝ)*(sp1) + (691494263864101/25000000000000 : ℝ)*(sp2) + (514397507354383/50000000000000 : ℝ)*(sp3) + (2576735481/20000000000000 : ℝ)*(sp4) + (105107999/2500000000000 : ℝ)*(sp7) + (1028799219028727/100000000000000 : ℝ)*(f.failure) + (345747274649709/12500000000000 : ℝ)*(f.sum) + (6318450212291/1455000000000000000000000000 : ℝ)*base65 + (16527412884052067/4546875000000000000000000000000 : ℝ)*base67 + (10057550238145817/4546875000000000000000000000000 : ℝ)*base69 + (5387409087513029/2273437500000000000000000000000 : ℝ)*base72 + (7739478846101/1455000000000000000000000000 : ℝ)*base73 + (490694314758137/284179687500000000000000000000 : ℝ)*base75 + (13622117271895817/4546875000000000000000000000000 : ℝ)*base77 + (11711033991979183/4546875000000000000000000000000 : ℝ)*base80 + (5775016174213/727500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (13313033/2500000000000000000000 : ℝ)*base89 + (13313033/2500000000000000000000 : ℝ)*base91 + (13313033/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18978093225538875235102769/3789062500000000000000000000000 : ℝ) := by norm_num
    linear_combination (179309997/25000000000000 : ℝ)*(base19) + (771870561/100000000000000 : ℝ)*(base23) + (21203631/20000000000000 : ℝ)*(upper3) + (699229/2500000000000 : ℝ)*(lower4) + (26391353/25000000000000 : ℝ)*(upper5) + (121238776579931/6250000000000 : ℝ)*(major0) + (121238776579931/6250000000000 : ℝ)*(major1) + (121238776579931/6250000000000 : ℝ)*(major2) + (150505907/2500000000000 : ℝ)*(sp1) + (263868107/4000000000000 : ℝ)*(sp2) + (2827834278923457/100000000000000 : ℝ)*(sp4) + (2827827541447189/100000000000000 : ℝ)*(sp5) + (2827826910350221/100000000000000 : ℝ)*(sp6) + (42072256187171/4000000000000 : ℝ)*(sp7) + (42072256187171/4000000000000 : ℝ)*(f.failure) + (2827834278923457/100000000000000 : ℝ)*(f.sum) + (9772548619/7104492187500000000000000 : ℝ)*base65 + (352986046463388779/45468750000000000000000000000000 : ℝ)*base67 + (425128174062607529/45468750000000000000000000000000 : ℝ)*base69 + (329423527249170029/45468750000000000000000000000000 : ℝ)*base71 + (1007541667961/1818750000000000000000000000 : ℝ)*base74 + (570328038481357529/45468750000000000000000000000000 : ℝ)*base75 + (305477633676982529/45468750000000000000000000000000 : ℝ)*base77 + (742423519836513779/45468750000000000000000000000000 : ℝ)*base79 + (9181301778631/7275000000000000000000000000 : ℝ)*base81 + (1350691/100000000000000000000 : ℝ)*base90 + (1350691/100000000000000000000 : ℝ)*base92 + (1350691/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1678_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (46106879/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4479/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4593/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9673/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8677/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1678_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1678_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (46106879/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9673/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8677/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1678_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1678_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1678_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5039/1024 : ℝ) ≤ p) (hpb : p ≤ (5047/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (46106879/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9673/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8677/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1678_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
