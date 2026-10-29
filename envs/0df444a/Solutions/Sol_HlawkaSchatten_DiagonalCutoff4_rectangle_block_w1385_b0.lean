-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1385_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:24:16.027535+00:00
-- url     : https://prove2.me/submissions/0ac06356-7e41-49d3-8764-a6bdfd969886

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
theorem support_rectangle_w1385_s0_0 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-356799289/2000000000 : ℝ)*x 0 + (5978551437/10000000000 : ℝ)*x 1 + (4821064219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (356799289/2000000000 : ℝ)^4345 ≤ (10484993393149/100000000000000 : ℝ)^3321 := by
    have hnat : (356799289 : ℕ)^4345*100000000000000^3321 ≤ 10484993393149^3321*2000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      356799289 2000000000 10484993393149 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5978551437/10000000000 : ℝ)^4345 ≤ (51016584425669/100000000000000 : ℝ)^3321 := by
    have hnat : (5978551437 : ℕ)^4345*100000000000000^3321 ≤ 51016584425669^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5978551437 10000000000 51016584425669 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4821064219/10000000000 : ℝ)^4345 ≤ (19249211081821/50000000000000 : ℝ)^3321 := by
    have hnat : (4821064219 : ℕ)^4345*50000000000000^3321 ≤ 19249211081821^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4821064219 10000000000 19249211081821 50000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-356799289/2000000000 : ℝ), (5978551437/10000000000 : ℝ), (4821064219/10000000000 : ℝ)] ![(10484993393149/100000000000000 : ℝ), (51016584425669/100000000000000 : ℝ), (19249211081821/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-356799289/2000000000 : ℝ)|^4345 ≤ (10484993393149/100000000000000 : ℝ)^3321
        have hw : |(-356799289/2000000000 : ℝ)|=(356799289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5978551437/10000000000 : ℝ)|^4345 ≤ (51016584425669/100000000000000 : ℝ)^3321
        have hw : |(5978551437/10000000000 : ℝ)|=(5978551437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4821064219/10000000000 : ℝ)|^4345 ≤ (19249211081821/50000000000000 : ℝ)^3321
        have hw : |(4821064219/10000000000 : ℝ)|=(4821064219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_s0_1 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (137425099/250000000 : ℝ)*x 0 + (-2439877413/10000000000 : ℝ)*x 1 + (2410532467/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (137425099/250000000 : ℝ)^4345 ≤ (2856776795399/6250000000000 : ℝ)^3321 := by
    have hnat : (137425099 : ℕ)^4345*6250000000000^3321 ≤ 2856776795399^3321*250000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137425099 250000000 2856776795399 6250000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2439877413/10000000000 : ℝ)^4345 ≤ (631725665323/4000000000000 : ℝ)^3321 := by
    have hnat : (2439877413 : ℕ)^4345*4000000000000^3321 ≤ 631725665323^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2439877413 10000000000 631725665323 4000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2410532467/5000000000 : ℝ)^4345 ≤ (4812303704219/12500000000000 : ℝ)^3321 := by
    have hnat : (2410532467 : ℕ)^4345*12500000000000^3321 ≤ 4812303704219^3321*5000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2410532467 5000000000 4812303704219 12500000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(137425099/250000000 : ℝ), (-2439877413/10000000000 : ℝ), (2410532467/5000000000 : ℝ)] ![(2856776795399/6250000000000 : ℝ), (631725665323/4000000000000 : ℝ), (4812303704219/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(137425099/250000000 : ℝ)|^4345 ≤ (2856776795399/6250000000000 : ℝ)^3321
        have hw : |(137425099/250000000 : ℝ)|=(137425099/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2439877413/10000000000 : ℝ)|^4345 ≤ (631725665323/4000000000000 : ℝ)^3321
        have hw : |(-2439877413/10000000000 : ℝ)|=(2439877413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2410532467/5000000000 : ℝ)|^4345 ≤ (4812303704219/12500000000000 : ℝ)^3321
        have hw : |(2410532467/5000000000 : ℝ)|=(2410532467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_s0_2 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2748501897/5000000000 : ℝ)*x 0 + (4821064119/10000000000 : ℝ)*x 1 + (-243987863/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2748501897/5000000000 : ℝ)^4345 ≤ (45708426920461/100000000000000 : ℝ)^3321 := by
    have hnat : (2748501897 : ℕ)^4345*100000000000000^3321 ≤ 45708426920461^3321*5000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2748501897 5000000000 45708426920461 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4821064119/10000000000 : ℝ)^4345 ≤ (4812302639859/12500000000000 : ℝ)^3321 := by
    have hnat : (4821064119 : ℕ)^4345*12500000000000^3321 ≤ 4812302639859^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4821064119 10000000000 4812302639859 12500000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (243987863/1000000000 : ℝ)^4345 ≤ (7896575969797/50000000000000 : ℝ)^3321 := by
    have hnat : (243987863 : ℕ)^4345*50000000000000^3321 ≤ 7896575969797^3321*1000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243987863 1000000000 7896575969797 50000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2748501897/5000000000 : ℝ), (4821064119/10000000000 : ℝ), (-243987863/1000000000 : ℝ)] ![(45708426920461/100000000000000 : ℝ), (4812302639859/12500000000000 : ℝ), (7896575969797/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2748501897/5000000000 : ℝ)|^4345 ≤ (45708426920461/100000000000000 : ℝ)^3321
        have hw : |(2748501897/5000000000 : ℝ)|=(2748501897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4821064119/10000000000 : ℝ)|^4345 ≤ (4812302639859/12500000000000 : ℝ)^3321
        have hw : |(4821064119/10000000000 : ℝ)|=(4821064119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-243987863/1000000000 : ℝ)|^4345 ≤ (7896575969797/50000000000000 : ℝ)^3321
        have hw : |(-243987863/1000000000 : ℝ)|=(243987863/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_s0_3 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4172380101/10000000000 : ℝ)*x 0 + (1552353671/5000000000 : ℝ)*x 1 + (1113685711/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4172380101/10000000000 : ℝ)^4345 ≤ (7966594430407/25000000000000 : ℝ)^3321 := by
    have hnat : (4172380101 : ℕ)^4345*25000000000000^3321 ≤ 7966594430407^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172380101 10000000000 7966594430407 25000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1552353671/5000000000 : ℝ)^4345 ≤ (21646609577837/100000000000000 : ℝ)^3321 := by
    have hnat : (1552353671 : ℕ)^4345*100000000000000^3321 ≤ 21646609577837^3321*5000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1552353671 5000000000 21646609577837 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1113685711/2000000000 : ℝ)^4345 ≤ (46487012687233/100000000000000 : ℝ)^3321 := by
    have hnat : (1113685711 : ℕ)^4345*100000000000000^3321 ≤ 46487012687233^3321*2000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1113685711 2000000000 46487012687233 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4172380101/10000000000 : ℝ), (1552353671/5000000000 : ℝ), (1113685711/2000000000 : ℝ)] ![(7966594430407/25000000000000 : ℝ), (21646609577837/100000000000000 : ℝ), (46487012687233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4172380101/10000000000 : ℝ)|^4345 ≤ (7966594430407/25000000000000 : ℝ)^3321
        have hw : |(4172380101/10000000000 : ℝ)|=(4172380101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1552353671/5000000000 : ℝ)|^4345 ≤ (21646609577837/100000000000000 : ℝ)^3321
        have hw : |(1552353671/5000000000 : ℝ)|=(1552353671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1113685711/2000000000 : ℝ)|^4345 ≤ (46487012687233/100000000000000 : ℝ)^3321
        have hw : |(1113685711/2000000000 : ℝ)|=(1113685711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_s0_4 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-447058033/2500000000 : ℝ)*x 0 + (4850773799/10000000000 : ℝ)*x 1 + (5947779911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (447058033/2500000000 : ℝ)^4345 ≤ (1314696924673/12500000000000 : ℝ)^3321 := by
    have hnat : (447058033 : ℕ)^4345*12500000000000^3321 ≤ 1314696924673^3321*2500000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447058033 2500000000 1314696924673 12500000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4850773799/10000000000 : ℝ)^4345 ≤ (242556959901/625000000000 : ℝ)^3321 := by
    have hnat : (4850773799 : ℕ)^4345*625000000000^3321 ≤ 242556959901^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4850773799 10000000000 242556959901 625000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5947779911/10000000000 : ℝ)^4345 ≤ (50673311000941/100000000000000 : ℝ)^3321 := by
    have hnat : (5947779911 : ℕ)^4345*100000000000000^3321 ≤ 50673311000941^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5947779911 10000000000 50673311000941 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-447058033/2500000000 : ℝ), (4850773799/10000000000 : ℝ), (5947779911/10000000000 : ℝ)] ![(1314696924673/12500000000000 : ℝ), (242556959901/625000000000 : ℝ), (50673311000941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-447058033/2500000000 : ℝ)|^4345 ≤ (1314696924673/12500000000000 : ℝ)^3321
        have hw : |(-447058033/2500000000 : ℝ)|=(447058033/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4850773799/10000000000 : ℝ)|^4345 ≤ (242556959901/625000000000 : ℝ)^3321
        have hw : |(4850773799/10000000000 : ℝ)|=(4850773799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5947779911/10000000000 : ℝ)|^4345 ≤ (50673311000941/100000000000000 : ℝ)^3321
        have hw : |(5947779911/10000000000 : ℝ)|=(5947779911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_s0_5 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5181300731/10000000000 : ℝ)*x 0 + (-131316313/1000000000 : ℝ)*x 1 + (5947779731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5181300731/10000000000 : ℝ)^4345 ≤ (5288087430007/12500000000000 : ℝ)^3321 := by
    have hnat : (5181300731 : ℕ)^4345*12500000000000^3321 ≤ 5288087430007^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181300731 10000000000 5288087430007 12500000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131316313/1000000000 : ℝ)^4345 ≤ (7021991558971/100000000000000 : ℝ)^3321 := by
    have hnat : (131316313 : ℕ)^4345*100000000000000^3321 ≤ 7021991558971^3321*1000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131316313 1000000000 7021991558971 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5947779731/10000000000 : ℝ)^4345 ≤ (50673308994539/100000000000000 : ℝ)^3321 := by
    have hnat : (5947779731 : ℕ)^4345*100000000000000^3321 ≤ 50673308994539^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5947779731 10000000000 50673308994539 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5181300731/10000000000 : ℝ), (-131316313/1000000000 : ℝ), (5947779731/10000000000 : ℝ)] ![(5288087430007/12500000000000 : ℝ), (7021991558971/100000000000000 : ℝ), (50673308994539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5181300731/10000000000 : ℝ)|^4345 ≤ (5288087430007/12500000000000 : ℝ)^3321
        have hw : |(5181300731/10000000000 : ℝ)|=(5181300731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-131316313/1000000000 : ℝ)|^4345 ≤ (7021991558971/100000000000000 : ℝ)^3321
        have hw : |(-131316313/1000000000 : ℝ)|=(131316313/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5947779731/10000000000 : ℝ)|^4345 ≤ (50673308994539/100000000000000 : ℝ)^3321
        have hw : |(5947779731/10000000000 : ℝ)|=(5947779731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_s0_6 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5181300397/10000000000 : ℝ)*x 0 + (118955597/200000000 : ℝ)*x 1 + (-1313163449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5181300397/10000000000 : ℝ)^4345 ≤ (42304695872119/100000000000000 : ℝ)^3321 := by
    have hnat : (5181300397 : ℕ)^4345*100000000000000^3321 ≤ 42304695872119^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181300397 10000000000 42304695872119 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (118955597/200000000 : ℝ)^4345 ≤ (50673310320993/100000000000000 : ℝ)^3321 := by
    have hnat : (118955597 : ℕ)^4345*100000000000000^3321 ≤ 50673310320993^3321*200000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118955597 200000000 50673310320993 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313163449/10000000000 : ℝ)^4345 ≤ (175549844769/2500000000000 : ℝ)^3321 := by
    have hnat : (1313163449 : ℕ)^4345*2500000000000^3321 ≤ 175549844769^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313163449 10000000000 175549844769 2500000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5181300397/10000000000 : ℝ), (118955597/200000000 : ℝ), (-1313163449/10000000000 : ℝ)] ![(42304695872119/100000000000000 : ℝ), (50673310320993/100000000000000 : ℝ), (175549844769/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5181300397/10000000000 : ℝ)|^4345 ≤ (42304695872119/100000000000000 : ℝ)^3321
        have hw : |(5181300397/10000000000 : ℝ)|=(5181300397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(118955597/200000000 : ℝ)|^4345 ≤ (50673310320993/100000000000000 : ℝ)^3321
        have hw : |(118955597/200000000 : ℝ)|=(118955597/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1313163449/10000000000 : ℝ)|^4345 ≤ (175549844769/2500000000000 : ℝ)^3321
        have hw : |(-1313163449/10000000000 : ℝ)|=(1313163449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_s0_7 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (836278659/2000000000 : ℝ)*x 0 + (5505191077/10000000000 : ℝ)*x 1 + (3170204833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (836278659/2000000000 : ℝ)^4345 ≤ (31956471126323/100000000000000 : ℝ)^3321 := by
    have hnat : (836278659 : ℕ)^4345*100000000000000^3321 ≤ 31956471126323^3321*2000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      836278659 2000000000 31956471126323 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5505191077/10000000000 : ℝ)^4345 ≤ (45797517262059/100000000000000 : ℝ)^3321 := by
    have hnat : (5505191077 : ℕ)^4345*100000000000000^3321 ≤ 45797517262059^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5505191077 10000000000 45797517262059 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3170204833/10000000000 : ℝ)^4345 ≤ (556150290149/2500000000000 : ℝ)^3321 := by
    have hnat : (3170204833 : ℕ)^4345*2500000000000^3321 ≤ 556150290149^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3170204833 10000000000 556150290149 2500000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(836278659/2000000000 : ℝ), (5505191077/10000000000 : ℝ), (3170204833/10000000000 : ℝ)] ![(31956471126323/100000000000000 : ℝ), (45797517262059/100000000000000 : ℝ), (556150290149/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(836278659/2000000000 : ℝ)|^4345 ≤ (31956471126323/100000000000000 : ℝ)^3321
        have hw : |(836278659/2000000000 : ℝ)|=(836278659/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5505191077/10000000000 : ℝ)|^4345 ≤ (45797517262059/100000000000000 : ℝ)^3321
        have hw : |(5505191077/10000000000 : ℝ)|=(5505191077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3170204833/10000000000 : ℝ)|^4345 ≤ (556150290149/2500000000000 : ℝ)^3321
        have hw : |(3170204833/10000000000 : ℝ)|=(3170204833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1385_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78212721/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (433/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5313/20000 : ℝ)*pair X 0 0 := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (543/128 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^543 ≤ (0 : ℝ)^128 := by
      have hnat : (0 : ℕ)^543*1^128 ≤ 0^128*1^543 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 543 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 543 128 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (543/128 : ℝ) ≤ (512629834597232183/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^543 ≤ (512629834597232183/25000000000000000000 : ℝ)^128 := by
      have hnat : (2 : ℕ)^543*25000000000000000000^128 ≤ 512629834597232183^128*5^543 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 512629834597232183 25000000000000000000 543 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (512629834597232183/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 543 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (543/128 : ℝ) := by
    have hpowers : (1 : ℝ)^128 ≤ (1 : ℝ)^543 := by
      have hnat : (1 : ℕ)^128*1^543 ≤ 1^543*1^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 128 543 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 543 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (25512629834597232183/25000000000000000000 : ℝ) ≤ (401918484720563/400000000000000 : ℝ) ^ (543/128 : ℝ) := by
    have hpowers : (25512629834597232183/25000000000000000000 : ℝ)^128 ≤ (401918484720563/400000000000000 : ℝ)^543 := by
      have hnat : (25512629834597232183 : ℕ)^128*400000000000000^543 ≤ 401918484720563^543*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25512629834597232183 25000000000000000000 401918484720563 400000000000000 128 543 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (401918484720563/400000000000000 : ℝ)) (X := (25512629834597232183/25000000000000000000 : ℝ)) (by norm_num) 543 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (13012629834597232183/12500000000000000000 : ℝ) ≤ (201918484720563/200000000000000 : ℝ) ^ (543/128 : ℝ) := by
    have hpowers : (13012629834597232183/12500000000000000000 : ℝ)^128 ≤ (201918484720563/200000000000000 : ℝ)^543 := by
      have hnat : (13012629834597232183 : ℕ)^128*200000000000000^543 ≤ 201918484720563^543*12500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13012629834597232183 12500000000000000000 201918484720563 200000000000000 128 543 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (201918484720563/200000000000000 : ℝ)) (X := (13012629834597232183/12500000000000000000 : ℝ)) (by norm_num) 543 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(1918484720563/160000000000000 : ℝ)*(0 : ℝ))^(543/128 : ℝ) := by
    rw [show (1 : ℝ)+2*(1918484720563/160000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(512629834597232183/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(1918484720563/160000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(543/128 : ℝ) := by
    rw [show (1 : ℝ)+(1918484720563/160000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(401918484720563/400000000000000 : ℝ) by norm_num, show 1+(512629834597232183/25000000000000000000 : ℝ)+(0 : ℝ)=(25512629834597232183/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(512629834597232183/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(1918484720563/160000000000000 : ℝ)*(2/5 : ℝ))^(543/128 : ℝ) := by
    rw [show (1 : ℝ)+2*(1918484720563/160000000000000 : ℝ)*(2/5 : ℝ)=(201918484720563/200000000000000 : ℝ) by norm_num, show 1+2*(512629834597232183/25000000000000000000 : ℝ)=(13012629834597232183/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(1918484720563/160000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (543/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1918484720563/160000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(1918484720563/160000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (543/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1918484720563/160000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(1918484720563/160000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (543/128 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1918484720563/160000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-356799289/2000000000 : ℝ)*X 0 0+(5978551437/10000000000 : ℝ)*X 0 1+(4821064219/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((137425099/250000000 : ℝ)*X 1 0+(-2439877413/10000000000 : ℝ)*X 1 1+(2410532467/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2748501897/5000000000 : ℝ)*X 2 0+(4821064119/10000000000 : ℝ)*X 2 1+(-243987863/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4172380101/10000000000 : ℝ)*X 0 0+(1552353671/5000000000 : ℝ)*X 0 1+(1113685711/2000000000 : ℝ)*X 0 2+(4172380101/10000000000 : ℝ)*X 1 0+(1552353671/5000000000 : ℝ)*X 1 1+(1113685711/2000000000 : ℝ)*X 1 2+(4172380101/10000000000 : ℝ)*X 2 0+(1552353671/5000000000 : ℝ)*X 2 1+(1113685711/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-447058033/2500000000 : ℝ)*X 0 0+(4850773799/10000000000 : ℝ)*X 0 1+(5947779911/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5181300731/10000000000 : ℝ)*X 1 0+(-131316313/1000000000 : ℝ)*X 1 1+(5947779731/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5181300397/10000000000 : ℝ)*X 2 0+(118955597/200000000 : ℝ)*X 2 1+(-1313163449/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((836278659/2000000000 : ℝ)*X 0 0+(5505191077/10000000000 : ℝ)*X 0 1+(3170204833/10000000000 : ℝ)*X 0 2+(836278659/2000000000 : ℝ)*X 1 0+(5505191077/10000000000 : ℝ)*X 1 1+(3170204833/10000000000 : ℝ)*X 1 2+(836278659/2000000000 : ℝ)*X 2 0+(5505191077/10000000000 : ℝ)*X 2 1+(3170204833/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11603079426478062000759/2000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (135709793/50000000000000 : ℝ)*(base1) + (2451911/10000000000000 : ℝ)*(base16) + (266793317/20000000000000 : ℝ)*(base19) + (1332395999/100000000000000 : ℝ)*(base23) + (243988347/100000000000000 : ℝ)*(upper3) + (317460485204123/50000000000000 : ℝ)*(major0) + (317460485204123/50000000000000 : ℝ)*(major1) + (317460485204123/50000000000000 : ℝ)*(major2) + (863945098847093/100000000000000 : ℝ)*(sp0) + (863946716989461/100000000000000 : ℝ)*(sp1) + (215986685769789/25000000000000 : ℝ)*(sp2) + (25368210531717/6250000000000 : ℝ)*(sp3) + (3248047649/100000000000000 : ℝ)*(sp4) + (254003701/12500000000000 : ℝ)*(sp7) + (202946835978333/50000000000000 : ℝ)*(f.failure) + (215987018868789/25000000000000 : ℝ)*(f.sum) + (15686266565249/4000000000000000000000000000 : ℝ)*base65 + (45246963025249/8000000000000000000000000000 : ℝ)*base67 + (35879246241249/8000000000000000000000000000 : ℝ)*base69 + (76145201745249/8000000000000000000000000000 : ℝ)*base71 + (15074779093249/4000000000000000000000000000 : ℝ)*base73 + (55341518497249/8000000000000000000000000000 : ℝ)*base75 + (97112783313249/8000000000000000000000000000 : ℝ)*base77 + (109269104049249/8000000000000000000000000000 : ℝ)*base79 + (3215581905249/4000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (29025907/2500000000000000000000 : ℝ)*base90 + (29025907/2500000000000000000000 : ℝ)*base92 + (29025907/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6461790577840333275753/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (79542847/5000000000000 : ℝ)*(base19) + (382530771/25000000000000 : ℝ)*(base23) + (155472807/100000000000000 : ℝ)*(base32) + (221307639/100000000000000 : ℝ)*(upper3) + (29752977/20000000000000 : ℝ)*(upper5) + (83739956287459/12500000000000 : ℝ)*(major0) + (83739956287459/12500000000000 : ℝ)*(major1) + (83739956287459/12500000000000 : ℝ)*(major2) + (112865283/3125000000000 : ℝ)*(sp1) + (3579327521/100000000000000 : ℝ)*(sp2) + (455785690163837/50000000000000 : ℝ)*(sp4) + (455783088890839/50000000000000 : ℝ)*(sp5) + (227891567719267/25000000000000 : ℝ)*(sp6) + (107066887351459/25000000000000 : ℝ)*(sp7) + (214133852439321/50000000000000 : ℝ)*(f.failure) + (455785690163837/50000000000000 : ℝ)*(f.sum) + (934132332583/1000000000000000000000000000 : ℝ)*base66 + (4530961476583/2000000000000000000000000000 : ℝ)*base68 + (11545808484583/2000000000000000000000000000 : ℝ)*base70 + (1245040323417/2000000000000000000000000000 : ℝ)*base71 + (6131584784583/1000000000000000000000000000 : ℝ)*base74 + (6206156300583/2000000000000000000000000000 : ℝ)*base76 + (6101555739417/2000000000000000000000000000 : ℝ)*base77 + (8577067977417/2000000000000000000000000000 : ℝ)*base79 + (6822425306583/1000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (17197559/2500000000000000000000 : ℝ)*base90 + (17197559/2500000000000000000000 : ℝ)*base92 + (17197559/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1385_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78212721/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (433/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5313/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1385_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1385_s1_0 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1962626443/10000000000 : ℝ)*x 0 + (1124674577/2000000000 : ℝ)*x 1 + (632724459/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1962626443/10000000000 : ℝ)^4345 ≤ (11879293066259/100000000000000 : ℝ)^3321 := by
    have hnat : (1962626443 : ℕ)^4345*100000000000000^3321 ≤ 11879293066259^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1962626443 10000000000 11879293066259 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1124674577/2000000000 : ℝ)^4345 ≤ (9417609999957/20000000000000 : ℝ)^3321 := by
    have hnat : (1124674577 : ℕ)^4345*20000000000000^3321 ≤ 9417609999957^3321*2000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124674577 2000000000 9417609999957 20000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (632724459/1250000000 : ℝ)^4345 ≤ (20516328457613/50000000000000 : ℝ)^3321 := by
    have hnat : (632724459 : ℕ)^4345*50000000000000^3321 ≤ 20516328457613^3321*1250000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      632724459 1250000000 20516328457613 50000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1962626443/10000000000 : ℝ), (1124674577/2000000000 : ℝ), (632724459/1250000000 : ℝ)] ![(11879293066259/100000000000000 : ℝ), (9417609999957/20000000000000 : ℝ), (20516328457613/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1962626443/10000000000 : ℝ)|^4345 ≤ (11879293066259/100000000000000 : ℝ)^3321
        have hw : |(-1962626443/10000000000 : ℝ)|=(1962626443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1124674577/2000000000 : ℝ)|^4345 ≤ (9417609999957/20000000000000 : ℝ)^3321
        have hw : |(1124674577/2000000000 : ℝ)|=(1124674577/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(632724459/1250000000 : ℝ)|^4345 ≤ (20516328457613/50000000000000 : ℝ)^3321
        have hw : |(632724459/1250000000 : ℝ)|=(632724459/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_s1_1 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1350317961/2500000000 : ℝ)*x 0 + (-1130613569/5000000000 : ℝ)*x 1 + (1265449279/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1350317961/2500000000 : ℝ)^4345 ≤ (44669761427017/100000000000000 : ℝ)^3321 := by
    have hnat : (1350317961 : ℕ)^4345*100000000000000^3321 ≤ 44669761427017^3321*2500000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350317961 2500000000 44669761427017 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1130613569/5000000000 : ℝ)^4345 ≤ (14297566335209/100000000000000 : ℝ)^3321 := by
    have hnat : (1130613569 : ℕ)^4345*100000000000000^3321 ≤ 14297566335209^3321*5000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130613569 5000000000 14297566335209 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1265449279/2500000000 : ℝ)^4345 ≤ (4103267223009/10000000000000 : ℝ)^3321 := by
    have hnat : (1265449279 : ℕ)^4345*10000000000000^3321 ≤ 4103267223009^3321*2500000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1265449279 2500000000 4103267223009 10000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1350317961/2500000000 : ℝ), (-1130613569/5000000000 : ℝ), (1265449279/2500000000 : ℝ)] ![(44669761427017/100000000000000 : ℝ), (14297566335209/100000000000000 : ℝ), (4103267223009/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1350317961/2500000000 : ℝ)|^4345 ≤ (44669761427017/100000000000000 : ℝ)^3321
        have hw : |(1350317961/2500000000 : ℝ)|=(1350317961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1130613569/5000000000 : ℝ)|^4345 ≤ (14297566335209/100000000000000 : ℝ)^3321
        have hw : |(-1130613569/5000000000 : ℝ)|=(1130613569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1265449279/2500000000 : ℝ)|^4345 ≤ (4103267223009/10000000000000 : ℝ)^3321
        have hw : |(1265449279/2500000000 : ℝ)|=(1265449279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_s1_2 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (270063631/500000000 : ℝ)*x 0 + (1012359171/2000000000 : ℝ)*x 1 + (-2261227739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270063631/500000000 : ℝ)^4345 ≤ (8933953964711/20000000000000 : ℝ)^3321 := by
    have hnat : (270063631 : ℕ)^4345*20000000000000^3321 ≤ 8933953964711^3321*500000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270063631 500000000 8933953964711 20000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1012359171/2000000000 : ℝ)^4345 ≤ (41032658856099/100000000000000 : ℝ)^3321 := by
    have hnat : (1012359171 : ℕ)^4345*100000000000000^3321 ≤ 41032658856099^3321*2000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1012359171 2000000000 41032658856099 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2261227739/10000000000 : ℝ)^4345 ≤ (2859514261401/20000000000000 : ℝ)^3321 := by
    have hnat : (2261227739 : ℕ)^4345*20000000000000^3321 ≤ 2859514261401^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2261227739 10000000000 2859514261401 20000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(270063631/500000000 : ℝ), (1012359171/2000000000 : ℝ), (-2261227739/10000000000 : ℝ)] ![(8933953964711/20000000000000 : ℝ), (41032658856099/100000000000000 : ℝ), (2859514261401/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(270063631/500000000 : ℝ)|^4345 ≤ (8933953964711/20000000000000 : ℝ)^3321
        have hw : |(270063631/500000000 : ℝ)|=(270063631/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1012359171/2000000000 : ℝ)|^4345 ≤ (41032658856099/100000000000000 : ℝ)^3321
        have hw : |(1012359171/2000000000 : ℝ)|=(1012359171/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2261227739/10000000000 : ℝ)|^4345 ≤ (2859514261401/20000000000000 : ℝ)^3321
        have hw : |(-2261227739/10000000000 : ℝ)|=(2261227739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_s1_3 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (428460167/1000000000 : ℝ)*x 0 + (744972021/2000000000 : ℝ)*x 1 + (4920177629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (428460167/1000000000 : ℝ)^4345 ≤ (8248090422569/25000000000000 : ℝ)^3321 := by
    have hnat : (428460167 : ℕ)^4345*25000000000000^3321 ≤ 8248090422569^3321*1000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428460167 1000000000 8248090422569 25000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (744972021/2000000000 : ℝ)^4345 ≤ (27470441809479/100000000000000 : ℝ)^3321 := by
    have hnat : (744972021 : ℕ)^4345*100000000000000^3321 ≤ 27470441809479^3321*2000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      744972021 2000000000 27470441809479 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4920177629/10000000000 : ℝ)^4345 ≤ (19768598246607/50000000000000 : ℝ)^3321 := by
    have hnat : (4920177629 : ℕ)^4345*50000000000000^3321 ≤ 19768598246607^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4920177629 10000000000 19768598246607 50000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(428460167/1000000000 : ℝ), (744972021/2000000000 : ℝ), (4920177629/10000000000 : ℝ)] ![(8248090422569/25000000000000 : ℝ), (27470441809479/100000000000000 : ℝ), (19768598246607/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(428460167/1000000000 : ℝ)|^4345 ≤ (8248090422569/25000000000000 : ℝ)^3321
        have hw : |(428460167/1000000000 : ℝ)|=(428460167/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(744972021/2000000000 : ℝ)|^4345 ≤ (27470441809479/100000000000000 : ℝ)^3321
        have hw : |(744972021/2000000000 : ℝ)|=(744972021/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4920177629/10000000000 : ℝ)|^4345 ≤ (19768598246607/50000000000000 : ℝ)^3321
        have hw : |(4920177629/10000000000 : ℝ)|=(4920177629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_s1_4 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-981544769/5000000000 : ℝ)*x 0 + (79197063/156250000 : ℝ)*x 1 + (2808218331/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (981544769/5000000000 : ℝ)^4345 ≤ (2970740119657/25000000000000 : ℝ)^3321 := by
    have hnat : (981544769 : ℕ)^4345*25000000000000^3321 ≤ 2970740119657^3321*5000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      981544769 5000000000 2970740119657 25000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (79197063/156250000 : ℝ)^4345 ≤ (8220993057323/20000000000000 : ℝ)^3321 := by
    have hnat : (79197063 : ℕ)^4345*20000000000000^3321 ≤ 8220993057323^3321*156250000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79197063 156250000 8220993057323 20000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2808218331/5000000000 : ℝ)^4345 ≤ (47012074221507/100000000000000 : ℝ)^3321 := by
    have hnat : (2808218331 : ℕ)^4345*100000000000000^3321 ≤ 47012074221507^3321*5000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2808218331 5000000000 47012074221507 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-981544769/5000000000 : ℝ), (79197063/156250000 : ℝ), (2808218331/5000000000 : ℝ)] ![(2970740119657/25000000000000 : ℝ), (8220993057323/20000000000000 : ℝ), (47012074221507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-981544769/5000000000 : ℝ)|^4345 ≤ (2970740119657/25000000000000 : ℝ)^3321
        have hw : |(-981544769/5000000000 : ℝ)|=(981544769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(79197063/156250000 : ℝ)|^4345 ≤ (8220993057323/20000000000000 : ℝ)^3321
        have hw : |(79197063/156250000 : ℝ)|=(79197063/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2808218331/5000000000 : ℝ)|^4345 ≤ (47012074221507/100000000000000 : ℝ)^3321
        have hw : |(2808218331/5000000000 : ℝ)|=(2808218331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_s1_5 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2627520191/5000000000 : ℝ)*x 0 + (-1706587391/10000000000 : ℝ)*x 1 + (1404109181/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2627520191/5000000000 : ℝ)^4345 ≤ (43094142029659/100000000000000 : ℝ)^3321 := by
    have hnat : (2627520191 : ℕ)^4345*100000000000000^3321 ≤ 43094142029659^3321*5000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627520191 5000000000 43094142029659 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1706587391/10000000000 : ℝ)^4345 ≤ (4946891525459/50000000000000 : ℝ)^3321 := by
    have hnat : (1706587391 : ℕ)^4345*50000000000000^3321 ≤ 4946891525459^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1706587391 10000000000 4946891525459 50000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1404109181/2500000000 : ℝ)^4345 ≤ (23506037450247/50000000000000 : ℝ)^3321 := by
    have hnat : (1404109181 : ℕ)^4345*50000000000000^3321 ≤ 23506037450247^3321*2500000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1404109181 2500000000 23506037450247 50000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2627520191/5000000000 : ℝ), (-1706587391/10000000000 : ℝ), (1404109181/2500000000 : ℝ)] ![(43094142029659/100000000000000 : ℝ), (4946891525459/50000000000000 : ℝ), (23506037450247/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2627520191/5000000000 : ℝ)|^4345 ≤ (43094142029659/100000000000000 : ℝ)^3321
        have hw : |(2627520191/5000000000 : ℝ)|=(2627520191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1706587391/10000000000 : ℝ)|^4345 ≤ (4946891525459/50000000000000 : ℝ)^3321
        have hw : |(-1706587391/10000000000 : ℝ)|=(1706587391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1404109181/2500000000 : ℝ)|^4345 ≤ (23506037450247/50000000000000 : ℝ)^3321
        have hw : |(1404109181/2500000000 : ℝ)|=(1404109181/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_s1_6 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1051008149/2000000000 : ℝ)*x 0 + (2808218527/5000000000 : ℝ)*x 1 + (-1706586401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051008149/2000000000 : ℝ)^4345 ≤ (43094145924321/100000000000000 : ℝ)^3321 := by
    have hnat : (1051008149 : ℕ)^4345*100000000000000^3321 ≤ 43094145924321^3321*2000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051008149 2000000000 43094145924321 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2808218527/5000000000 : ℝ)^4345 ≤ (23506039257227/50000000000000 : ℝ)^3321 := by
    have hnat : (2808218527 : ℕ)^4345*50000000000000^3321 ≤ 23506039257227^3321*5000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2808218527 5000000000 23506039257227 50000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1706586401/10000000000 : ℝ)^4345 ≤ (9893775541783/100000000000000 : ℝ)^3321 := by
    have hnat : (1706586401 : ℕ)^4345*100000000000000^3321 ≤ 9893775541783^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1706586401 10000000000 9893775541783 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051008149/2000000000 : ℝ), (2808218527/5000000000 : ℝ), (-1706586401/10000000000 : ℝ)] ![(43094145924321/100000000000000 : ℝ), (23506039257227/50000000000000 : ℝ), (9893775541783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051008149/2000000000 : ℝ)|^4345 ≤ (43094145924321/100000000000000 : ℝ)^3321
        have hw : |(1051008149/2000000000 : ℝ)|=(1051008149/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2808218527/5000000000 : ℝ)|^4345 ≤ (23506039257227/50000000000000 : ℝ)^3321
        have hw : |(2808218527/5000000000 : ℝ)|=(2808218527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1706586401/10000000000 : ℝ)|^4345 ≤ (9893775541783/100000000000000 : ℝ)^3321
        have hw : |(-1706586401/10000000000 : ℝ)|=(1706586401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_s1_7 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4285588889/10000000000 : ℝ)*x 0 + (981133963/2000000000 : ℝ)*x 1 + (1869810449/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4285588889/10000000000 : ℝ)^4345 ≤ (33002307789523/100000000000000 : ℝ)^3321 := by
    have hnat : (4285588889 : ℕ)^4345*100000000000000^3321 ≤ 33002307789523^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4285588889 10000000000 33002307789523 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (981133963/2000000000 : ℝ)^4345 ≤ (39384738441029/100000000000000 : ℝ)^3321 := by
    have hnat : (981133963 : ℕ)^4345*100000000000000^3321 ≤ 39384738441029^3321*2000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      981133963 2000000000 39384738441029 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1869810449/5000000000 : ℝ)^4345 ≤ (13806476879177/50000000000000 : ℝ)^3321 := by
    have hnat : (1869810449 : ℕ)^4345*50000000000000^3321 ≤ 13806476879177^3321*5000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1869810449 5000000000 13806476879177 50000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4285588889/10000000000 : ℝ), (981133963/2000000000 : ℝ), (1869810449/5000000000 : ℝ)] ![(33002307789523/100000000000000 : ℝ), (39384738441029/100000000000000 : ℝ), (13806476879177/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4285588889/10000000000 : ℝ)|^4345 ≤ (33002307789523/100000000000000 : ℝ)^3321
        have hw : |(4285588889/10000000000 : ℝ)|=(4285588889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(981133963/2000000000 : ℝ)|^4345 ≤ (39384738441029/100000000000000 : ℝ)^3321
        have hw : |(981133963/2000000000 : ℝ)|=(981133963/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1869810449/5000000000 : ℝ)|^4345 ≤ (13806476879177/50000000000000 : ℝ)^3321
        have hw : |(1869810449/5000000000 : ℝ)|=(1869810449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1385_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78212721/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5313/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (433/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (3639/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4787/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5313/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (433/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5313/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (433/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5313/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (433/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5313/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (433/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5313/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (433/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5313/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (433/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (433/25000 : ℝ) ^ (543/128 : ℝ) ≤ (673937873027/20000000000000000000 : ℝ) := by
    have hpowers : (433/25000 : ℝ)^543 ≤ (673937873027/20000000000000000000 : ℝ)^128 := by
      have hnat : (433 : ℕ)^543*20000000000000000000^128 ≤ 673937873027^128*25000^543 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        433 25000 673937873027 20000000000000000000 543 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (433/25000 : ℝ)) (X := (673937873027/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 543 128 (by norm_num) hpowers
    exact h
  have hpowhi : (5313/20000 : ℝ) ^ (543/128 : ℝ) ≤ (361255373366510713/100000000000000000000 : ℝ) := by
    have hpowers : (5313/20000 : ℝ)^543 ≤ (361255373366510713/100000000000000000000 : ℝ)^128 := by
      have hnat : (5313 : ℕ)^543*100000000000000000000^128 ≤ 361255373366510713^128*20000^543 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5313 20000 361255373366510713 100000000000000000000 543 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5313/20000 : ℝ)) (X := (361255373366510713/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 543 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000000673937873027/10000000000000000000 : ℝ) ≤ (5000000079432823/5000000000000000 : ℝ) ^ (543/128 : ℝ) := by
    have hpowers : (10000000673937873027/10000000000000000000 : ℝ)^128 ≤ (5000000079432823/5000000000000000 : ℝ)^543 := by
      have hnat : (10000000673937873027 : ℕ)^128*5000000000000000^543 ≤ 5000000079432823^543*10000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000000673937873027 10000000000000000000 5000000079432823 5000000000000000 128 543 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000079432823/5000000000000000 : ℝ)) (X := (10000000673937873027/10000000000000000000 : ℝ)) (by norm_num) 543 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (12545157342881984481/12500000000000000000 : ℝ) ≤ (5004252064318273/5000000000000000 : ℝ) ^ (543/128 : ℝ) := by
    have hpowers : (12545157342881984481/12500000000000000000 : ℝ)^128 ≤ (5004252064318273/5000000000000000 : ℝ)^543 := by
      have hnat : (12545157342881984481 : ℕ)^128*5000000000000000^543 ≤ 5004252064318273^543*12500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12545157342881984481 12500000000000000000 5004252064318273 5000000000000000 128 543 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004252064318273/5000000000000000 : ℝ)) (X := (12545157342881984481/12500000000000000000 : ℝ)) (by norm_num) 543 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50361255373366510713/50000000000000000000 : ℝ) ≤ (5008504049203723/5000000000000000 : ℝ) ^ (543/128 : ℝ) := by
    have hpowers : (50361255373366510713/50000000000000000000 : ℝ)^128 ≤ (5008504049203723/5000000000000000 : ℝ)^543 := by
      have hnat : (50361255373366510713 : ℕ)^128*5000000000000000^543 ≤ 5008504049203723^543*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50361255373366510713 50000000000000000000 5008504049203723 5000000000000000 128 543 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5008504049203723/5000000000000000 : ℝ)) (X := (50361255373366510713/50000000000000000000 : ℝ)) (by norm_num) 543 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(673937873027/20000000000000000000 : ℝ) ≤ ((124150273096912094759/124165000000000000000 : ℝ)+2*(85039697709/24833000000000 : ℝ)*(433/25000 : ℝ))^(543/128 : ℝ) := by
    rw [show (124150273096912094759/124165000000000000000 : ℝ)+2*(85039697709/24833000000000 : ℝ)*(433/25000 : ℝ)=(5000000079432823/5000000000000000 : ℝ) by norm_num, show 1+2*(673937873027/20000000000000000000 : ℝ)=(10000000673937873027/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(361255373366510713/100000000000000000000 : ℝ)+(673937873027/20000000000000000000 : ℝ) ≤ ((124150273096912094759/124165000000000000000 : ℝ)+(85039697709/24833000000000 : ℝ)*((5313/20000 : ℝ)+(433/25000 : ℝ)))^(543/128 : ℝ) := by
    rw [show (124150273096912094759/124165000000000000000 : ℝ)+(85039697709/24833000000000 : ℝ)*((5313/20000 : ℝ)+(433/25000 : ℝ))=(5004252064318273/5000000000000000 : ℝ) by norm_num, show 1+(361255373366510713/100000000000000000000 : ℝ)+(673937873027/20000000000000000000 : ℝ)=(12545157342881984481/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(361255373366510713/100000000000000000000 : ℝ) ≤ ((124150273096912094759/124165000000000000000 : ℝ)+2*(85039697709/24833000000000 : ℝ)*(5313/20000 : ℝ))^(543/128 : ℝ) := by
    rw [show (124150273096912094759/124165000000000000000 : ℝ)+2*(85039697709/24833000000000 : ℝ)*(5313/20000 : ℝ)=(5008504049203723/5000000000000000 : ℝ) by norm_num, show 1+2*(361255373366510713/100000000000000000000 : ℝ)=(50361255373366510713/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (124150273096912094759/124165000000000000000 : ℝ)*(X 1 0+X 2 0)+(85039697709/24833000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (543/128 : ℝ)) (lo := (433/25000 : ℝ)) (hi := (5313/20000 : ℝ)) (c := (124150273096912094759/124165000000000000000 : ℝ)) (alpha := (85039697709/24833000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (124150273096912094759/124165000000000000000 : ℝ)*(X 0 1+X 2 1)+(85039697709/24833000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (543/128 : ℝ)) (lo := (433/25000 : ℝ)) (hi := (5313/20000 : ℝ)) (c := (124150273096912094759/124165000000000000000 : ℝ)) (alpha := (85039697709/24833000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (124150273096912094759/124165000000000000000 : ℝ)*(X 0 2+X 1 2)+(85039697709/24833000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (543/128 : ℝ)) (lo := (433/25000 : ℝ)) (hi := (5313/20000 : ℝ)) (c := (124150273096912094759/124165000000000000000 : ℝ)) (alpha := (85039697709/24833000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1962626443/10000000000 : ℝ)*X 0 0+(1124674577/2000000000 : ℝ)*X 0 1+(632724459/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1350317961/2500000000 : ℝ)*X 1 0+(-1130613569/5000000000 : ℝ)*X 1 1+(1265449279/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((270063631/500000000 : ℝ)*X 2 0+(1012359171/2000000000 : ℝ)*X 2 1+(-2261227739/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((428460167/1000000000 : ℝ)*X 0 0+(744972021/2000000000 : ℝ)*X 0 1+(4920177629/10000000000 : ℝ)*X 0 2+(428460167/1000000000 : ℝ)*X 1 0+(744972021/2000000000 : ℝ)*X 1 1+(4920177629/10000000000 : ℝ)*X 1 2+(428460167/1000000000 : ℝ)*X 2 0+(744972021/2000000000 : ℝ)*X 2 1+(4920177629/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-981544769/5000000000 : ℝ)*X 0 0+(79197063/156250000 : ℝ)*X 0 1+(2808218331/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2627520191/5000000000 : ℝ)*X 1 0+(-1706587391/10000000000 : ℝ)*X 1 1+(1404109181/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1051008149/2000000000 : ℝ)*X 2 0+(2808218527/5000000000 : ℝ)*X 2 1+(-1706586401/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4285588889/10000000000 : ℝ)*X 0 0+(981133963/2000000000 : ℝ)*X 0 1+(1869810449/5000000000 : ℝ)*X 0 2+(4285588889/10000000000 : ℝ)*X 1 0+(981133963/2000000000 : ℝ)*X 1 1+(1869810449/5000000000 : ℝ)*X 1 2+(4285588889/10000000000 : ℝ)*X 2 0+(981133963/2000000000 : ℝ)*X 2 1+(1869810449/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1588700118011445326985195789/326750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (724481319/100000000000000 : ℝ)*(base19) + (255476039/25000000000000 : ℝ)*(base23) + (6737923/25000000000000 : ℝ)*(upper2) + (123303619/100000000000000 : ℝ)*(upper3) + (1308660630625083/100000000000000 : ℝ)*(major0) + (1308660630625083/100000000000000 : ℝ)*(major1) + (1308660630625083/100000000000000 : ℝ)*(major2) + (445177198676411/25000000000000 : ℝ)*(sp0) + (111294808345987/6250000000000 : ℝ)*(sp1) + (445179082281219/25000000000000 : ℝ)*(sp2) + (836600155143487/100000000000000 : ℝ)*(sp3) + (4431655733/50000000000000 : ℝ)*(sp4) + (306988079/100000000000000 : ℝ)*(sp6) + (65720373/2000000000000 : ℝ)*(sp7) + (836603441162137/100000000000000 : ℝ)*(f.failure) + (178071765801711/10000000000000 : ℝ)*(f.sum) + (30731787333/8168750000000000000000000 : ℝ)*base65 + (862845638098565263/653500000000000000000000000000000 : ℝ)*base67 + (1794338652212434737/653500000000000000000000000000000 : ℝ)*base70 + (3893187415529934737/653500000000000000000000000000000 : ℝ)*base72 + (4625106814437/1307000000000000000000000000 : ℝ)*base73 + (5681249878154434737/653500000000000000000000000000000 : ℝ)*base76 + (1349102324575565263/653500000000000000000000000000000 : ℝ)*base77 + (2528065480380434737/653500000000000000000000000000000 : ℝ)*base80 + (11758957687/6535000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (13055223/5000000000000000000000 : ℝ)*base90 + (13055223/5000000000000000000000 : ℝ)*base92 + (13055223/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6236011324783420349162036877/1552062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (154047973/100000000000000 : ℝ)*(base1) + (1142446223/100000000000000 : ℝ)*(base19) + (1349757509/100000000000000 : ℝ)*(base23) + (109348049/100000000000000 : ℝ)*(upper3) + (42126023/25000000000000 : ℝ)*(upper5) + (670750000628801/50000000000000 : ℝ)*(major0) + (670750000628801/50000000000000 : ℝ)*(major1) + (670750000628801/50000000000000 : ℝ)*(major2) + (5701863089/100000000000000 : ℝ)*(sp1) + (8620557133/100000000000000 : ℝ)*(sp2) + (228175369564173/12500000000000 : ℝ)*(sp4) + (912697979078049/50000000000000 : ℝ)*(sp5) + (114087052009423/6250000000000 : ℝ)*(sp6) + (857596912072257/100000000000000 : ℝ)*(sp7) + (85759706612023/10000000000000 : ℝ)*(f.failure) + (182540280246541/10000000000000 : ℝ)*(f.sum) + (19160622623487/24833000000000000000000000000 : ℝ)*base65 + (75580703709588196041/6208250000000000000000000000000000 : ℝ)*base68 + (31811003121858946041/6208250000000000000000000000000000 : ℝ)*base70 + (36876668359564696041/6208250000000000000000000000000000 : ℝ)*base72 + (17638372914371/4966600000000000000000000000 : ℝ)*base74 + (3777727498480053959/6208250000000000000000000000000000 : ℝ)*base75 + (69367700362975696041/6208250000000000000000000000000000 : ℝ)*base78 + (66941333423804946041/6208250000000000000000000000000000 : ℝ)*base80 + (62324532426037/24833000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (144583/500000000000000000000 : ℝ)*base89 + (144583/500000000000000000000 : ℝ)*base91 + (144583/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1385_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78212721/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5313/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (433/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3639/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4787/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1385_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1385_s2_0 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1999174219/10000000000 : ℝ)*x 0 + (218741721/400000000 : ℝ)*x 1 + (259657893/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1999174219/10000000000 : ℝ)^4345 ≤ (2433908925181/20000000000000 : ℝ)^3321 := by
    have hnat : (1999174219 : ℕ)^4345*20000000000000^3321 ≤ 2433908925181^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1999174219 10000000000 2433908925181 20000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (218741721/400000000 : ℝ)^4345 ≤ (22699524057363/50000000000000 : ℝ)^3321 := by
    have hnat : (218741721 : ℕ)^4345*50000000000000^3321 ≤ 22699524057363^3321*400000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218741721 400000000 22699524057363 50000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (259657893/500000000 : ℝ)^4345 ≤ (42431407248607/100000000000000 : ℝ)^3321 := by
    have hnat : (259657893 : ℕ)^4345*100000000000000^3321 ≤ 42431407248607^3321*500000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259657893 500000000 42431407248607 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1999174219/10000000000 : ℝ), (218741721/400000000 : ℝ), (259657893/500000000 : ℝ)] ![(2433908925181/20000000000000 : ℝ), (22699524057363/50000000000000 : ℝ), (42431407248607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1999174219/10000000000 : ℝ)|^4345 ≤ (2433908925181/20000000000000 : ℝ)^3321
        have hw : |(-1999174219/10000000000 : ℝ)|=(1999174219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(218741721/400000000 : ℝ)|^4345 ≤ (22699524057363/50000000000000 : ℝ)^3321
        have hw : |(218741721/400000000 : ℝ)|=(218741721/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(259657893/500000000 : ℝ)|^4345 ≤ (42431407248607/100000000000000 : ℝ)^3321
        have hw : |(259657893/500000000 : ℝ)|=(259657893/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_s2_1 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2681501697/5000000000 : ℝ)*x 0 + (-2141149589/10000000000 : ℝ)*x 1 + (5193157789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681501697/5000000000 : ℝ)^4345 ≤ (44256139119533/100000000000000 : ℝ)^3321 := by
    have hnat : (2681501697 : ℕ)^4345*100000000000000^3321 ≤ 44256139119533^3321*5000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681501697 5000000000 44256139119533 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2141149589/10000000000 : ℝ)^4345 ≤ (13312454377271/100000000000000 : ℝ)^3321 := by
    have hnat : (2141149589 : ℕ)^4345*100000000000000^3321 ≤ 13312454377271^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141149589 10000000000 13312454377271 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5193157789/10000000000 : ℝ)^4345 ≤ (42431406489619/100000000000000 : ℝ)^3321 := by
    have hnat : (5193157789 : ℕ)^4345*100000000000000^3321 ≤ 42431406489619^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5193157789 10000000000 42431406489619 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681501697/5000000000 : ℝ), (-2141149589/10000000000 : ℝ), (5193157789/10000000000 : ℝ)] ![(44256139119533/100000000000000 : ℝ), (13312454377271/100000000000000 : ℝ), (42431406489619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681501697/5000000000 : ℝ)|^4345 ≤ (44256139119533/100000000000000 : ℝ)^3321
        have hw : |(2681501697/5000000000 : ℝ)|=(2681501697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2141149589/10000000000 : ℝ)|^4345 ≤ (13312454377271/100000000000000 : ℝ)^3321
        have hw : |(-2141149589/10000000000 : ℝ)|=(2141149589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5193157789/10000000000 : ℝ)|^4345 ≤ (42431406489619/100000000000000 : ℝ)^3321
        have hw : |(5193157789/10000000000 : ℝ)|=(5193157789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_s2_2 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (335187703/625000000 : ℝ)*x 0 + (324572371/625000000 : ℝ)*x 1 + (-214114959/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335187703/625000000 : ℝ)^4345 ≤ (691502149113/1562500000000 : ℝ)^3321 := by
    have hnat : (335187703 : ℕ)^4345*1562500000000^3321 ≤ 691502149113^3321*625000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335187703 625000000 691502149113 1562500000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (324572371/625000000 : ℝ)^4345 ≤ (8486281612209/20000000000000 : ℝ)^3321 := by
    have hnat : (324572371 : ℕ)^4345*20000000000000^3321 ≤ 8486281612209^3321*625000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324572371 625000000 8486281612209 20000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (214114959/1000000000 : ℝ)^4345 ≤ (6656227192703/50000000000000 : ℝ)^3321 := by
    have hnat : (214114959 : ℕ)^4345*50000000000000^3321 ≤ 6656227192703^3321*1000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214114959 1000000000 6656227192703 50000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335187703/625000000 : ℝ), (324572371/625000000 : ℝ), (-214114959/1000000000 : ℝ)] ![(691502149113/1562500000000 : ℝ), (8486281612209/20000000000000 : ℝ), (6656227192703/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335187703/625000000 : ℝ)|^4345 ≤ (691502149113/1562500000000 : ℝ)^3321
        have hw : |(335187703/625000000 : ℝ)|=(335187703/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(324572371/625000000 : ℝ)|^4345 ≤ (8486281612209/20000000000000 : ℝ)^3321
        have hw : |(324572371/625000000 : ℝ)|=(324572371/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-214114959/1000000000 : ℝ)|^4345 ≤ (6656227192703/50000000000000 : ℝ)^3321
        have hw : |(-214114959/1000000000 : ℝ)|=(214114959/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_s2_3 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2155141407/5000000000 : ℝ)*x 0 + (80526367/200000000 : ℝ)*x 1 + (4612478381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155141407/5000000000 : ℝ)^4345 ≤ (6650265067603/20000000000000 : ℝ)^3321 := by
    have hnat : (2155141407 : ℕ)^4345*20000000000000^3321 ≤ 6650265067603^3321*5000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155141407 5000000000 6650265067603 20000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (80526367/200000000 : ℝ)^4345 ≤ (30414812038677/100000000000000 : ℝ)^3321 := by
    have hnat : (80526367 : ℕ)^4345*100000000000000^3321 ≤ 30414812038677^3321*200000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80526367 200000000 30414812038677 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4612478381/10000000000 : ℝ)^4345 ≤ (36333862613819/100000000000000 : ℝ)^3321 := by
    have hnat : (4612478381 : ℕ)^4345*100000000000000^3321 ≤ 36333862613819^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4612478381 10000000000 36333862613819 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2155141407/5000000000 : ℝ), (80526367/200000000 : ℝ), (4612478381/10000000000 : ℝ)] ![(6650265067603/20000000000000 : ℝ), (30414812038677/100000000000000 : ℝ), (36333862613819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2155141407/5000000000 : ℝ)|^4345 ≤ (6650265067603/20000000000000 : ℝ)^3321
        have hw : |(2155141407/5000000000 : ℝ)|=(2155141407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(80526367/200000000 : ℝ)|^4345 ≤ (30414812038677/100000000000000 : ℝ)^3321
        have hw : |(80526367/200000000 : ℝ)|=(80526367/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4612478381/10000000000 : ℝ)|^4345 ≤ (36333862613819/100000000000000 : ℝ)^3321
        have hw : |(4612478381/10000000000 : ℝ)|=(4612478381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_s2_4 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-999614301/5000000000 : ℝ)*x 0 + (64935083/125000000 : ℝ)*x 1 + (5466880271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (999614301/5000000000 : ℝ)^4345 ≤ (3042494436809/25000000000000 : ℝ)^3321 := by
    have hnat : (999614301 : ℕ)^4345*25000000000000^3321 ≤ 3042494436809^3321*5000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999614301 5000000000 3042494436809 25000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (64935083/125000000 : ℝ)^4345 ≤ (21224516766697/50000000000000 : ℝ)^3321 := by
    have hnat : (64935083 : ℕ)^4345*50000000000000^3321 ≤ 21224516766697^3321*125000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64935083 125000000 21224516766697 50000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5466880271/10000000000 : ℝ)^4345 ≤ (141815589689/312500000000 : ℝ)^3321 := by
    have hnat : (5466880271 : ℕ)^4345*312500000000^3321 ≤ 141815589689^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5466880271 10000000000 141815589689 312500000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-999614301/5000000000 : ℝ), (64935083/125000000 : ℝ), (5466880271/10000000000 : ℝ)] ![(3042494436809/25000000000000 : ℝ), (21224516766697/50000000000000 : ℝ), (141815589689/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-999614301/5000000000 : ℝ)|^4345 ≤ (3042494436809/25000000000000 : ℝ)^3321
        have hw : |(-999614301/5000000000 : ℝ)|=(999614301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(64935083/125000000 : ℝ)|^4345 ≤ (21224516766697/50000000000000 : ℝ)^3321
        have hw : |(64935083/125000000 : ℝ)|=(64935083/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5466880271/10000000000 : ℝ)|^4345 ≤ (141815589689/312500000000 : ℝ)^3321
        have hw : |(5466880271/10000000000 : ℝ)|=(5466880271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_s2_5 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5291701417/10000000000 : ℝ)*x 0 + (-1867427751/10000000000 : ℝ)*x 1 + (5466879957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5291701417/10000000000 : ℝ)^4345 ≤ (43487904130097/100000000000000 : ℝ)^3321 := by
    have hnat : (5291701417 : ℕ)^4345*100000000000000^3321 ≤ 43487904130097^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5291701417 10000000000 43487904130097 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1867427751/10000000000 : ℝ)^4345 ≤ (2226222113229/20000000000000 : ℝ)^3321 := by
    have hnat : (1867427751 : ℕ)^4345*20000000000000^3321 ≤ 2226222113229^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1867427751 10000000000 2226222113229 20000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5466879957/10000000000 : ℝ)^4345 ≤ (17726947379/39062500000 : ℝ)^3321 := by
    have hnat : (5466879957 : ℕ)^4345*39062500000^3321 ≤ 17726947379^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5466879957 10000000000 17726947379 39062500000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5291701417/10000000000 : ℝ), (-1867427751/10000000000 : ℝ), (5466879957/10000000000 : ℝ)] ![(43487904130097/100000000000000 : ℝ), (2226222113229/20000000000000 : ℝ), (17726947379/39062500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5291701417/10000000000 : ℝ)|^4345 ≤ (43487904130097/100000000000000 : ℝ)^3321
        have hw : |(5291701417/10000000000 : ℝ)|=(5291701417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1867427751/10000000000 : ℝ)|^4345 ≤ (2226222113229/20000000000000 : ℝ)^3321
        have hw : |(-1867427751/10000000000 : ℝ)|=(1867427751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5466879957/10000000000 : ℝ)|^4345 ≤ (17726947379/39062500000 : ℝ)^3321
        have hw : |(5466879957/10000000000 : ℝ)|=(5466879957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_s2_6 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (33073143/62500000 : ℝ)*x 0 + (1366720001/2500000000 : ℝ)*x 1 + (-466856417/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33073143/62500000 : ℝ)^4345 ≤ (43487919860447/100000000000000 : ℝ)^3321 := by
    have hnat : (33073143 : ℕ)^4345*100000000000000^3321 ≤ 43487919860447^3321*62500000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33073143 62500000 43487919860447 100000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1366720001/2500000000 : ℝ)^4345 ≤ (4538098580069/10000000000000 : ℝ)^3321 := by
    have hnat : (1366720001 : ℕ)^4345*10000000000000^3321 ≤ 4538098580069^3321*2500000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366720001 2500000000 4538098580069 10000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (466856417/2500000000 : ℝ)^4345 ≤ (1391386790213/12500000000000 : ℝ)^3321 := by
    have hnat : (466856417 : ℕ)^4345*12500000000000^3321 ≤ 1391386790213^3321*2500000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466856417 2500000000 1391386790213 12500000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33073143/62500000 : ℝ), (1366720001/2500000000 : ℝ), (-466856417/2500000000 : ℝ)] ![(43487919860447/100000000000000 : ℝ), (4538098580069/10000000000000 : ℝ), (1391386790213/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33073143/62500000 : ℝ)|^4345 ≤ (43487919860447/100000000000000 : ℝ)^3321
        have hw : |(33073143/62500000 : ℝ)|=(33073143/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1366720001/2500000000 : ℝ)|^4345 ≤ (4538098580069/10000000000000 : ℝ)^3321
        have hw : |(1366720001/2500000000 : ℝ)|=(1366720001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-466856417/2500000000 : ℝ)|^4345 ≤ (1391386790213/12500000000000 : ℝ)^3321
        have hw : |(-466856417/2500000000 : ℝ)|=(466856417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1385_s2_7 (p : ℝ) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4310400083/10000000000 : ℝ)*x 0 + (4608969487/10000000000 : ℝ)*x 1 + (4029856749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4310400083/10000000000 : ℝ)^4345 ≤ (16626254474711/50000000000000 : ℝ)^3321 := by
    have hnat : (4310400083 : ℕ)^4345*50000000000000^3321 ≤ 16626254474711^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310400083 10000000000 16626254474711 50000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4608969487/10000000000 : ℝ)^4345 ≤ (7259540705757/20000000000000 : ℝ)^3321 := by
    have hnat : (4608969487 : ℕ)^4345*20000000000000^3321 ≤ 7259540705757^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4608969487 10000000000 7259540705757 20000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4029856749/10000000000 : ℝ)^4345 ≤ (6089957501763/20000000000000 : ℝ)^3321 := by
    have hnat : (4029856749 : ℕ)^4345*20000000000000^3321 ≤ 6089957501763^3321*10000000000^4345 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4029856749 10000000000 6089957501763 20000000000000 4345 3321 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4345/1024 : ℝ)) 4345 3321 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4310400083/10000000000 : ℝ), (4608969487/10000000000 : ℝ), (4029856749/10000000000 : ℝ)] ![(16626254474711/50000000000000 : ℝ), (7259540705757/20000000000000 : ℝ), (6089957501763/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4310400083/10000000000 : ℝ)|^4345 ≤ (16626254474711/50000000000000 : ℝ)^3321
        have hw : |(4310400083/10000000000 : ℝ)|=(4310400083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4608969487/10000000000 : ℝ)|^4345 ≤ (7259540705757/20000000000000 : ℝ)^3321
        have hw : |(4608969487/10000000000 : ℝ)|=(4608969487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4029856749/10000000000 : ℝ)|^4345 ≤ (6089957501763/20000000000000 : ℝ)^3321
        have hw : |(4029856749/10000000000 : ℝ)|=(4029856749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1385_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78212721/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4787/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3639/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (253/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1993/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4787/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3639/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4787/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3639/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4787/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3639/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4787/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3639/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4787/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3639/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4787/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3639/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3639/50000 : ℝ) ^ (543/128 : ℝ) ≤ (1487447851311589/100000000000000000000 : ℝ) := by
    have hpowers : (3639/50000 : ℝ)^543 ≤ (1487447851311589/100000000000000000000 : ℝ)^128 := by
      have hnat : (3639 : ℕ)^543*100000000000000000000^128 ≤ 1487447851311589^128*50000^543 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3639 50000 1487447851311589 100000000000000000000 543 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3639/50000 : ℝ)) (X := (1487447851311589/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 543 128 (by norm_num) hpowers
    exact h
  have hpowhi : (4787/25000 : ℝ) ^ (543/128 : ℝ) ≤ (90080946494879677/100000000000000000000 : ℝ) := by
    have hpowers : (4787/25000 : ℝ)^543 ≤ (90080946494879677/100000000000000000000 : ℝ)^128 := by
      have hnat : (4787 : ℕ)^543*100000000000000000000^128 ≤ 90080946494879677^128*25000^543 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4787 25000 90080946494879677 100000000000000000000 543 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4787/25000 : ℝ)) (X := (90080946494879677/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 543 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001487447851311589/50000000000000000000 : ℝ) ≤ (5000035062828837/5000000000000000 : ℝ) ^ (543/128 : ℝ) := by
    have hpowers : (50001487447851311589/50000000000000000000 : ℝ)^128 ≤ (5000035062828837/5000000000000000 : ℝ)^543 := by
      have hnat : (50001487447851311589 : ℕ)^128*5000000000000000^543 ≤ 5000035062828837^543*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001487447851311589 50000000000000000000 5000035062828837 5000000000000000 128 543 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000035062828837/5000000000000000 : ℝ)) (X := (50001487447851311589/50000000000000000000 : ℝ)) (by norm_num) 543 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (50045784197173095633/50000000000000000000 : ℝ) ≤ (10002157763426023/10000000000000000 : ℝ) ^ (543/128 : ℝ) := by
    have hpowers : (50045784197173095633/50000000000000000000 : ℝ)^128 ≤ (10002157763426023/10000000000000000 : ℝ)^543 := by
      have hnat : (50045784197173095633 : ℕ)^128*10000000000000000^543 ≤ 10002157763426023^543*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50045784197173095633 50000000000000000000 10002157763426023 10000000000000000 128 543 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002157763426023/10000000000000000 : ℝ)) (X := (50045784197173095633/50000000000000000000 : ℝ)) (by norm_num) 543 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50090080946494879677/50000000000000000000 : ℝ) ≤ (2501061350298593/2500000000000000 : ℝ) ^ (543/128 : ℝ) := by
    have hpowers : (50090080946494879677/50000000000000000000 : ℝ)^128 ≤ (2501061350298593/2500000000000000 : ℝ)^543 := by
      have hnat : (50090080946494879677 : ℕ)^128*2500000000000000^543 ≤ 2501061350298593^543*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50090080946494879677 50000000000000000000 2501061350298593 2500000000000000 128 543 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501061350298593/2500000000000000 : ℝ)) (X := (50090080946494879677/50000000000000000000 : ℝ)) (by norm_num) 543 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1487447851311589/100000000000000000000 : ℝ) ≤ ((1854225699003132849/1854687500000000000 : ℝ)+2*(2087637768349/1187000000000000 : ℝ)*(3639/50000 : ℝ))^(543/128 : ℝ) := by
    rw [show (1854225699003132849/1854687500000000000 : ℝ)+2*(2087637768349/1187000000000000 : ℝ)*(3639/50000 : ℝ)=(5000035062828837/5000000000000000 : ℝ) by norm_num, show 1+2*(1487447851311589/100000000000000000000 : ℝ)=(50001487447851311589/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(90080946494879677/100000000000000000000 : ℝ)+(1487447851311589/100000000000000000000 : ℝ) ≤ ((1854225699003132849/1854687500000000000 : ℝ)+(2087637768349/1187000000000000 : ℝ)*((4787/25000 : ℝ)+(3639/50000 : ℝ)))^(543/128 : ℝ) := by
    rw [show (1854225699003132849/1854687500000000000 : ℝ)+(2087637768349/1187000000000000 : ℝ)*((4787/25000 : ℝ)+(3639/50000 : ℝ))=(10002157763426023/10000000000000000 : ℝ) by norm_num, show 1+(90080946494879677/100000000000000000000 : ℝ)+(1487447851311589/100000000000000000000 : ℝ)=(50045784197173095633/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(90080946494879677/100000000000000000000 : ℝ) ≤ ((1854225699003132849/1854687500000000000 : ℝ)+2*(2087637768349/1187000000000000 : ℝ)*(4787/25000 : ℝ))^(543/128 : ℝ) := by
    rw [show (1854225699003132849/1854687500000000000 : ℝ)+2*(2087637768349/1187000000000000 : ℝ)*(4787/25000 : ℝ)=(2501061350298593/2500000000000000 : ℝ) by norm_num, show 1+2*(90080946494879677/100000000000000000000 : ℝ)=(50090080946494879677/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1854225699003132849/1854687500000000000 : ℝ)*(X 1 0+X 2 0)+(2087637768349/1187000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (543/128 : ℝ)) (lo := (3639/50000 : ℝ)) (hi := (4787/25000 : ℝ)) (c := (1854225699003132849/1854687500000000000 : ℝ)) (alpha := (2087637768349/1187000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1854225699003132849/1854687500000000000 : ℝ)*(X 0 1+X 2 1)+(2087637768349/1187000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (543/128 : ℝ)) (lo := (3639/50000 : ℝ)) (hi := (4787/25000 : ℝ)) (c := (1854225699003132849/1854687500000000000 : ℝ)) (alpha := (2087637768349/1187000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1854225699003132849/1854687500000000000 : ℝ)*(X 0 2+X 1 2)+(2087637768349/1187000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (543/128 : ℝ)) (lo := (3639/50000 : ℝ)) (hi := (4787/25000 : ℝ)) (c := (1854225699003132849/1854687500000000000 : ℝ)) (alpha := (2087637768349/1187000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1999174219/10000000000 : ℝ)*X 0 0+(218741721/400000000 : ℝ)*X 0 1+(259657893/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2681501697/5000000000 : ℝ)*X 1 0+(-2141149589/10000000000 : ℝ)*X 1 1+(5193157789/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((335187703/625000000 : ℝ)*X 2 0+(324572371/625000000 : ℝ)*X 2 1+(-214114959/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2155141407/5000000000 : ℝ)*X 0 0+(80526367/200000000 : ℝ)*X 0 1+(4612478381/10000000000 : ℝ)*X 0 2+(2155141407/5000000000 : ℝ)*X 1 0+(80526367/200000000 : ℝ)*X 1 1+(4612478381/10000000000 : ℝ)*X 1 2+(2155141407/5000000000 : ℝ)*X 2 0+(80526367/200000000 : ℝ)*X 2 1+(4612478381/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-999614301/5000000000 : ℝ)*X 0 0+(64935083/125000000 : ℝ)*X 0 1+(5466880271/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5291701417/10000000000 : ℝ)*X 1 0+(-1867427751/10000000000 : ℝ)*X 1 1+(5466879957/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((33073143/62500000 : ℝ)*X 2 0+(1366720001/2500000000 : ℝ)*X 2 1+(-466856417/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4310400083/10000000000 : ℝ)*X 0 0+(4608969487/10000000000 : ℝ)*X 0 1+(4029856749/10000000000 : ℝ)*X 0 2+(4310400083/10000000000 : ℝ)*X 1 0+(4608969487/10000000000 : ℝ)*X 1 1+(4029856749/10000000000 : ℝ)*X 1 2+(4310400083/10000000000 : ℝ)*X 2 0+(4608969487/10000000000 : ℝ)*X 2 1+(4029856749/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1385_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (443041873536066930318297657/92734375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26830047/3125000000000 : ℝ)*(base19) + (164983637/25000000000000 : ℝ)*(base23) + (53506787/100000000000000 : ℝ)*(lower2) + (39798379/25000000000000 : ℝ)*(upper3) + (14723333/25000000000000 : ℝ)*(upper5) + (2668662428417373/100000000000000 : ℝ)*(major0) + (2668662428417373/100000000000000 : ℝ)*(major1) + (2668662428417373/100000000000000 : ℝ)*(major2) + (1815644000884093/50000000000000 : ℝ)*(sp0) + (1815647731314763/50000000000000 : ℝ)*(sp1) + (1815647830628241/50000000000000 : ℝ)*(sp2) + (170602303852329/10000000000000 : ℝ)*(sp3) + (2079855711/25000000000000 : ℝ)*(sp4) + (5337869197/100000000000000 : ℝ)*(sp7) + (213253547049061/12500000000000 : ℝ)*(f.failure) + (363129632119103/10000000000000 : ℝ)*(f.sum) + (529905441170027/59350000000000000000000000000 : ℝ)*base65 + (2308347603161161979/370937500000000000000000000000000 : ℝ)*base67 + (1698987622103036979/370937500000000000000000000000000 : ℝ)*base69 + (4762899498185536979/370937500000000000000000000000000 : ℝ)*base71 + (16510252733427/59350000000000000000000000000 : ℝ)*base73 + (1560210507506161979/370937500000000000000000000000000 : ℝ)*base75 + (3789395435496786979/370937500000000000000000000000000 : ℝ)*base77 + (4150551445675536979/370937500000000000000000000000000 : ℝ)*base79 + (61906293928127/59350000000000000000000000000 : ℝ)*base81 + (54981/625000000000000000000 : ℝ)*base89 + (54981/625000000000000000000 : ℝ)*base91 + (54981/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (684850965659003410451750859/92734375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (242110951/20000000000000 : ℝ)*(base19) + (42951093/1250000000000 : ℝ)*(base23) + (144317869/50000000000000 : ℝ)*(upper3) + (166309043/50000000000000 : ℝ)*(lower4) + (70102129/100000000000000 : ℝ)*(upper5) + (1350564195825061/50000000000000 : ℝ)*(major0) + (1350564195825061/50000000000000 : ℝ)*(major1) + (1350564195825061/50000000000000 : ℝ)*(major2) + (2643435957/50000000000000 : ℝ)*(sp1) + (24196408721/50000000000000 : ℝ)*(sp2) + (1837736624241307/50000000000000 : ℝ)*(sp4) + (459433343881993/12500000000000 : ℝ)*(sp5) + (918855354894433/25000000000000 : ℝ)*(sp6) + (69071331545929/4000000000000 : ℝ)*(sp7) + (69071331545929/4000000000000 : ℝ)*(f.failure) + (1837736624241307/50000000000000 : ℝ)*(f.sum) + (2940512606141/7418750000000000000000000000 : ℝ)*base65 + (415805979956820547/185468750000000000000000000000000 : ℝ)*base68 + (348436567895570547/185468750000000000000000000000000 : ℝ)*base70 + (1249131427223179453/185468750000000000000000000000000 : ℝ)*base71 + (14544102769043/14837500000000000000000000000 : ℝ)*base74 + (521292398054429453/185468750000000000000000000000000 : ℝ)*base75 + (714791790158695547/185468750000000000000000000000000 : ℝ)*base78 + (116131820294320547/185468750000000000000000000000000 : ℝ)*base80 + (31510288212107/14837500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (437191/200000000000000000000 : ℝ)*base90 + (437191/200000000000000000000 : ℝ)*base92 + (437191/200000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1385_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78212721/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4787/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3639/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (253/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1993/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1385_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1385_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78212721/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (253/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1993/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1385_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1385_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1385_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (543/128 : ℝ) ≤ p) (hpb : p ≤ (4345/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78212721/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (253/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1993/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1385_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
