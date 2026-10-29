-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1675_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:27:49.848353+00:00
-- url     : https://prove2.me/submissions/022cc382-d3b9-4fee-84d4-f4ee917671a7

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
theorem support_rectangle_w1675_s0_0 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1446334251/10000000000 : ℝ)*x 0 + (721710933/1250000000 : ℝ)*x 1 + (614932641/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1446334251/10000000000 : ℝ)^5023 ≤ (1101929240371/12500000000000 : ℝ)^3999 := by
    have hnat : (1446334251 : ℕ)^5023*12500000000000^3999 ≤ 1101929240371^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1446334251 10000000000 1101929240371 12500000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (721710933/1250000000 : ℝ)^5023 ≤ (50161444917521/100000000000000 : ℝ)^3999 := by
    have hnat : (721710933 : ℕ)^5023*100000000000000^3999 ≤ 50161444917521^3999*1250000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      721710933 1250000000 50161444917521 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (614932641/1250000000 : ℝ)^5023 ≤ (41023121148483/100000000000000 : ℝ)^3999 := by
    have hnat : (614932641 : ℕ)^5023*100000000000000^3999 ≤ 41023121148483^3999*1250000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      614932641 1250000000 41023121148483 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1446334251/10000000000 : ℝ), (721710933/1250000000 : ℝ), (614932641/1250000000 : ℝ)] ![(1101929240371/12500000000000 : ℝ), (50161444917521/100000000000000 : ℝ), (41023121148483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1446334251/10000000000 : ℝ)|^5023 ≤ (1101929240371/12500000000000 : ℝ)^3999
        have hw : |(-1446334251/10000000000 : ℝ)|=(1446334251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(721710933/1250000000 : ℝ)|^5023 ≤ (50161444917521/100000000000000 : ℝ)^3999
        have hw : |(721710933/1250000000 : ℝ)|=(721710933/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(614932641/1250000000 : ℝ)|^5023 ≤ (41023121148483/100000000000000 : ℝ)^3999
        have hw : |(614932641/1250000000 : ℝ)|=(614932641/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_s0_1 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2714900659/5000000000 : ℝ)*x 0 + (-1914674571/10000000000 : ℝ)*x 1 + (153733183/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2714900659/5000000000 : ℝ)^5023 ≤ (46437801287547/100000000000000 : ℝ)^3999 := by
    have hnat : (2714900659 : ℕ)^5023*100000000000000^3999 ≤ 46437801287547^3999*5000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714900659 5000000000 46437801287547 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1914674571/10000000000 : ℝ)^5023 ≤ (12539069922407/100000000000000 : ℝ)^3999 := by
    have hnat : (1914674571 : ℕ)^5023*100000000000000^3999 ≤ 12539069922407^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1914674571 10000000000 12539069922407 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (153733183/312500000 : ℝ)^5023 ≤ (41023128773737/100000000000000 : ℝ)^3999 := by
    have hnat : (153733183 : ℕ)^5023*100000000000000^3999 ≤ 41023128773737^3999*312500000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153733183 312500000 41023128773737 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2714900659/5000000000 : ℝ), (-1914674571/10000000000 : ℝ), (153733183/312500000 : ℝ)] ![(46437801287547/100000000000000 : ℝ), (12539069922407/100000000000000 : ℝ), (41023128773737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2714900659/5000000000 : ℝ)|^5023 ≤ (46437801287547/100000000000000 : ℝ)^3999
        have hw : |(2714900659/5000000000 : ℝ)|=(2714900659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1914674571/10000000000 : ℝ)|^5023 ≤ (12539069922407/100000000000000 : ℝ)^3999
        have hw : |(-1914674571/10000000000 : ℝ)|=(1914674571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(153733183/312500000 : ℝ)|^5023 ≤ (41023128773737/100000000000000 : ℝ)^3999
        have hw : |(153733183/312500000 : ℝ)|=(153733183/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_s0_2 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2714901231/5000000000 : ℝ)*x 0 + (2459730513/5000000000 : ℝ)*x 1 + (-957337067/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2714901231/5000000000 : ℝ)^5023 ≤ (46437813576801/100000000000000 : ℝ)^3999 := by
    have hnat : (2714901231 : ℕ)^5023*100000000000000^3999 ≤ 46437813576801^3999*5000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714901231 5000000000 46437813576801 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2459730513/5000000000 : ℝ)^5023 ≤ (41023120080109/100000000000000 : ℝ)^3999 := by
    have hnat : (2459730513 : ℕ)^5023*100000000000000^3999 ≤ 41023120080109^3999*5000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2459730513 5000000000 41023120080109 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (957337067/5000000000 : ℝ)^5023 ≤ (12539066327699/100000000000000 : ℝ)^3999 := by
    have hnat : (957337067 : ℕ)^5023*100000000000000^3999 ≤ 12539066327699^3999*5000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      957337067 5000000000 12539066327699 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2714901231/5000000000 : ℝ), (2459730513/5000000000 : ℝ), (-957337067/5000000000 : ℝ)] ![(46437813576801/100000000000000 : ℝ), (41023120080109/100000000000000 : ℝ), (12539066327699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2714901231/5000000000 : ℝ)|^5023 ≤ (46437813576801/100000000000000 : ℝ)^3999
        have hw : |(2714901231/5000000000 : ℝ)|=(2714901231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2459730513/5000000000 : ℝ)|^5023 ≤ (41023120080109/100000000000000 : ℝ)^3999
        have hw : |(2459730513/5000000000 : ℝ)|=(2459730513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-957337067/5000000000 : ℝ)|^5023 ≤ (12539066327699/100000000000000 : ℝ)^3999
        have hw : |(-957337067/5000000000 : ℝ)|=(957337067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_s0_3 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (162794521/400000000 : ℝ)*x 0 + (3039971827/10000000000 : ℝ)*x 1 + (5319819001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (162794521/400000000 : ℝ)^5023 ≤ (32330113310413/100000000000000 : ℝ)^3999 := by
    have hnat : (162794521 : ℕ)^5023*100000000000000^3999 ≤ 32330113310413^3999*400000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162794521 400000000 32330113310413 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3039971827/10000000000 : ℝ)^5023 ≤ (5602618743859/25000000000000 : ℝ)^3999 := by
    have hnat : (3039971827 : ℕ)^5023*25000000000000^3999 ≤ 5602618743859^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3039971827 10000000000 5602618743859 25000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5319819001/10000000000 : ℝ)^5023 ≤ (45259411702563/100000000000000 : ℝ)^3999 := by
    have hnat : (5319819001 : ℕ)^5023*100000000000000^3999 ≤ 45259411702563^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5319819001 10000000000 45259411702563 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(162794521/400000000 : ℝ), (3039971827/10000000000 : ℝ), (5319819001/10000000000 : ℝ)] ![(32330113310413/100000000000000 : ℝ), (5602618743859/25000000000000 : ℝ), (45259411702563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(162794521/400000000 : ℝ)|^5023 ≤ (32330113310413/100000000000000 : ℝ)^3999
        have hw : |(162794521/400000000 : ℝ)|=(162794521/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3039971827/10000000000 : ℝ)|^5023 ≤ (5602618743859/25000000000000 : ℝ)^3999
        have hw : |(3039971827/10000000000 : ℝ)|=(3039971827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5319819001/10000000000 : ℝ)|^5023 ≤ (45259411702563/100000000000000 : ℝ)^3999
        have hw : |(5319819001/10000000000 : ℝ)|=(5319819001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_s0_4 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1448645663/10000000000 : ℝ)*x 0 + (4941225691/10000000000 : ℝ)*x 1 + (1150230437/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1448645663/10000000000 : ℝ)^5023 ≤ (220828327403/2500000000000 : ℝ)^3999 := by
    have hnat : (1448645663 : ℕ)^5023*2500000000000^3999 ≤ 220828327403^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1448645663 10000000000 220828327403 2500000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4941225691/10000000000 : ℝ)^5023 ≤ (1650048704507/4000000000000 : ℝ)^3999 := by
    have hnat : (4941225691 : ℕ)^5023*4000000000000^3999 ≤ 1650048704507^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4941225691 10000000000 1650048704507 4000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1150230437/2000000000 : ℝ)^5023 ≤ (9983129853939/20000000000000 : ℝ)^3999 := by
    have hnat : (1150230437 : ℕ)^5023*20000000000000^3999 ≤ 9983129853939^3999*2000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1150230437 2000000000 9983129853939 20000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1448645663/10000000000 : ℝ), (4941225691/10000000000 : ℝ), (1150230437/2000000000 : ℝ)] ![(220828327403/2500000000000 : ℝ), (1650048704507/4000000000000 : ℝ), (9983129853939/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1448645663/10000000000 : ℝ)|^5023 ≤ (220828327403/2500000000000 : ℝ)^3999
        have hw : |(-1448645663/10000000000 : ℝ)|=(1448645663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4941225691/10000000000 : ℝ)|^5023 ≤ (1650048704507/4000000000000 : ℝ)^3999
        have hw : |(4941225691/10000000000 : ℝ)|=(4941225691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1150230437/2000000000 : ℝ)|^5023 ≤ (9983129853939/20000000000000 : ℝ)^3999
        have hw : |(1150230437/2000000000 : ℝ)|=(1150230437/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_s0_5 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2598690301/5000000000 : ℝ)*x 0 + (-1082984773/10000000000 : ℝ)*x 1 + (1150230083/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2598690301/5000000000 : ℝ)^5023 ≤ (43954886633163/100000000000000 : ℝ)^3999 := by
    have hnat : (2598690301 : ℕ)^5023*100000000000000^3999 ≤ 43954886633163^3999*5000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598690301 5000000000 43954886633163 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082984773/10000000000 : ℝ)^5023 ≤ (3064741694773/50000000000000 : ℝ)^3999 := by
    have hnat : (1082984773 : ℕ)^5023*50000000000000^3999 ≤ 3064741694773^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082984773 10000000000 3064741694773 50000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1150230083/2000000000 : ℝ)^5023 ≤ (49915629973713/100000000000000 : ℝ)^3999 := by
    have hnat : (1150230083 : ℕ)^5023*100000000000000^3999 ≤ 49915629973713^3999*2000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1150230083 2000000000 49915629973713 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2598690301/5000000000 : ℝ), (-1082984773/10000000000 : ℝ), (1150230083/2000000000 : ℝ)] ![(43954886633163/100000000000000 : ℝ), (3064741694773/50000000000000 : ℝ), (49915629973713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2598690301/5000000000 : ℝ)|^5023 ≤ (43954886633163/100000000000000 : ℝ)^3999
        have hw : |(2598690301/5000000000 : ℝ)|=(2598690301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1082984773/10000000000 : ℝ)|^5023 ≤ (3064741694773/50000000000000 : ℝ)^3999
        have hw : |(-1082984773/10000000000 : ℝ)|=(1082984773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1150230083/2000000000 : ℝ)|^5023 ≤ (49915629973713/100000000000000 : ℝ)^3999
        have hw : |(1150230083/2000000000 : ℝ)|=(1150230083/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_s0_6 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5197380477/10000000000 : ℝ)*x 0 + (5751150081/10000000000 : ℝ)*x 1 + (-1082985471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5197380477/10000000000 : ℝ)^5023 ≤ (43954885305327/100000000000000 : ℝ)^3999 := by
    have hnat : (5197380477 : ℕ)^5023*100000000000000^3999 ≤ 43954885305327^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5197380477 10000000000 43954885305327 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5751150081/10000000000 : ℝ)^5023 ≤ (998312526651/2000000000000 : ℝ)^3999 := by
    have hnat : (5751150081 : ℕ)^5023*2000000000000^3999 ≤ 998312526651^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5751150081 10000000000 998312526651 2000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082985471/10000000000 : ℝ)^5023 ≤ (1532372087921/25000000000000 : ℝ)^3999 := by
    have hnat : (1082985471 : ℕ)^5023*25000000000000^3999 ≤ 1532372087921^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082985471 10000000000 1532372087921 25000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5197380477/10000000000 : ℝ), (5751150081/10000000000 : ℝ), (-1082985471/10000000000 : ℝ)] ![(43954885305327/100000000000000 : ℝ), (998312526651/2000000000000 : ℝ), (1532372087921/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5197380477/10000000000 : ℝ)|^5023 ≤ (43954885305327/100000000000000 : ℝ)^3999
        have hw : |(5197380477/10000000000 : ℝ)|=(5197380477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5751150081/10000000000 : ℝ)|^5023 ≤ (998312526651/2000000000000 : ℝ)^3999
        have hw : |(5751150081/10000000000 : ℝ)|=(5751150081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1082985471/10000000000 : ℝ)|^5023 ≤ (1532372087921/25000000000000 : ℝ)^3999
        have hw : |(-1082985471/10000000000 : ℝ)|=(1082985471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_s0_7 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2038014687/5000000000 : ℝ)*x 0 + (526173067/1000000000 : ℝ)*x 1 + (3100118019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2038014687/5000000000 : ℝ)^5023 ≤ (8097913115889/25000000000000 : ℝ)^3999 := by
    have hnat : (2038014687 : ℕ)^5023*25000000000000^3999 ≤ 8097913115889^3999*5000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2038014687 5000000000 8097913115889 25000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526173067/1000000000 : ℝ)^5023 ≤ (22319768799489/50000000000000 : ℝ)^3999 := by
    have hnat : (526173067 : ℕ)^5023*50000000000000^3999 ≤ 22319768799489^3999*1000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526173067 1000000000 22319768799489 50000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3100118019/10000000000 : ℝ)^5023 ≤ (22968809916591/100000000000000 : ℝ)^3999 := by
    have hnat : (3100118019 : ℕ)^5023*100000000000000^3999 ≤ 22968809916591^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3100118019 10000000000 22968809916591 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2038014687/5000000000 : ℝ), (526173067/1000000000 : ℝ), (3100118019/10000000000 : ℝ)] ![(8097913115889/25000000000000 : ℝ), (22319768799489/50000000000000 : ℝ), (22968809916591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2038014687/5000000000 : ℝ)|^5023 ≤ (8097913115889/25000000000000 : ℝ)^3999
        have hw : |(2038014687/5000000000 : ℝ)|=(2038014687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526173067/1000000000 : ℝ)|^5023 ≤ (22319768799489/50000000000000 : ℝ)^3999
        have hw : |(526173067/1000000000 : ℝ)|=(526173067/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3100118019/10000000000 : ℝ)|^5023 ≤ (22968809916591/100000000000000 : ℝ)^3999
        have hw : |(3100118019/10000000000 : ℝ)|=(3100118019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1675_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183445147/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1229/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (11613/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (5015/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5015 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5015*1^1024 ≤ 0^1024*1^5015 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5015 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5015 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5015/1024 : ℝ) ≤ (1124875225952713671/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5015 ≤ (1124875225952713671/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5015*100000000000000000000^1024 ≤ 1124875225952713671^1024*5^5015 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1124875225952713671 100000000000000000000 5015 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1124875225952713671/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5015 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5015/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5015 := by
      have hnat : (1 : ℕ)^1024*1^5015 ≤ 1^5015*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5015 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5015 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101124875225952713671/100000000000000000000 : ℝ) ≤ (10022866419849957/10000000000000000 : ℝ) ^ (5015/1024 : ℝ) := by
    have hpowers : (101124875225952713671/100000000000000000000 : ℝ)^1024 ≤ (10022866419849957/10000000000000000 : ℝ)^5015 := by
      have hnat : (101124875225952713671 : ℕ)^1024*10000000000000000^5015 ≤ 10022866419849957^5015*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101124875225952713671 100000000000000000000 10022866419849957 10000000000000000 1024 5015 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10022866419849957/10000000000000000 : ℝ)) (X := (101124875225952713671/100000000000000000000 : ℝ)) (by norm_num) 5015 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51124875225952713671/50000000000000000000 : ℝ) ≤ (5022866419849957/5000000000000000 : ℝ) ^ (5015/1024 : ℝ) := by
    have hpowers : (51124875225952713671/50000000000000000000 : ℝ)^1024 ≤ (5022866419849957/5000000000000000 : ℝ)^5015 := by
      have hnat : (51124875225952713671 : ℕ)^1024*5000000000000000^5015 ≤ 5022866419849957^5015*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51124875225952713671 50000000000000000000 5022866419849957 5000000000000000 1024 5015 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5022866419849957/5000000000000000 : ℝ)) (X := (51124875225952713671/50000000000000000000 : ℝ)) (by norm_num) 5015 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(22866419849957/4000000000000000 : ℝ)*(0 : ℝ))^(5015/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(22866419849957/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1124875225952713671/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(22866419849957/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5015/1024 : ℝ) := by
    rw [show (1 : ℝ)+(22866419849957/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10022866419849957/10000000000000000 : ℝ) by norm_num, show 1+(1124875225952713671/100000000000000000000 : ℝ)+(0 : ℝ)=(101124875225952713671/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1124875225952713671/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(22866419849957/4000000000000000 : ℝ)*(2/5 : ℝ))^(5015/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(22866419849957/4000000000000000 : ℝ)*(2/5 : ℝ)=(5022866419849957/5000000000000000 : ℝ) by norm_num, show 1+2*(1124875225952713671/100000000000000000000 : ℝ)=(51124875225952713671/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(22866419849957/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5015/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (22866419849957/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(22866419849957/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5015/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (22866419849957/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(22866419849957/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5015/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (22866419849957/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1446334251/10000000000 : ℝ)*X 0 0+(721710933/1250000000 : ℝ)*X 0 1+(614932641/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2714900659/5000000000 : ℝ)*X 1 0+(-1914674571/10000000000 : ℝ)*X 1 1+(153733183/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2714901231/5000000000 : ℝ)*X 2 0+(2459730513/5000000000 : ℝ)*X 2 1+(-957337067/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((162794521/400000000 : ℝ)*X 0 0+(3039971827/10000000000 : ℝ)*X 0 1+(5319819001/10000000000 : ℝ)*X 0 2+(162794521/400000000 : ℝ)*X 1 0+(3039971827/10000000000 : ℝ)*X 1 1+(5319819001/10000000000 : ℝ)*X 1 2+(162794521/400000000 : ℝ)*X 2 0+(3039971827/10000000000 : ℝ)*X 2 1+(5319819001/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1448645663/10000000000 : ℝ)*X 0 0+(4941225691/10000000000 : ℝ)*X 0 1+(1150230437/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2598690301/5000000000 : ℝ)*X 1 0+(-1082984773/10000000000 : ℝ)*X 1 1+(1150230083/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5197380477/10000000000 : ℝ)*X 2 0+(5751150081/10000000000 : ℝ)*X 2 1+(-1082985471/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2038014687/5000000000 : ℝ)*X 0 0+(526173067/1000000000 : ℝ)*X 0 1+(3100118019/10000000000 : ℝ)*X 0 2+(2038014687/5000000000 : ℝ)*X 1 0+(526173067/1000000000 : ℝ)*X 1 1+(3100118019/10000000000 : ℝ)*X 1 2+(2038014687/5000000000 : ℝ)*X 2 0+(526173067/1000000000 : ℝ)*X 2 1+(3100118019/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (576299631993181792247781/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (780129/800000000000 : ℝ)*(base1) + (1063833501/100000000000000 : ℝ)*(base19) + (655239323/50000000000000 : ℝ)*(base23) + (15124127/50000000000000 : ℝ)*(upper3) + (241125951/100000000000000 : ℝ)*(upper5) + (804645319475211/100000000000000 : ℝ)*(major0) + (804645319475211/100000000000000 : ℝ)*(major1) + (804645319475211/100000000000000 : ℝ)*(major2) + (585327015878739/50000000000000 : ℝ)*(sp0) + (146332431654337/12500000000000 : ℝ)*(sp1) + (1170659206589551/100000000000000 : ℝ)*(sp2) + (8772561257993/2000000000000 : ℝ)*(sp3) + (6582826843/100000000000000 : ℝ)*(sp4) + (884683283/50000000000000 : ℝ)*(sp7) + (21931496489117/5000000000000 : ℝ)*(f.failure) + (1170660517068197/100000000000000 : ℝ)*(f.sum) + (575603408484073/200000000000000000000000000000 : ℝ)*base66 + (806316970915927/400000000000000000000000000000 : ℝ)*base67 + (1820876783715927/400000000000000000000000000000 : ℝ)*base69 + (208987503884073/400000000000000000000000000000 : ℝ)*base72 + (1162720269884073/200000000000000000000000000000 : ℝ)*base74 + (1561941328915927/400000000000000000000000000000 : ℝ)*base75 + (215354402515927/400000000000000000000000000000 : ℝ)*base77 + (741867037484073/400000000000000000000000000000 : ℝ)*base80 + (852281113084073/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (3034801/500000000000000000000 : ℝ)*base90 + (3034801/500000000000000000000 : ℝ)*base92 + (3034801/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (91236853200988663833021/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (308602129/50000000000000 : ℝ)*(base19) + (706969923/100000000000000 : ℝ)*(base23) + (82816781/100000000000000 : ℝ)*(upper2) + (3715187/6250000000000 : ℝ)*(upper5) + (848648964372349/100000000000000 : ℝ)*(major0) + (848648964372349/100000000000000 : ℝ)*(major1) + (848648964372349/100000000000000 : ℝ)*(major2) + (189130877/50000000000000 : ℝ)*(sp0) + (903728133/100000000000000 : ℝ)*(sp1) + (5934541/50000000000000 : ℝ)*(sp2) + (617340100732881/50000000000000 : ℝ)*(sp4) + (9877432470361/800000000000 : ℝ)*(sp5) + (1234679860888511/100000000000000 : ℝ)*(sp6) + (462617288192611/100000000000000 : ℝ)*(sp7) + (462617288192611/100000000000000 : ℝ)*(f.failure) + (308670144931879/25000000000000 : ℝ)*(f.sum) + (774473448838993/200000000000000000000000000000 : ℝ)*base65 + (372930152438993/400000000000000000000000000000 : ℝ)*base67 + (125879176761007/400000000000000000000000000000 : ℝ)*base70 + (127940763561007/400000000000000000000000000000 : ℝ)*base72 + (789650899238993/200000000000000000000000000000 : ℝ)*base73 + (398027526838993/400000000000000000000000000000 : ℝ)*base75 + (1565645201638993/400000000000000000000000000000 : ℝ)*base77 + (832420502438993/400000000000000000000000000000 : ℝ)*base79 + (44017471638993/200000000000000000000000000000 : ℝ)*base81 + (10791183/10000000000000000000000 : ℝ)*base90 + (10791183/10000000000000000000000 : ℝ)*base92 + (10791183/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1675_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183445147/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1229/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (11613/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1675_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1675_s1_0 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1541592461/10000000000 : ℝ)*x 0 + (5523949221/10000000000 : ℝ)*x 1 + (2553541943/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1541592461/10000000000 : ℝ)^5023 ≤ (1910151449709/20000000000000 : ℝ)^3999 := by
    have hnat : (1541592461 : ℕ)^5023*20000000000000^3999 ≤ 1910151449709^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1541592461 10000000000 1910151449709 20000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5523949221/10000000000 : ℝ)^5023 ≤ (47451407067117/100000000000000 : ℝ)^3999 := by
    have hnat : (5523949221 : ℕ)^5023*100000000000000^3999 ≤ 47451407067117^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5523949221 10000000000 47451407067117 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2553541943/5000000000 : ℝ)^5023 ≤ (2149891783523/5000000000000 : ℝ)^3999 := by
    have hnat : (2553541943 : ℕ)^5023*5000000000000^3999 ≤ 2149891783523^3999*5000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2553541943 5000000000 2149891783523 5000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1541592461/10000000000 : ℝ), (5523949221/10000000000 : ℝ), (2553541943/5000000000 : ℝ)] ![(1910151449709/20000000000000 : ℝ), (47451407067117/100000000000000 : ℝ), (2149891783523/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1541592461/10000000000 : ℝ)|^5023 ≤ (1910151449709/20000000000000 : ℝ)^3999
        have hw : |(-1541592461/10000000000 : ℝ)|=(1541592461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5523949221/10000000000 : ℝ)|^5023 ≤ (47451407067117/100000000000000 : ℝ)^3999
        have hw : |(5523949221/10000000000 : ℝ)|=(5523949221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2553541943/5000000000 : ℝ)|^5023 ≤ (2149891783523/5000000000000 : ℝ)^3999
        have hw : |(2553541943/5000000000 : ℝ)|=(2553541943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_s1_1 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5363255501/10000000000 : ℝ)*x 0 + (-219967821/1250000000 : ℝ)*x 1 + (5107083877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363255501/10000000000 : ℝ)^5023 ≤ (22862033824261/50000000000000 : ℝ)^3999 := by
    have hnat : (5363255501 : ℕ)^5023*50000000000000^3999 ≤ 22862033824261^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363255501 10000000000 22862033824261 50000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (219967821/1250000000 : ℝ)^5023 ≤ (2255619351251/20000000000000 : ℝ)^3999 := by
    have hnat : (219967821 : ℕ)^5023*20000000000000^3999 ≤ 2255619351251^3999*1250000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219967821 1250000000 2255619351251 20000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5107083877/10000000000 : ℝ)^5023 ≤ (10749458893821/25000000000000 : ℝ)^3999 := by
    have hnat : (5107083877 : ℕ)^5023*25000000000000^3999 ≤ 10749458893821^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5107083877 10000000000 10749458893821 25000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363255501/10000000000 : ℝ), (-219967821/1250000000 : ℝ), (5107083877/10000000000 : ℝ)] ![(22862033824261/50000000000000 : ℝ), (2255619351251/20000000000000 : ℝ), (10749458893821/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363255501/10000000000 : ℝ)|^5023 ≤ (22862033824261/50000000000000 : ℝ)^3999
        have hw : |(5363255501/10000000000 : ℝ)|=(5363255501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-219967821/1250000000 : ℝ)|^5023 ≤ (2255619351251/20000000000000 : ℝ)^3999
        have hw : |(-219967821/1250000000 : ℝ)|=(219967821/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5107083877/10000000000 : ℝ)|^5023 ≤ (10749458893821/25000000000000 : ℝ)^3999
        have hw : |(5107083877/10000000000 : ℝ)|=(5107083877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_s1_2 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (83800861/156250000 : ℝ)*x 0 + (1276771067/2500000000 : ℝ)*x 1 + (-219967823/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83800861/156250000 : ℝ)^5023 ≤ (45724063397253/100000000000000 : ℝ)^3999 := by
    have hnat : (83800861 : ℕ)^5023*100000000000000^3999 ≤ 45724063397253^3999*156250000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83800861 156250000 45724063397253 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1276771067/2500000000 : ℝ)^5023 ≤ (42997839710157/100000000000000 : ℝ)^3999 := by
    have hnat : (1276771067 : ℕ)^5023*100000000000000^3999 ≤ 42997839710157^3999*2500000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1276771067 2500000000 42997839710157 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219967823/1250000000 : ℝ)^5023 ≤ (176220263829/1562500000000 : ℝ)^3999 := by
    have hnat : (219967823 : ℕ)^5023*1562500000000^3999 ≤ 176220263829^3999*1250000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219967823 1250000000 176220263829 1562500000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83800861/156250000 : ℝ), (1276771067/2500000000 : ℝ), (-219967823/1250000000 : ℝ)] ![(45724063397253/100000000000000 : ℝ), (42997839710157/100000000000000 : ℝ), (176220263829/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83800861/156250000 : ℝ)|^5023 ≤ (45724063397253/100000000000000 : ℝ)^3999
        have hw : |(83800861/156250000 : ℝ)|=(83800861/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1276771067/2500000000 : ℝ)|^5023 ≤ (42997839710157/100000000000000 : ℝ)^3999
        have hw : |(1276771067/2500000000 : ℝ)|=(1276771067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-219967823/1250000000 : ℝ)|^5023 ≤ (176220263829/1562500000000 : ℝ)^3999
        have hw : |(-219967823/1250000000 : ℝ)|=(219967823/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_s1_3 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4146452959/10000000000 : ℝ)*x 0 + (18080513/50000000 : ℝ)*x 1 + (2364337623/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4146452959/10000000000 : ℝ)^5023 ≤ (16548076441729/50000000000000 : ℝ)^3999 := by
    have hnat : (4146452959 : ℕ)^5023*50000000000000^3999 ≤ 16548076441729^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4146452959 10000000000 16548076441729 50000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (18080513/50000000 : ℝ)^5023 ≤ (13934522766299/50000000000000 : ℝ)^3999 := by
    have hnat : (18080513 : ℕ)^5023*50000000000000^3999 ≤ 13934522766299^3999*50000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18080513 50000000 13934522766299 50000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2364337623/5000000000 : ℝ)^5023 ≤ (39034801567731/100000000000000 : ℝ)^3999 := by
    have hnat : (2364337623 : ℕ)^5023*100000000000000^3999 ≤ 39034801567731^3999*5000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2364337623 5000000000 39034801567731 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4146452959/10000000000 : ℝ), (18080513/50000000 : ℝ), (2364337623/5000000000 : ℝ)] ![(16548076441729/50000000000000 : ℝ), (13934522766299/50000000000000 : ℝ), (39034801567731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4146452959/10000000000 : ℝ)|^5023 ≤ (16548076441729/50000000000000 : ℝ)^3999
        have hw : |(4146452959/10000000000 : ℝ)|=(4146452959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(18080513/50000000 : ℝ)|^5023 ≤ (13934522766299/50000000000000 : ℝ)^3999
        have hw : |(18080513/50000000 : ℝ)|=(18080513/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2364337623/5000000000 : ℝ)|^5023 ≤ (39034801567731/100000000000000 : ℝ)^3999
        have hw : |(2364337623/5000000000 : ℝ)|=(2364337623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_s1_4 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1541857549/10000000000 : ℝ)*x 0 + (5112242957/10000000000 : ℝ)*x 1 + (21557423/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1541857549/10000000000 : ℝ)^5023 ≤ (1194102519433/12500000000000 : ℝ)^3999 := by
    have hnat : (1541857549 : ℕ)^5023*12500000000000^3999 ≤ 1194102519433^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1541857549 10000000000 1194102519433 12500000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5112242957/10000000000 : ℝ)^5023 ≤ (21526200264579/50000000000000 : ℝ)^3999 := by
    have hnat : (5112242957 : ℕ)^5023*50000000000000^3999 ≤ 21526200264579^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5112242957 10000000000 21526200264579 50000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21557423/39062500 : ℝ)^5023 ≤ (11848694827207/25000000000000 : ℝ)^3999 := by
    have hnat : (21557423 : ℕ)^5023*25000000000000^3999 ≤ 11848694827207^3999*39062500^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21557423 39062500 11848694827207 25000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1541857549/10000000000 : ℝ), (5112242957/10000000000 : ℝ), (21557423/39062500 : ℝ)] ![(1194102519433/12500000000000 : ℝ), (21526200264579/50000000000000 : ℝ), (11848694827207/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1541857549/10000000000 : ℝ)|^5023 ≤ (1194102519433/12500000000000 : ℝ)^3999
        have hw : |(-1541857549/10000000000 : ℝ)|=(1541857549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5112242957/10000000000 : ℝ)|^5023 ≤ (21526200264579/50000000000000 : ℝ)^3999
        have hw : |(5112242957/10000000000 : ℝ)|=(5112242957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21557423/39062500 : ℝ)|^5023 ≤ (11848694827207/25000000000000 : ℝ)^3999
        have hw : |(21557423/39062500 : ℝ)|=(21557423/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_s1_5 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251915013/10000000000 : ℝ)*x 0 + (-1348128373/10000000000 : ℝ)*x 1 + (2759350629/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251915013/10000000000 : ℝ)^5023 ≤ (44534964872071/100000000000000 : ℝ)^3999 := by
    have hnat : (5251915013 : ℕ)^5023*100000000000000^3999 ≤ 44534964872071^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251915013 10000000000 44534964872071 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348128373/10000000000 : ℝ)^5023 ≤ (504390333699/6250000000000 : ℝ)^3999 := by
    have hnat : (1348128373 : ℕ)^5023*6250000000000^3999 ≤ 504390333699^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348128373 10000000000 504390333699 6250000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2759350629/5000000000 : ℝ)^5023 ≤ (23697394886167/50000000000000 : ℝ)^3999 := by
    have hnat : (2759350629 : ℕ)^5023*50000000000000^3999 ≤ 23697394886167^3999*5000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2759350629 5000000000 23697394886167 50000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251915013/10000000000 : ℝ), (-1348128373/10000000000 : ℝ), (2759350629/5000000000 : ℝ)] ![(44534964872071/100000000000000 : ℝ), (504390333699/6250000000000 : ℝ), (23697394886167/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251915013/10000000000 : ℝ)|^5023 ≤ (44534964872071/100000000000000 : ℝ)^3999
        have hw : |(5251915013/10000000000 : ℝ)|=(5251915013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1348128373/10000000000 : ℝ)|^5023 ≤ (504390333699/6250000000000 : ℝ)^3999
        have hw : |(-1348128373/10000000000 : ℝ)|=(1348128373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2759350629/5000000000 : ℝ)|^5023 ≤ (23697394886167/50000000000000 : ℝ)^3999
        have hw : |(2759350629/5000000000 : ℝ)|=(2759350629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_s1_6 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251916737/10000000000 : ℝ)*x 0 + (5518700767/10000000000 : ℝ)*x 1 + (-337031659/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251916737/10000000000 : ℝ)^5023 ≤ (222674916173/500000000000 : ℝ)^3999 := by
    have hnat : (5251916737 : ℕ)^5023*500000000000^3999 ≤ 222674916173^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251916737 10000000000 222674916173 500000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5518700767/10000000000 : ℝ)^5023 ≤ (23697392237929/50000000000000 : ℝ)^3999 := by
    have hnat : (5518700767 : ℕ)^5023*50000000000000^3999 ≤ 23697392237929^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5518700767 10000000000 23697392237929 50000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337031659/2500000000 : ℝ)^5023 ≤ (8070232278467/100000000000000 : ℝ)^3999 := by
    have hnat : (337031659 : ℕ)^5023*100000000000000^3999 ≤ 8070232278467^3999*2500000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337031659 2500000000 8070232278467 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251916737/10000000000 : ℝ), (5518700767/10000000000 : ℝ), (-337031659/2500000000 : ℝ)] ![(222674916173/500000000000 : ℝ), (23697392237929/50000000000000 : ℝ), (8070232278467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251916737/10000000000 : ℝ)|^5023 ≤ (222674916173/500000000000 : ℝ)^3999
        have hw : |(5251916737/10000000000 : ℝ)|=(5251916737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5518700767/10000000000 : ℝ)|^5023 ≤ (23697392237929/50000000000000 : ℝ)^3999
        have hw : |(5518700767/10000000000 : ℝ)|=(5518700767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-337031659/2500000000 : ℝ)|^5023 ≤ (8070232278467/100000000000000 : ℝ)^3999
        have hw : |(-337031659/2500000000 : ℝ)|=(337031659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_s1_7 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4147158549/10000000000 : ℝ)*x 0 + (4714903203/10000000000 : ℝ)*x 1 + (3630110657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4147158549/10000000000 : ℝ)^5023 ≤ (4137903379507/12500000000000 : ℝ)^3999 := by
    have hnat : (4147158549 : ℕ)^5023*12500000000000^3999 ≤ 4137903379507^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4147158549 10000000000 4137903379507 12500000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4714903203/10000000000 : ℝ)^5023 ≤ (972301417183/2500000000000 : ℝ)^3999 := by
    have hnat : (4714903203 : ℕ)^5023*2500000000000^3999 ≤ 972301417183^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4714903203 10000000000 972301417183 2500000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3630110657/10000000000 : ℝ)^5023 ≤ (28004716262809/100000000000000 : ℝ)^3999 := by
    have hnat : (3630110657 : ℕ)^5023*100000000000000^3999 ≤ 28004716262809^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3630110657 10000000000 28004716262809 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4147158549/10000000000 : ℝ), (4714903203/10000000000 : ℝ), (3630110657/10000000000 : ℝ)] ![(4137903379507/12500000000000 : ℝ), (972301417183/2500000000000 : ℝ), (28004716262809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4147158549/10000000000 : ℝ)|^5023 ≤ (4137903379507/12500000000000 : ℝ)^3999
        have hw : |(4147158549/10000000000 : ℝ)|=(4147158549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4714903203/10000000000 : ℝ)|^5023 ≤ (972301417183/2500000000000 : ℝ)^3999
        have hw : |(4714903203/10000000000 : ℝ)|=(4714903203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3630110657/10000000000 : ℝ)|^5023 ≤ (28004716262809/100000000000000 : ℝ)^3999
        have hw : |(3630110657/10000000000 : ℝ)|=(3630110657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1675_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183445147/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (11613/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1229/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (57/625 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8987/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (11613/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1229/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (11613/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1229/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (11613/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1229/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (11613/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1229/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (11613/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1229/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (11613/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1229/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1229/25000 : ℝ) ^ (5015/1024 : ℝ) ≤ (19551958520727/50000000000000000000 : ℝ) := by
    have hpowers : (1229/25000 : ℝ)^5015 ≤ (19551958520727/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1229 : ℕ)^5015*50000000000000000000^1024 ≤ 19551958520727^1024*25000^5015 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1229 25000 19551958520727 50000000000000000000 5015 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1229/25000 : ℝ)) (X := (19551958520727/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5015 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (11613/50000 : ℝ) ^ (5015/1024 : ℝ) ≤ (78502682449562499/100000000000000000000 : ℝ) := by
    have hpowers : (11613/50000 : ℝ)^5015 ≤ (78502682449562499/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11613 : ℕ)^5015*100000000000000000000^1024 ≤ 78502682449562499^1024*50000^5015 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11613 50000 78502682449562499 100000000000000000000 5015 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11613/50000 : ℝ)) (X := (78502682449562499/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5015 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000019551958520727/25000000000000000000 : ℝ) ≤ (2500000399226307/2500000000000000 : ℝ) ^ (5015/1024 : ℝ) := by
    have hpowers : (25000019551958520727/25000000000000000000 : ℝ)^1024 ≤ (2500000399226307/2500000000000000 : ℝ)^5015 := by
      have hnat : (25000019551958520727 : ℕ)^1024*2500000000000000^5015 ≤ 2500000399226307^5015*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000019551958520727 25000000000000000000 2500000399226307 2500000000000000 1024 5015 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000399226307/2500000000000000 : ℝ)) (X := (25000019551958520727/25000000000000000000 : ℝ)) (by norm_num) 5015 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100078541786366603953/100000000000000000000 : ℝ) ≤ (250040080591153/250000000000000 : ℝ) ^ (5015/1024 : ℝ) := by
    have hpowers : (100078541786366603953/100000000000000000000 : ℝ)^1024 ≤ (250040080591153/250000000000000 : ℝ)^5015 := by
      have hnat : (100078541786366603953 : ℕ)^1024*250000000000000^5015 ≤ 250040080591153^5015*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100078541786366603953 100000000000000000000 250040080591153 250000000000000 1024 5015 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250040080591153/250000000000000 : ℝ)) (X := (100078541786366603953/100000000000000000000 : ℝ)) (by norm_num) 5015 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50078502682449562499/50000000000000000000 : ℝ) ≤ (2500801212596753/2500000000000000 : ℝ) ^ (5015/1024 : ℝ) := by
    have hpowers : (50078502682449562499/50000000000000000000 : ℝ)^1024 ≤ (2500801212596753/2500000000000000 : ℝ)^5015 := by
      have hnat : (50078502682449562499 : ℕ)^1024*2500000000000000^5015 ≤ 2500801212596753^5015*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50078502682449562499 50000000000000000000 2500801212596753 2500000000000000 1024 5015 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500801212596753/2500000000000000 : ℝ)) (X := (50078502682449562499/50000000000000000000 : ℝ)) (by norm_num) 5015 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(19551958520727/50000000000000000000 : ℝ) ≤ ((22885535255652284317/22887500000000000000 : ℝ)+2*(400406685223/457750000000000 : ℝ)*(1229/25000 : ℝ))^(5015/1024 : ℝ) := by
    rw [show (22885535255652284317/22887500000000000000 : ℝ)+2*(400406685223/457750000000000 : ℝ)*(1229/25000 : ℝ)=(2500000399226307/2500000000000000 : ℝ) by norm_num, show 1+2*(19551958520727/50000000000000000000 : ℝ)=(25000019551958520727/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(78502682449562499/100000000000000000000 : ℝ)+(19551958520727/50000000000000000000 : ℝ) ≤ ((22885535255652284317/22887500000000000000 : ℝ)+(400406685223/457750000000000 : ℝ)*((11613/50000 : ℝ)+(1229/25000 : ℝ)))^(5015/1024 : ℝ) := by
    rw [show (22885535255652284317/22887500000000000000 : ℝ)+(400406685223/457750000000000 : ℝ)*((11613/50000 : ℝ)+(1229/25000 : ℝ))=(250040080591153/250000000000000 : ℝ) by norm_num, show 1+(78502682449562499/100000000000000000000 : ℝ)+(19551958520727/50000000000000000000 : ℝ)=(100078541786366603953/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(78502682449562499/100000000000000000000 : ℝ) ≤ ((22885535255652284317/22887500000000000000 : ℝ)+2*(400406685223/457750000000000 : ℝ)*(11613/50000 : ℝ))^(5015/1024 : ℝ) := by
    rw [show (22885535255652284317/22887500000000000000 : ℝ)+2*(400406685223/457750000000000 : ℝ)*(11613/50000 : ℝ)=(2500801212596753/2500000000000000 : ℝ) by norm_num, show 1+2*(78502682449562499/100000000000000000000 : ℝ)=(50078502682449562499/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22885535255652284317/22887500000000000000 : ℝ)*(X 1 0+X 2 0)+(400406685223/457750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5015/1024 : ℝ)) (lo := (1229/25000 : ℝ)) (hi := (11613/50000 : ℝ)) (c := (22885535255652284317/22887500000000000000 : ℝ)) (alpha := (400406685223/457750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22885535255652284317/22887500000000000000 : ℝ)*(X 0 1+X 2 1)+(400406685223/457750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5015/1024 : ℝ)) (lo := (1229/25000 : ℝ)) (hi := (11613/50000 : ℝ)) (c := (22885535255652284317/22887500000000000000 : ℝ)) (alpha := (400406685223/457750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22885535255652284317/22887500000000000000 : ℝ)*(X 0 2+X 1 2)+(400406685223/457750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5015/1024 : ℝ)) (lo := (1229/25000 : ℝ)) (hi := (11613/50000 : ℝ)) (c := (22885535255652284317/22887500000000000000 : ℝ)) (alpha := (400406685223/457750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1541592461/10000000000 : ℝ)*X 0 0+(5523949221/10000000000 : ℝ)*X 0 1+(2553541943/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5363255501/10000000000 : ℝ)*X 1 0+(-219967821/1250000000 : ℝ)*X 1 1+(5107083877/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((83800861/156250000 : ℝ)*X 2 0+(1276771067/2500000000 : ℝ)*X 2 1+(-219967823/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4146452959/10000000000 : ℝ)*X 0 0+(18080513/50000000 : ℝ)*X 0 1+(2364337623/5000000000 : ℝ)*X 0 2+(4146452959/10000000000 : ℝ)*X 1 0+(18080513/50000000 : ℝ)*X 1 1+(2364337623/5000000000 : ℝ)*X 1 2+(4146452959/10000000000 : ℝ)*X 2 0+(18080513/50000000 : ℝ)*X 2 1+(2364337623/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1541857549/10000000000 : ℝ)*X 0 0+(5112242957/10000000000 : ℝ)*X 0 1+(21557423/39062500 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5251915013/10000000000 : ℝ)*X 1 0+(-1348128373/10000000000 : ℝ)*X 1 1+(2759350629/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5251916737/10000000000 : ℝ)*X 2 0+(5518700767/10000000000 : ℝ)*X 2 1+(-337031659/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4147158549/10000000000 : ℝ)*X 0 0+(4714903203/10000000000 : ℝ)*X 0 1+(3630110657/10000000000 : ℝ)*X 0 2+(4147158549/10000000000 : ℝ)*X 1 0+(4714903203/10000000000 : ℝ)*X 1 1+(3630110657/10000000000 : ℝ)*X 1 2+(4147158549/10000000000 : ℝ)*X 2 0+(4714903203/10000000000 : ℝ)*X 2 1+(3630110657/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4882744040011871953978707891/572187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1278754739/100000000000000 : ℝ)*(base19) + (270216443/25000000000000 : ℝ)*(base23) + (95642513/50000000000000 : ℝ)*(upper3) + (10897491/100000000000000 : ℝ)*(upper4) + (140278387/100000000000000 : ℝ)*(upper5) + (1648852015105559/100000000000000 : ℝ)*(major0) + (1648852015105559/100000000000000 : ℝ)*(major1) + (1648852015105559/100000000000000 : ℝ)*(major2) + (2398867605523271/100000000000000 : ℝ)*(sp0) + (599719206951661/25000000000000 : ℝ)*(sp1) + (2398877025695611/100000000000000 : ℝ)*(sp2) + (449410784629371/50000000000000 : ℝ)*(sp3) + (328157441/3125000000000 : ℝ)*(sp4) + (4069942037/100000000000000 : ℝ)*(sp7) + (898825639200779/100000000000000 : ℝ)*(f.failure) + (2398878106561383/100000000000000 : ℝ)*(f.sum) + (101192414726757/22887500000000000000000000000 : ℝ)*base65 + (3643999307010568203/2288750000000000000000000000000000 : ℝ)*base67 + (1085626736351818203/2288750000000000000000000000000000 : ℝ)*base69 + (1873610558986818203/2288750000000000000000000000000000 : ℝ)*base71 + (168027146817089/45775000000000000000000000000 : ℝ)*base73 + (19554943360094318203/2288750000000000000000000000000000 : ℝ)*base75 + (1900080212138181797/2288750000000000000000000000000000 : ℝ)*base78 + (5254481281681818203/2288750000000000000000000000000000 : ℝ)*base79 + (64388004618861/45775000000000000000000000000 : ℝ)*base82 + (33830487/10000000000000000000000 : ℝ)*base90 + (33830487/10000000000000000000000 : ℝ)*base92 + (33830487/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (764510875290252882800990739/71523437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (216831861/50000000000000 : ℝ)*(base19) + (904883573/50000000000000 : ℝ)*(base23) + (176752767/100000000000000 : ℝ)*(upper2) + (360278831/100000000000000 : ℝ)*(upper3) + (577816321/100000000000000 : ℝ)*(upper5) + (105691317874407/6250000000000 : ℝ)*(major0) + (105691317874407/6250000000000 : ℝ)*(major1) + (105691317874407/6250000000000 : ℝ)*(major2) + (883182879/50000000000000 : ℝ)*(sp1) + (12707091249/100000000000000 : ℝ)*(sp2) + (246028707998871/10000000000000 : ℝ)*(sp4) + (246028487995923/10000000000000 : ℝ)*(sp5) + (492054512626063/20000000000000 : ℝ)*(sp6) + (460917367846889/50000000000000 : ℝ)*(sp7) + (460917367846889/50000000000000 : ℝ)*(f.failure) + (246028707998871/10000000000000 : ℝ)*(f.sum) + (57503300847237/11443750000000000000000000000 : ℝ)*base66 + (870022044215137519/143046875000000000000000000000000 : ℝ)*base67 + (48904532385018731/143046875000000000000000000000000 : ℝ)*base70 + (127540581507206231/143046875000000000000000000000000 : ℝ)*base72 + (6416280482397/2860937500000000000000000000 : ℝ)*base73 + (369708123963612481/143046875000000000000000000000000 : ℝ)*base76 + (297133829493852339/35761718750000000000000000000000 : ℝ)*base78 + (50118640918876553/71523437500000000000000000000000 : ℝ)*base80 + (10782375246949/22887500000000000000000000000 : ℝ)*base82 + (26097683/5000000000000000000000 : ℝ)*base89 + (26097683/5000000000000000000000 : ℝ)*base91 + (26097683/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1675_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183445147/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (11613/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1229/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (57/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8987/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1675_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1675_s2_0 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1548863583/10000000000 : ℝ)*x 0 + (2747719919/5000000000 : ℝ)*x 1 + (5130784811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1548863583/10000000000 : ℝ)^5023 ≤ (1921474757351/20000000000000 : ℝ)^3999 := by
    have hnat : (1548863583 : ℕ)^5023*20000000000000^3999 ≤ 1921474757351^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1548863583 10000000000 1921474757351 20000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2747719919/5000000000 : ℝ)^5023 ≤ (11786000402379/25000000000000 : ℝ)^3999 := by
    have hnat : (2747719919 : ℕ)^5023*25000000000000^3999 ≤ 11786000402379^3999*5000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2747719919 5000000000 11786000402379 25000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5130784811/10000000000 : ℝ)^5023 ≤ (8649724918211/20000000000000 : ℝ)^3999 := by
    have hnat : (5130784811 : ℕ)^5023*20000000000000^3999 ≤ 8649724918211^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5130784811 10000000000 8649724918211 20000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1548863583/10000000000 : ℝ), (2747719919/5000000000 : ℝ), (5130784811/10000000000 : ℝ)] ![(1921474757351/20000000000000 : ℝ), (11786000402379/25000000000000 : ℝ), (8649724918211/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1548863583/10000000000 : ℝ)|^5023 ≤ (1921474757351/20000000000000 : ℝ)^3999
        have hw : |(-1548863583/10000000000 : ℝ)|=(1548863583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2747719919/5000000000 : ℝ)|^5023 ≤ (11786000402379/25000000000000 : ℝ)^3999
        have hw : |(2747719919/5000000000 : ℝ)|=(2747719919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5130784811/10000000000 : ℝ)|^5023 ≤ (8649724918211/20000000000000 : ℝ)^3999
        have hw : |(5130784811/10000000000 : ℝ)|=(5130784811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_s2_1 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677842037/5000000000 : ℝ)*x 0 + (-1738626267/10000000000 : ℝ)*x 1 + (205231393/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677842037/5000000000 : ℝ)^5023 ≤ (11410750943669/25000000000000 : ℝ)^3999 := by
    have hnat : (2677842037 : ℕ)^5023*25000000000000^3999 ≤ 11410750943669^3999*5000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677842037 5000000000 11410750943669 25000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1738626267/10000000000 : ℝ)^5023 ≤ (11108371466591/100000000000000 : ℝ)^3999 := by
    have hnat : (1738626267 : ℕ)^5023*100000000000000^3999 ≤ 11108371466591^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1738626267 10000000000 11108371466591 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (205231393/400000000 : ℝ)^5023 ≤ (43248624739283/100000000000000 : ℝ)^3999 := by
    have hnat : (205231393 : ℕ)^5023*100000000000000^3999 ≤ 43248624739283^3999*400000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205231393 400000000 43248624739283 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677842037/5000000000 : ℝ), (-1738626267/10000000000 : ℝ), (205231393/400000000 : ℝ)] ![(11410750943669/25000000000000 : ℝ), (11108371466591/100000000000000 : ℝ), (43248624739283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677842037/5000000000 : ℝ)|^5023 ≤ (11410750943669/25000000000000 : ℝ)^3999
        have hw : |(2677842037/5000000000 : ℝ)|=(2677842037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1738626267/10000000000 : ℝ)|^5023 ≤ (11108371466591/100000000000000 : ℝ)^3999
        have hw : |(-1738626267/10000000000 : ℝ)|=(1738626267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(205231393/400000000 : ℝ)|^5023 ≤ (43248624739283/100000000000000 : ℝ)^3999
        have hw : |(205231393/400000000 : ℝ)|=(205231393/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_s2_2 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535568437/1000000000 : ℝ)*x 0 + (5130784747/10000000000 : ℝ)*x 1 + (-217328247/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535568437/1000000000 : ℝ)^5023 ≤ (22821503471621/50000000000000 : ℝ)^3999 := by
    have hnat : (535568437 : ℕ)^5023*50000000000000^3999 ≤ 22821503471621^3999*1000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535568437 1000000000 22821503471621 50000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5130784747/10000000000 : ℝ)^5023 ≤ (8649724782689/20000000000000 : ℝ)^3999 := by
    have hnat : (5130784747 : ℕ)^5023*20000000000000^3999 ≤ 8649724782689^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5130784747 10000000000 8649724782689 20000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217328247/1250000000 : ℝ)^5023 ≤ (5554184565629/50000000000000 : ℝ)^3999 := by
    have hnat : (217328247 : ℕ)^5023*50000000000000^3999 ≤ 5554184565629^3999*1250000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217328247 1250000000 5554184565629 50000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535568437/1000000000 : ℝ), (5130784747/10000000000 : ℝ), (-217328247/1250000000 : ℝ)] ![(22821503471621/50000000000000 : ℝ), (8649724782689/20000000000000 : ℝ), (5554184565629/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535568437/1000000000 : ℝ)|^5023 ≤ (22821503471621/50000000000000 : ℝ)^3999
        have hw : |(535568437/1000000000 : ℝ)|=(535568437/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5130784747/10000000000 : ℝ)|^5023 ≤ (8649724782689/20000000000000 : ℝ)^3999
        have hw : |(5130784747/10000000000 : ℝ)|=(5130784747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-217328247/1250000000 : ℝ)|^5023 ≤ (5554184565629/50000000000000 : ℝ)^3999
        have hw : |(-217328247/1250000000 : ℝ)|=(217328247/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_s2_3 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4152009047/10000000000 : ℝ)*x 0 + (1842618069/5000000000 : ℝ)*x 1 + (931693319/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4152009047/10000000000 : ℝ)^5023 ≤ (33151865831103/100000000000000 : ℝ)^3999 := by
    have hnat : (4152009047 : ℕ)^5023*100000000000000^3999 ≤ 33151865831103^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4152009047 10000000000 33151865831103 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1842618069/5000000000 : ℝ)^5023 ≤ (7134978996939/25000000000000 : ℝ)^3999 := by
    have hnat : (1842618069 : ℕ)^5023*25000000000000^3999 ≤ 7134978996939^3999*5000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1842618069 5000000000 7134978996939 25000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (931693319/2000000000 : ℝ)^5023 ≤ (7661643634503/20000000000000 : ℝ)^3999 := by
    have hnat : (931693319 : ℕ)^5023*20000000000000^3999 ≤ 7661643634503^3999*2000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      931693319 2000000000 7661643634503 20000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4152009047/10000000000 : ℝ), (1842618069/5000000000 : ℝ), (931693319/2000000000 : ℝ)] ![(33151865831103/100000000000000 : ℝ), (7134978996939/25000000000000 : ℝ), (7661643634503/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4152009047/10000000000 : ℝ)|^5023 ≤ (33151865831103/100000000000000 : ℝ)^3999
        have hw : |(4152009047/10000000000 : ℝ)|=(4152009047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1842618069/5000000000 : ℝ)|^5023 ≤ (7134978996939/25000000000000 : ℝ)^3999
        have hw : |(1842618069/5000000000 : ℝ)|=(1842618069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(931693319/2000000000 : ℝ)|^5023 ≤ (7661643634503/20000000000000 : ℝ)^3999
        have hw : |(931693319/2000000000 : ℝ)|=(931693319/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_s2_4 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-12392321/80000000 : ℝ)*x 0 + (5134737569/10000000000 : ℝ)*x 1 + (5491427559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (12392321/80000000 : ℝ)^5023 ≤ (9608749277501/100000000000000 : ℝ)^3999 := by
    have hnat : (12392321 : ℕ)^5023*100000000000000^3999 ≤ 9608749277501^3999*80000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12392321 80000000 9608749277501 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5134737569/10000000000 : ℝ)^5023 ≤ (43290479203711/100000000000000 : ℝ)^3999 := by
    have hnat : (5134737569 : ℕ)^5023*100000000000000^3999 ≤ 43290479203711^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5134737569 10000000000 43290479203711 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5491427559/10000000000 : ℝ)^5023 ≤ (47100771505757/100000000000000 : ℝ)^3999 := by
    have hnat : (5491427559 : ℕ)^5023*100000000000000^3999 ≤ 47100771505757^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5491427559 10000000000 47100771505757 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-12392321/80000000 : ℝ), (5134737569/10000000000 : ℝ), (5491427559/10000000000 : ℝ)] ![(9608749277501/100000000000000 : ℝ), (43290479203711/100000000000000 : ℝ), (47100771505757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-12392321/80000000 : ℝ)|^5023 ≤ (9608749277501/100000000000000 : ℝ)^3999
        have hw : |(-12392321/80000000 : ℝ)|=(12392321/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5134737569/10000000000 : ℝ)|^5023 ≤ (43290479203711/100000000000000 : ℝ)^3999
        have hw : |(5134737569/10000000000 : ℝ)|=(5134737569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5491427559/10000000000 : ℝ)|^5023 ≤ (47100771505757/100000000000000 : ℝ)^3999
        have hw : |(5491427559/10000000000 : ℝ)|=(5491427559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_s2_5 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5258383217/10000000000 : ℝ)*x 0 + (-55119321/400000000 : ℝ)*x 1 + (1098285511/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5258383217/10000000000 : ℝ)^5023 ≤ (1115096733413/2500000000000 : ℝ)^3999 := by
    have hnat : (5258383217 : ℕ)^5023*2500000000000^3999 ≤ 1115096733413^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258383217 10000000000 1115096733413 2500000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (55119321/400000000 : ℝ)^5023 ≤ (2073839796689/25000000000000 : ℝ)^3999 := by
    have hnat : (55119321 : ℕ)^5023*25000000000000^3999 ≤ 2073839796689^3999*400000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55119321 400000000 2073839796689 25000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1098285511/2000000000 : ℝ)^5023 ≤ (47100771462663/100000000000000 : ℝ)^3999 := by
    have hnat : (1098285511 : ℕ)^5023*100000000000000^3999 ≤ 47100771462663^3999*2000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098285511 2000000000 47100771462663 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5258383217/10000000000 : ℝ), (-55119321/400000000 : ℝ), (1098285511/2000000000 : ℝ)] ![(1115096733413/2500000000000 : ℝ), (2073839796689/25000000000000 : ℝ), (47100771462663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5258383217/10000000000 : ℝ)|^5023 ≤ (1115096733413/2500000000000 : ℝ)^3999
        have hw : |(5258383217/10000000000 : ℝ)|=(5258383217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-55119321/400000000 : ℝ)|^5023 ≤ (2073839796689/25000000000000 : ℝ)^3999
        have hw : |(-55119321/400000000 : ℝ)|=(55119321/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1098285511/2000000000 : ℝ)|^5023 ≤ (47100771462663/100000000000000 : ℝ)^3999
        have hw : |(1098285511/2000000000 : ℝ)|=(1098285511/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_s2_6 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (657297903/1250000000 : ℝ)*x 0 + (109828551/200000000 : ℝ)*x 1 + (-1377983023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (657297903/1250000000 : ℝ)^5023 ≤ (22301934705551/50000000000000 : ℝ)^3999 := by
    have hnat : (657297903 : ℕ)^5023*50000000000000^3999 ≤ 22301934705551^3999*1250000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657297903 1250000000 22301934705551 50000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (109828551/200000000 : ℝ)^5023 ≤ (11775192852199/25000000000000 : ℝ)^3999 := by
    have hnat : (109828551 : ℕ)^5023*25000000000000^3999 ≤ 11775192852199^3999*200000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109828551 200000000 11775192852199 25000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1377983023/10000000000 : ℝ)^5023 ≤ (8295359171633/100000000000000 : ℝ)^3999 := by
    have hnat : (1377983023 : ℕ)^5023*100000000000000^3999 ≤ 8295359171633^3999*10000000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377983023 10000000000 8295359171633 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(657297903/1250000000 : ℝ), (109828551/200000000 : ℝ), (-1377983023/10000000000 : ℝ)] ![(22301934705551/50000000000000 : ℝ), (11775192852199/25000000000000 : ℝ), (8295359171633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(657297903/1250000000 : ℝ)|^5023 ≤ (22301934705551/50000000000000 : ℝ)^3999
        have hw : |(657297903/1250000000 : ℝ)|=(657297903/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(109828551/200000000 : ℝ)|^5023 ≤ (11775192852199/25000000000000 : ℝ)^3999
        have hw : |(109828551/200000000 : ℝ)|=(109828551/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1377983023/10000000000 : ℝ)|^5023 ≤ (8295359171633/100000000000000 : ℝ)^3999
        have hw : |(-1377983023/10000000000 : ℝ)|=(1377983023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1675_s2_7 (p : ℝ) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (129765011/312500000 : ℝ)*x 0 + (145247391/312500000 : ℝ)*x 1 + (461993193/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129765011/312500000 : ℝ)^5023 ≤ (331565926593/1000000000000 : ℝ)^3999 := by
    have hnat : (129765011 : ℕ)^5023*1000000000000^3999 ≤ 331565926593^3999*312500000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129765011 312500000 331565926593 1000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (145247391/312500000 : ℝ)^5023 ≤ (38199277362083/100000000000000 : ℝ)^3999 := by
    have hnat : (145247391 : ℕ)^5023*100000000000000^3999 ≤ 38199277362083^3999*312500000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      145247391 312500000 38199277362083 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (461993193/1250000000 : ℝ)^5023 ≤ (28644129963809/100000000000000 : ℝ)^3999 := by
    have hnat : (461993193 : ℕ)^5023*100000000000000^3999 ≤ 28644129963809^3999*1250000000^5023 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      461993193 1250000000 28644129963809 100000000000000 5023 3999 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5023/1024 : ℝ)) 5023 3999 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(129765011/312500000 : ℝ), (145247391/312500000 : ℝ), (461993193/1250000000 : ℝ)] ![(331565926593/1000000000000 : ℝ), (38199277362083/100000000000000 : ℝ), (28644129963809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(129765011/312500000 : ℝ)|^5023 ≤ (331565926593/1000000000000 : ℝ)^3999
        have hw : |(129765011/312500000 : ℝ)|=(129765011/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(145247391/312500000 : ℝ)|^5023 ≤ (38199277362083/100000000000000 : ℝ)^3999
        have hw : |(145247391/312500000 : ℝ)|=(145247391/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(461993193/1250000000 : ℝ)|^5023 ≤ (28644129963809/100000000000000 : ℝ)^3999
        have hw : |(461993193/1250000000 : ℝ)|=(461993193/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1675_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183445147/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8987/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (57/625 : ℝ)*pair X i i ≤ pair X i h) :
    (1927/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17379/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8987/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (57/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8987/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (57/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8987/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (57/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8987/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (57/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8987/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (57/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8987/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (57/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (57/625 : ℝ) ^ (5015/1024 : ℝ) ≤ (806520379711191/100000000000000000000 : ℝ) := by
    have hpowers : (57/625 : ℝ)^5015 ≤ (806520379711191/100000000000000000000 : ℝ)^1024 := by
      have hnat : (57 : ℕ)^5015*100000000000000000000^1024 ≤ 806520379711191^1024*625^5015 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57 625 806520379711191 100000000000000000000 5015 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (57/625 : ℝ)) (X := (806520379711191/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5015 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8987/50000 : ℝ) ^ (5015/1024 : ℝ) ≤ (2796158138974483/12500000000000000000 : ℝ) := by
    have hpowers : (8987/50000 : ℝ)^5015 ≤ (2796158138974483/12500000000000000000 : ℝ)^1024 := by
      have hnat : (8987 : ℕ)^5015*12500000000000000000^1024 ≤ 2796158138974483^1024*50000^5015 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8987 50000 2796158138974483 12500000000000000000 5015 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8987/50000 : ℝ)) (X := (2796158138974483/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5015 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000806520379711191/50000000000000000000 : ℝ) ≤ (62500205850341/62500000000000 : ℝ) ^ (5015/1024 : ℝ) := by
    have hpowers : (50000806520379711191/50000000000000000000 : ℝ)^1024 ≤ (62500205850341/62500000000000 : ℝ)^5015 := by
      have hnat : (50000806520379711191 : ℕ)^1024*62500000000000^5015 ≤ 62500205850341^5015*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000806520379711191 50000000000000000000 62500205850341 62500000000000 1024 5015 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (62500205850341/62500000000000 : ℝ)) (X := (50000806520379711191/50000000000000000000 : ℝ)) (by norm_num) 5015 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20004635157098301411/20000000000000000000 : ℝ) ≤ (5000236588396123/5000000000000000 : ℝ) ^ (5015/1024 : ℝ) := by
    have hpowers : (20004635157098301411/20000000000000000000 : ℝ)^1024 ≤ (5000236588396123/5000000000000000 : ℝ)^5015 := by
      have hnat : (20004635157098301411 : ℕ)^1024*5000000000000000^5015 ≤ 5000236588396123^5015*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20004635157098301411 20000000000000000000 5000236588396123 5000000000000000 1024 5015 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000236588396123/5000000000000000 : ℝ)) (X := (20004635157098301411/20000000000000000000 : ℝ)) (by norm_num) 5015 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6252796158138974483/6250000000000000000 : ℝ) ≤ (2500228354382483/2500000000000000 : ℝ) ^ (5015/1024 : ℝ) := by
    have hpowers : (6252796158138974483/6250000000000000000 : ℝ)^1024 ≤ (2500228354382483/2500000000000000 : ℝ)^5015 := by
      have hnat : (6252796158138974483 : ℕ)^1024*2500000000000000^5015 ≤ 2500228354382483^5015*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252796158138974483 6250000000000000000 2500228354382483 2500000000000000 1024 5015 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500228354382483/2500000000000000 : ℝ)) (X := (6252796158138974483/6250000000000000000 : ℝ)) (by norm_num) 5015 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(806520379711191/100000000000000000000 : ℝ) ≤ ((2912245448183279/2912500000000000 : ℝ)+2*(220120368843/442700000000000 : ℝ)*(57/625 : ℝ))^(5015/1024 : ℝ) := by
    rw [show (2912245448183279/2912500000000000 : ℝ)+2*(220120368843/442700000000000 : ℝ)*(57/625 : ℝ)=(62500205850341/62500000000000 : ℝ) by norm_num, show 1+2*(806520379711191/100000000000000000000 : ℝ)=(50000806520379711191/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2796158138974483/12500000000000000000 : ℝ)+(806520379711191/100000000000000000000 : ℝ) ≤ ((2912245448183279/2912500000000000 : ℝ)+(220120368843/442700000000000 : ℝ)*((8987/50000 : ℝ)+(57/625 : ℝ)))^(5015/1024 : ℝ) := by
    rw [show (2912245448183279/2912500000000000 : ℝ)+(220120368843/442700000000000 : ℝ)*((8987/50000 : ℝ)+(57/625 : ℝ))=(5000236588396123/5000000000000000 : ℝ) by norm_num, show 1+(2796158138974483/12500000000000000000 : ℝ)+(806520379711191/100000000000000000000 : ℝ)=(20004635157098301411/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2796158138974483/12500000000000000000 : ℝ) ≤ ((2912245448183279/2912500000000000 : ℝ)+2*(220120368843/442700000000000 : ℝ)*(8987/50000 : ℝ))^(5015/1024 : ℝ) := by
    rw [show (2912245448183279/2912500000000000 : ℝ)+2*(220120368843/442700000000000 : ℝ)*(8987/50000 : ℝ)=(2500228354382483/2500000000000000 : ℝ) by norm_num, show 1+2*(2796158138974483/12500000000000000000 : ℝ)=(6252796158138974483/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2912245448183279/2912500000000000 : ℝ)*(X 1 0+X 2 0)+(220120368843/442700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5015/1024 : ℝ)) (lo := (57/625 : ℝ)) (hi := (8987/50000 : ℝ)) (c := (2912245448183279/2912500000000000 : ℝ)) (alpha := (220120368843/442700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2912245448183279/2912500000000000 : ℝ)*(X 0 1+X 2 1)+(220120368843/442700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5015/1024 : ℝ)) (lo := (57/625 : ℝ)) (hi := (8987/50000 : ℝ)) (c := (2912245448183279/2912500000000000 : ℝ)) (alpha := (220120368843/442700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2912245448183279/2912500000000000 : ℝ)*(X 0 2+X 1 2)+(220120368843/442700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5015/1024 : ℝ)) (lo := (57/625 : ℝ)) (hi := (8987/50000 : ℝ)) (c := (2912245448183279/2912500000000000 : ℝ)) (alpha := (220120368843/442700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1548863583/10000000000 : ℝ)*X 0 0+(2747719919/5000000000 : ℝ)*X 0 1+(5130784811/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677842037/5000000000 : ℝ)*X 1 0+(-1738626267/10000000000 : ℝ)*X 1 1+(205231393/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((535568437/1000000000 : ℝ)*X 2 0+(5130784747/10000000000 : ℝ)*X 2 1+(-217328247/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4152009047/10000000000 : ℝ)*X 0 0+(1842618069/5000000000 : ℝ)*X 0 1+(931693319/2000000000 : ℝ)*X 0 2+(4152009047/10000000000 : ℝ)*X 1 0+(1842618069/5000000000 : ℝ)*X 1 1+(931693319/2000000000 : ℝ)*X 1 2+(4152009047/10000000000 : ℝ)*X 2 0+(1842618069/5000000000 : ℝ)*X 2 1+(931693319/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-12392321/80000000 : ℝ)*X 0 0+(5134737569/10000000000 : ℝ)*X 0 1+(5491427559/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5258383217/10000000000 : ℝ)*X 1 0+(-55119321/400000000 : ℝ)*X 1 1+(1098285511/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((657297903/1250000000 : ℝ)*X 2 0+(109828551/200000000 : ℝ)*X 2 1+(-1377983023/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((129765011/312500000 : ℝ)*X 0 0+(145247391/312500000 : ℝ)*X 0 1+(461993193/1250000000 : ℝ)*X 0 2+(129765011/312500000 : ℝ)*X 1 0+(145247391/312500000 : ℝ)*X 1 1+(461993193/1250000000 : ℝ)*X 1 2+(129765011/312500000 : ℝ)*X 2 0+(145247391/312500000 : ℝ)*X 2 1+(461993193/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1675_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24349597470946968949668291/2766875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1121995667/100000000000000 : ℝ)*(base19) + (1213975469/100000000000000 : ℝ)*(base23) + (31911657/100000000000000 : ℝ)*(lower2) + (71181639/50000000000000 : ℝ)*(upper3) + (291219599/100000000000000 : ℝ)*(upper5) + (942462958830189/50000000000000 : ℝ)*(major0) + (942462958830189/50000000000000 : ℝ)*(major1) + (942462958830189/50000000000000 : ℝ)*(major2) + (342790687315197/12500000000000 : ℝ)*(sp0) + (342791960513771/12500000000000 : ℝ)*(sp1) + (1371167796065183/50000000000000 : ℝ)*(sp2) + (6421940785897/625000000000 : ℝ)*(sp3) + (11307584259/100000000000000 : ℝ)*(sp4) + (4210124841/100000000000000 : ℝ)*(sp7) + (513757367934181/50000000000000 : ℝ)*(f.failure) + (548467361221167/20000000000000 : ℝ)*(f.sum) + (31067887744361/22135000000000000000000000000 : ℝ)*base66 + (23523603808840139/2766875000000000000000000000000 : ℝ)*base67 + (7177245500046389/2766875000000000000000000000000 : ℝ)*base69 + (1722535121505191/691718750000000000000000000000 : ℝ)*base71 + (62643254764347/11067500000000000000000000000 : ℝ)*base73 + (224694386182309/691718750000000000000000000000 : ℝ)*base76 + (719142037050217/345859375000000000000000000000 : ℝ)*base78 + (2167584894901007/1383437500000000000000000000000 : ℝ)*base79 + (28916507299387/11067500000000000000000000000 : ℝ)*base81 + (19869607/5000000000000000000000 : ℝ)*base89 + (19869607/5000000000000000000000 : ℝ)*base91 + (19869607/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16987653472658852090857263/2766875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (224738827/25000000000000 : ℝ)*(base19) + (974257821/100000000000000 : ℝ)*(base23) + (132166343/100000000000000 : ℝ)*(upper3) + (31694861/100000000000000 : ℝ)*(lower4) + (499929/390625000000 : ℝ)*(upper5) + (1927003454130707/100000000000000 : ℝ)*(major0) + (1927003454130707/100000000000000 : ℝ)*(major1) + (1927003454130707/100000000000000 : ℝ)*(major2) + (7542443687/100000000000000 : ℝ)*(sp1) + (8152855867/100000000000000 : ℝ)*(sp2) + (700888643389639/25000000000000 : ℝ)*(sp4) + (2803546132159561/100000000000000 : ℝ)*(sp5) + (700886361611217/25000000000000 : ℝ)*(sp6) + (52522606502387/5000000000000 : ℝ)*(sp7) + (52522606502387/5000000000000 : ℝ)*(f.failure) + (700888643389639/25000000000000 : ℝ)*(f.sum) + (106449294770299/22135000000000000000000000000 : ℝ)*base66 + (3165567054904517/1383437500000000000000000000000 : ℝ)*base68 + (9187175387792017/1383437500000000000000000000000 : ℝ)*base70 + (16036113661869659/2766875000000000000000000000000 : ℝ)*base72 + (39321796107509/22135000000000000000000000000 : ℝ)*base74 + (4932604812521321/691718750000000000000000000000 : ℝ)*base76 + (1676143089942223/345859375000000000000000000000 : ℝ)*base78 + (14824841843243409/2766875000000000000000000000000 : ℝ)*base80 + (73460362635539/22135000000000000000000000000 : ℝ)*base82 + (4065889/500000000000000000000 : ℝ)*base89 + (4065889/500000000000000000000 : ℝ)*base91 + (4065889/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1675_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183445147/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8987/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (57/625 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1927/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17379/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1675_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1675_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183445147/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1927/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17379/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1675_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1675_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1675_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5015/1024 : ℝ) ≤ p) (hpb : p ≤ (5023/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (183445147/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1927/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17379/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1675_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
