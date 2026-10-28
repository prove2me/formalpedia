-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1284_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:24:18.069236+00:00
-- url     : https://prove2.me/submissions/c864ef55-3670-4374-b1e3-b3c83f791cdd

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
theorem support_rectangle_w1284_s3_0 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-261586981/1250000000 : ℝ)*x 0 + (5435282689/10000000000 : ℝ)*x 1 + (5224674599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (261586981/1250000000 : ℝ)^1061 ≤ (6362857870913/50000000000000 : ℝ)^805 := by
    have hnat : (261586981 : ℕ)^1061*50000000000000^805 ≤ 6362857870913^805*1250000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261586981 1250000000 6362857870913 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5435282689/10000000000 : ℝ)^1061 ≤ (44773339368847/100000000000000 : ℝ)^805 := by
    have hnat : (5435282689 : ℕ)^1061*100000000000000^805 ≤ 44773339368847^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435282689 10000000000 44773339368847 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5224674599/10000000000 : ℝ)^1061 ≤ (8500188973981/20000000000000 : ℝ)^805 := by
    have hnat : (5224674599 : ℕ)^1061*20000000000000^805 ≤ 8500188973981^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224674599 10000000000 8500188973981 20000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-261586981/1250000000 : ℝ), (5435282689/10000000000 : ℝ), (5224674599/10000000000 : ℝ)] ![(6362857870913/50000000000000 : ℝ), (44773339368847/100000000000000 : ℝ), (8500188973981/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-261586981/1250000000 : ℝ)|^1061 ≤ (6362857870913/50000000000000 : ℝ)^805
        have hw : |(-261586981/1250000000 : ℝ)|=(261586981/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5435282689/10000000000 : ℝ)|^1061 ≤ (44773339368847/100000000000000 : ℝ)^805
        have hw : |(5435282689/10000000000 : ℝ)|=(5435282689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5224674599/10000000000 : ℝ)|^1061 ≤ (8500188973981/20000000000000 : ℝ)^805
        have hw : |(5224674599/10000000000 : ℝ)|=(5224674599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s3_1 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5354859787/10000000000 : ℝ)*x 0 + (-17191477/78125000 : ℝ)*x 1 + (2612337287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354859787/10000000000 : ℝ)^1061 ≤ (21951117545157/50000000000000 : ℝ)^805 := by
    have hnat : (5354859787 : ℕ)^1061*50000000000000^805 ≤ 21951117545157^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354859787 10000000000 21951117545157 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17191477/78125000 : ℝ)^1061 ≤ (1359682029761/10000000000000 : ℝ)^805 := by
    have hnat : (17191477 : ℕ)^1061*10000000000000^805 ≤ 1359682029761^805*78125000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17191477 78125000 1359682029761 10000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2612337287/5000000000 : ℝ)^1061 ≤ (21250472300933/50000000000000 : ℝ)^805 := by
    have hnat : (2612337287 : ℕ)^1061*50000000000000^805 ≤ 21250472300933^805*5000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612337287 5000000000 21250472300933 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354859787/10000000000 : ℝ), (-17191477/78125000 : ℝ), (2612337287/5000000000 : ℝ)] ![(21951117545157/50000000000000 : ℝ), (1359682029761/10000000000000 : ℝ), (21250472300933/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354859787/10000000000 : ℝ)|^1061 ≤ (21951117545157/50000000000000 : ℝ)^805
        have hw : |(5354859787/10000000000 : ℝ)|=(5354859787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-17191477/78125000 : ℝ)|^1061 ≤ (1359682029761/10000000000000 : ℝ)^805
        have hw : |(-17191477/78125000 : ℝ)|=(17191477/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2612337287/5000000000 : ℝ)|^1061 ≤ (21250472300933/50000000000000 : ℝ)^805
        have hw : |(2612337287/5000000000 : ℝ)|=(2612337287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s3_2 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5354859687/10000000000 : ℝ)*x 0 + (1306168743/2500000000 : ℝ)*x 1 + (-275063583/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354859687/10000000000 : ℝ)^1061 ≤ (43902234009731/100000000000000 : ℝ)^805 := by
    have hnat : (5354859687 : ℕ)^1061*100000000000000^805 ≤ 43902234009731^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354859687 10000000000 43902234009731 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1306168743/2500000000 : ℝ)^1061 ≤ (8500189773811/20000000000000 : ℝ)^805 := by
    have hnat : (1306168743 : ℕ)^1061*20000000000000^805 ≤ 8500189773811^805*2500000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306168743 2500000000 8500189773811 20000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (275063583/1250000000 : ℝ)^1061 ≤ (1699602138149/12500000000000 : ℝ)^805 := by
    have hnat : (275063583 : ℕ)^1061*12500000000000^805 ≤ 1699602138149^805*1250000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275063583 1250000000 1699602138149 12500000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354859687/10000000000 : ℝ), (1306168743/2500000000 : ℝ), (-275063583/1250000000 : ℝ)] ![(43902234009731/100000000000000 : ℝ), (8500189773811/20000000000000 : ℝ), (1699602138149/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354859687/10000000000 : ℝ)|^1061 ≤ (43902234009731/100000000000000 : ℝ)^805
        have hw : |(5354859687/10000000000 : ℝ)|=(5354859687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1306168743/2500000000 : ℝ)|^1061 ≤ (8500189773811/20000000000000 : ℝ)^805
        have hw : |(1306168743/2500000000 : ℝ)|=(1306168743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-275063583/1250000000 : ℝ)|^1061 ≤ (1699602138149/12500000000000 : ℝ)^805
        have hw : |(-275063583/1250000000 : ℝ)|=(275063583/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s3_3 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1085133169/2500000000 : ℝ)*x 0 + (4129911049/10000000000 : ℝ)*x 1 + (4561437249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1085133169/2500000000 : ℝ)^1061 ≤ (3328719582677/10000000000000 : ℝ)^805 := by
    have hnat : (1085133169 : ℕ)^1061*10000000000000^805 ≤ 3328719582677^805*2500000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085133169 2500000000 3328719582677 10000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4129911049/10000000000 : ℝ)^1061 ≤ (31174899981417/100000000000000 : ℝ)^805 := by
    have hnat : (4129911049 : ℕ)^1061*100000000000000^805 ≤ 31174899981417^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4129911049 10000000000 31174899981417 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4561437249/10000000000 : ℝ)^1061 ≤ (35537904180659/100000000000000 : ℝ)^805 := by
    have hnat : (4561437249 : ℕ)^1061*100000000000000^805 ≤ 35537904180659^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4561437249 10000000000 35537904180659 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1085133169/2500000000 : ℝ), (4129911049/10000000000 : ℝ), (4561437249/10000000000 : ℝ)] ![(3328719582677/10000000000000 : ℝ), (31174899981417/100000000000000 : ℝ), (35537904180659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1085133169/2500000000 : ℝ)|^1061 ≤ (3328719582677/10000000000000 : ℝ)^805
        have hw : |(1085133169/2500000000 : ℝ)|=(1085133169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4129911049/10000000000 : ℝ)|^1061 ≤ (31174899981417/100000000000000 : ℝ)^805
        have hw : |(4129911049/10000000000 : ℝ)|=(4129911049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4561437249/10000000000 : ℝ)|^1061 ≤ (35537904180659/100000000000000 : ℝ)^805
        have hw : |(4561437249/10000000000 : ℝ)|=(4561437249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s3_4 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-6539747/31250000 : ℝ)*x 0 + (5225587037/10000000000 : ℝ)*x 1 + (1358591119/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6539747/31250000 : ℝ)^1061 ≤ (2545180324529/20000000000000 : ℝ)^805 := by
    have hnat : (6539747 : ℕ)^1061*20000000000000^805 ≤ 2545180324529^805*31250000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6539747 31250000 2545180324529 20000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5225587037/10000000000 : ℝ)^1061 ≤ (21255363959859/50000000000000 : ℝ)^805 := by
    have hnat : (5225587037 : ℕ)^1061*50000000000000^805 ≤ 21255363959859^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225587037 10000000000 21255363959859 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358591119/2500000000 : ℝ)^1061 ≤ (44763370437057/100000000000000 : ℝ)^805 := by
    have hnat : (1358591119 : ℕ)^1061*100000000000000^805 ≤ 44763370437057^805*2500000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358591119 2500000000 44763370437057 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-6539747/31250000 : ℝ), (5225587037/10000000000 : ℝ), (1358591119/2500000000 : ℝ)] ![(2545180324529/20000000000000 : ℝ), (21255363959859/50000000000000 : ℝ), (44763370437057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-6539747/31250000 : ℝ)|^1061 ≤ (2545180324529/20000000000000 : ℝ)^805
        have hw : |(-6539747/31250000 : ℝ)|=(6539747/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5225587037/10000000000 : ℝ)|^1061 ≤ (21255363959859/50000000000000 : ℝ)^805
        have hw : |(5225587037/10000000000 : ℝ)|=(5225587037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358591119/2500000000 : ℝ)|^1061 ≤ (44763370437057/100000000000000 : ℝ)^805
        have hw : |(1358591119/2500000000 : ℝ)|=(1358591119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s3_5 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (530098901/1000000000 : ℝ)*x 0 + (-1990819059/10000000000 : ℝ)*x 1 + (10613993/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530098901/1000000000 : ℝ)^1061 ≤ (2707565629869/6250000000000 : ℝ)^805 := by
    have hnat : (530098901 : ℕ)^1061*6250000000000^805 ≤ 2707565629869^805*1000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530098901 1000000000 2707565629869 6250000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1990819059/10000000000 : ℝ)^1061 ≤ (11915580121967/100000000000000 : ℝ)^805 := by
    have hnat : (1990819059 : ℕ)^1061*100000000000000^805 ≤ 11915580121967^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1990819059 10000000000 11915580121967 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10613993/19531250 : ℝ)^1061 ≤ (44763369785661/100000000000000 : ℝ)^805 := by
    have hnat : (10613993 : ℕ)^1061*100000000000000^805 ≤ 44763369785661^805*19531250^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10613993 19531250 44763369785661 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530098901/1000000000 : ℝ), (-1990819059/10000000000 : ℝ), (10613993/19531250 : ℝ)] ![(2707565629869/6250000000000 : ℝ), (11915580121967/100000000000000 : ℝ), (44763369785661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530098901/1000000000 : ℝ)|^1061 ≤ (2707565629869/6250000000000 : ℝ)^805
        have hw : |(530098901/1000000000 : ℝ)|=(530098901/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1990819059/10000000000 : ℝ)|^1061 ≤ (11915580121967/100000000000000 : ℝ)^805
        have hw : |(-1990819059/10000000000 : ℝ)|=(1990819059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(10613993/19531250 : ℝ)|^1061 ≤ (44763369785661/100000000000000 : ℝ)^805
        have hw : |(10613993/19531250 : ℝ)|=(10613993/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s3_6 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2650494511/5000000000 : ℝ)*x 0 + (1086872877/2000000000 : ℝ)*x 1 + (-497704771/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2650494511/5000000000 : ℝ)^1061 ≤ (21660525103579/50000000000000 : ℝ)^805 := by
    have hnat : (2650494511 : ℕ)^1061*50000000000000^805 ≤ 21660525103579^805*5000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2650494511 5000000000 21660525103579 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086872877/2000000000 : ℝ)^1061 ≤ (44763369449107/100000000000000 : ℝ)^805 := by
    have hnat : (1086872877 : ℕ)^1061*100000000000000^805 ≤ 44763369449107^805*2000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086872877 2000000000 44763369449107 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (497704771/2500000000 : ℝ)^1061 ≤ (11915580319183/100000000000000 : ℝ)^805 := by
    have hnat : (497704771 : ℕ)^1061*100000000000000^805 ≤ 11915580319183^805*2500000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497704771 2500000000 11915580319183 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2650494511/5000000000 : ℝ), (1086872877/2000000000 : ℝ), (-497704771/2500000000 : ℝ)] ![(21660525103579/50000000000000 : ℝ), (44763369449107/100000000000000 : ℝ), (11915580319183/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2650494511/5000000000 : ℝ)|^1061 ≤ (21660525103579/50000000000000 : ℝ)^805
        have hw : |(2650494511/5000000000 : ℝ)|=(2650494511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1086872877/2000000000 : ℝ)|^1061 ≤ (44763369449107/100000000000000 : ℝ)^805
        have hw : |(1086872877/2000000000 : ℝ)|=(1086872877/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-497704771/2500000000 : ℝ)|^1061 ≤ (11915580319183/100000000000000 : ℝ)^805
        have hw : |(-497704771/2500000000 : ℝ)|=(497704771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s3_7 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (868116071/2000000000 : ℝ)*x 0 + (1139891921/2500000000 : ℝ)*x 1 + (4131791943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (868116071/2000000000 : ℝ)^1061 ≤ (2080479859633/6250000000000 : ℝ)^805 := by
    have hnat : (868116071 : ℕ)^1061*6250000000000^805 ≤ 2080479859633^805*2000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      868116071 2000000000 2080479859633 6250000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1139891921/2500000000 : ℝ)^1061 ≤ (17759353844311/50000000000000 : ℝ)^805 := by
    have hnat : (1139891921 : ℕ)^1061*50000000000000^805 ≤ 17759353844311^805*2500000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1139891921 2500000000 17759353844311 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4131791943/10000000000 : ℝ)^1061 ≤ (15596807271149/50000000000000 : ℝ)^805 := by
    have hnat : (4131791943 : ℕ)^1061*50000000000000^805 ≤ 15596807271149^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4131791943 10000000000 15596807271149 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(868116071/2000000000 : ℝ), (1139891921/2500000000 : ℝ), (4131791943/10000000000 : ℝ)] ![(2080479859633/6250000000000 : ℝ), (17759353844311/50000000000000 : ℝ), (15596807271149/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(868116071/2000000000 : ℝ)|^1061 ≤ (2080479859633/6250000000000 : ℝ)^805
        have hw : |(868116071/2000000000 : ℝ)|=(868116071/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1139891921/2500000000 : ℝ)|^1061 ≤ (17759353844311/50000000000000 : ℝ)^805
        have hw : |(1139891921/2500000000 : ℝ)|=(1139891921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4131791943/10000000000 : ℝ)|^1061 ≤ (15596807271149/50000000000000 : ℝ)^805
        have hw : |(4131791943/10000000000 : ℝ)|=(4131791943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1284_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152447821/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8177/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1889/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5311/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15077/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8177/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1889/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8177/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1889/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8177/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1889/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8177/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1889/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8177/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1889/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8177/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1889/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1889/20000 : ℝ) ^ (4243/1024 : ℝ) ≤ (2835719641349281/50000000000000000000 : ℝ) := by
    have hpowers : (1889/20000 : ℝ)^4243 ≤ (2835719641349281/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1889 : ℕ)^4243*50000000000000000000^1024 ≤ 2835719641349281^1024*20000^4243 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1889 20000 2835719641349281 50000000000000000000 4243 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1889/20000 : ℝ)) (X := (2835719641349281/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8177/50000 : ℝ) ^ (4243/1024 : ℝ) ≤ (27578968329890273/50000000000000000000 : ℝ) := by
    have hpowers : (8177/50000 : ℝ)^4243 ≤ (27578968329890273/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8177 : ℕ)^4243*50000000000000000000^1024 ≤ 27578968329890273^1024*50000^4243 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8177 50000 27578968329890273 50000000000000000000 4243 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8177/50000 : ℝ)) (X := (27578968329890273/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002835719641349281/25000000000000000000 : ℝ) ≤ (5000136867875569/5000000000000000 : ℝ) ^ (4243/1024 : ℝ) := by
    have hpowers : (25002835719641349281/25000000000000000000 : ℝ)^1024 ≤ (5000136867875569/5000000000000000 : ℝ)^4243 := by
      have hnat : (25002835719641349281 : ℕ)^1024*5000000000000000^4243 ≤ 5000136867875569^4243*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002835719641349281 25000000000000000000 5000136867875569 5000000000000000 1024 4243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000136867875569/5000000000000000 : ℝ)) (X := (25002835719641349281/25000000000000000000 : ℝ)) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25015207343985619777/25000000000000000000 : ℝ) ≤ (10001467709478691/10000000000000000 : ℝ) ^ (4243/1024 : ℝ) := by
    have hpowers : (25015207343985619777/25000000000000000000 : ℝ)^1024 ≤ (10001467709478691/10000000000000000 : ℝ)^4243 := by
      have hnat : (25015207343985619777 : ℕ)^1024*10000000000000000^4243 ≤ 10001467709478691^4243*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015207343985619777 25000000000000000000 10001467709478691 10000000000000000 1024 4243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001467709478691/10000000000000000 : ℝ)) (X := (25015207343985619777/25000000000000000000 : ℝ)) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25027578968329890273/25000000000000000000 : ℝ) ≤ (2500665420801561/2500000000000000 : ℝ) ^ (4243/1024 : ℝ) := by
    have hpowers : (25027578968329890273/25000000000000000000 : ℝ)^1024 ≤ (2500665420801561/2500000000000000 : ℝ)^4243 := by
      have hnat : (25027578968329890273 : ℕ)^1024*2500000000000000^4243 ≤ 2500665420801561^4243*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25027578968329890273 25000000000000000000 2500665420801561 2500000000000000 1024 4243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500665420801561/2500000000000000 : ℝ)) (X := (25027578968329890273/25000000000000000000 : ℝ)) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2835719641349281/50000000000000000000 : ℝ) ≤ ((4316833567286946017/4318125000000000000 : ℝ)+2*(1193973727553/690900000000000 : ℝ)*(1889/20000 : ℝ))^(4243/1024 : ℝ) := by
    rw [show (4316833567286946017/4318125000000000000 : ℝ)+2*(1193973727553/690900000000000 : ℝ)*(1889/20000 : ℝ)=(5000136867875569/5000000000000000 : ℝ) by norm_num, show 1+2*(2835719641349281/50000000000000000000 : ℝ)=(25002835719641349281/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27578968329890273/50000000000000000000 : ℝ)+(2835719641349281/50000000000000000000 : ℝ) ≤ ((4316833567286946017/4318125000000000000 : ℝ)+(1193973727553/690900000000000 : ℝ)*((8177/50000 : ℝ)+(1889/20000 : ℝ)))^(4243/1024 : ℝ) := by
    rw [show (4316833567286946017/4318125000000000000 : ℝ)+(1193973727553/690900000000000 : ℝ)*((8177/50000 : ℝ)+(1889/20000 : ℝ))=(10001467709478691/10000000000000000 : ℝ) by norm_num, show 1+(27578968329890273/50000000000000000000 : ℝ)+(2835719641349281/50000000000000000000 : ℝ)=(25015207343985619777/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27578968329890273/50000000000000000000 : ℝ) ≤ ((4316833567286946017/4318125000000000000 : ℝ)+2*(1193973727553/690900000000000 : ℝ)*(8177/50000 : ℝ))^(4243/1024 : ℝ) := by
    rw [show (4316833567286946017/4318125000000000000 : ℝ)+2*(1193973727553/690900000000000 : ℝ)*(8177/50000 : ℝ)=(2500665420801561/2500000000000000 : ℝ) by norm_num, show 1+2*(27578968329890273/50000000000000000000 : ℝ)=(25027578968329890273/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4316833567286946017/4318125000000000000 : ℝ)*(X 1 0+X 2 0)+(1193973727553/690900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4243/1024 : ℝ)) (lo := (1889/20000 : ℝ)) (hi := (8177/50000 : ℝ)) (c := (4316833567286946017/4318125000000000000 : ℝ)) (alpha := (1193973727553/690900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4316833567286946017/4318125000000000000 : ℝ)*(X 0 1+X 2 1)+(1193973727553/690900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4243/1024 : ℝ)) (lo := (1889/20000 : ℝ)) (hi := (8177/50000 : ℝ)) (c := (4316833567286946017/4318125000000000000 : ℝ)) (alpha := (1193973727553/690900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4316833567286946017/4318125000000000000 : ℝ)*(X 0 2+X 1 2)+(1193973727553/690900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4243/1024 : ℝ)) (lo := (1889/20000 : ℝ)) (hi := (8177/50000 : ℝ)) (c := (4316833567286946017/4318125000000000000 : ℝ)) (alpha := (1193973727553/690900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-261586981/1250000000 : ℝ)*X 0 0+(5435282689/10000000000 : ℝ)*X 0 1+(5224674599/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5354859787/10000000000 : ℝ)*X 1 0+(-17191477/78125000 : ℝ)*X 1 1+(2612337287/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354859687/10000000000 : ℝ)*X 2 0+(1306168743/2500000000 : ℝ)*X 2 1+(-275063583/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1085133169/2500000000 : ℝ)*X 0 0+(4129911049/10000000000 : ℝ)*X 0 1+(4561437249/10000000000 : ℝ)*X 0 2+(1085133169/2500000000 : ℝ)*X 1 0+(4129911049/10000000000 : ℝ)*X 1 1+(4561437249/10000000000 : ℝ)*X 1 2+(1085133169/2500000000 : ℝ)*X 2 0+(4129911049/10000000000 : ℝ)*X 2 1+(4561437249/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-6539747/31250000 : ℝ)*X 0 0+(5225587037/10000000000 : ℝ)*X 0 1+(1358591119/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((530098901/1000000000 : ℝ)*X 1 0+(-1990819059/10000000000 : ℝ)*X 1 1+(10613993/19531250 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2650494511/5000000000 : ℝ)*X 2 0+(1086872877/2000000000 : ℝ)*X 2 1+(-497704771/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((868116071/2000000000 : ℝ)*X 0 0+(1139891921/2500000000 : ℝ)*X 0 1+(4131791943/10000000000 : ℝ)*X 0 2+(868116071/2000000000 : ℝ)*X 1 0+(1139891921/2500000000 : ℝ)*X 1 1+(4131791943/10000000000 : ℝ)*X 1 2+(868116071/2000000000 : ℝ)*X 2 0+(1139891921/2500000000 : ℝ)*X 2 1+(4131791943/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (105869710130121138519397413/17992187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (962338771/100000000000000 : ℝ)*(base19) + (895043117/100000000000000 : ℝ)*(base23) + (507989/4000000000000 : ℝ)*(upper4) + (85041029/50000000000000 : ℝ)*(upper5) + (1766394532563453/50000000000000 : ℝ)*(major0) + (1766394532563453/50000000000000 : ℝ)*(major1) + (1766394532563453/50000000000000 : ℝ)*(major2) + (2374088100819789/50000000000000 : ℝ)*(sp0) + (4748196588808321/100000000000000 : ℝ)*(sp1) + (4748201138284851/100000000000000 : ℝ)*(sp2) + (1158683592810053/50000000000000 : ℝ)*(sp3) + (25831688389/100000000000000 : ℝ)*(sp4) + (1120545219/25000000000000 : ℝ)*(sp5) + (544697849/6250000000000 : ℝ)*(sp7) + (231737590078569/10000000000000 : ℝ)*(f.failure) + (148381313541499/3125000000000 : ℝ)*(f.sum) + (31223441245037/5757500000000000000000000000 : ℝ)*base66 + (37277123932744433/71968750000000000000000000000000 : ℝ)*base68 + (254574206575974317/71968750000000000000000000000000 : ℝ)*base69 + (791245432265056933/71968750000000000000000000000000 : ℝ)*base72 + (2797773114461/2878750000000000000000000000 : ℝ)*base74 + (637052827699349317/71968750000000000000000000000000 : ℝ)*base75 + (363797207225994433/71968750000000000000000000000000 : ℝ)*base78 + (103774128517463183/71968750000000000000000000000000 : ℝ)*base80 + (48466446453/1439375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (2848149/1000000000000000000000 : ℝ)*base89 + (2848149/1000000000000000000000 : ℝ)*base91 + (2848149/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (231049263830541691334545531/35984375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (49848477/3125000000000 : ℝ)*(base19) + (828036639/50000000000000 : ℝ)*(base23) + (18884351/12500000000000 : ℝ)*(upper3) + (27901697/100000000000000 : ℝ)*(lower4) + (176218479/100000000000000 : ℝ)*(upper5) + (445466445182233/12500000000000 : ℝ)*(major0) + (445466445182233/12500000000000 : ℝ)*(major1) + (445466445182233/12500000000000 : ℝ)*(major2) + (6539114929/25000000000000 : ℝ)*(sp1) + (25905032009/100000000000000 : ℝ)*(sp2) + (191591596070779/4000000000000 : ℝ)*(sp4) + (957952430031699/20000000000000 : ℝ)*(sp5) + (1197440585166047/25000000000000 : ℝ)*(sp6) + (584418251779713/25000000000000 : ℝ)*(sp7) + (584418251779713/25000000000000 : ℝ)*(f.failure) + (191591596070779/4000000000000 : ℝ)*(f.sum) + (30342739680977/8636250000000000000000000000 : ℝ)*base66 + (849023982835972547/107953125000000000000000000000000 : ℝ)*base67 + (149399487319802789/53976562500000000000000000000000 : ℝ)*base70 + (14548193130134291/13494140625000000000000000000000 : ℝ)*base72 + (25984676664277/34545000000000000000000000000 : ℝ)*base73 + (198889420564290961/53976562500000000000000000000000 : ℝ)*base75 + (426803826596535047/107953125000000000000000000000000 : ℝ)*base77 + (161590668264259711/53976562500000000000000000000000 : ℝ)*base79 + (17486569276067/8636250000000000000000000000 : ℝ)*base82 + (18855373/2500000000000000000000 : ℝ)*base89 + (18855373/2500000000000000000000 : ℝ)*base91 + (18855373/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1284_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152447821/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8177/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1889/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5311/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15077/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1284_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1284_s4_0 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2094700251/10000000000 : ℝ)*x 0 + (1083910753/2000000000 : ℝ)*x 1 + (5239090183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2094700251/10000000000 : ℝ)^1061 ≤ (1274178318511/10000000000000 : ℝ)^805 := by
    have hnat : (2094700251 : ℕ)^1061*10000000000000^805 ≤ 1274178318511^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2094700251 10000000000 1274178318511 10000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083910753/2000000000 : ℝ)^1061 ≤ (22301323156507/50000000000000 : ℝ)^805 := by
    have hnat : (1083910753 : ℕ)^1061*50000000000000^805 ≤ 22301323156507^805*2000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083910753 2000000000 22301323156507 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5239090183/10000000000 : ℝ)^1061 ≤ (42655570490341/100000000000000 : ℝ)^805 := by
    have hnat : (5239090183 : ℕ)^1061*100000000000000^805 ≤ 42655570490341^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239090183 10000000000 42655570490341 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2094700251/10000000000 : ℝ), (1083910753/2000000000 : ℝ), (5239090183/10000000000 : ℝ)] ![(1274178318511/10000000000000 : ℝ), (22301323156507/50000000000000 : ℝ), (42655570490341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2094700251/10000000000 : ℝ)|^1061 ≤ (1274178318511/10000000000000 : ℝ)^805
        have hw : |(-2094700251/10000000000 : ℝ)|=(2094700251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083910753/2000000000 : ℝ)|^1061 ≤ (22301323156507/50000000000000 : ℝ)^805
        have hw : |(1083910753/2000000000 : ℝ)|=(1083910753/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5239090183/10000000000 : ℝ)|^1061 ≤ (42655570490341/100000000000000 : ℝ)^805
        have hw : |(5239090183/10000000000 : ℝ)|=(5239090183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s4_1 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (167215331/312500000 : ℝ)*x 0 + (-8542089/39062500 : ℝ)*x 1 + (1309772527/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167215331/312500000 : ℝ)^1061 ≤ (21929674854859/50000000000000 : ℝ)^805 := by
    have hnat : (167215331 : ℕ)^1061*50000000000000^805 ≤ 21929674854859^805*312500000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167215331 312500000 21929674854859 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8542089/39062500 : ℝ)^1061 ≤ (2697016118863/20000000000000 : ℝ)^805 := by
    have hnat : (8542089 : ℕ)^1061*20000000000000^805 ≤ 2697016118863^805*39062500^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8542089 39062500 2697016118863 20000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1309772527/2500000000 : ℝ)^1061 ≤ (21327784842759/50000000000000 : ℝ)^805 := by
    have hnat : (1309772527 : ℕ)^1061*50000000000000^805 ≤ 21327784842759^805*2500000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309772527 2500000000 21327784842759 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167215331/312500000 : ℝ), (-8542089/39062500 : ℝ), (1309772527/2500000000 : ℝ)] ![(21929674854859/50000000000000 : ℝ), (2697016118863/20000000000000 : ℝ), (21327784842759/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167215331/312500000 : ℝ)|^1061 ≤ (21929674854859/50000000000000 : ℝ)^805
        have hw : |(167215331/312500000 : ℝ)|=(167215331/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8542089/39062500 : ℝ)|^1061 ≤ (2697016118863/20000000000000 : ℝ)^805
        have hw : |(-8542089/39062500 : ℝ)|=(8542089/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1309772527/2500000000 : ℝ)|^1061 ≤ (21327784842759/50000000000000 : ℝ)^805
        have hw : |(1309772527/2500000000 : ℝ)|=(1309772527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s4_2 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5350890679/10000000000 : ℝ)*x 0 + (1047817987/2000000000 : ℝ)*x 1 + (-136673431/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350890679/10000000000 : ℝ)^1061 ≤ (43859350649603/100000000000000 : ℝ)^805 := by
    have hnat : (5350890679 : ℕ)^1061*100000000000000^805 ≤ 43859350649603^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350890679 10000000000 43859350649603 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1047817987/2000000000 : ℝ)^1061 ≤ (21327783914529/50000000000000 : ℝ)^805 := by
    have hnat : (1047817987 : ℕ)^1061*50000000000000^805 ≤ 21327783914529^805*2000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047817987 2000000000 21327783914529 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (136673431/625000000 : ℝ)^1061 ≤ (674254075231/5000000000000 : ℝ)^805 := by
    have hnat : (136673431 : ℕ)^1061*5000000000000^805 ≤ 674254075231^805*625000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136673431 625000000 674254075231 5000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350890679/10000000000 : ℝ), (1047817987/2000000000 : ℝ), (-136673431/625000000 : ℝ)] ![(43859350649603/100000000000000 : ℝ), (21327783914529/50000000000000 : ℝ), (674254075231/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350890679/10000000000 : ℝ)|^1061 ≤ (43859350649603/100000000000000 : ℝ)^805
        have hw : |(5350890679/10000000000 : ℝ)|=(5350890679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1047817987/2000000000 : ℝ)|^1061 ≤ (21327783914529/50000000000000 : ℝ)^805
        have hw : |(1047817987/2000000000 : ℝ)|=(1047817987/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-136673431/625000000 : ℝ)|^1061 ≤ (674254075231/5000000000000 : ℝ)^805
        have hw : |(-136673431/625000000 : ℝ)|=(136673431/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s4_3 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2170872623/5000000000 : ℝ)*x 0 + (4160639711/10000000000 : ℝ)*x 1 + (2265201073/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2170872623/5000000000 : ℝ)^1061 ≤ (8324863175699/25000000000000 : ℝ)^805 := by
    have hnat : (2170872623 : ℕ)^1061*25000000000000^805 ≤ 8324863175699^805*5000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170872623 5000000000 8324863175699 25000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4160639711/10000000000 : ℝ)^1061 ≤ (3148098365459/10000000000000 : ℝ)^805 := by
    have hnat : (4160639711 : ℕ)^1061*10000000000000^805 ≤ 3148098365459^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4160639711 10000000000 3148098365459 10000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2265201073/5000000000 : ℝ)^1061 ≤ (3521956361903/10000000000000 : ℝ)^805 := by
    have hnat : (2265201073 : ℕ)^1061*10000000000000^805 ≤ 3521956361903^805*5000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2265201073 5000000000 3521956361903 10000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2170872623/5000000000 : ℝ), (4160639711/10000000000 : ℝ), (2265201073/5000000000 : ℝ)] ![(8324863175699/25000000000000 : ℝ), (3148098365459/10000000000000 : ℝ), (3521956361903/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2170872623/5000000000 : ℝ)|^1061 ≤ (8324863175699/25000000000000 : ℝ)^805
        have hw : |(2170872623/5000000000 : ℝ)|=(2170872623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4160639711/10000000000 : ℝ)|^1061 ≤ (3148098365459/10000000000000 : ℝ)^805
        have hw : |(4160639711/10000000000 : ℝ)|=(4160639711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2265201073/5000000000 : ℝ)|^1061 ≤ (3521956361903/10000000000000 : ℝ)^805
        have hw : |(2265201073/5000000000 : ℝ)|=(2265201073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s4_4 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-4189429/20000000 : ℝ)*x 0 + (1047952201/2000000000 : ℝ)*x 1 + (541887957/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4189429/20000000 : ℝ)^1061 ≤ (12741897423661/100000000000000 : ℝ)^805 := by
    have hnat : (4189429 : ℕ)^1061*100000000000000^805 ≤ 12741897423661^805*20000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4189429 20000000 12741897423661 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1047952201/2000000000 : ℝ)^1061 ≤ (21331384607169/50000000000000 : ℝ)^805 := by
    have hnat : (1047952201 : ℕ)^1061*50000000000000^805 ≤ 21331384607169^805*2000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047952201 2000000000 21331384607169 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541887957/1000000000 : ℝ)^1061 ≤ (44595333347297/100000000000000 : ℝ)^805 := by
    have hnat : (541887957 : ℕ)^1061*100000000000000^805 ≤ 44595333347297^805*1000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541887957 1000000000 44595333347297 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4189429/20000000 : ℝ), (1047952201/2000000000 : ℝ), (541887957/1000000000 : ℝ)] ![(12741897423661/100000000000000 : ℝ), (21331384607169/50000000000000 : ℝ), (44595333347297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4189429/20000000 : ℝ)|^1061 ≤ (12741897423661/100000000000000 : ℝ)^805
        have hw : |(-4189429/20000000 : ℝ)|=(4189429/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1047952201/2000000000 : ℝ)|^1061 ≤ (21331384607169/50000000000000 : ℝ)^805
        have hw : |(1047952201/2000000000 : ℝ)|=(1047952201/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541887957/1000000000 : ℝ)|^1061 ≤ (44595333347297/100000000000000 : ℝ)^805
        have hw : |(541887957/1000000000 : ℝ)|=(541887957/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s4_5 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5304734187/10000000000 : ℝ)*x 0 + (-25087317/125000000 : ℝ)*x 1 + (169339979/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304734187/10000000000 : ℝ)^1061 ≤ (43361394425781/100000000000000 : ℝ)^805 := by
    have hnat : (5304734187 : ℕ)^1061*100000000000000^805 ≤ 43361394425781^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304734187 10000000000 43361394425781 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (25087317/125000000 : ℝ)^1061 ≤ (602163742007/5000000000000 : ℝ)^805 := by
    have hnat : (25087317 : ℕ)^1061*5000000000000^805 ≤ 602163742007^805*125000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25087317 125000000 602163742007 5000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169339979/312500000 : ℝ)^1061 ≤ (8919066144477/20000000000000 : ℝ)^805 := by
    have hnat : (169339979 : ℕ)^1061*20000000000000^805 ≤ 8919066144477^805*312500000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169339979 312500000 8919066144477 20000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304734187/10000000000 : ℝ), (-25087317/125000000 : ℝ), (169339979/312500000 : ℝ)] ![(43361394425781/100000000000000 : ℝ), (602163742007/5000000000000 : ℝ), (8919066144477/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304734187/10000000000 : ℝ)|^1061 ≤ (43361394425781/100000000000000 : ℝ)^805
        have hw : |(5304734187/10000000000 : ℝ)|=(5304734187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-25087317/125000000 : ℝ)|^1061 ≤ (602163742007/5000000000000 : ℝ)^805
        have hw : |(-25087317/125000000 : ℝ)|=(25087317/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169339979/312500000 : ℝ)|^1061 ≤ (8919066144477/20000000000000 : ℝ)^805
        have hw : |(169339979/312500000 : ℝ)|=(169339979/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s4_6 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2652367227/5000000000 : ℝ)*x 0 + (1354719909/2500000000 : ℝ)*x 1 + (-2006984573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652367227/5000000000 : ℝ)^1061 ≤ (43361397302321/100000000000000 : ℝ)^805 := by
    have hnat : (2652367227 : ℕ)^1061*100000000000000^805 ≤ 43361397302321^805*5000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652367227 5000000000 43361397302321 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1354719909/2500000000 : ℝ)^1061 ≤ (22297667031591/50000000000000 : ℝ)^805 := by
    have hnat : (1354719909 : ℕ)^1061*50000000000000^805 ≤ 22297667031591^805*2500000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354719909 2500000000 22297667031591 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2006984573/10000000000 : ℝ)^1061 ≤ (12043268615781/100000000000000 : ℝ)^805 := by
    have hnat : (2006984573 : ℕ)^1061*100000000000000^805 ≤ 12043268615781^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2006984573 10000000000 12043268615781 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652367227/5000000000 : ℝ), (1354719909/2500000000 : ℝ), (-2006984573/10000000000 : ℝ)] ![(43361397302321/100000000000000 : ℝ), (22297667031591/50000000000000 : ℝ), (12043268615781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652367227/5000000000 : ℝ)|^1061 ≤ (43361397302321/100000000000000 : ℝ)^805
        have hw : |(2652367227/5000000000 : ℝ)|=(2652367227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1354719909/2500000000 : ℝ)|^1061 ≤ (22297667031591/50000000000000 : ℝ)^805
        have hw : |(1354719909/2500000000 : ℝ)|=(1354719909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2006984573/10000000000 : ℝ)|^1061 ≤ (12043268615781/100000000000000 : ℝ)^805
        have hw : |(-2006984573/10000000000 : ℝ)|=(2006984573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s4_7 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1085443639/2500000000 : ℝ)*x 0 + (4529028683/10000000000 : ℝ)*x 1 + (4162021021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1085443639/2500000000 : ℝ)^1061 ≤ (33299748987033/100000000000000 : ℝ)^805 := by
    have hnat : (1085443639 : ℕ)^1061*100000000000000^805 ≤ 33299748987033^805*2500000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085443639 2500000000 33299748987033 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4529028683/10000000000 : ℝ)^1061 ≤ (35205491394789/100000000000000 : ℝ)^805 := by
    have hnat : (4529028683 : ℕ)^1061*100000000000000^805 ≤ 35205491394789^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4529028683 10000000000 35205491394789 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4162021021/10000000000 : ℝ)^1061 ≤ (3149475961123/10000000000000 : ℝ)^805 := by
    have hnat : (4162021021 : ℕ)^1061*10000000000000^805 ≤ 3149475961123^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4162021021 10000000000 3149475961123 10000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1085443639/2500000000 : ℝ), (4529028683/10000000000 : ℝ), (4162021021/10000000000 : ℝ)] ![(33299748987033/100000000000000 : ℝ), (35205491394789/100000000000000 : ℝ), (3149475961123/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1085443639/2500000000 : ℝ)|^1061 ≤ (33299748987033/100000000000000 : ℝ)^805
        have hw : |(1085443639/2500000000 : ℝ)|=(1085443639/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4529028683/10000000000 : ℝ)|^1061 ≤ (35205491394789/100000000000000 : ℝ)^805
        have hw : |(4529028683/10000000000 : ℝ)|=(4529028683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4162021021/10000000000 : ℝ)|^1061 ≤ (3149475961123/10000000000000 : ℝ)^805
        have hw : |(4162021021/10000000000 : ℝ)|=(4162021021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1284_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152447821/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15077/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5311/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1093/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14749/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15077/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5311/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15077/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5311/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15077/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5311/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15077/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5311/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15077/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5311/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15077/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5311/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5311/50000 : ℝ) ^ (4243/1024 : ℝ) ≤ (18452810987727/200000000000000000 : ℝ) := by
    have hpowers : (5311/50000 : ℝ)^4243 ≤ (18452810987727/200000000000000000 : ℝ)^1024 := by
      have hnat : (5311 : ℕ)^4243*200000000000000000^1024 ≤ 18452810987727^1024*50000^4243 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5311 50000 18452810987727 200000000000000000 4243 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5311/50000 : ℝ)) (X := (18452810987727/200000000000000000 : ℝ)) (by norm_num) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15077/100000 : ℝ) ^ (4243/1024 : ℝ) ≤ (39382474146360541/100000000000000000000 : ℝ) := by
    have hpowers : (15077/100000 : ℝ)^4243 ≤ (39382474146360541/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15077 : ℕ)^4243*100000000000000000000^1024 ≤ 39382474146360541^1024*100000^4243 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15077 100000 39382474146360541 100000000000000000000 4243 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15077/100000 : ℝ)) (X := (39382474146360541/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (100018452810987727/100000000000000000 : ℝ) ≤ (10000445306527233/10000000000000000 : ℝ) ^ (4243/1024 : ℝ) := by
    have hpowers : (100018452810987727/100000000000000000 : ℝ)^1024 ≤ (10000445306527233/10000000000000000 : ℝ)^4243 := by
      have hnat : (100018452810987727 : ℕ)^1024*10000000000000000^4243 ≤ 10000445306527233^4243*100000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100018452810987727 100000000000000000 10000445306527233 10000000000000000 1024 4243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000445306527233/10000000000000000 : ℝ)) (X := (100018452810987727/100000000000000000 : ℝ)) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048608879640224041/100000000000000000000 : ℝ) ≤ (10001172904014691/10000000000000000 : ℝ) ^ (4243/1024 : ℝ) := by
    have hpowers : (100048608879640224041/100000000000000000000 : ℝ)^1024 ≤ (10001172904014691/10000000000000000 : ℝ)^4243 := by
      have hnat : (100048608879640224041 : ℕ)^1024*10000000000000000^4243 ≤ 10001172904014691^4243*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048608879640224041 100000000000000000000 10001172904014691 10000000000000000 1024 4243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001172904014691/10000000000000000 : ℝ)) (X := (100048608879640224041/100000000000000000000 : ℝ)) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50039382474146360541/50000000000000000000 : ℝ) ≤ (10001900501502149/10000000000000000 : ℝ) ^ (4243/1024 : ℝ) := by
    have hpowers : (50039382474146360541/50000000000000000000 : ℝ)^1024 ≤ (10001900501502149/10000000000000000 : ℝ)^4243 := by
      have hnat : (50039382474146360541 : ℕ)^1024*10000000000000000^4243 ≤ 10001900501502149^4243*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50039382474146360541 50000000000000000000 10001900501502149 10000000000000000 1024 4243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001900501502149/10000000000000000 : ℝ)) (X := (50039382474146360541/50000000000000000000 : ℝ)) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(18452810987727/200000000000000000 : ℝ) ≤ ((44536526759555265263/44550000000000000000 : ℝ)+2*(363798743729/222750000000000 : ℝ)*(5311/50000 : ℝ))^(4243/1024 : ℝ) := by
    rw [show (44536526759555265263/44550000000000000000 : ℝ)+2*(363798743729/222750000000000 : ℝ)*(5311/50000 : ℝ)=(10000445306527233/10000000000000000 : ℝ) by norm_num, show 1+2*(18452810987727/200000000000000000 : ℝ)=(100018452810987727/100000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(39382474146360541/100000000000000000000 : ℝ)+(18452810987727/200000000000000000 : ℝ) ≤ ((44536526759555265263/44550000000000000000 : ℝ)+(363798743729/222750000000000 : ℝ)*((15077/100000 : ℝ)+(5311/50000 : ℝ)))^(4243/1024 : ℝ) := by
    rw [show (44536526759555265263/44550000000000000000 : ℝ)+(363798743729/222750000000000 : ℝ)*((15077/100000 : ℝ)+(5311/50000 : ℝ))=(10001172904014691/10000000000000000 : ℝ) by norm_num, show 1+(39382474146360541/100000000000000000000 : ℝ)+(18452810987727/200000000000000000 : ℝ)=(100048608879640224041/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(39382474146360541/100000000000000000000 : ℝ) ≤ ((44536526759555265263/44550000000000000000 : ℝ)+2*(363798743729/222750000000000 : ℝ)*(15077/100000 : ℝ))^(4243/1024 : ℝ) := by
    rw [show (44536526759555265263/44550000000000000000 : ℝ)+2*(363798743729/222750000000000 : ℝ)*(15077/100000 : ℝ)=(10001900501502149/10000000000000000 : ℝ) by norm_num, show 1+2*(39382474146360541/100000000000000000000 : ℝ)=(50039382474146360541/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (44536526759555265263/44550000000000000000 : ℝ)*(X 1 0+X 2 0)+(363798743729/222750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4243/1024 : ℝ)) (lo := (5311/50000 : ℝ)) (hi := (15077/100000 : ℝ)) (c := (44536526759555265263/44550000000000000000 : ℝ)) (alpha := (363798743729/222750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (44536526759555265263/44550000000000000000 : ℝ)*(X 0 1+X 2 1)+(363798743729/222750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4243/1024 : ℝ)) (lo := (5311/50000 : ℝ)) (hi := (15077/100000 : ℝ)) (c := (44536526759555265263/44550000000000000000 : ℝ)) (alpha := (363798743729/222750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (44536526759555265263/44550000000000000000 : ℝ)*(X 0 2+X 1 2)+(363798743729/222750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4243/1024 : ℝ)) (lo := (5311/50000 : ℝ)) (hi := (15077/100000 : ℝ)) (c := (44536526759555265263/44550000000000000000 : ℝ)) (alpha := (363798743729/222750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2094700251/10000000000 : ℝ)*X 0 0+(1083910753/2000000000 : ℝ)*X 0 1+(5239090183/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167215331/312500000 : ℝ)*X 1 0+(-8542089/39062500 : ℝ)*X 1 1+(1309772527/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350890679/10000000000 : ℝ)*X 2 0+(1047817987/2000000000 : ℝ)*X 2 1+(-136673431/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2170872623/5000000000 : ℝ)*X 0 0+(4160639711/10000000000 : ℝ)*X 0 1+(2265201073/5000000000 : ℝ)*X 0 2+(2170872623/5000000000 : ℝ)*X 1 0+(4160639711/10000000000 : ℝ)*X 1 1+(2265201073/5000000000 : ℝ)*X 1 2+(2170872623/5000000000 : ℝ)*X 2 0+(4160639711/10000000000 : ℝ)*X 2 1+(2265201073/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-4189429/20000000 : ℝ)*X 0 0+(1047952201/2000000000 : ℝ)*X 0 1+(541887957/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5304734187/10000000000 : ℝ)*X 1 0+(-25087317/125000000 : ℝ)*X 1 1+(169339979/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652367227/5000000000 : ℝ)*X 2 0+(1354719909/2500000000 : ℝ)*X 2 1+(-2006984573/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1085443639/2500000000 : ℝ)*X 0 0+(4529028683/10000000000 : ℝ)*X 0 1+(4162021021/10000000000 : ℝ)*X 0 2+(1085443639/2500000000 : ℝ)*X 1 0+(4529028683/10000000000 : ℝ)*X 1 1+(4162021021/10000000000 : ℝ)*X 1 2+(1085443639/2500000000 : ℝ)*X 2 0+(4529028683/10000000000 : ℝ)*X 2 1+(4162021021/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (119272880829165837064662863/30937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1254447391/100000000000000 : ℝ)*(base19) + (1238758227/100000000000000 : ℝ)*(base23) + (255990439/100000000000000 : ℝ)*(upper3) + (3537787/6250000000000 : ℝ)*(upper4) + (3361931/5000000000000 : ℝ)*(upper5) + (515361443054397/12500000000000 : ℝ)*(major0) + (515361443054397/12500000000000 : ℝ)*(major1) + (515361443054397/12500000000000 : ℝ)*(major2) + (2770652750871563/50000000000000 : ℝ)*(sp0) + (2770660457864633/50000000000000 : ℝ)*(sp1) + (554132093141843/10000000000000 : ℝ)*(sp2) + (1352224124667881/50000000000000 : ℝ)*(sp3) + (4167108383/25000000000000 : ℝ)*(sp4) + (6270424213/50000000000000 : ℝ)*(sp7) + (676115197546047/25000000000000 : ℝ)*(f.failure) + (5541322170176657/100000000000000 : ℝ)*(f.sum) + (12691732609343/3712500000000000000000000000 : ℝ)*base65 + (160310168597237621/61875000000000000000000000000000 : ℝ)*base68 + (506986184780987621/61875000000000000000000000000000 : ℝ)*base70 + (218595935146512379/61875000000000000000000000000000 : ℝ)*base71 + (8791892380691/1856250000000000000000000000 : ℝ)*base74 + (245746242987762379/61875000000000000000000000000000 : ℝ)*base75 + (151934996832762379/61875000000000000000000000000000 : ℝ)*base77 + (835734214527762379/61875000000000000000000000000000 : ℝ)*base79 + (1363707879307/3712500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (12313587/2500000000000000000000 : ℝ)*base89 + (12313587/2500000000000000000000 : ℝ)*base91 + (12313587/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1013091527535379485061731229/123750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (394331579/20000000000000 : ℝ)*(base19) + (1269376133/50000000000000 : ℝ)*(base23) + (19473887/10000000000000 : ℝ)*(upper3) + (4167541/100000000000000 : ℝ)*(lower4) + (4153820218923351/100000000000000 : ℝ)*(major0) + (4153820218923351/100000000000000 : ℝ)*(major1) + (4153820218923351/100000000000000 : ℝ)*(major2) + (637852963/2000000000000 : ℝ)*(sp1) + (7983831437/12500000000000 : ℝ)*(sp2) + (2670704291/100000000000000 : ℝ)*(sp3) + (1395722833762103/25000000000000 : ℝ)*(sp4) + (174464295960699/3125000000000 : ℝ)*(sp5) + (111656498512893/2000000000000 : ℝ)*(sp6) + (681186539801847/25000000000000 : ℝ)*(sp7) + (2724748829911679/100000000000000 : ℝ)*(f.failure) + (1395722833762103/25000000000000 : ℝ)*(f.sum) + (230288389973/232031250000000000000000000 : ℝ)*base65 + (2330911624463406257/495000000000000000000000000000000 : ℝ)*base67 + (1997147722508406257/495000000000000000000000000000000 : ℝ)*base69 + (395052771788406257/495000000000000000000000000000000 : ℝ)*base71 + (11007987009961/7425000000000000000000000000 : ℝ)*base73 + (2265161679171593743/495000000000000000000000000000000 : ℝ)*base76 + (3850431324128406257/495000000000000000000000000000000 : ℝ)*base77 + (519772904963406257/495000000000000000000000000000000 : ℝ)*base79 + (534220470907/3712500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (13998541/10000000000000000000000 : ℝ)*base90 + (13998541/10000000000000000000000 : ℝ)*base92 + (13998541/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1284_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152447821/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15077/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5311/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1093/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1284_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1284_s5_0 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-209507871/1000000000 : ℝ)*x 0 + (2708173533/5000000000 : ℝ)*x 1 + (327628017/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (209507871/1000000000 : ℝ)^1061 ≤ (12744817489483/100000000000000 : ℝ)^805 := by
    have hnat : (209507871 : ℕ)^1061*100000000000000^805 ≤ 12744817489483^805*1000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209507871 1000000000 12744817489483 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2708173533/5000000000 : ℝ)^1061 ≤ (44567865964427/100000000000000 : ℝ)^805 := by
    have hnat : (2708173533 : ℕ)^1061*100000000000000^805 ≤ 44567865964427^805*5000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708173533 5000000000 44567865964427 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327628017/625000000 : ℝ)^1061 ≤ (42687316533607/100000000000000 : ℝ)^805 := by
    have hnat : (327628017 : ℕ)^1061*100000000000000^805 ≤ 42687316533607^805*625000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327628017 625000000 42687316533607 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-209507871/1000000000 : ℝ), (2708173533/5000000000 : ℝ), (327628017/625000000 : ℝ)] ![(12744817489483/100000000000000 : ℝ), (44567865964427/100000000000000 : ℝ), (42687316533607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-209507871/1000000000 : ℝ)|^1061 ≤ (12744817489483/100000000000000 : ℝ)^805
        have hw : |(-209507871/1000000000 : ℝ)|=(209507871/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2708173533/5000000000 : ℝ)|^1061 ≤ (44567865964427/100000000000000 : ℝ)^805
        have hw : |(2708173533/5000000000 : ℝ)|=(2708173533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(327628017/625000000 : ℝ)|^1061 ≤ (42687316533607/100000000000000 : ℝ)^805
        have hw : |(327628017/625000000 : ℝ)|=(327628017/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s5_1 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2675039321/5000000000 : ℝ)*x 0 + (-436789469/2000000000 : ℝ)*x 1 + (2621024163/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675039321/5000000000 : ℝ)^1061 ≤ (5481322274801/12500000000000 : ℝ)^805 := by
    have hnat : (2675039321 : ℕ)^1061*12500000000000^805 ≤ 5481322274801^805*5000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675039321 5000000000 5481322274801 12500000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (436789469/2000000000 : ℝ)^1061 ≤ (2692420934821/20000000000000 : ℝ)^805 := by
    have hnat : (436789469 : ℕ)^1061*20000000000000^805 ≤ 2692420934821^805*2000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436789469 2000000000 2692420934821 20000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621024163/5000000000 : ℝ)^1061 ≤ (1333978659787/3125000000000 : ℝ)^805 := by
    have hnat : (2621024163 : ℕ)^1061*3125000000000^805 ≤ 1333978659787^805*5000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621024163 5000000000 1333978659787 3125000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675039321/5000000000 : ℝ), (-436789469/2000000000 : ℝ), (2621024163/5000000000 : ℝ)] ![(5481322274801/12500000000000 : ℝ), (2692420934821/20000000000000 : ℝ), (1333978659787/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675039321/5000000000 : ℝ)|^1061 ≤ (5481322274801/12500000000000 : ℝ)^805
        have hw : |(2675039321/5000000000 : ℝ)|=(2675039321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-436789469/2000000000 : ℝ)|^1061 ≤ (2692420934821/20000000000000 : ℝ)^805
        have hw : |(-436789469/2000000000 : ℝ)|=(436789469/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621024163/5000000000 : ℝ)|^1061 ≤ (1333978659787/3125000000000 : ℝ)^805
        have hw : |(2621024163/5000000000 : ℝ)|=(2621024163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s5_2 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5350078747/10000000000 : ℝ)*x 0 + (655256047/1250000000 : ℝ)*x 1 + (-109197357/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350078747/10000000000 : ℝ)^1061 ≤ (21925289666349/50000000000000 : ℝ)^805 := by
    have hnat : (5350078747 : ℕ)^1061*50000000000000^805 ≤ 21925289666349^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350078747 10000000000 21925289666349 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655256047/1250000000 : ℝ)^1061 ≤ (42687317649829/100000000000000 : ℝ)^805 := by
    have hnat : (655256047 : ℕ)^1061*100000000000000^805 ≤ 42687317649829^805*1250000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655256047 1250000000 42687317649829 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (109197357/500000000 : ℝ)^1061 ≤ (13462103008607/100000000000000 : ℝ)^805 := by
    have hnat : (109197357 : ℕ)^1061*100000000000000^805 ≤ 13462103008607^805*500000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109197357 500000000 13462103008607 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350078747/10000000000 : ℝ), (655256047/1250000000 : ℝ), (-109197357/500000000 : ℝ)] ![(21925289666349/50000000000000 : ℝ), (42687317649829/100000000000000 : ℝ), (13462103008607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350078747/10000000000 : ℝ)|^1061 ≤ (21925289666349/50000000000000 : ℝ)^805
        have hw : |(5350078747/10000000000 : ℝ)|=(5350078747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655256047/1250000000 : ℝ)|^1061 ≤ (42687317649829/100000000000000 : ℝ)^805
        have hw : |(655256047/1250000000 : ℝ)|=(655256047/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-109197357/500000000 : ℝ)|^1061 ≤ (13462103008607/100000000000000 : ℝ)^805
        have hw : |(-109197357/500000000 : ℝ)|=(109197357/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s5_3 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (542746373/1250000000 : ℝ)*x 0 + (833385229/2000000000 : ℝ)*x 1 + (1131014513/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542746373/1250000000 : ℝ)^1061 ≤ (266413876987/800000000000 : ℝ)^805 := by
    have hnat : (542746373 : ℕ)^1061*800000000000^805 ≤ 266413876987^805*1250000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542746373 1250000000 266413876987 800000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (833385229/2000000000 : ℝ)^1061 ≤ (15771845349937/50000000000000 : ℝ)^805 := by
    have hnat : (833385229 : ℕ)^1061*50000000000000^805 ≤ 15771845349937^805*2000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833385229 2000000000 15771845349937 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1131014513/2500000000 : ℝ)^1061 ≤ (8788643664783/25000000000000 : ℝ)^805 := by
    have hnat : (1131014513 : ℕ)^1061*25000000000000^805 ≤ 8788643664783^805*2500000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131014513 2500000000 8788643664783 25000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(542746373/1250000000 : ℝ), (833385229/2000000000 : ℝ), (1131014513/2500000000 : ℝ)] ![(266413876987/800000000000 : ℝ), (15771845349937/50000000000000 : ℝ), (8788643664783/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(542746373/1250000000 : ℝ)|^1061 ≤ (266413876987/800000000000 : ℝ)^805
        have hw : |(542746373/1250000000 : ℝ)|=(542746373/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(833385229/2000000000 : ℝ)|^1061 ≤ (15771845349937/50000000000000 : ℝ)^805
        have hw : |(833385229/2000000000 : ℝ)|=(833385229/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1131014513/2500000000 : ℝ)|^1061 ≤ (8788643664783/25000000000000 : ℝ)^805
        have hw : |(1131014513/2500000000 : ℝ)|=(1131014513/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s5_4 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1047545681/5000000000 : ℝ)*x 0 + (5242673887/10000000000 : ℝ)*x 1 + (1353929637/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1047545681/5000000000 : ℝ)^1061 ≤ (12744918930217/100000000000000 : ℝ)^805 := by
    have hnat : (1047545681 : ℕ)^1061*100000000000000^805 ≤ 12744918930217^805*5000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047545681 5000000000 12744918930217 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242673887/10000000000 : ℝ)^1061 ≤ (21347015664133/50000000000000 : ℝ)^805 := by
    have hnat : (5242673887 : ℕ)^1061*50000000000000^805 ≤ 21347015664133^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242673887 10000000000 21347015664133 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353929637/2500000000 : ℝ)^1061 ≤ (11140262432321/25000000000000 : ℝ)^805 := by
    have hnat : (1353929637 : ℕ)^1061*25000000000000^805 ≤ 11140262432321^805*2500000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353929637 2500000000 11140262432321 25000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1047545681/5000000000 : ℝ), (5242673887/10000000000 : ℝ), (1353929637/2500000000 : ℝ)] ![(12744918930217/100000000000000 : ℝ), (21347015664133/50000000000000 : ℝ), (11140262432321/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1047545681/5000000000 : ℝ)|^1061 ≤ (12744918930217/100000000000000 : ℝ)^805
        have hw : |(-1047545681/5000000000 : ℝ)|=(1047545681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242673887/10000000000 : ℝ)|^1061 ≤ (21347015664133/50000000000000 : ℝ)^805
        have hw : |(5242673887/10000000000 : ℝ)|=(5242673887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353929637/2500000000 : ℝ)|^1061 ≤ (11140262432321/25000000000000 : ℝ)^805
        have hw : |(1353929637/2500000000 : ℝ)|=(1353929637/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s5_5 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1326374811/2500000000 : ℝ)*x 0 + (-2010276739/10000000000 : ℝ)*x 1 + (676964821/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326374811/2500000000 : ℝ)^1061 ≤ (21684818500021/50000000000000 : ℝ)^805 := by
    have hnat : (1326374811 : ℕ)^1061*50000000000000^805 ≤ 21684818500021^805*2500000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326374811 2500000000 21684818500021 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2010276739/10000000000 : ℝ)^1061 ≤ (603465652077/5000000000000 : ℝ)^805 := by
    have hnat : (2010276739 : ℕ)^1061*5000000000000^805 ≤ 603465652077^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010276739 10000000000 603465652077 5000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676964821/1250000000 : ℝ)^1061 ≤ (22280524973089/50000000000000 : ℝ)^805 := by
    have hnat : (676964821 : ℕ)^1061*50000000000000^805 ≤ 22280524973089^805*1250000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676964821 1250000000 22280524973089 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326374811/2500000000 : ℝ), (-2010276739/10000000000 : ℝ), (676964821/1250000000 : ℝ)] ![(21684818500021/50000000000000 : ℝ), (603465652077/5000000000000 : ℝ), (22280524973089/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326374811/2500000000 : ℝ)|^1061 ≤ (21684818500021/50000000000000 : ℝ)^805
        have hw : |(1326374811/2500000000 : ℝ)|=(1326374811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2010276739/10000000000 : ℝ)|^1061 ≤ (603465652077/5000000000000 : ℝ)^805
        have hw : |(-2010276739/10000000000 : ℝ)|=(2010276739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676964821/1250000000 : ℝ)|^1061 ≤ (22280524973089/50000000000000 : ℝ)^805
        have hw : |(676964821/1250000000 : ℝ)|=(676964821/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s5_6 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305499249/10000000000 : ℝ)*x 0 + (1083143711/2000000000 : ℝ)*x 1 + (-8041107/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305499249/10000000000 : ℝ)^1061 ≤ (5421204631739/12500000000000 : ℝ)^805 := by
    have hnat : (5305499249 : ℕ)^1061*12500000000000^805 ≤ 5421204631739^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305499249 10000000000 5421204631739 12500000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083143711/2000000000 : ℝ)^1061 ≤ (44561049805197/100000000000000 : ℝ)^805 := by
    have hnat : (1083143711 : ℕ)^1061*100000000000000^805 ≤ 44561049805197^805*2000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083143711 2000000000 44561049805197 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8041107/40000000 : ℝ)^1061 ≤ (1508664141073/12500000000000 : ℝ)^805 := by
    have hnat : (8041107 : ℕ)^1061*12500000000000^805 ≤ 1508664141073^805*40000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8041107 40000000 1508664141073 12500000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305499249/10000000000 : ℝ), (1083143711/2000000000 : ℝ), (-8041107/40000000 : ℝ)] ![(5421204631739/12500000000000 : ℝ), (44561049805197/100000000000000 : ℝ), (1508664141073/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305499249/10000000000 : ℝ)|^1061 ≤ (5421204631739/12500000000000 : ℝ)^805
        have hw : |(5305499249/10000000000 : ℝ)|=(5305499249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083143711/2000000000 : ℝ)|^1061 ≤ (44561049805197/100000000000000 : ℝ)^805
        have hw : |(1083143711/2000000000 : ℝ)|=(1083143711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8041107/40000000 : ℝ)|^1061 ≤ (1508664141073/12500000000000 : ℝ)^805
        have hw : |(-8041107/40000000 : ℝ)|=(8041107/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_s5_7 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4341996879/10000000000 : ℝ)*x 0 + (1130694093/2500000000 : ℝ)*x 1 + (166728617/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4341996879/10000000000 : ℝ)^1061 ≤ (16650998195451/50000000000000 : ℝ)^805 := by
    have hnat : (4341996879 : ℕ)^1061*50000000000000^805 ≤ 16650998195451^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4341996879 10000000000 16650998195451 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1130694093/2500000000 : ℝ)^1061 ≤ (35141448634219/100000000000000 : ℝ)^805 := by
    have hnat : (1130694093 : ℕ)^1061*100000000000000^805 ≤ 35141448634219^805*2500000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130694093 2500000000 35141448634219 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (166728617/400000000 : ℝ)^1061 ≤ (7889138740021/25000000000000 : ℝ)^805 := by
    have hnat : (166728617 : ℕ)^1061*25000000000000^805 ≤ 7889138740021^805*400000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166728617 400000000 7889138740021 25000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4341996879/10000000000 : ℝ), (1130694093/2500000000 : ℝ), (166728617/400000000 : ℝ)] ![(16650998195451/50000000000000 : ℝ), (35141448634219/100000000000000 : ℝ), (7889138740021/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4341996879/10000000000 : ℝ)|^1061 ≤ (16650998195451/50000000000000 : ℝ)^805
        have hw : |(4341996879/10000000000 : ℝ)|=(4341996879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1130694093/2500000000 : ℝ)|^1061 ≤ (35141448634219/100000000000000 : ℝ)^805
        have hw : |(1130694093/2500000000 : ℝ)|=(1130694093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(166728617/400000000 : ℝ)|^1061 ≤ (7889138740021/25000000000000 : ℝ)^805
        have hw : |(166728617/400000000 : ℝ)|=(166728617/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1284_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152447821/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1093/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (10993/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7341/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14749/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1093/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14749/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1093/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14749/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1093/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14749/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1093/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14749/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1093/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14749/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1093/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1093/10000 : ℝ) ^ (4243/1024 : ℝ) ≤ (10386520092533271/100000000000000000000 : ℝ) := by
    have hpowers : (1093/10000 : ℝ)^4243 ≤ (10386520092533271/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1093 : ℕ)^4243*100000000000000000000^1024 ≤ 10386520092533271^1024*10000^4243 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1093 10000 10386520092533271 100000000000000000000 4243 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1093/10000 : ℝ)) (X := (10386520092533271/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14749/100000 : ℝ) ^ (4243/1024 : ℝ) ≤ (35951935323677569/100000000000000000000 : ℝ) := by
    have hpowers : (14749/100000 : ℝ)^4243 ≤ (35951935323677569/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14749 : ℕ)^4243*100000000000000000000^1024 ≤ 35951935323677569^1024*100000^4243 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14749 100000 35951935323677569 100000000000000000000 4243 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14749/100000 : ℝ)) (X := (35951935323677569/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010386520092533271/50000000000000000000 : ℝ) ≤ (10000501294300819/10000000000000000 : ℝ) ^ (4243/1024 : ℝ) := by
    have hpowers : (50010386520092533271/50000000000000000000 : ℝ)^1024 ≤ (10000501294300819/10000000000000000 : ℝ)^4243 := by
      have hnat : (50010386520092533271 : ℕ)^1024*10000000000000000^4243 ≤ 10000501294300819^4243*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010386520092533271 50000000000000000000 10000501294300819 10000000000000000 1024 4243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000501294300819/10000000000000000 : ℝ)) (X := (50010386520092533271/50000000000000000000 : ℝ)) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2501158461385405271/2500000000000000000 : ℝ) ≤ (5000559064811923/5000000000000000 : ℝ) ^ (4243/1024 : ℝ) := by
    have hpowers : (2501158461385405271/2500000000000000000 : ℝ)^1024 ≤ (5000559064811923/5000000000000000 : ℝ)^4243 := by
      have hnat : (2501158461385405271 : ℕ)^1024*5000000000000000^4243 ≤ 5000559064811923^4243*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501158461385405271 2500000000000000000 5000559064811923 5000000000000000 1024 4243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000559064811923/5000000000000000 : ℝ)) (X := (2501158461385405271/2500000000000000000 : ℝ)) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035951935323677569/50000000000000000000 : ℝ) ≤ (10001734964946873/10000000000000000 : ℝ) ^ (4243/1024 : ℝ) := by
    have hpowers : (50035951935323677569/50000000000000000000 : ℝ)^1024 ≤ (10001734964946873/10000000000000000 : ℝ)^4243 := by
      have hnat : (50035951935323677569 : ℕ)^1024*10000000000000000^4243 ≤ 10001734964946873^4243*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035951935323677569 50000000000000000000 10001734964946873 10000000000000000 1024 4243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001734964946873/10000000000000000 : ℝ)) (X := (50035951935323677569/50000000000000000000 : ℝ)) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10386520092533271/100000000000000000000 : ℝ) ≤ ((38178430422773457541/38190000000000000000 : ℝ)+2*(616835323027/381900000000000 : ℝ)*(1093/10000 : ℝ))^(4243/1024 : ℝ) := by
    rw [show (38178430422773457541/38190000000000000000 : ℝ)+2*(616835323027/381900000000000 : ℝ)*(1093/10000 : ℝ)=(10000501294300819/10000000000000000 : ℝ) by norm_num, show 1+2*(10386520092533271/100000000000000000000 : ℝ)=(50010386520092533271/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35951935323677569/100000000000000000000 : ℝ)+(10386520092533271/100000000000000000000 : ℝ) ≤ ((38178430422773457541/38190000000000000000 : ℝ)+(616835323027/381900000000000 : ℝ)*((14749/100000 : ℝ)+(1093/10000 : ℝ)))^(4243/1024 : ℝ) := by
    rw [show (38178430422773457541/38190000000000000000 : ℝ)+(616835323027/381900000000000 : ℝ)*((14749/100000 : ℝ)+(1093/10000 : ℝ))=(5000559064811923/5000000000000000 : ℝ) by norm_num, show 1+(35951935323677569/100000000000000000000 : ℝ)+(10386520092533271/100000000000000000000 : ℝ)=(2501158461385405271/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35951935323677569/100000000000000000000 : ℝ) ≤ ((38178430422773457541/38190000000000000000 : ℝ)+2*(616835323027/381900000000000 : ℝ)*(14749/100000 : ℝ))^(4243/1024 : ℝ) := by
    rw [show (38178430422773457541/38190000000000000000 : ℝ)+2*(616835323027/381900000000000 : ℝ)*(14749/100000 : ℝ)=(10001734964946873/10000000000000000 : ℝ) by norm_num, show 1+2*(35951935323677569/100000000000000000000 : ℝ)=(50035951935323677569/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (38178430422773457541/38190000000000000000 : ℝ)*(X 1 0+X 2 0)+(616835323027/381900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4243/1024 : ℝ)) (lo := (1093/10000 : ℝ)) (hi := (14749/100000 : ℝ)) (c := (38178430422773457541/38190000000000000000 : ℝ)) (alpha := (616835323027/381900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (38178430422773457541/38190000000000000000 : ℝ)*(X 0 1+X 2 1)+(616835323027/381900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4243/1024 : ℝ)) (lo := (1093/10000 : ℝ)) (hi := (14749/100000 : ℝ)) (c := (38178430422773457541/38190000000000000000 : ℝ)) (alpha := (616835323027/381900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (38178430422773457541/38190000000000000000 : ℝ)*(X 0 2+X 1 2)+(616835323027/381900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4243/1024 : ℝ)) (lo := (1093/10000 : ℝ)) (hi := (14749/100000 : ℝ)) (c := (38178430422773457541/38190000000000000000 : ℝ)) (alpha := (616835323027/381900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-209507871/1000000000 : ℝ)*X 0 0+(2708173533/5000000000 : ℝ)*X 0 1+(327628017/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675039321/5000000000 : ℝ)*X 1 0+(-436789469/2000000000 : ℝ)*X 1 1+(2621024163/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350078747/10000000000 : ℝ)*X 2 0+(655256047/1250000000 : ℝ)*X 2 1+(-109197357/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((542746373/1250000000 : ℝ)*X 0 0+(833385229/2000000000 : ℝ)*X 0 1+(1131014513/2500000000 : ℝ)*X 0 2+(542746373/1250000000 : ℝ)*X 1 0+(833385229/2000000000 : ℝ)*X 1 1+(1131014513/2500000000 : ℝ)*X 1 2+(542746373/1250000000 : ℝ)*X 2 0+(833385229/2000000000 : ℝ)*X 2 1+(1131014513/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1047545681/5000000000 : ℝ)*X 0 0+(5242673887/10000000000 : ℝ)*X 0 1+(1353929637/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326374811/2500000000 : ℝ)*X 1 0+(-2010276739/10000000000 : ℝ)*X 1 1+(676964821/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305499249/10000000000 : ℝ)*X 2 0+(1083143711/2000000000 : ℝ)*X 2 1+(-8041107/40000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4341996879/10000000000 : ℝ)*X 0 0+(1130694093/2500000000 : ℝ)*X 0 1+(166728617/400000000 : ℝ)*X 0 2+(4341996879/10000000000 : ℝ)*X 1 0+(1130694093/2500000000 : ℝ)*X 1 1+(166728617/400000000 : ℝ)*X 1 2+(4341996879/10000000000 : ℝ)*X 2 0+(1130694093/2500000000 : ℝ)*X 2 1+(166728617/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1622427046891516084127535153/318250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (747283447/50000000000000 : ℝ)*(base19) + (762550319/50000000000000 : ℝ)*(base23) + (8781207/20000000000000 : ℝ)*(lower2) + (278657949/100000000000000 : ℝ)*(upper3) + (240381587/50000000000000 : ℝ)*(upper5) + (2134359002164333/50000000000000 : ℝ)*(major0) + (2134359002164333/50000000000000 : ℝ)*(major1) + (2134359002164333/50000000000000 : ℝ)*(major2) + (5737291726242123/100000000000000 : ℝ)*(sp0) + (5737316916222959/100000000000000 : ℝ)*(sp1) + (1147463377137843/20000000000000 : ℝ)*(sp2) + (700025669071197/25000000000000 : ℝ)*(sp3) + (26684547731/100000000000000 : ℝ)*(sp4) + (14751650549/100000000000000 : ℝ)*(sp7) + (2800117427935337/100000000000000 : ℝ)*(f.failure) + (5737318410789853/100000000000000 : ℝ)*(f.sum) + (165726059716937/19095000000000000000000000000 : ℝ)*base65 + (36875581775449314847/1909500000000000000000000000000000 : ℝ)*base68 + (26942048360998314847/1909500000000000000000000000000000 : ℝ)*base70 + (13613666365210314847/1909500000000000000000000000000000 : ℝ)*base72 + (4009197115153/19095000000000000000000000000 : ℝ)*base74 + (2130202582396685153/1909500000000000000000000000000000 : ℝ)*base75 + (2879311590183185153/1909500000000000000000000000000000 : ℝ)*base77 + (24074300124536814847/1909500000000000000000000000000000 : ℝ)*base80 + (47068795766113/19095000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (54550677/10000000000000000000000 : ℝ)*base89 + (54550677/10000000000000000000000 : ℝ)*base91 + (54550677/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (386288601242756997341365049/39781250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (215681857/12500000000000 : ℝ)*(base19) + (29327111/1562500000000 : ℝ)*(base23) + (1558563/781250000000 : ℝ)*(upper3) + (34081977/50000000000000 : ℝ)*(lower4) + (51635049/25000000000000 : ℝ)*(upper5) + (268726351859239/6250000000000 : ℝ)*(major0) + (268726351859239/6250000000000 : ℝ)*(major1) + (268726351859239/6250000000000 : ℝ)*(major2) + (6944870959/20000000000000 : ℝ)*(sp1) + (18406840003/50000000000000 : ℝ)*(sp2) + (5778853899396633/100000000000000 : ℝ)*(sp4) + (5778817449586981/100000000000000 : ℝ)*(sp5) + (5778815208781523/100000000000000 : ℝ)*(sp6) + (282038903642173/10000000000000 : ℝ)*(sp7) + (282038903642173/10000000000000 : ℝ)*(f.failure) + (5778853899396633/100000000000000 : ℝ)*(f.sum) + (14287903820633/4773750000000000000000000000 : ℝ)*base66 + (661080007853941201/238687500000000000000000000000000 : ℝ)*base68 + (1572161676938753701/238687500000000000000000000000000 : ℝ)*base70 + (581831349904371299/238687500000000000000000000000000 : ℝ)*base71 + (97833017493361/9547500000000000000000000000 : ℝ)*base74 + (779927604962121299/238687500000000000000000000000000 : ℝ)*base75 + (772356919479691201/238687500000000000000000000000000 : ℝ)*base78 + (3096505728100816201/238687500000000000000000000000000 : ℝ)*base80 + (6099933928247/1193437500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (2444967/1000000000000000000000 : ℝ)*base90 + (2444967/1000000000000000000000 : ℝ)*base92 + (2444967/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1284_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152447821/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14749/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1093/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10993/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7341/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1284_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1284_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152447821/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8177/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1889/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10993/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7341/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1284_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1284_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1284_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152447821/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8177/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1889/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10993/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7341/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1284_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
